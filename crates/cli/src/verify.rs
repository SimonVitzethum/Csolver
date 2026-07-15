use super::*;

/// Dispatch a path to the appropriate frontend, then verify.
#[allow(clippy::too_many_arguments)]
pub(crate) fn verify_path(
    path: &Path,
    json: bool,
    closed_world: bool,
    bug_finding: bool,
    assume_valid_params: bool,
    assume_valid_returns: bool,
    assume_valid_loop_ptrs: bool,
    assume_param_buffer_len: bool,
    assume_struct_tail: bool,
    assume_valid_mmio: bool,
    assume_field_invariants: bool,
    aliasing_model: bool,
    pre_file: Option<&Path>,
    entry_patterns: Option<Vec<String>>,
) -> Result<ExitCode, String> {
    // Turnkey: a `.rs` file is compiled to MIR by us, then verified with a
    // coverage report — the user does not hand-run rustc.
    if path.extension().and_then(|e| e.to_str()) == Some("rs") {
        return verify_rust_source(path, json);
    }
    // An ISO 9660 image (`.iso` or the `CD001` magic): a *container* — enumerate the
    // object files inside (UEFI `.efi`/PE, loose `.exe`/`.dll`, ELF) and verify each.
    if path.extension().and_then(|e| e.to_str()) == Some("iso")
        || read_head(path, 0x8006).is_ok_and(|h| csolver_elf::iso::is_iso(&h))
    {
        return verify_iso(path, json, bug_finding, assume_valid_params);
    }
    // A WIM image (`.wim`/`.esd` or the `MSWIM` magic): a *container* holding a
    // deduplicated pool of file resources — decompress each and verify the object files.
    if matches!(path.extension().and_then(|e| e.to_str()), Some("wim") | Some("esd"))
        || read_head(path, 208).is_ok_and(|h| csolver_elf::wim::is_wim(&h))
    {
        return verify_wim(path, json, bug_finding, assume_valid_params);
    }
    let level = detect_level(path)?;
    // LLVM/MIR are mature; an ELF object is decoded via `csolver-asm` (x86-64 /
    // AArch64) and verified; the textual `.s` frontend is still a stub (reports its
    // honest status rather than pretending to have analyzed the input).
    let lowering = match level {
        SourceLevel::Llvm => {
            use csolver_ir::Frontend;
            let source = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
            if let Some(hint) = llvm_attribute_hint(&source) {
                eprintln!("{hint}");
            }
            csolver_llvm::LlvmFrontend.lower(csolver_llvm::LlvmInput {
                source,
                name: path.display().to_string(),
            })
        }
        SourceLevel::Asm => {
            use csolver_ir::Frontend;
            let source = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
            // Auto-detect x86 (AT&T/Intel) vs. AArch64 and the syntax from the source.
            let (arch, syntax) = csolver_asm::detect(&source);
            csolver_asm::AsmFrontend.lower(csolver_asm::AsmInput { source, arch, syntax })
        }
        SourceLevel::Elf => {
            let bytes = std::fs::read(path).map_err(|e| e.to_string())?;
            lower_elf(&bytes)
        }
        SourceLevel::Mir => {
            use csolver_ir::Frontend;
            let source = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
            csolver_mir::MirFrontend.lower(csolver_mir::MirInput {
                source,
                name: path.display().to_string(),
            })
        }
    };

    match lowering {
        Ok(mut module) => {
            // Apply an opt-in precondition sidecar before verification.
            if let Some(pf) = pre_file {
                let text = std::fs::read_to_string(pf).map_err(|e| e.to_string())?;
                let preconds = csolver_verifier::precond::parse(&text)?;
                let n = csolver_verifier::precond::apply(&mut module, &preconds)?;
                if !json {
                    eprintln!("applied {n} precondition(s) from {}", pf.display());
                }
            }
            let config = Config {
                level,
                closed_world,
                bug_finding,
                assume_valid_params,
                assume_valid_returns,
                assume_valid_loop_ptrs,
                assume_param_buffer_len,
                assume_struct_tail,
                assume_valid_mmio,
                assume_field_invariants,
                aliasing_model,
                entry_patterns,
                ..Config::default()
            };
            let report = verify_module(&module, &config);
            emit(&report, json);
            Ok(verdict_code(report.verdict))
        }
        Err(e) => {
            // A frontend that cannot lower yields a tool error, not a verdict.
            Err(format!(
                "could not analyze {} at level {level}: {e}\n\
                 hint: try `solver demo` to exercise the verifier on built-in MSIR",
                path.display()
            ))
        }
    }
}

/// Heuristic function discovery for a **stripped** x86-64 image: scan each executable
/// section for function prologues — `endbr64` (F3 0F 1E FA, opens CET-built functions)
/// and `push rbp; mov rbp, rsp` (55 48 89 E5) — and synthesize a function at each
/// (sized to the next candidate or the section end; recursive-descent decode stops at
/// its `ret`, so the overshoot is harmless). Deduped against existing symbol addresses.
/// Sound: a spurious start only produces an UNKNOWN function.
fn discover_x86_functions(image: &csolver_elf::Image, bytes: &[u8]) -> Vec<csolver_elf::Symbol> {
    const MAX_DISCOVERED: usize = 20_000;
    let known: std::collections::HashSet<u64> = image.symbols.iter().map(|s| s.address).collect();
    let mut out: Vec<csolver_elf::Symbol> = Vec::new();
    for (si, sec) in image.sections.iter().enumerate() {
        if !sec.executable || !sec.has_data || sec.size == 0 {
            continue;
        }
        let start = sec.file_offset as usize;
        let end = (start + sec.size as usize).min(bytes.len());
        let Some(data) = bytes.get(start..end) else { continue };
        // Collect candidate offsets (section-relative) at a prologue pattern.
        let mut starts: Vec<u64> = Vec::new();
        let mut i = 0usize;
        while i + 4 <= data.len() {
            let endbr = data[i..i + 4] == [0xf3, 0x0f, 0x1e, 0xfa];
            let frame = data[i..i + 4] == [0x55, 0x48, 0x89, 0xe5];
            if endbr || frame {
                starts.push(sec.address + i as u64);
                i += 4;
            } else {
                i += 1;
            }
            if starts.len() >= MAX_DISCOVERED {
                break;
            }
        }
        // Size each candidate to the next one (or the section end).
        for k in 0..starts.len() {
            let addr = starts[k];
            if known.contains(&addr) {
                continue;
            }
            let next = starts.get(k + 1).copied().unwrap_or(sec.address + sec.size);
            out.push(csolver_elf::Symbol {
                name: format!("fn_{addr:x}"),
                address: addr,
                size: next.saturating_sub(addr),
                is_function: true,
                section_index: si as u16,
            });
        }
    }
    out
}

/// Read the first `n` bytes of `path` (for a magic sniff that needs more than the
/// 4-byte header — e.g. ISO 9660's `CD001` at offset 0x8001).
fn read_head(path: &Path, n: usize) -> Result<Vec<u8>, String> {
    use std::io::Read;
    let mut f = std::fs::File::open(path).map_err(|e| e.to_string())?;
    let mut buf = vec![0u8; n];
    let read = f.read(&mut buf).map_err(|e| e.to_string())?;
    buf.truncate(read);
    Ok(buf)
}

/// Verify every **object file inside an ISO 9660 image** — a container the pipeline
/// unpacks: enumerate its files, and for each whose bytes carry an ELF / PE / Mach-O
/// magic, decode and verify it (UEFI `.efi` boot apps are PE, so a boot/install image's
/// binaries are analysed this way). Prints a per-file verdict; the exit code is the
/// worst verdict over all analysed files.
fn verify_iso(path: &Path, json: bool, bug_finding: bool, assume_valid_params: bool) -> Result<ExitCode, String> {
    let bytes = std::fs::read(path).map_err(|e| e.to_string())?;
    // An ISO may be a plain ISO 9660, a UDF volume, or a **hybrid** (every Windows install ISO:
    // the ISO 9660 side is a stub, the real files live in UDF). Gather from both readers and
    // deduplicate by byte offset, so a boot `.efi`/`.exe` is found wherever it is stored.
    let mut files = csolver_elf::iso::list_files(&bytes).unwrap_or_default();
    if csolver_elf::udf::is_udf(&bytes) {
        if let Ok(udf_files) = csolver_elf::udf::list_files(&bytes) {
            files.extend(udf_files.into_iter().map(|u| csolver_elf::iso::IsoFile {
                path: u.path,
                offset: u.offset,
                size: u.size,
            }));
        }
    }
    files.sort_by_key(|f| f.offset);
    files.dedup_by_key(|f| f.offset);
    if files.is_empty() {
        return Err("no ISO 9660 or UDF files found in the image".to_string());
    }
    let (mut any_fail, mut any_unknown, mut analyzed) = (false, false, 0usize);
    let mut lines: Vec<String> = Vec::new();
    for f in &files {
        let end = f.offset.saturating_add(f.size).min(bytes.len());
        let Some(slice) = bytes.get(f.offset..end) else { continue };
        if csolver_elf::detect_format(slice).is_none() {
            continue; // not an object file — skip (data/resource/boot-catalog)
        }
        analyzed += 1;
        match lower_elf(slice) {
            Ok(module) => {
                let config = Config {
                    level: SourceLevel::Elf,
                    bug_finding,
                    assume_valid_params,
                    ..Config::default()
                };
                let report = verify_module(&module, &config);
                match report.verdict {
                    Verdict::Fail => any_fail = true,
                    Verdict::Unknown => any_unknown = true,
                    Verdict::Pass => {}
                }
                lines.push(format!("  {:<44} {:?}  ({} fn)", f.path, report.verdict, module.functions.len()));
            }
            Err(e) => lines.push(format!("  {:<44} not analyzed: {e}", f.path)),
        }
    }
    if !json {
        eprintln!(
            "ISO {}: {} file(s), {} object file(s) analysed",
            path.display(),
            files.len(),
            analyzed
        );
        for l in &lines {
            eprintln!("{l}");
        }
    }
    let worst = if any_fail {
        Verdict::Fail
    } else if any_unknown {
        Verdict::Unknown
    } else {
        Verdict::Pass
    };
    Ok(verdict_code(worst))
}

/// Verify every **object file inside a WIM image** — a Windows imaging container
/// (`install.wim` / `boot.wim`). Its file contents live as a deduplicated pool of
/// resources: decompress each (XPRESS chunks; a raw chunk is copied; LZX/LZMS resources
/// are reported as not-decoded, never fabricated) and, for each whose bytes carry an
/// ELF / PE / Mach-O magic, decode and verify it. The exit code is the worst verdict.
fn verify_wim(path: &Path, json: bool, bug_finding: bool, assume_valid_params: bool) -> Result<ExitCode, String> {
    let bytes = std::fs::read(path).map_err(|e| e.to_string())?;
    let resources = csolver_elf::wim::data_resources(&bytes).map_err(|e| e.to_string())?;
    let (mut any_fail, mut any_unknown, mut analyzed, mut skipped_compressed) = (false, false, 0usize, 0usize);
    let mut lines: Vec<String> = Vec::new();
    for (i, entry) in resources.iter().enumerate() {
        let blob = match csolver_elf::wim::extract(&bytes, entry) {
            Ok(b) => b,
            Err(_) => {
                // LZX/LZMS or a malformed resource — cannot read its bytes, so cannot verify.
                skipped_compressed += 1;
                continue;
            }
        };
        if csolver_elf::detect_format(&blob).is_none() {
            continue; // not an object file — a data file / registry hive / etc.
        }
        analyzed += 1;
        let label = format!("resource #{i} ({} bytes)", blob.len());
        match lower_elf(&blob) {
            Ok(module) => {
                let config = Config {
                    level: SourceLevel::Elf,
                    bug_finding,
                    assume_valid_params,
                    ..Config::default()
                };
                let report = verify_module(&module, &config);
                match report.verdict {
                    Verdict::Fail => any_fail = true,
                    Verdict::Unknown => any_unknown = true,
                    Verdict::Pass => {}
                }
                lines.push(format!("  {:<44} {:?}  ({} fn)", label, report.verdict, module.functions.len()));
            }
            Err(e) => lines.push(format!("  {label:<44} not analyzed: {e}")),
        }
    }
    if !json {
        eprintln!(
            "WIM {}: {} resource(s), {} object file(s) analysed, {} compressed resource(s) skipped",
            path.display(),
            resources.len(),
            analyzed,
            skipped_compressed
        );
        for l in &lines {
            eprintln!("{l}");
        }
    }
    let worst = if any_fail {
        Verdict::Fail
    } else if any_unknown {
        Verdict::Unknown
    } else {
        Verdict::Pass
    };
    Ok(verdict_code(worst))
}

/// Lower an ELF object/binary to MSIR: parse it (`csolver-elf`), then decode each
/// defined function symbol's `.text` bytes with the machine-code decoder for the
/// object's architecture (`csolver-asm`) and link them into one whole-program module.
/// So `solver verify <elf>` analyses a compiled binary with no source — lower precision
/// than the LLVM path (flat byte memory, no types), but real. `Unsupported` when the
/// architecture is not decodable or the object has no sized function symbols.
pub(crate) fn lower_elf(bytes: &[u8]) -> csolver_core::Result<csolver_ir::Module> {
    use std::collections::HashMap;
    // Any supported object format (ELF / PE-Windows / Mach-O-macOS) → the common Image,
    // then the SAME per-architecture decode + verify. Relocations are ELF-specific (a
    // PE/Mach-O image carries none in `relocations`), so the RIP-relative global
    // resolution below simply finds nothing there and those accesses stay opaque —
    // sound, and everything else (stack/register/param reasoning) is unchanged.
    let mut image = csolver_elf::load_object(bytes)?;
    if !matches!(image.machine, csolver_elf::EM_X86_64 | csolver_elf::EM_AARCH64) {
        return Err(csolver_core::Error::unsupported(format!(
            "object machine {} is not decodable (only x86-64 and AArch64)",
            image.machine
        )));
    }
    // Stripped binary (no symbol table, no exports — only maybe an entry point):
    // discover functions heuristically by scanning executable sections for x86-64
    // prologues (`endbr64`, `push rbp; mov rbp, rsp`). Each candidate is decoded
    // independently (recursive descent stops at its `ret`), so a spurious start only
    // yields an UNKNOWN function, never a false PASS of another.
    if image.functions().count() <= 1 && image.machine == csolver_elf::EM_X86_64 {
        let discovered = discover_x86_functions(&image, bytes);
        image.symbols.extend(discovered);
    }
    // The offset a PC-relative relocation addresses *within* its target symbol:
    // `addend + 4` (the disp32 is measured from the end of its own 4 bytes). Only
    // the direct PC-relative kinds — a GOT-indirect access reads a pointer *to* the
    // symbol, a different shape, so it stays an opaque access.
    let pcrel_off = |r: &csolver_elf::Relocation| -> Option<i64> {
        // R_X86_64_PC32=2, PLT32=4, GOTPCRELX=41, REX_GOTPCRELX=42 (relaxed to direct).
        matches!(r.kind, 2 | 4 | 41 | 42).then(|| r.addend + 4)
    };
    // Global regions the RIP-relative accesses resolve to (name → size/writability).
    let mut globals: HashMap<String, csolver_ir::GlobalDef> = HashMap::new();
    // A PE (Windows) / Mach-O (macOS) linked image carries no per-instruction
    // relocations: a `[rip + disp32]` is *self*-relative, so a global access is resolved
    // from the section table (target VA = function VA + disp position + 4 + disp32) to the
    // CONTAINING SECTION — register every section as a global region up front so the
    // executor can seed it. Section-wide bounds are looser than a per-symbol size (a recall
    // loss), but always contain the target — sound (never a false PASS). ELF keeps its
    // precise per-symbol relocation resolution below.
    let self_relative = image.relocations.is_empty();
    if self_relative {
        for s in &image.sections {
            if !s.name.is_empty() && s.size > 0 && !s.executable {
                globals.entry(s.name.clone()).or_insert(csolver_ir::GlobalDef {
                    size: s.size,
                    align: 1,
                    writable: s.writable,
                });
            }
        }
    }
    let mut modules: Vec<csolver_ir::Module> = Vec::new();
    for sym in image.functions() {
        let Some(code) = image.function_code(sym, bytes) else { continue };
        let sec_addr = image.sections.get(sym.section_index as usize).map_or(0, |s| s.address);
        let func_off = sym.address.saturating_sub(sec_addr); // function start within its section
        // Relocations patching this function's section (by `sh_info`).
        let relocs: Vec<&csolver_elf::Relocation> = image
            .relocations
            .iter()
            .filter(|(patched, _)| *patched == sym.section_index as usize)
            .flat_map(|(_, rs)| rs.iter())
            .collect();
        // Register every resolvable target global (known size) so the executor seeds it.
        for r in &relocs {
            if pcrel_off(r).is_some() {
                if let Some(t) = image.symbols.get(r.symbol as usize) {
                    if t.size > 0 && !t.name.is_empty() {
                        let writable =
                            image.sections.get(t.section_index as usize).is_none_or(|s| s.writable);
                        globals.entry(t.name.clone()).or_insert(csolver_ir::GlobalDef {
                            size: t.size,
                            align: 1,
                            writable,
                        });
                    }
                }
            }
        }
        // Map a function-relative disp32 position to (target global, offset-within-it).
        let resolve = |disp_pos: usize| -> Option<(String, i64)> {
            // ELF: a per-symbol relocation gives the exact target and addend.
            if !self_relative {
                let at = func_off + disp_pos as u64;
                let r = relocs.iter().find(|r| r.offset == at)?;
                let off = pcrel_off(r)?;
                let t = image.symbols.get(r.symbol as usize)?;
                return (t.size > 0 && !t.name.is_empty()).then(|| (t.name.clone(), off));
            }
            // PE/Mach-O linked image: the disp32 is self-relative. target VA = function VA
            // + (disp position + 4) + disp32. The `+4` is exact for `lea`/loads/reg-stores
            // (no trailing immediate — the size-critical, pointer-forming cases); a direct
            // store with an immediate undershoots but stays in the same section. Resolve to
            // the containing section (registered above).
            let disp = i32::from_le_bytes(code.get(disp_pos..disp_pos + 4)?.try_into().ok()?) as i64;
            let target = (sym.address as i64).checked_add(disp_pos as i64 + 4 + disp)?;
            let target = u64::try_from(target).ok()?;
            let sec = image.section_at(target)?;
            (!sec.name.is_empty() && !sec.executable)
                .then(|| (sec.name.clone(), (target - sec.address) as i64))
        };
        // Map a `call rel32`'s disp32 position to the callee's symbol name. Unlike `resolve`
        // this accepts a size-0 *undefined* symbol — an imported `malloc`/`free`/`copy_from_user`
        // has no size in the object, but a call target is a function, not a sized data region.
        // (ELF only: a PE/Mach-O direct call needs a VA→symbol map, left opaque for now.)
        let resolve_call = |disp_pos: usize| -> Option<String> {
            if self_relative {
                return None;
            }
            let at = func_off + disp_pos as u64;
            let r = relocs.iter().find(|r| r.offset == at)?;
            let t = image.symbols.get(r.symbol as usize)?;
            (!t.name.is_empty()).then(|| t.name.clone())
        };
        let m = match image.machine {
            csolver_elf::EM_X86_64 => csolver_asm::x86::decode_function_reloc(&sym.name, code, &resolve, &resolve_call),
            _ => csolver_asm::arm64::decode_function(&sym.name, code),
        };
        modules.push(m);
    }
    if modules.is_empty() {
        return Err(csolver_core::Error::unsupported(
            "ELF: no decodable function symbols (need a symbol table with sized functions)",
        ));
    }
    let mut m = csolver_ir::merge_modules(modules, "elf");
    m.globals = globals;
    // DWARF `.debug_info`: recover each pointer parameter's pointee byte size, which the
    // machine code alone cannot supply. Installed as `raw_ptr_hints` (like the LLVM/DWARF
    // path) — applied only under the opt-in `--assume-valid-params`, where a pointer
    // parameter becomes a valid region of that size (a prove-only `param-valid` assumption).
    let pointee = csolver_elf::parameter_pointee_sizes(&image, bytes);
    for f in &m.functions {
        if let Some(sizes) = pointee.get(&f.name) {
            for (i, sz) in sizes.iter().enumerate() {
                if let Some(size) = sz.filter(|s| *s > 0) {
                    let align = 1u32 << size.trailing_zeros().min(4);
                    m.raw_ptr_hints.insert((f.id, i as u32), (size, align));
                }
            }
        }
    }
    // Model the memory effect of a direct call to a contracted API (allocator / free /
    // user-copy) instead of leaving it an opaque havoc — the biggest binary-vs-LLVM recall gap.
    apply_binary_call_contracts(&mut m);
    Ok(m)
}

/// Rewrite each decoded direct call to a **contracted API** (allocator / deallocator /
/// user-copy) into the memory-effect MSIR the LLVM front-end emits for the same call, so the
/// binary path models a heap allocation / free / user-copy instead of an opaque call. The
/// call carries the SysV argument registers as its args (see the decoder's `named_call`), so a
/// contract's `arg<k>` reads the k-th of them, and `rax` is its result. Only the memory
/// effects (`Alloc`/`Free`/`Write`/`Read`) are applied; provenance/capability effects need the
/// label machinery the binary path does not reconstruct, and a `Product` size needs a temp
/// the flat decode has no allocator for — those leave the (named, still-summarisable) call in
/// place: sound, only less precise. Reuses the same `crates/contracts` data as the LLVM path.
fn apply_binary_call_contracts(m: &mut csolver_ir::Module) {
    use csolver_contracts::{Contracts, Effect, Fill, ReadSink, SizeExpr};
    use csolver_core::RegionKind;
    use csolver_ir::{Callee, Inst, MemKind, Operand, Type};
    static CONTRACTS: std::sync::OnceLock<Contracts> = std::sync::OnceLock::new();
    let contracts = CONTRACTS.get_or_init(Contracts::defaults);
    // A size that references only arguments / constants; a `Product` needs a temp register
    // the flat decode cannot allocate, so it is treated as unresolvable (the call is kept).
    let size_op = |size: &SizeExpr, args: &[Operand]| -> Option<Operand> {
        match size {
            SizeExpr::Arg(i) => args.get(*i).cloned(),
            SizeExpr::Const(n) => Some(Operand::int(64, *n as u128)),
            SizeExpr::Product(..) => None,
        }
    };
    for f in &mut m.functions {
        for b in &mut f.blocks {
            let mut out = Vec::with_capacity(b.insts.len());
            for inst in std::mem::take(&mut b.insts) {
                let Inst::Call { dst, callee: Callee::Symbol(name), args, .. } = &inst else {
                    out.push(inst);
                    continue;
                };
                let Some(contract) = contracts.lookup(name) else {
                    out.push(inst);
                    continue;
                };
                let mut effects = Vec::new();
                for effect in &contract.effects {
                    match effect {
                        Effect::Alloc { size, align, external } => {
                            if let (Some(d), Some(count)) = (*dst, size_op(size, args)) {
                                let region = if *external { RegionKind::Global } else { RegionKind::Heap };
                                effects.push(Inst::Alloc { dst: d, region, elem: Type::int(8), count, align: *align });
                            }
                        }
                        Effect::Free { ptr } => {
                            if let Some(a) = args.get(*ptr) {
                                effects.push(Inst::Dealloc { region: RegionKind::Heap, ptr: a.clone() });
                            }
                        }
                        Effect::Write { ptr, len, fill, from } => {
                            if let (Some(a), Some(len)) = (args.get(*ptr), size_op(len, args)) {
                                let kind = match fill { Fill::User => MemKind::UserFill, Fill::Undef => MemKind::Set };
                                let src = from.and_then(|k| args.get(k)).cloned();
                                effects.push(Inst::MemIntrinsic { kind, dst: a.clone(), src, len });
                            }
                        }
                        Effect::Read { ptr, len, sink } => {
                            if let (Some(a), Some(len)) = (args.get(*ptr), size_op(len, args)) {
                                let kind = match sink { ReadSink::Internal => MemKind::Set, ReadSink::User => MemKind::UserDrain };
                                effects.push(Inst::MemIntrinsic { kind, dst: a.clone(), src: None, len });
                            }
                        }
                        _ => {} // provenance / capability / typestate — not modelled in the binary path
                    }
                }
                if effects.is_empty() {
                    out.push(inst); // no applicable memory effect — keep the (named) call
                } else {
                    out.extend(effects);
                }
            }
            b.insts = out;
        }
    }
}

/// Turnkey: compile a `.rs` file to MIR ourselves, verify it, and print a
/// coverage report. The coverage report lifts the never-silently-skip discipline
/// of the inner layers to the whole file: a function that failed to emit or lower
/// is reported, not folded into a flattering "everything checked". A turnkey user
/// looks less, so the tool must say what it did *not* verify — loudly.
pub(crate) fn verify_rust_source(path: &Path, json: bool) -> Result<ExitCode, String> {
    use csolver_ir::Frontend;
    let mir = emit_mir(path)?;
    let module = csolver_mir::MirFrontend
        .lower(csolver_mir::MirInput { source: mir, name: path.display().to_string() })
        .map_err(|e| format!("could not lower the emitted MIR of {}: {e}", path.display()))?;
    let config = Config { level: SourceLevel::Mir, ..Config::default() };
    let report = verify_module(&module, &config);
    if !json {
        eprint!("{}", render_coverage(path, &module, &report));
    }
    emit(&report, json);
    Ok(verdict_code(report.verdict))
}

/// Emit a `.rs` file's MIR text. Prefers `+nightly -Z mir-include-spans` so
/// obligations carry a source `FILE:LINE:COL`; falls back to stable (no spans)
/// when nightly is unavailable — the same graceful degradation the span parser
/// uses. A genuine compile error (stable also fails) is surfaced, never swallowed.
pub(crate) fn emit_mir(path: &Path) -> Result<String, String> {
    let base = ["--edition", "2021", "--crate-type=lib", "--emit=mir", "-o", "-"];
    let mut last_err = String::new();
    // Nightly first (with source spans), then stable.
    for nightly in [true, false] {
        let mut cmd = std::process::Command::new("rustc");
        if nightly {
            cmd.arg("+nightly");
        }
        cmd.args(base);
        if nightly {
            cmd.arg("-Zmir-include-spans");
        }
        match cmd.arg(path).output() {
            Ok(o) if o.status.success() => {
                return String::from_utf8(o.stdout)
                    .map_err(|_| "rustc emitted non-UTF-8 MIR".to_string());
            }
            Ok(o) => last_err = String::from_utf8_lossy(&o.stderr).trim().to_string(),
            Err(e) => last_err = format!("could not run rustc: {e}"),
        }
    }
    Err(format!("could not compile {} to MIR:\n{last_err}", path.display()))
}

/// A crate-/file-level coverage report: how many functions were found, how many
/// verified (and to what), and — the point — how many were **not analyzed**, named
/// individually. A `PASS` verdict on the analyzed set means nothing if a fifth of
/// the functions silently never reached the analyzer.
pub(crate) fn render_coverage(
    path: &Path,
    module: &csolver_ir::Module,
    report: &csolver_verifier::ModuleReport,
) -> String {
    use std::fmt::Write as _;
    let not_analyzed = &module.unanalyzed;
    let analyzed = module.functions.len();
    let found = analyzed + not_analyzed.len();
    let pass = report.count(Verdict::Pass);
    let fail = report.count(Verdict::Fail);
    // Total UNKNOWN includes the not-analyzed (they verify as UNKNOWN); split them
    // so "unknown but analyzed" is not confused with "never analyzed".
    let unknown_analyzed = report.count(Verdict::Unknown).saturating_sub(not_analyzed.len());

    let mut s = String::new();
    let _ = writeln!(s, "coverage {}: {found} function(s) found", path.display());
    if found == 0 {
        let _ = writeln!(
            s,
            "  WARNING: MIR emitted but 0 functions found — an emission or parse gap; \
             nothing was verified, so a PASS here would be meaningless."
        );
        return s;
    }
    let _ = writeln!(s, "  analyzed {analyzed}: {pass} PASS, {fail} FAIL, {unknown_analyzed} UNKNOWN");
    if not_analyzed.is_empty() {
        let _ = writeln!(s, "  not analyzed: 0 — every function found was analyzed");
    } else {
        let _ = writeln!(
            s,
            "  NOT ANALYZED {} (could not lower/parse — NOT covered by the verdict):",
            not_analyzed.len()
        );
        for (name, reason) in not_analyzed {
            let _ = writeln!(s, "    - {name}: {reason}");
        }
    }
    s
}

/// A hint when a `.ll` input carries pointer parameters but no
/// `dereferenceable` attributes — the signature of rustc's *debug* emission,
/// which omits the parameter attributes the provenance analysis feeds on.
/// Measured: oorandom verifies 14/14 PASS on attributed IR vs 25/29 on debug
/// IR; the verdicts on unattributed IR are sound but much more conservative.
/// Advisory only: it never changes a verdict, only tells the user why so many
/// obligations may come back UNKNOWN and how to emit richer input.
pub(crate) fn llvm_attribute_hint(source: &str) -> Option<&'static str> {
    let has_ptr_params = source.lines().any(|l| {
        l.starts_with("define") && (l.contains("(ptr") || l.contains(", ptr") || l.contains(" ptr %"))
    });
    let has_attrs = source.contains("dereferenceable");
    (has_ptr_params && !has_attrs).then_some(
        "note: this IR has pointer parameters but no `dereferenceable` attributes \
         (rustc's debug emission omits them).\n\
         note: pointer-heavy code will verify mostly UNKNOWN without them — emit with\n\
         note:   rustc --emit=llvm-ir -O -C no-prepopulate-passes\n\
         note: to keep the attributes without LLVM optimization passes.",
    )
}

/// Decide which level an input is, by extension / magic bytes.
pub(crate) fn detect_level(path: &Path) -> Result<SourceLevel, String> {
    if path.is_dir() || path.join("Cargo.toml").is_file() {
        return Ok(SourceLevel::Mir);
    }
    match path.extension().and_then(|e| e.to_str()) {
        Some("ll") => Ok(SourceLevel::Llvm),
        Some("mir") => Ok(SourceLevel::Mir),
        Some("s" | "asm" | "S") => Ok(SourceLevel::Asm),
        // A Windows import library / object may be `.lib`/`.obj`; macOS `.dylib`/`.o`.
        // These and any extensionless binary are sniffed by magic below.
        _ => {
            // Sniff the object-file magic (ELF / PE-Windows / Mach-O-macOS). `SourceLevel::Elf`
            // now names the whole binary path (the loader dispatches on the real format).
            let magic = read_magic(path)?;
            if csolver_elf::detect_format(&magic).is_some() {
                Ok(SourceLevel::Elf)
            } else {
                Err(format!(
                    "cannot determine input type of {} (expected .ll, .s, or an ELF/PE/Mach-O binary, or a crate dir)",
                    path.display()
                ))
            }
        }
    }
}

pub(crate) fn read_magic(path: &Path) -> Result<[u8; 4], String> {
    use std::io::Read;
    let mut file = std::fs::File::open(path).map_err(|e| e.to_string())?;
    let mut buf = [0u8; 4];
    match file.read_exact(&mut buf) {
        Ok(()) => Ok(buf),
        Err(_) => Ok([0; 4]),
    }
}

pub(crate) fn emit(report: &csolver_verifier::ModuleReport, json: bool) {
    if json {
        println!("{}", render_json(report));
    } else {
        print!("{}", render_text(report));
    }
}

pub(crate) fn verdict_code(verdict: Verdict) -> ExitCode {
    match verdict {
        Verdict::Pass => ExitCode::from(0),
        Verdict::Fail => ExitCode::from(1),
        Verdict::Unknown => ExitCode::from(2),
    }
}
