use super::*;

/// A single dynamic-section entry.
#[derive(Debug, Clone)]
#[allow(missing_docs)]
pub struct DynamicEntry {
    pub tag: u64,
    pub val: u64,
}

/// A parsed GNU hash table for fast dynamic-symbol lookup by name.
#[derive(Debug, Clone)]
#[allow(missing_docs)]
pub struct GnuHash {
    pub nbuckets: u32,
    pub symoffset: u32,
    pub bloom: Vec<u64>,
    pub buckets: Vec<u32>,
    pub chains: Vec<u32>,
}

/// A parsed ELF note (from `SHT_NOTE` or `PT_NOTE`).
#[derive(Debug, Clone)]
#[allow(missing_docs)]
pub struct Note {
    pub type_: u32,
    pub name: String,
    pub desc: Vec<u8>,
}

/// A single version-definition entry.
#[derive(Debug, Clone)]
#[allow(missing_docs)]
pub struct VerDef {
    pub ndx: u16,
    pub flags: u16,
    pub name: String,
}

/// A single version-need entry (a needed dependency with its version indexes).
#[derive(Debug, Clone)]
#[allow(missing_docs)]
pub struct VerNeed {
    pub file: String,
    pub versions: Vec<(u16, String)>,
}

/// A typed relocation kind. Both x86-64 and AArch64 constants are
/// represented; the machine type determines which variant is applicable.
// The variant names follow ELF-specified naming (R_X86_64_* / R_AARCH64_*).
#[allow(non_camel_case_types, missing_docs)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelTy {
    // x86-64
    R_X86_64_NONE,
    R_X86_64_64,
    R_X86_64_PC32,
    R_X86_64_GOT32,
    R_X86_64_PLT32,
    R_X86_64_COPY,
    R_X86_64_GLOB_DAT,
    R_X86_64_JUMP_SLOT,
    R_X86_64_RELATIVE,
    R_X86_64_GOTPCREL,
    R_X86_64_32,
    R_X86_64_32S,
    R_X86_64_16,
    R_X86_64_PC16,
    R_X86_64_8,
    R_X86_64_PC8,
    R_X86_64_DTPMOD64,
    R_X86_64_DTPOFF64,
    R_X86_64_TPOFF64,
    R_X86_64_TLSGD,
    R_X86_64_TLSLD,
    R_X86_64_DTPOFF32,
    R_X86_64_GOTTPOFF,
    R_X86_64_TPOFF32,
    R_X86_64_PC64,
    R_X86_64_GOTOFF64,
    R_X86_64_GOTPC32,
    R_X86_64_GOT64,
    R_X86_64_GOTPCREL64,
    R_X86_64_GOTPC64,
    R_X86_64_GOTPLT64,
    R_X86_64_PLTOFF64,
    R_X86_64_SIZE32,
    R_X86_64_SIZE64,
    R_X86_64_GOTPC32_TLSDESC,
    R_X86_64_TLSDESC_CALL,
    R_X86_64_TLSDESC,
    R_X86_64_IRELATIVE,
    // AArch64
    R_AARCH64_NONE,
    R_AARCH64_ABS64,
    R_AARCH64_ABS32,
    R_AARCH64_ABS16,
    R_AARCH64_PREL64,
    R_AARCH64_PREL32,
    R_AARCH64_PREL16,
    R_AARCH64_MOVW_UABS_G0,
    R_AARCH64_MOVW_UABS_G0_NC,
    R_AARCH64_MOVW_UABS_G1,
    R_AARCH64_MOVW_UABS_G1_NC,
    R_AARCH64_MOVW_UABS_G2,
    R_AARCH64_MOVW_UABS_G2_NC,
    R_AARCH64_MOVW_UABS_G3,
    R_AARCH64_ADR_PREL_PG_HI21,
    R_AARCH64_ADR_PREL_LO21,
    R_AARCH64_ADD_ABS_LO12_NC,
    R_AARCH64_LDST8_ABS_LO12_NC,
    R_AARCH64_LDST16_ABS_LO12_NC,
    R_AARCH64_LDST32_ABS_LO12_NC,
    R_AARCH64_LDST64_ABS_LO12_NC,
    R_AARCH64_LDST128_ABS_LO12_NC,
    R_AARCH64_CONDBR19,
    R_AARCH64_JUMP26,
    R_AARCH64_CALL26,
    R_AARCH64_TSTBR14,
    /// Catch-all for unknown relocation types.
    Other(u32),
}

impl RelTy {
    /// Convert a raw ELF relocation kind value to the typed representation.
    /// The caller must know the machine type (x86-64 vs AArch64) to interpret
    /// overlapping values correctly.
    pub fn from_kind(kind: u32) -> Self {
        match kind {
            0 => Self::R_X86_64_NONE,
            1 => Self::R_X86_64_64,
            2 => Self::R_X86_64_PC32,
            3 => Self::R_X86_64_GOT32,
            4 => Self::R_X86_64_PLT32,
            5 => Self::R_X86_64_COPY,
            6 => Self::R_X86_64_GLOB_DAT,
            7 => Self::R_X86_64_JUMP_SLOT,
            8 => Self::R_X86_64_RELATIVE,
            9 => Self::R_X86_64_GOTPCREL,
            10 => Self::R_X86_64_32,
            11 => Self::R_X86_64_32S,
            12 => Self::R_X86_64_16,
            13 => Self::R_X86_64_PC16,
            14 => Self::R_X86_64_8,
            15 => Self::R_X86_64_PC8,
            16 => Self::R_X86_64_DTPMOD64,
            17 => Self::R_X86_64_DTPOFF64,
            18 => Self::R_X86_64_TPOFF64,
            19 => Self::R_X86_64_TLSGD,
            20 => Self::R_X86_64_TLSLD,
            21 => Self::R_X86_64_DTPOFF32,
            22 => Self::R_X86_64_GOTTPOFF,
            23 => Self::R_X86_64_TPOFF32,
            24 => Self::R_X86_64_PC64,
            25 => Self::R_X86_64_GOTOFF64,
            26 => Self::R_X86_64_GOTPC32,
            27 => Self::R_X86_64_GOT64,
            28 => Self::R_X86_64_GOTPCREL64,
            29 => Self::R_X86_64_GOTPC64,
            30 => Self::R_X86_64_GOTPLT64,
            31 => Self::R_X86_64_PLTOFF64,
            32 => Self::R_X86_64_SIZE32,
            33 => Self::R_X86_64_SIZE64,
            34 => Self::R_X86_64_GOTPC32_TLSDESC,
            35 => Self::R_X86_64_TLSDESC_CALL,
            36 => Self::R_X86_64_TLSDESC,
            37 => Self::R_X86_64_IRELATIVE,
            // AArch64-specific values (257+). These don't overlap x86-64 (0-37).
            257 => Self::R_AARCH64_ABS64,
            258 => Self::R_AARCH64_ABS32,
            259 => Self::R_AARCH64_ABS16,
            260 => Self::R_AARCH64_PREL64,
            261 => Self::R_AARCH64_PREL32,
            262 => Self::R_AARCH64_PREL16,
            263 => Self::R_AARCH64_MOVW_UABS_G0,
            264 => Self::R_AARCH64_MOVW_UABS_G0_NC,
            265 => Self::R_AARCH64_MOVW_UABS_G1,
            266 => Self::R_AARCH64_MOVW_UABS_G1_NC,
            267 => Self::R_AARCH64_MOVW_UABS_G2,
            268 => Self::R_AARCH64_MOVW_UABS_G2_NC,
            269 => Self::R_AARCH64_MOVW_UABS_G3,
            274 => Self::R_AARCH64_ADR_PREL_LO21,
            275 => Self::R_AARCH64_ADR_PREL_PG_HI21,
            277 => Self::R_AARCH64_ADD_ABS_LO12_NC,
            278 => Self::R_AARCH64_LDST8_ABS_LO12_NC,
            279 => Self::R_AARCH64_CONDBR19,
            280 => Self::R_AARCH64_TSTBR14,
            282 => Self::R_AARCH64_JUMP26,
            283 => Self::R_AARCH64_CALL26,
            284 => Self::R_AARCH64_LDST16_ABS_LO12_NC,
            285 => Self::R_AARCH64_LDST32_ABS_LO12_NC,
            286 => Self::R_AARCH64_LDST64_ABS_LO12_NC,
            299 => Self::R_AARCH64_LDST128_ABS_LO12_NC,
            _ => Self::Other(kind),
        }
    }
}

impl Relocation {
    /// The typed relocation kind.
    pub fn ty(&self) -> RelTy {
        RelTy::from_kind(self.kind)
    }
}

// --- bounds-checked little-endian readers ----------------------------------

pub(crate) fn read_u16(bytes: &[u8], off: usize) -> Result<u16> {
    let b = bytes
        .get(off..off + 2)
        .ok_or_else(|| Error::parse("ELF: truncated (u16)"))?;
    Ok(u16::from_le_bytes([b[0], b[1]]))
}

pub(crate) fn read_u32(bytes: &[u8], off: usize) -> Result<u32> {
    let b = bytes
        .get(off..off + 4)
        .ok_or_else(|| Error::parse("ELF: truncated (u32)"))?;
    Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
}

pub(crate) fn read_u64(bytes: &[u8], off: usize) -> Result<u64> {
    let b = bytes
        .get(off..off + 8)
        .ok_or_else(|| Error::parse("ELF: truncated (u64)"))?;
    Ok(u64::from_le_bytes([
        b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
    ]))
}

pub(crate) fn read_i64(bytes: &[u8], off: usize) -> Result<i64> {
    let b = bytes
        .get(off..off + 8)
        .ok_or_else(|| Error::parse("ELF: truncated (i64)"))?;
    Ok(i64::from_le_bytes([
        b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
    ]))
}

/// Read a NUL-terminated string at byte offset `off` within a string table
/// `tab`. Returns an error if the offset is past the end of the table or if no
/// NUL terminator is found within the remaining bytes (the entire table is
/// treated as the well-formed region; a missing terminator is a parse error).
pub(crate) fn read_str(tab: &[u8], off: u32) -> Result<String> {
    let start = usize::try_from(off)
        .map_err(|_| Error::parse("ELF: string-table offset overflow"))?;
    if start > tab.len() {
        return Err(Error::parse("ELF: string offset past end of string table"));
    }
    let end = tab[start..]
        .iter()
        .position(|&c| c == 0)
        .ok_or_else(|| Error::parse("ELF: non-NUL-terminated string in string table"))?;
    let slice = &tab[start..start + end];
    Ok(String::from_utf8_lossy(slice).into_owned())
}

// --- helper: convert a u64 offset/size to usize with overflow check ---------

pub(crate) fn u64_to_usize(v: u64, what: &str) -> Result<usize> {
    usize::try_from(v).map_err(|_| {
        Error::parse(format!("ELF: {what} value {v} exceeds platform address space"))
    })
}

// --- section-header parsing support ----------------------------------------

/// A raw section header.
pub(crate) struct SecHdr {
    pub(crate) name_off: u32,
    pub(crate) sh_type: u32,
    pub(crate) flags: u64,
    pub(crate) addr: u64,
    pub(crate) offset: u64,
    pub(crate) size: u64,
    pub(crate) link: u32,
    pub(crate) info: u32,
    pub(crate) entsize: u64,
}

/// Read one section header at byte offset `base` within `bytes`.
pub(crate) fn read_sec_hdr(bytes: &[u8], base: usize) -> Result<SecHdr> {
    Ok(SecHdr {
        name_off: read_u32(bytes, base)?,
        sh_type: read_u32(bytes, base + 4)?,
        flags: read_u64(bytes, base + 8)?,
        addr: read_u64(bytes, base + 16)?,
        offset: read_u64(bytes, base + 24)?,
        size: read_u64(bytes, base + 32)?,
        link: read_u32(bytes, base + 40)?,
        info: read_u32(bytes, base + 44)?,
        entsize: read_u64(bytes, base + 56)?,
    })
}

// --- symbol-parsing support -------------------------------------------------

/// A raw symbol-table entry (ELF64: 24 bytes).
pub(crate) struct RawSym {
    pub(crate) st_name: u32,
    pub(crate) st_info: u8,
    pub(crate) st_shndx: u16,
    pub(crate) st_value: u64,
    pub(crate) st_size: u64,
}

/// Read one symbol-table entry at byte offset `base` within `bytes`.
pub(crate) fn read_sym(bytes: &[u8], base: usize) -> Result<RawSym> {
    Ok(RawSym {
        st_name: read_u32(bytes, base)?,
        st_info: *bytes.get(base + 4).ok_or_else(|| Error::parse("ELF: truncated symbol (info)"))?,
        st_shndx: read_u16(bytes, base + 6)?,
        st_value: read_u64(bytes, base + 8)?,
        st_size: read_u64(bytes, base + 16)?,
    })
}
