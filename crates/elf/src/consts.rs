pub(crate) const ELF_HEADER_LEN: usize = 64;
pub(crate) const SECTION_HEADER_LEN: usize = 64;
pub(crate) const PROGRAM_HEADER_LEN: usize = 56;
pub(crate) const SYM_ENTRY_LEN: u64 = 24;
pub(crate) const RELA_ENTRY_LEN: u64 = 24;
pub(crate) const REL_ENTRY_LEN: u64 = 8;

pub(crate) const SHT_SYMTAB: u32 = 2;
pub(crate) const SHT_HASH: u32 = 5;
pub(crate) const SHT_RELA: u32 = 4;
pub(crate) const SHT_REL: u32 = 9;
pub(crate) const SHT_NOBITS: u32 = 8;
pub(crate) const SHT_DYNAMIC: u32 = 6;
pub(crate) const SHT_NOTE: u32 = 7;
pub(crate) const SHT_GNU_HASH: u32 = 0x6ffffff6;
pub(crate) const SHT_GNU_VERDEF: u32 = 0x6ffffffd;
pub(crate) const SHT_GNU_VERNEED: u32 = 0x6ffffffe;
#[allow(dead_code)]
pub(crate) const SHT_GNU_VERSYM: u32 = 0x6ffffff0;

pub(crate) const SHF_WRITE: u64 = 0x1;
pub(crate) const SHF_EXECINSTR: u64 = 0x4;
pub(crate) const SHF_COMPRESSED: u64 = 0x800;

pub(crate) const STT_FUNC: u8 = 2;
#[allow(dead_code)]
pub(crate) const STT_OBJECT: u8 = 1;
pub(crate) const STT_GNU_IFUNC: u8 = 10;

#[allow(dead_code)]
pub(crate) const SHN_UNDEF: u16 = 0;
pub(crate) const SHN_XINDEX: u16 = 0xffff;

// --- Architecture-independent relocation type constants (x86-64) ---
#[allow(dead_code, missing_docs)]
pub mod r_x86_64 {
    pub const NONE: u32 = 0;
    pub const R_64: u32 = 1;
    pub const PC32: u32 = 2;
    pub const GOT32: u32 = 3;
    pub const PLT32: u32 = 4;
    pub const COPY: u32 = 5;
    pub const GLOB_DAT: u32 = 6;
    pub const JUMP_SLOT: u32 = 7;
    pub const RELATIVE: u32 = 8;
    pub const GOTPCREL: u32 = 9;
    pub const R_32: u32 = 10;
    pub const R_32S: u32 = 11;
    pub const R_16: u32 = 12;
    pub const PC16: u32 = 13;
    pub const R_8: u32 = 14;
    pub const PC8: u32 = 15;
    pub const DTPMOD64: u32 = 16;
    pub const DTPOFF64: u32 = 17;
    pub const TPOFF64: u32 = 18;
    pub const TLSGD: u32 = 19;
    pub const TLSLD: u32 = 20;
    pub const DTPOFF32: u32 = 21;
    pub const GOTTPOFF: u32 = 22;
    pub const TPOFF32: u32 = 23;
    pub const PC64: u32 = 24;
    pub const GOTOFF64: u32 = 25;
    pub const GOTPC32: u32 = 26;
    pub const GOT64: u32 = 27;
    pub const GOTPCREL64: u32 = 28;
    pub const GOTPC64: u32 = 29;
    pub const GOTPLT64: u32 = 30;
    pub const PLTOFF64: u32 = 31;
    pub const SIZE32: u32 = 32;
    pub const SIZE64: u32 = 33;
    pub const GOTPC32_TLSDESC: u32 = 34;
    pub const TLSDESC_CALL: u32 = 35;
    pub const TLSDESC: u32 = 36;
    pub const IRELATIVE: u32 = 37;
}
#[allow(dead_code, missing_docs)]
pub mod r_aarch64 {
    pub const NONE: u32 = 0;
    pub const ABS64: u32 = 257;
    pub const ABS32: u32 = 258;
    pub const ABS16: u32 = 259;
    pub const PREL64: u32 = 260;
    pub const PREL32: u32 = 261;
    pub const PREL16: u32 = 262;
    pub const MOVW_UABS_G0: u32 = 263;
    pub const MOVW_UABS_G0_NC: u32 = 264;
    pub const MOVW_UABS_G1: u32 = 265;
    pub const MOVW_UABS_G1_NC: u32 = 266;
    pub const MOVW_UABS_G2: u32 = 267;
    pub const MOVW_UABS_G2_NC: u32 = 268;
    pub const MOVW_UABS_G3: u32 = 269;
    pub const ADR_PREL_PG_HI21: u32 = 275;
    pub const ADR_PREL_LO21: u32 = 274;
    pub const ADD_ABS_LO12_NC: u32 = 277;
    pub const LDST8_ABS_LO12_NC: u32 = 278;
    pub const LDST16_ABS_LO12_NC: u32 = 284;
    pub const LDST32_ABS_LO12_NC: u32 = 285;
    pub const LDST64_ABS_LO12_NC: u32 = 286;
    pub const LDST128_ABS_LO12_NC: u32 = 299;
    pub const CONDBR19: u32 = 279;
    pub const JUMP26: u32 = 282;
    pub const CALL26: u32 = 283;
}

// --- Dynamic section tags (DT_*) ---
#[allow(dead_code, missing_docs)]
pub(crate) mod dt {
    pub(crate) const NULL: u64 = 0;
    pub(crate) const NEEDED: u64 = 1;
    pub(crate) const PLTRELSZ: u64 = 2;
    pub(crate) const PLTGOT: u64 = 3;
    pub(crate) const HASH: u64 = 4;
    pub(crate) const STRTAB: u64 = 5;
    pub(crate) const SYMTAB: u64 = 6;
    pub(crate) const RELA: u64 = 7;
    pub(crate) const RELASZ: u64 = 8;
    pub(crate) const RELAENT: u64 = 9;
    pub(crate) const STRSZ: u64 = 10;
    pub(crate) const SYMENT: u64 = 11;
    pub(crate) const INIT: u64 = 12;
    pub(crate) const FINI: u64 = 13;
    pub(crate) const SONAME: u64 = 14;
    pub(crate) const RPATH: u64 = 15;
    pub(crate) const SYMBOLIC: u64 = 16;
    pub(crate) const REL: u64 = 17;
    pub(crate) const RELSZ: u64 = 18;
    pub(crate) const RELENT: u64 = 19;
    pub(crate) const PLTREL: u64 = 20;
    pub(crate) const DEBUG: u64 = 21;
    pub(crate) const TEXTREL: u64 = 22;
    pub(crate) const JMPREL: u64 = 23;
    pub(crate) const BIND_NOW: u64 = 24;
    pub(crate) const INIT_ARRAY: u64 = 25;
    pub(crate) const FINI_ARRAY: u64 = 26;
    pub(crate) const INIT_ARRAYSZ: u64 = 27;
    pub(crate) const FINI_ARRAYSZ: u64 = 28;
    pub(crate) const RUNPATH: u64 = 29;
    pub(crate) const FLAGS: u64 = 30;
    pub(crate) const PREINIT_ARRAY: u64 = 32;
    pub(crate) const PREINIT_ARRAYSZ: u64 = 33;
    pub(crate) const SYMTAB_SHNDX: u64 = 34;
    pub(crate) const GNU_HASH: u64 = 0x6ffffef5;
    pub(crate) const VERDEF: u64 = 0x6ffffffc;
    pub(crate) const VERNEED: u64 = 0x6ffffffe;
    pub(crate) const VERSYM: u64 = 0x6ffffff0;
}
