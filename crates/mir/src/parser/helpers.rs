use super::*;

pub(crate) fn is_bb(w: &str) -> bool {
    w.strip_prefix("bb").is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
}

pub(crate) fn bb_index(w: &str) -> Option<usize> {
    w.strip_prefix("bb").and_then(|n| n.parse().ok())
}

pub(crate) fn bin_kind(w: &str) -> Option<BinKind> {
    Some(match w {
        "Add" => BinKind::Add,
        "Sub" => BinKind::Sub,
        "Mul" => BinKind::Mul,
        "Lt" => BinKind::Lt,
        "Le" => BinKind::Le,
        "Gt" => BinKind::Gt,
        "Ge" => BinKind::Ge,
        "Eq" => BinKind::Eq,
        "Ne" => BinKind::Ne,
        "BitAnd" => BinKind::BitAnd,
        "BitOr" => BinKind::BitOr,
        "BitXor" => BinKind::BitXor,
        // A modelled-as-opaque arithmetic op (Div/Rem/Shl/Shr/Offset/checked …).
        "Offset" => BinKind::Offset,
        "Div" | "Rem" | "Shl" | "Shr" => BinKind::Other,
        _ => return None,
    })
}

/// The base operator of a checked-arithmetic rvalue (`AddWithOverflow`,
/// `CheckedAdd`, …) — these produce a `(result, overflow)` tuple.
pub(crate) fn checked_bin_kind(w: &str) -> Option<BinKind> {
    Some(match w {
        "AddWithOverflow" | "CheckedAdd" => BinKind::Add,
        "SubWithOverflow" | "CheckedSub" => BinKind::Sub,
        "MulWithOverflow" | "CheckedMul" => BinKind::Mul,
        _ => return None,
    })
}

pub(crate) fn int_type(w: &str) -> Option<MType> {
    let (signed, rest) = match w.as_bytes().first()? {
        b'i' => (true, &w[1..]),
        b'u' => (false, &w[1..]),
        _ if w == "bool" => return Some(MType::Bool),
        _ => return None,
    };
    let width = match rest {
        "8" => 8,
        "16" => 16,
        "32" => 32,
        "64" | "128" => 64, // 128-bit modelled at 64 (the BV width cap)
        "size" => 64,
        _ => return None,
    };
    Some(MType::Int { width, signed })
}
