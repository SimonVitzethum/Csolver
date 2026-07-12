//! ABBA lock-order cycle detection (G6).
//!
//! Each function contributes **lock-order edges** `(held-class → acquired-class)`
//! observed on some path (see `csolver_symbolic::lockclass` for how a lock is named
//! by a stable cross-function *class*). Across the whole program these edges form a
//! directed graph over lock classes. A **cycle** in this graph is a potential ABBA
//! deadlock: one thread takes the locks in one order, another in the reverse, and
//! they can wedge. The classic case is a 2-cycle `A→B` (in one function) and `B→A`
//! (in another), but any directed cycle is reported.
//!
//! Cycles are the strongly-connected components of size ≥ 2 (Tarjan). This is a
//! **bug-finding** heuristic: it has real false positives — a legitimate lock
//! hierarchy broken by a higher-level lock, `_nested` annotations, or `trylock`
//! back-off is not distinguished — so it is only ever run in bug-finding mode and
//! reported as a candidate, never as a soundness verdict.

use std::collections::HashMap;

/// One lock-order cycle: the lock classes on the cycle and the functions whose
/// acquisitions contributed an edge within it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockOrderCycle {
    /// The lock classes forming the cycle (an SCC), sorted for a stable report.
    pub classes: Vec<String>,
    /// The functions that acquire a lock while holding another within this cycle,
    /// sorted and de-duplicated.
    pub functions: Vec<String>,
}

/// An observed lock-order edge, tagged with the function it was seen in.
pub struct TaggedEdge<'a> {
    /// The function that acquired `to` while holding `from`.
    pub function: &'a str,
    /// The already-held lock class.
    pub from: &'a str,
    /// The newly-acquired lock class.
    pub to: &'a str,
}

/// Detect all ABBA lock-order cycles in the program's lock-order edges. Returns one
/// [`LockOrderCycle`] per non-trivial strongly-connected component, in a stable order.
pub fn detect_cycles(edges: &[TaggedEdge]) -> Vec<LockOrderCycle> {
    // Intern class names to dense node ids (a free function to avoid a closure that
    // would capture two `&mut` borrows at once).
    let mut id_of: HashMap<String, usize> = HashMap::new();
    let mut names: Vec<String> = Vec::new();
    let node = |s: &str, names: &mut Vec<String>, id_of: &mut HashMap<String, usize>| {
        if let Some(&i) = id_of.get(s) {
            i
        } else {
            let i = names.len();
            names.push(s.to_string());
            id_of.insert(s.to_string(), i);
            i
        }
    };

    let mut adj: Vec<Vec<usize>> = Vec::new();
    let ensure = |adj: &mut Vec<Vec<usize>>, n: usize| {
        while adj.len() <= n {
            adj.push(Vec::new());
        }
    };
    // Functions contributing an edge between a given (from,to) class pair.
    let mut edge_fns: HashMap<(usize, usize), Vec<String>> = HashMap::new();
    for e in edges {
        let u = node(e.from, &mut names, &mut id_of);
        let v = node(e.to, &mut names, &mut id_of);
        ensure(&mut adj, u.max(v));
        adj[u].push(v);
        edge_fns.entry((u, v)).or_default().push(e.function.to_string());
    }

    let sccs = tarjan_scc(&adj);
    let mut cycles = Vec::new();
    for scc in sccs {
        // A cycle is an SCC with ≥2 nodes, or a single node with a self-loop (which we
        // never emit — held≠acquired — so only the ≥2 case matters here).
        if scc.len() < 2 {
            continue;
        }
        let members: std::collections::HashSet<usize> = scc.iter().copied().collect();
        let mut classes: Vec<String> = scc.iter().map(|&i| names[i].clone()).collect();
        classes.sort();
        // Functions contributing an edge that stays *within* the SCC.
        let mut functions: Vec<String> = edge_fns
            .iter()
            .filter(|((u, v), _)| members.contains(u) && members.contains(v))
            .flat_map(|(_, fns)| fns.iter().cloned())
            .collect();
        functions.sort();
        functions.dedup();
        cycles.push(LockOrderCycle { classes, functions });
    }
    cycles.sort_by(|a, b| a.classes.cmp(&b.classes));
    cycles
}

/// Tarjan's strongly-connected-components algorithm (iterative-free recursion over a
/// small graph). Returns each SCC as a list of node ids.
fn tarjan_scc(adj: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = adj.len();
    let mut index = vec![usize::MAX; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut next_index = 0usize;
    let mut out: Vec<Vec<usize>> = Vec::new();

    // Explicit work stack to avoid deep recursion on large programs.
    // Frame: (node, next-neighbour-index).
    for start in 0..n {
        if index[start] != usize::MAX {
            continue;
        }
        let mut work: Vec<(usize, usize)> = vec![(start, 0)];
        while let Some(&(v, pi)) = work.last() {
            if pi == 0 {
                index[v] = next_index;
                low[v] = next_index;
                next_index += 1;
                stack.push(v);
                on_stack[v] = true;
            }
            if pi < adj[v].len() {
                // advance this frame's neighbour cursor
                if let Some(frame) = work.last_mut() {
                    frame.1 += 1;
                }
                let w = adj[v][pi];
                if index[w] == usize::MAX {
                    work.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
            } else {
                // done with v: if a root, pop its SCC.
                if low[v] == index[v] {
                    let mut comp = Vec::new();
                    while let Some(w) = stack.pop() {
                        on_stack[w] = false;
                        comp.push(w);
                        if w == v {
                            break;
                        }
                    }
                    out.push(comp);
                }
                work.pop();
                if let Some(&(parent, _)) = work.last() {
                    low[parent] = low[parent].min(low[v]);
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn abba_two_cycle_is_reported() {
        // f: A held, acquire B  → A→B ;  g: B held, acquire A → B→A.  Cycle {A,B}.
        let edges = vec![
            TaggedEdge { function: "f", from: "A", to: "B" },
            TaggedEdge { function: "g", from: "B", to: "A" },
        ];
        let cycles = detect_cycles(&edges);
        assert_eq!(cycles.len(), 1, "the A↔B cycle is reported");
        assert_eq!(cycles[0].classes, vec!["A".to_string(), "B".to_string()]);
        assert_eq!(cycles[0].functions, vec!["f".to_string(), "g".to_string()]);
    }

    #[test]
    fn consistent_order_has_no_cycle() {
        // Both functions take A before B — a consistent global order, no cycle.
        let edges = vec![
            TaggedEdge { function: "f", from: "A", to: "B" },
            TaggedEdge { function: "g", from: "A", to: "B" },
        ];
        assert!(detect_cycles(&edges).is_empty(), "a consistent lock order is not a cycle");
    }

    #[test]
    fn three_cycle_is_reported() {
        let edges = vec![
            TaggedEdge { function: "f", from: "A", to: "B" },
            TaggedEdge { function: "g", from: "B", to: "C" },
            TaggedEdge { function: "h", from: "C", to: "A" },
        ];
        let cycles = detect_cycles(&edges);
        assert_eq!(cycles.len(), 1);
        assert_eq!(cycles[0].classes, vec!["A".to_string(), "B".to_string(), "C".to_string()]);
    }
}
