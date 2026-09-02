//! Kata 1 
//! 
use std::collections::HashMap;
#[cfg(test)] use std::collections::HashSet; // property-test oracle only

/// xorshift64* PRNG, so the property test needs no external crate.
#[cfg(test)] struct Rng(u64);
#[cfg(test)] impl Rng {
    fn new(seed: u64) -> Self { Self(seed | 1) }
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn below(&mut self, n: usize) -> usize { (self.next_u64() % n as u64) as usize }
}

/// Oracle for the property test. Exposes `same_set`, never a representative
/// -- who represents a class is an implementation choice, not spec.
#[cfg(test)] struct NaiveUf(Vec<HashSet<usize>>);
#[cfg(test)] impl NaiveUf {
    fn new(n: usize) -> Self { Self((0..n).map(|i| HashSet::from([i])).collect()) }
    fn idx_of(&self, x: usize) -> usize { self.0.iter().position(|s| s.contains(&x)).unwrap() }
    fn same_set(&self, a: usize, b: usize) -> bool { self.idx_of(a) == self.idx_of(b) }
    fn union(&mut self, a: usize, b: usize) {
        let (ia, ib) = (self.idx_of(a), self.idx_of(b));
        if ia == ib {
            return;
        }
        let (lo, hi) = if ia < ib { (ia, ib) } else { (ib, ia) };
        let (hi_set, lo_set) = (self.0.swap_remove(hi), self.0.swap_remove(lo));
        self.0.push(lo_set.union(&hi_set).copied().collect());
    }
}

struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<u8>,
}
impl UnionFind {
    fn new(n: usize) -> Self { Self { parent: (0..n).collect(), rank: vec![0; n] } }
    fn push(&mut self) -> usize {
        let id = self.parent.len();
        self.parent.push(id);
        self.rank.push(0);
        id
    }
    fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            let root = self.find(self.parent[x]);
            self.parent[x] = root; // path compression
        }
        self.parent[x]
    }
    /// `Some((survivor, absorbed))` iff `a`/`b` were in different classes.
    fn union(&mut self, a: usize, b: usize) -> Option<(usize, usize)> {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return None;
        }
        let (survivor, absorbed) = if self.rank[ra] < self.rank[rb] {
            (rb, ra)
        } else if self.rank[ra] > self.rank[rb] {
            (ra, rb)
        } else {
            self.rank[ra] += 1;
            (ra, rb)
        };
        self.parent[absorbed] = survivor;
        Some((survivor, absorbed))
    }
}

type Id = usize;
#[derive(Clone, PartialEq, Eq, Hash)]
struct ENode {
    op: &'static str,
    children: Vec<Id>, // canonical as of last recanonicalization
}
struct EGraph {
    nodes: Vec<ENode>,
    uf: UnionFind,
    hashcons: HashMap<ENode, Id>,
    use_lists: HashMap<Id, Vec<Id>>, // class root -> parent node ids
    pending: Vec<(Id, Id)>,          // merges not yet reflected in parent keys
}
impl EGraph {
    fn new() -> Self {
        Self { nodes: vec![], uf: UnionFind::new(0), hashcons: HashMap::new(), use_lists: HashMap::new(), pending: vec![] }
    }
    fn find(&mut self, id: Id) -> Id { self.uf.find(id) }
    fn add(&mut self, op: &'static str, children: &[Id]) -> Id {
        let canon: Vec<Id> = children.iter().map(|&c| self.find(c)).collect();
        let key = ENode { op, children: canon.clone() };
        if let Some(&existing) = self.hashcons.get(&key) {
            return self.find(existing);
        }
        let id = self.uf.push();
        self.nodes.push(key.clone());
        self.hashcons.insert(key, id);
        for c in canon {
            self.use_lists.entry(c).or_default().push(id);
        }
        id
    }
    /// Updates the union-find right away, leaving parents' keys stale until `rebuild` fixes them -- that gap is the whole kata.
    fn union(&mut self, a: Id, b: Id) {
        if let Some(pair) = self.uf.union(a, b) {
            self.pending.push(pair);
        }
    }
    /// Walk each absorbed class's use-list, recanonicalize parents, and union any resulting hash-cons collision (congruence). Cascades.
    fn rebuild(&mut self) {
        while let Some((survivor, absorbed)) = self.pending.pop() {
            let survivor = self.find(survivor);
            if absorbed == survivor {
                continue; // already folded in by an earlier cascade step
            }
            for p in self.use_lists.remove(&absorbed).unwrap_or_default() {
                let old = self.nodes[p].clone();
                self.hashcons.remove(&old);
                let new_children: Vec<Id> = old.children.iter().map(|&c| self.find(c)).collect();
                let new_key = ENode { op: old.op, children: new_children.clone() };
                self.nodes[p] = new_key.clone();
                for c in new_children {
                    self.use_lists.entry(c).or_default().push(p);
                }
                match self.hashcons.get(&new_key).copied() {
                    Some(existing) if self.find(existing) != self.find(p) => self.union(existing, p),
                    Some(_) => {}
                    None => drop(self.hashcons.insert(new_key, p)),
                }
            }
        }
    }
}

/// Demo: the bug you get from *not* rebuilding.
fn main() {
    let mut g = EGraph::new();
    let a = g.add("a", &[]);
    let b = g.add("b", &[]);
    let fa = g.add("f", &[a]);
    let fb = g.add("f", &[b]);
    g.union(a, b);
    println!("without rebuild: same={}  (f(a)={}, f(b)={})", g.find(fa) == g.find(fb), g.find(fa), g.find(fb));
    g.rebuild();
    println!("after rebuild:   same={}  (f(a)={}, f(b)={})", g.find(fa) == g.find(fb), g.find(fa), g.find(fb));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn union_find_agrees_with_naive_model() {
        let (n, ops) = (10, 30);
        for seed in 0..20u64 {
            let mut fast = UnionFind::new(n);
            let mut naive = NaiveUf::new(n);
            let mut rng = Rng::new(seed);
            for _ in 0..ops {
                let (x, y) = (rng.below(n), rng.below(n));
                fast.union(x, y);
                naive.union(x, y);
                for i in 0..n {
                    for j in 0..n {
                        assert_eq!(fast.find(i) == fast.find(j), naive.same_set(i, j));
                    }
                }
            }
        }
    }

    #[test]
    fn hash_consing_reuses_identical_terms() {
        let mut g = EGraph::new();
        let a = g.add("a", &[]);
        assert_eq!(g.add("f", &[a]), g.add("f", &[a]));
    }

    #[test]
    fn rebuild_restores_congruence_and_cascades() {
        let mut g = EGraph::new();
        let a = g.add("a", &[]);
        let b = g.add("b", &[]);
        let (fa, fb) = (g.add("f", &[a]), g.add("f", &[b]));
        let (gfa, gfb) = (g.add("g", &[fa]), g.add("g", &[fb]));
        g.union(a, b);
        assert_ne!(g.find(fa), g.find(fb), "the bug: not congruent yet without rebuild");
        g.rebuild();
        assert_eq!(g.find(fa), g.find(fb));
        assert_eq!(g.find(gfa), g.find(gfb), "rebuild must cascade through nesting");
    }
}
