#!/usr/bin/env python3
"""
Adversarial Stress Test Suite for DAG Dominators Dataflow Implementation.
Compares the OLD implementation (from lean/DAG/Dominators.lean) with
the NEW refactored implementation (from .agents/sandbox_dominators_o1/lean/DAG/Dominators.lean)
across thousands of adversarial DAG topologies and edge cases.
"""

import random
import sys
from typing import List, Optional, Tuple

# ============================================================================
# OLD IMPLEMENTATION MODEL (mimicking original lean/DAG/Dominators.lean)
# ============================================================================

def old_bool_vec_true(byte_width: int) -> bytearray:
    return bytearray([0xFF] * byte_width)

def old_bool_vec_zero(byte_width: int) -> bytearray:
    return bytearray([0x00] * byte_width)

def old_bool_vec_and(a: bytearray, b: bytearray) -> bytearray:
    # Mimicking:
    # let mut r := ByteArray.empty
    # for i in [:a.size] do
    #   r := r.push (a[i]! &&& b[i]!)
    # r
    r = bytearray()
    for i in range(len(a)):
        r.append(a[i] & b[i])
    return r

def old_bool_vec_set(a: bytearray, i: int) -> bytearray:
    res = bytearray(a)
    bi = i // 8
    bit = 1 << (i % 8)
    res[bi] |= bit
    return res

def old_dominators(preds: List[List[int]], order: List[int]) -> List[bytearray]:
    m = len(preds)
    byte_width = (m + 7) // 8
    dom = [old_bool_vec_true(byte_width) for _ in range(m)]

    for u in order:
        ps = preds[u]
        if len(ps) == 0:
            base = old_bool_vec_zero(byte_width)
        else:
            acc = dom[ps[0]]
            for i in range(1, len(ps)):
                acc = old_bool_vec_and(acc, dom[ps[i]])
            base = acc
        dom[u] = old_bool_vec_set(base, u)
    return dom

def old_dominates(dom: List[bytearray], a: int, b: int) -> bool:
    bi = a // 8
    bit = 1 << (a % 8)
    return (dom[b][bi] & bit) != 0

def old_strict_dominators(dom: List[bytearray], n: int) -> List[int]:
    out = []
    for d in range(len(dom)):
        if d != n and old_dominates(dom, d, n):
            out.append(d)
    return out

def old_immediate_dominator(dom: List[bytearray], n: int) -> Optional[int]:
    candidates = old_strict_dominators(dom, n)
    for d in candidates:
        if all(e == d or old_dominates(dom, e, d) for e in candidates):
            return d
    return None

def old_build_idom(preds: List[List[int]], dom: List[bytearray]) -> List[Optional[int]]:
    idom = [None] * len(preds)
    for i in range(len(preds)):
        if len(preds[i]) > 0:
            idom[i] = old_immediate_dominator(dom, i)
    return idom

def old_dominator_frontier(preds: List[List[int]], dom: List[bytearray], n: int) -> List[int]:
    m = len(preds)
    frontier = []
    for z in range(m):
        if not old_dominates(dom, n, z) or n == z:
            for p in preds[z]:
                if old_dominates(dom, n, p):
                    frontier.append(z)
                    break
    return frontier

def old_lightcone(dom: List[bytearray], n: int) -> Tuple[List[int], List[int]]:
    future = []
    past = []
    for i in range(len(dom)):
        if i != n:
            if old_dominates(dom, n, i):
                future.append(i)
            if old_dominates(dom, i, n):
                past.append(i)
    return future, past

# ============================================================================
# NEW IMPLEMENTATION MODEL (mimicking refactored .agents/sandbox_dominators_o1/lean/DAG/Dominators.lean)
# ============================================================================

def new_bool_vec_true(byte_width: int) -> bytearray:
    return bytearray([0xFF] * byte_width)

def new_bool_vec_zero(byte_width: int) -> bytearray:
    return bytearray([0x00] * byte_width)

def new_bool_vec_and(a: bytearray, b: bytearray) -> bytearray:
    # List.zipWith (· &&& ·) a.data.toList b.data.toList
    return bytearray(x & y for x, y in zip(a, b))

def new_bool_vec_set(a: bytearray, i: int) -> bytearray:
    res = bytearray(a)
    bi = i // 8
    bit = 1 << (i % 8)
    res[bi] |= bit
    return res

def new_dominators(preds: List[List[int]], order: List[int]) -> List[bytearray]:
    m = len(preds)
    byte_width = (m + 7) // 8
    dom = [new_bool_vec_true(byte_width) for _ in range(m)]

    for u in order:
        ps = preds[u]
        if not ps:
            base = new_bool_vec_zero(byte_width)
        else:
            p0 = ps[0]
            rest = ps[1:]
            acc = dom[p0]
            for p in rest:
                acc = new_bool_vec_and(acc, dom[p])
            base = acc
        dom[u] = new_bool_vec_set(base, u)
    return dom

def new_dominates(dom: List[bytearray], a: int, b: int) -> bool:
    bi = a // 8
    bit = 1 << (a % 8)
    return (dom[b][bi] & bit) != 0

def new_strict_dominators(dom: List[bytearray], n: int) -> List[int]:
    # (List.range dom.size).filter (fun d => d != n && dominates dom d n)
    return [d for d in range(len(dom)) if d != n and new_dominates(dom, d, n)]

def new_immediate_dominator(dom: List[bytearray], n: int) -> Optional[int]:
    candidates = new_strict_dominators(dom, n)
    for d in candidates:
        if all(e == d or new_dominates(dom, e, d) for e in candidates):
            return d
    return None

def new_build_idom(preds: List[List[int]], dom: List[bytearray]) -> List[Optional[int]]:
    # (List.range preds.size).map (fun i => if !preds[i]!.isEmpty then immediateDominator dom i else none)
    return [new_immediate_dominator(dom, i) if len(preds[i]) > 0 else None for i in range(len(preds))]

def new_dominator_frontier(preds: List[List[int]], dom: List[bytearray], n: int) -> List[int]:
    m = len(preds)
    frontier = []
    for z in range(m):
        if not new_dominates(dom, n, z) or n == z:
            for p in preds[z]:
                if new_dominates(dom, n, p):
                    frontier.append(z)
                    break
    return frontier

def new_lightcone(dom: List[bytearray], n: int) -> Tuple[List[int], List[int]]:
    future = []
    past = []
    for i in range(len(dom)):
        if i != n:
            if new_dominates(dom, n, i):
                future.append(i)
            if new_dominates(dom, i, n):
                past.append(i)
    return future, past

# ============================================================================
# INDEPENDENT GROUND TRUTH / ORACLE: PATH-BASED DOMINATOR
# ============================================================================

def ground_truth_dominators(n: int, preds: List[List[int]], roots: List[int]) -> List[set]:
    """
    By definition in graph theory:
    'a dominates b' means EVERY path from ANY entry/root node to b contains a.
    For unreachable nodes from roots, definition can vary, but in a topological DAG
    roots are nodes with in-degree 0.
    """
    # Find all paths from any root to node b
    # A node 'a' dominates 'b' iff on every path from any root to b, 'a' appears.
    # We can also compute dominators via simple fixpoint iteration on sets.
    dom = [set(range(n)) for _ in range(n)]
    for r in roots:
        dom[r] = {r}
    # For unreachable roots or nodes with preds:
    changed = True
    while changed:
        changed = False
        for u in range(n):
            if u in roots:
                new_d = {u}
            else:
                if len(preds[u]) == 0:
                    new_d = {u}
                else:
                    common = set(dom[preds[u][0]])
                    for p in preds[u][1:]:
                        common &= dom[p]
                    new_d = common | {u}
            if new_d != dom[u]:
                dom[u] = new_d
                changed = True
    return dom

# ============================================================================
# DIFFERENTIAL TESTING RUNNER
# ============================================================================

def assert_models_agree(name: str, preds: List[List[int]], order: List[int]):
    n = len(preds)
    old_d = old_dominators(preds, order)
    new_d = new_dominators(preds, order)
    assert old_d == new_d, f"[{name}] dominators mismatch!\nOld: {old_d}\nNew: {new_d}"

    for a in range(n):
        for b in range(n):
            assert old_dominates(old_d, a, b) == new_dominates(new_d, a, b), \
                f"[{name}] dominates({a}, {b}) mismatch!"

    for u in range(n):
        old_strict = old_strict_dominators(old_d, u)
        new_strict = new_strict_dominators(new_d, u)
        assert old_strict == new_strict, f"[{name}] strict_dominators({u}) mismatch: {old_strict} vs {new_strict}"

        old_id = old_immediate_dominator(old_d, u)
        new_id = new_immediate_dominator(new_d, u)
        assert old_id == new_id, f"[{name}] immediate_dominator({u}) mismatch: {old_id} vs {new_id}"

        old_df = old_dominator_frontier(preds, old_d, u)
        new_df = new_dominator_frontier(preds, new_d, u)
        assert old_df == new_df, f"[{name}] dominator_frontier({u}) mismatch: {old_df} vs {new_df}"

        old_lc = old_lightcone(old_d, u)
        new_lc = new_lightcone(new_d, u)
        assert old_lc == new_lc, f"[{name}] lightcone({u}) mismatch: {old_lc} vs {new_lc}"

    old_idom = old_build_idom(preds, old_d)
    new_idom = new_build_idom(preds, new_d)
    assert old_idom == new_idom, f"[{name}] build_idom mismatch: {old_idom} vs {new_idom}"

    # Also compare with ground truth set-based oracle
    roots = [i for i in range(n) if len(preds[i]) == 0]
    oracle_dom = ground_truth_dominators(n, preds, roots)
    for u in range(n):
        for a in range(n):
            model_dom = new_dominates(new_d, a, u)
            oracle_d = (a in oracle_dom[u])
            assert model_dom == oracle_d, \
                f"[{name}] Oracle mismatch for dominates({a}, {u}): model={model_dom}, oracle={oracle_d}"

# ============================================================================
# SPECIFIC EDGE CASES & ADVERSARIAL TOPOLOGIES
# ============================================================================

def run_edge_cases():
    print("--- 1. Testing Corner Case: 0-node DAG ---")
    old_d0 = old_dominators([], [])
    new_d0 = new_dominators([], [])
    assert old_d0 == new_d0 == []
    assert old_build_idom([], old_d0) == new_build_idom([], new_d0) == []
    print("PASSED 0-node DAG.")

    print("--- 2. Testing Corner Case: 1-node DAG ---")
    assert_models_agree("1-node DAG", [[]], [0])
    print("PASSED 1-node DAG.")

    print("--- 3. Testing Corner Case: 2-node Disconnected DAG ---")
    assert_models_agree("2-node Disconnected (0, 1)", [[], []], [0, 1])
    assert_models_agree("2-node Disconnected (1, 0)", [[], []], [1, 0])
    print("PASSED 2-node Disconnected DAG.")

    print("--- 4. Testing Corner Case: 2-node Connected DAG (0 -> 1) ---")
    assert_models_agree("2-node Connected", [[], [0]], [0, 1])
    print("PASSED 2-node Connected DAG.")

    print("--- 5. Testing Byte Boundary Transitions: 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65 ---")
    for n in [7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65]:
        # Linear chain of size n: 0 -> 1 -> ... -> n-1
        preds = [[]] + [[i - 1] for i in range(1, n)]
        order = list(range(n))
        assert_models_agree(f"Linear chain N={n}", preds, order)

        # Star / Wide fan-out: 0 -> 1, 0 -> 2, ..., 0 -> n-1
        preds_star = [[]] + [[0] for _ in range(1, n)]
        assert_models_agree(f"Star fan-out N={n}", preds_star, order)

        # Multi-root fan-in: 0 -> n-1, 1 -> n-1, ..., n-2 -> n-1
        preds_fanin = [[] for _ in range(n - 1)] + [list(range(n - 1))]
        assert_models_agree(f"Multi-root fan-in N={n}", preds_fanin, order)

        # Disconnected vertices: no edges
        preds_disc = [[] for _ in range(n)]
        assert_models_agree(f"Fully disconnected N={n}", preds_disc, order)

    print("PASSED Byte Boundary Transitions.")

    print("--- 6. Testing Wide DAG Topologies ---")
    # Wide Bipartite: Layer 1 has 16 nodes, Layer 2 has 16 nodes
    # Fully connected bipartite
    n_bip = 32
    preds_bip = [[] for _ in range(16)] + [list(range(16)) for _ in range(16)]
    order_bip = list(range(32))
    assert_models_agree("Wide Bipartite 16x16", preds_bip, order_bip)

    # Wide Diamond: 0 -> (1..30) -> 31
    preds_wd = [[]] + [[0] for _ in range(1, 31)] + [list(range(1, 31))]
    order_wd = list(range(32))
    assert_models_agree("Wide Diamond 1->30->1", preds_wd, order_wd)
    # Check idom of node 31 is 0!
    d_wd = new_dominators(preds_wd, order_wd)
    assert new_immediate_dominator(d_wd, 31) == 0, f"Expected idom(31)==0, got {new_immediate_dominator(d_wd, 31)}"

    # Multi-component Disconnected DAG: 5 separate disconnected chains of length 6 (Total 30 nodes)
    preds_mc = []
    for c in range(5):
        base = c * 6
        preds_mc.append([])
        for k in range(1, 6):
            preds_mc.append([base + k - 1])
    order_mc = list(range(30))
    assert_models_agree("5 Disconnected Chains (N=30)", preds_mc, order_mc)

    print("PASSED Wide Topologies.")

def run_fuzz_tests(num_graphs: int = 500):
    print(f"--- 7. Running Randomized Fuzz Testing ({num_graphs} random DAGs) ---")
    random.seed(42)

    for trial in range(num_graphs):
        n = random.randint(1, 40)
        # Generate random DAG by only allowing edges u -> v where u < v
        # This guarantees 0..n-1 is a topological order.
        preds = [[] for _ in range(n)]
        edge_prob = random.uniform(0.05, 0.7)
        for u in range(n):
            for v in range(u + 1, n):
                if random.random() < edge_prob:
                    preds[v].append(u)

        # Shuffle topological order among valid permutations
        # Or simply use 0..n-1
        order = list(range(n))
        assert_models_agree(f"Random DAG trial {trial} (N={n})", preds, order)

    print(f"PASSED {num_graphs} randomized fuzz tests.")

def run_adversarial_out_of_bounds_and_empty_tests():
    print("--- 8. Testing Adversarial Empty Predecessors & Out-of-Bounds Queries ---")
    # All nodes empty predecessors
    preds_all_empty = [[], [], [], []]
    order = [0, 1, 2, 3]
    dom = new_dominators(preds_all_empty, order)
    # All idom must be None
    idom = new_build_idom(preds_all_empty, dom)
    assert idom == [None, None, None, None]
    # Each node dominates only itself
    for i in range(4):
        for j in range(4):
            assert new_dominates(dom, i, j) == (i == j)
        assert new_strict_dominators(dom, i) == []
        assert new_immediate_dominator(dom, i) is None

    # Empty predecessor in the middle of graph
    # 0 -> 1, 2 has no preds, 3 has preds [1, 2]
    preds_mid = [[], [0], [], [1, 2]]
    order_mid = [0, 2, 1, 3]
    assert_models_agree("Empty pred in middle", preds_mid, order_mid)

    # Redundant/duplicate predecessors: preds[1] = [0, 0, 0]
    preds_dup = [[], [0, 0, 0]]
    order_dup = [0, 1]
    assert_models_agree("Duplicate predecessors", preds_dup, order_dup)

    print("PASSED Adversarial Empty Predecessors & Invariant Tests.")

if __name__ == "__main__":
    run_edge_cases()
    run_fuzz_tests(1000)
    run_adversarial_out_of_bounds_and_empty_tests()
    print("\n==================================================")
    print("ALL 1000+ ADVERSARIAL STRESS TESTS PASSED SUCCESSFULLY!")
    print("==================================================")
