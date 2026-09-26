#!/usr/bin/env python3
"""
CAS Dominators Verification Script
Models the exact dataflow dominator algorithm from DAG/Dominators.lean
and verifies all assertions symbolically and computationally on:
- chainPreds: 0 -> 1 -> 2
- diamondPreds: 0 -> 1 -> 3, 0 -> 2 -> 3
- multiRootPreds: 0 -> 2, 1 -> 2 (two roots: 0 and 1)
"""

import sys
from typing import List, Optional, Tuple

def bool_vec_true(byte_width: int) -> bytearray:
    return bytearray([0xFF] * byte_width)

def bool_vec_zero(byte_width: int) -> bytearray:
    return bytearray([0x00] * byte_width)

def bool_vec_and(a: bytearray, b: bytearray) -> bytearray:
    return bytearray(x & y for x, y in zip(a, b))

def bool_vec_set(a: bytearray, i: int) -> bytearray:
    res = bytearray(a)
    bi = i // 8
    bit = 1 << (i % 8)
    res[bi] |= bit
    return res

def dominators(preds: List[List[int]], order: List[int]) -> List[bytearray]:
    m = len(preds)
    byte_width = (m + 7) // 8
    dom = [bool_vec_true(byte_width) for _ in range(m)]

    for u in order:
        ps = preds[u]
        if len(ps) == 0:
            base = bool_vec_zero(byte_width)
        else:
            acc = dom[ps[0]]
            for p in ps[1:]:
                acc = bool_vec_and(acc, dom[p])
            base = acc
        dom[u] = bool_vec_set(base, u)
    return dom

def dominates(dom: List[bytearray], a: int, b: int) -> bool:
    bi = a // 8
    bit = 1 << (a % 8)
    return (dom[b][bi] & bit) != 0

def strict_dominators(dom: List[bytearray], n: int) -> List[int]:
    return [d for d in range(len(dom)) if d != n and dominates(dom, d, n)]

def immediate_dominator(dom: List[bytearray], n: int) -> Optional[int]:
    candidates = strict_dominators(dom, n)
    for d in candidates:
        if all(e == d or dominates(dom, e, d) for e in candidates):
            return d
    return None

def build_idom(preds: List[List[int]], dom: List[bytearray]) -> List[Optional[int]]:
    idom = [None] * len(preds)
    for i in range(len(preds)):
        if len(preds[i]) > 0:
            idom[i] = immediate_dominator(dom, i)
    return idom

def verify_chain():
    chain_preds = [[], [0], [1]]
    chain_order = [0, 1, 2]
    dom = dominators(chain_preds, chain_order)
    idom = build_idom(chain_preds, dom)
    expected = [None, 0, 1]
    print(f"[Chain] computed idom: {idom}, expected: {expected}")
    assert idom == expected, f"Chain idom mismatch: {idom} != {expected}"
    # Verify exact dominator bitsets:
    # 0 is dominated only by 0: {0}
    # 1 is dominated by 0, 1: {0, 1}
    # 2 is dominated by 0, 1, 2: {0, 1, 2}
    assert dominates(dom, 0, 0) and dominates(dom, 0, 1) and dominates(dom, 0, 2)
    assert not dominates(dom, 1, 0) and dominates(dom, 1, 1) and dominates(dom, 1, 2)
    assert not dominates(dom, 2, 0) and not dominates(dom, 2, 1) and dominates(dom, 2, 2)
    print("[Chain] All assertions PASSED.")

def verify_diamond():
    diamond_preds = [[], [0], [0], [1, 2]]
    diamond_order = [0, 1, 2, 3]
    dom = dominators(diamond_preds, diamond_order)
    idom = build_idom(diamond_preds, dom)
    expected = [None, 0, 0, 0]
    print(f"[Diamond] computed idom: {idom}, expected: {expected}")
    assert idom == expected, f"Diamond idom mismatch: {idom} != {expected}"
    # In diamond, both 1 and 2 branch from 0 and merge at 3.
    # Paths to 3: 0->1->3 and 0->2->3.
    # Common ancestors on all paths: 0 and 3.
    # Neither 1 nor 2 dominates 3.
    assert dominates(dom, 0, 3)
    assert not dominates(dom, 1, 3)
    assert not dominates(dom, 2, 3)
    assert strict_dominators(dom, 3) == [0]
    assert immediate_dominator(dom, 3) == 0
    print("[Diamond] All assertions PASSED.")

def verify_multi_root():
    multi_root_preds = [[], [], [0, 1]]
    multi_root_order = [0, 1, 2]
    dom = dominators(multi_root_preds, multi_root_order)
    idom = build_idom(multi_root_preds, dom)
    expected = [None, None, None]
    print(f"[Multi-root] computed idom: {idom}, expected: {expected}")
    assert idom == expected, f"Multi-root idom mismatch: {idom} != {expected}"
    
    dom_0_1 = dominates(dom, 0, 1)
    dom_1_0 = dominates(dom, 1, 0)
    print(f"[Multi-root] dominates dom 0 1: {dom_0_1}, dominates dom 1 0: {dom_1_0}")
    assert dom_0_1 is False
    assert dom_1_0 is False
    # For node 2: paths are from root 0 or root 1.
    # Neither 0 nor 1 is on ALL paths from roots to 2.
    # Hence strict dominators of 2 is empty.
    assert strict_dominators(dom, 2) == []
    assert immediate_dominator(dom, 2) is None
    print("[Multi-root] All assertions PASSED.")

if __name__ == "__main__":
    print("=== Running CAS Dominators Verification Suite ===")
    verify_chain()
    verify_diamond()
    verify_multi_root()
    print("=== All CAS Dominators Verifications PASSED ===")
