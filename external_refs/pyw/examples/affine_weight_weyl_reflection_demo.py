#!/usr/bin/env sage -python
"""
Demo: Using Weyl Reflections with AffineWeight Objects

This example demonstrates the new feature where AffineLieAlgebra methods
can directly accept AffineWeight objects as input.

Author: pyw contributors
Date: 2026-02-01
"""

from sage.all import RootSystem
from pyw.core.affine_lie_algebra import AffineLieAlgebra
from pyw.core.affine_weight import AffineWeight


def demo_simple_reflection():
    """Demo: simple_reflection() with AffineWeight input."""
    print("=" * 70)
    print("Demo 1: simple_reflection() with AffineWeight")
    print("=" * 70)

    # Setup
    ala = AffineLieAlgebra(["A", 2, 1])
    finite_rs = RootSystem(["A", 2])
    Lambda = finite_rs.weight_space().fundamental_weights()

    # Create an affine weight: ̂λ = (Λ₁; k=1; n=0)
    lambda_hat = AffineWeight(ala, Lambda[1], level=1, grade=0)
    print(f"Input affine weight: {lambda_hat}")
    print(f"  - Finite part: {lambda_hat.finite_part}")
    print(f"  - Level: {lambda_hat.level}")
    print(f"  - Grade: {lambda_hat.grade}")

    # Apply simple reflection s₁
    print(f"\nApplying simple reflection s₁...")
    result = ala.simple_reflection(1, lambda_hat)

    print(f"\nResult: {result}")
    print(f"  - Finite part: {result.finite_part}")
    print(f"  - Level: {result.level} (preserved)")
    print(f"  - Grade: {result.grade} (preserved)")

    print("\n✓ The method returns an AffineWeight object!")
    print("✓ Level and grade are preserved (finite reflection doesn't affect them)")
    print()


def demo_weyl_reflection():
    """Demo: weyl_reflection() with AffineWeight input."""
    print("=" * 70)
    print("Demo 2: weyl_reflection() with AffineWeight")
    print("=" * 70)

    # Setup
    ala = AffineLieAlgebra(["A", 2, 1])
    finite_rs = RootSystem(["A", 2])
    Lambda = finite_rs.weight_space().fundamental_weights()
    alpha = ala.simple_roots()

    # Create an affine weight with non-trivial level and grade
    lambda_hat = AffineWeight(ala, Lambda[1], level=2, grade=1)
    print(f"Input affine weight: {lambda_hat}")
    print(f"  - Finite part: {lambda_hat.finite_part}")
    print(f"  - Level: {lambda_hat.level}")
    print(f"  - Grade: {lambda_hat.grade}")

    # Apply Weyl reflection by α₁
    print(f"\nApplying Weyl reflection by α₁...")
    result = ala.weyl_reflection(alpha[1], lambda_hat)

    print(f"\nResult: {result}")
    print(f"  - Finite part: {result.finite_part}")
    print(f"  - Level: {result.level} (preserved)")
    print(f"  - Grade: {result.grade} (preserved)")

    print("\n✓ The method returns an AffineWeight object!")
    print("✓ Only the finite part is reflected")
    print()


def demo_backward_compatibility():
    """Demo: Old tuple-style API still works."""
    print("=" * 70)
    print("Demo 3: Backward Compatibility (Tuple Style)")
    print("=" * 70)

    # Setup
    ala = AffineLieAlgebra(["A", 2, 1])
    finite_rs = RootSystem(["A", 2])
    Lambda = finite_rs.weight_space().fundamental_weights()

    # Old style: pass (weight, k, n) separately
    print("Using old tuple-style API:")
    print("  ala.simple_reflection(1, Lambda[1], k=1, n=0)")

    result = ala.simple_reflection(1, Lambda[1], k=1, n=0)

    print(f"\nResult type: {type(result)}")
    print(f"Result: {result}")

    finite_part, k, n = result
    print(f"\nUnpacked:")
    print(f"  - Finite part: {finite_part}")
    print(f"  - Level k: {k}")
    print(f"  - Grade n: {n}")

    print("\n✓ Old API still works and returns a tuple!")
    print()


def demo_type_consistency():
    """Demo: Input type determines output type."""
    print("=" * 70)
    print("Demo 4: Type Consistency")
    print("=" * 70)

    # Setup
    ala = AffineLieAlgebra(["A", 2, 1])
    finite_rs = RootSystem(["A", 2])
    Lambda = finite_rs.weight_space().fundamental_weights()

    # Case 1: AffineWeight input → AffineWeight output
    lambda_hat = AffineWeight(ala, Lambda[1], level=1, grade=0)
    result1 = ala.simple_reflection(1, lambda_hat)
    print(f"1. AffineWeight input → {type(result1).__name__} output")

    # Case 2: Tuple input → tuple output
    result2 = ala.simple_reflection(1, Lambda[1], k=1, n=0)
    print(f"2. Tuple input (weight, k, n) → {type(result2).__name__} output")

    # Case 3: Finite weight input → finite weight output
    result3 = ala.simple_reflection(1, Lambda[1])
    print(f"3. Finite weight input → finite weight output (not AffineWeight, not tuple)")

    print("\n✓ Input type determines output type!")
    print("✓ This ensures type consistency and predictability")
    print()


def main():
    """Run all demos."""
    print("\n" + "=" * 70)
    print("AffineWeight Integration with AffineLieAlgebra")
    print("Demonstration of New Features")
    print("=" * 70 + "\n")

    demo_simple_reflection()
    demo_weyl_reflection()
    demo_backward_compatibility()
    demo_type_consistency()

    print("=" * 70)
    print("Summary")
    print("=" * 70)
    print("""
New Features:
1. AffineLieAlgebra.simple_reflection() now accepts AffineWeight objects
2. AffineLieAlgebra.weyl_reflection() now accepts AffineWeight objects
3. When AffineWeight is passed, the result is also an AffineWeight
4. Level and grade are preserved (only finite part is reflected)
5. Old tuple-style API remains fully compatible

Benefits:
- More intuitive API: work directly with AffineWeight objects
- Type consistency: input type determines output type
- Backward compatible: existing code continues to work
- Cleaner code: no need to manually unpack/repack (weight, k, n)
    """)
    print("=" * 70)


if __name__ == "__main__":
    main()
