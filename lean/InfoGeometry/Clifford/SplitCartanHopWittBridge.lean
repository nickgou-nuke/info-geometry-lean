import InfoGeometry.Clifford.ClNNBilinear
import Mathlib.Tactic.NormNum

/-!
# Split Cartan Hops and Witt CAR Pairs

This file formalizes the finite, concrete part of the split-signature picture:
the anti-diagonal Cartan generator in the head hyperbolic plane is a
`Bsplit`-skew infinitesimal `so(n+1,n+1)` operator, and the two null directions
it diagonalizes are exactly the normalized Witt directions whose Clifford
generators satisfy the CAR relation.

It does not identify the vector representation with the spin/Fock
representation directly.  The bridge proved here is the correct owner-level
statement: the same split head plane supplies both the anti-diagonal vector
Cartan hop and the null Clifford/CAR pair.
-/

namespace SplitCartanHopWittBridge

open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.ClNNBilinear
open InfoGeometry.CliffordTower

/-! ## Vector-side anti-diagonal Cartan hop -/

/-- The anti-diagonal swap on one split physical/ghost pair. -/
@[rep_depth krein]
noncomputable def pairSwap : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (LinearMap.snd ℝ ℝ ℝ).prod (LinearMap.fst ℝ ℝ ℝ)

@[rep_depth krein, simp]
theorem pairSwap_apply (x : ℝ × ℝ) :
    pairSwap x = (x.2, x.1) := by
  rfl

/--
The anti-diagonal Cartan hop on the head split plane.

On a vector `((a,b), tail) : SplitSpace (n+1)` it returns `((b,a), 0)`.
This is the recursive `SplitSpace` version of the matrix
`E_{i,i+n} + E_{i+n,i}` acting on one physical/ghost pair and vanishing on the
other modes.
-/
@[rep_depth krein]
noncomputable def headCartanHop (n : ℕ) : Carrier (n + 1) →ₗ[ℝ] Carrier (n + 1) :=
  (LinearMap.inl ℝ (ℝ × ℝ) (Carrier n)).comp
    (pairSwap.comp (LinearMap.fst ℝ (ℝ × ℝ) (Carrier n)))

@[rep_depth krein, simp]
theorem headCartanHop_apply (n : ℕ) (x : ℝ × ℝ) (xs : Carrier n) :
    headCartanHop n (x, xs) = ((x.2, x.1), 0) := by
  rfl

@[rep_depth krein, simp]
theorem headCartanHop_headPair (n : ℕ) (x : ℝ × ℝ) :
    headCartanHop n (headPair n x) = headPair n (x.2, x.1) := by
  rfl

@[rep_depth krein, simp]
theorem headCartanHop_tailLift (n : ℕ) (xs : Carrier n) :
    headCartanHop n (tailLift n xs) = 0 := by
  change (((0, 0), (0 : Carrier n)) = ((0, 0), (0 : Carrier n)))
  rfl

/--
The head anti-diagonal Cartan hop is `Bsplit`-skew:
`B(hx,y) + B(x,hy) = 0`.

This is the recursive split-space form of the Lie algebra condition
`Xᵀη + ηX = 0`.
-/
@[rep_depth krein]
theorem headCartanHop_bilinear_skew
    (n : ℕ) (x y : Carrier (n + 1)) :
    hyperbolicBilinear (n + 1) (headCartanHop n x) y +
      hyperbolicBilinear (n + 1) x (headCartanHop n y) = 0 := by
  rcases x with ⟨⟨a, b⟩, xs⟩
  rcases y with ⟨⟨c, d⟩, ys⟩
  rw [headCartanHop_apply, headCartanHop_apply]
  simp [hyperbolicBilinear, splitB11_apply]

/--
On the selected head plane, the anti-diagonal hop flips the sign of the split
quadratic form.  Consequently it preserves the null cone inside that plane.
-/
@[rep_depth krein]
theorem headCartanHop_headPair_quadratic_neg
    (n : ℕ) (x : ℝ × ℝ) :
    hyperbolicQuadratic (n + 1) (headCartanHop n (headPair n x)) =
      - hyperbolicQuadratic (n + 1) (headPair n x) := by
  rcases x with ⟨a, b⟩
  rw [headCartanHop_headPair]
  simp [headPair, hyperbolicQuadratic]

@[rep_depth krein]
theorem headCartanHop_preserves_head_null
    (n : ℕ) {x : ℝ × ℝ}
    (hx : hyperbolicQuadratic (n + 1) (headPair n x) = 0) :
    hyperbolicQuadratic (n + 1) (headCartanHop n (headPair n x)) = 0 := by
  rw [headCartanHop_headPair_quadratic_neg, hx, neg_zero]

/-! ## Null/Witt directions diagonalized by the hop -/

@[rep_depth krein, simp]
theorem headCartanHop_headNullMinus (n : ℕ) :
    headCartanHop n (headNullMinus n) = headNullMinus n := by
  simp [headNullMinus, headPair]

@[rep_depth krein, simp]
theorem headCartanHop_headNullPlus (n : ℕ) :
    headCartanHop n (headNullPlus n) = -headNullPlus n := by
  simp [headNullPlus, headPair]
  apply Prod.ext
  · apply Prod.ext
    · rw [Prod.fst_neg, Prod.fst_neg]
    · rw [Prod.fst_neg, Prod.snd_neg]
      norm_num
  · rw [Prod.snd_neg]
    simp

/-! ## Clifford/Witt CAR readback -/

/--
The head anti-diagonal Cartan hop and the Witt CAR pair are two readbacks of
the same split head plane.

The vector-side hop diagonalizes the normalized null directions, while the
Clifford-side generators attached to those directions are square-zero and
satisfy the normalized CAR relation.
-/
@[rep_depth krein]
theorem split_cartan_hop_witt_car_bridge (n : ℕ) :
    headCartanHop n (headNullMinus n) = headNullMinus n ∧
    headCartanHop n (headNullPlus n) = -headNullPlus n ∧
    gammaHeadNullMinus n * gammaHeadNullMinus n = 0 ∧
    gammaHeadNullPlus n * gammaHeadNullPlus n = 0 ∧
    gammaHeadNullMinus n * gammaHeadNullPlus n +
      gammaHeadNullPlus n * gammaHeadNullMinus n = 1 := by
  exact ⟨headCartanHop_headNullMinus n,
    headCartanHop_headNullPlus n,
    gammaHeadNullMinus_sq n,
    gammaHeadNullPlus_sq n,
    gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap_from_hyperbolic_pairing n⟩

/--
Finite `Cl(5,5)`/`so(5,5)` head-mode specialization.

This is the first-mode window of the five physical/ghost pairs: the
anti-diagonal vector Cartan hop on the head pair is `Bsplit`-skew and its
normalized null directions give the split Clifford/Witt CAR pair.
-/
@[rep_depth krein]
theorem o55_antidiagonal_cartan_hop_realizes_split_clifford_witt_pair :
    headCartanHop 4 (headNullMinus 4) = headNullMinus 4 ∧
    headCartanHop 4 (headNullPlus 4) = -headNullPlus 4 ∧
    gammaHeadNullMinus 4 * gammaHeadNullMinus 4 = 0 ∧
    gammaHeadNullPlus 4 * gammaHeadNullPlus 4 = 0 ∧
    gammaHeadNullMinus 4 * gammaHeadNullPlus 4 +
      gammaHeadNullPlus 4 * gammaHeadNullMinus 4 = 1 :=
  split_cartan_hop_witt_car_bridge 4

end SplitCartanHopWittBridge
