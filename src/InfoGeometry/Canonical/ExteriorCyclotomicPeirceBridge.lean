import InfoGeometry.Clifford.ExteriorDegreePhaseFour
import InfoGeometry.Clifford.SplitClifford55ExteriorParity
import InfoGeometry.Canonical.HodgeStar4DFiniteLinearBridge

/-!
# Existing chiral spinors and Hodge sectors in the finite Peirce construction

The real 32-dimensional exterior spinor, its parity, and its neutral Clifford
action are the existing owners. The fourth-order complex exterior-degree
construction is separate from the existing six-component Hodge operator.
No equality of these different carriers or meanings of grading is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.ExteriorCyclotomicPeirceBridge

open InfoGeometry.Core.FinitePeirceMatrix
open InfoGeometry.Algebra.FourthRootPeirceProjectors
open InfoGeometry.Clifford.ExteriorDegreePhaseFour
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.SplitClifford55ExteriorParity
open InfoGeometry.Canonical.HodgeStar4DFinite
open InfoGeometry.Canonical.HodgeStar4DFiniteLinearBridge

section GeneralParity

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- An odd operator has zero diagonal corners for an actual involution. -/
theorem odd_diagonal_zero (G X : A) (hG : G*G = 1) (hX : G*X = -(X*G)) :
    ((1/2 : ℝ) • (1+G)) * X * ((1/2 : ℝ) • (1+G)) = 0 ∧
      ((1/2 : ℝ) • (1-G)) * X * ((1/2 : ℝ) • (1-G)) = 0 := by
  have hGXG : G*X*G = -X := by
    rw [hX, neg_mul, mul_assoc, hG, mul_one]
  constructor <;>
    simp only [smul_mul_assoc, mul_smul_comm,
      add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one] <;>
    rw [hGXG, hX] <;> module

/-- Even operators have zero off-diagonal corners. -/
theorem even_offDiagonal_zero (G X : A) (hG : G*G = 1) (hX : G*X = X*G) :
    ((1/2 : ℝ) • (1+G)) * X * ((1/2 : ℝ) • (1-G)) = 0 ∧
      ((1/2 : ℝ) • (1-G)) * X * ((1/2 : ℝ) • (1+G)) = 0 := by
  have hGXG : G*X*G = X := by rw [hX, mul_assoc, hG, mul_one]
  constructor <;>
    simp only [smul_mul_assoc, mul_smul_comm,
      add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one] <;>
    rw [hGXG, hX] <;> module

end GeneralParity

/-- The actual two chiral projectors on the repository's exterior spinor space. -/
def spinProjector : Fin 2 → SpinorEnd := ![chiralProjectorPlus, chiralProjectorMinus]

/-- Existing proved laws populate the native complete-idempotent predicate. -/
def spinProjectorsComplete : CompleteOrthogonalIdempotents spinProjector where
  idem k := by
    fin_cases k
    · exact chiralProjectorPlus_idempotent
    · exact chiralProjectorMinus_idempotent
  ortho j k hjk := by
    fin_cases j <;> fin_cases k
    · exact False.elim (hjk rfl)
    · exact chiralProjectors_plus_mul_minus
    · exact chiralProjectors_minus_mul_plus
    · exact False.elim (hjk rfl)
  complete := by simpa [spinProjector, Fin.sum_univ_two] using chiralProjectors_add

/-- Full operator Peirce decomposition on the existing real exterior-spinor carrier. -/
def realSpinorCornerEquiv : SpinorEnd ≃ₗ[ℝ] cornerSpace (K := ℝ) spinProjector :=
  cornerEquiv spinProjector spinProjectorsComplete

theorem realSpinor_blocks_reconstruct (X : SpinorEnd) :
    assemble (blocks spinProjector X) = X := assemble_blocks _ spinProjectorsComplete X

theorem realSpinor_blocks_mul (X Y : SpinorEnd) :
    blocks spinProjector (X*Y) = blocks spinProjector X * blocks spinProjector Y :=
  blocks_mul _ spinProjectorsComplete X Y

/-- The actual wedge-plus-contraction action is odd, as an operator equality. -/
theorem neutralAction_odd (w : NeutralSpace) :
    gradeLinear * neutralAction w = -(neutralAction w * gradeLinear) := by
  apply LinearMap.ext
  intro x
  exact gradeInvolution_neutralAction w x

/-- Therefore all Clifford vector actions have zero chiral diagonal blocks. -/
theorem neutralAction_diagonal_zero (w : NeutralSpace) :
    chiralProjectorPlus * neutralAction w * chiralProjectorPlus = 0 ∧
      chiralProjectorMinus * neutralAction w * chiralProjectorMinus = 0 := by
  exact odd_diagonal_zero gradeLinear (neutralAction w) gradeLinear_sq (neutralAction_odd w)

/-- Products of two actual vector actions are even, not necessarily scalar. -/
theorem neutralAction_pair_even (w z : NeutralSpace) :
    gradeLinear * (neutralAction w * neutralAction z) =
      (neutralAction w * neutralAction z) * gradeLinear := by
  apply LinearMap.ext
  intro x
  change gradeInvolution (neutralAction w (neutralAction z x)) =
    neutralAction w (neutralAction z (gradeInvolution x))
  rw [gradeInvolution_neutralAction, gradeInvolution_neutralAction, map_neg, neg_neg]

theorem neutralAction_pair_offDiagonal_zero (w z : NeutralSpace) :
    chiralProjectorPlus * (neutralAction w * neutralAction z) * chiralProjectorMinus = 0 ∧
      chiralProjectorMinus * (neutralAction w * neutralAction z) * chiralProjectorPlus = 0 := by
  exact even_offDiagonal_zero gradeLinear (neutralAction w * neutralAction z)
    gradeLinear_sq (neutralAction_pair_even w z)

/-- The whole existing even Clifford algebra, not only generator pairs, is block diagonal. -/
theorem evenClifford_offDiagonal_zero (a : CliffordAlgebra.even NeutralQ) :
    chiralProjectorPlus * neutralCliffordRepEven a * chiralProjectorMinus = 0 ∧
      chiralProjectorMinus * neutralCliffordRepEven a * chiralProjectorPlus = 0 := by
  constructor
  · apply LinearMap.ext
    intro x
    change chiralProjectorPlus (neutralCliffordRepEven a (chiralProjectorMinus x)) = 0
    obtain ⟨y, hy⟩ := neutralCliffordRepEven_mem_minus a (chiralProjectorMinus x)
      (LinearMap.mem_range_self _ x)
    rw [← hy]
    exact DFunLike.congr_fun chiralProjectors_plus_mul_minus y
  · apply LinearMap.ext
    intro x
    change chiralProjectorMinus (neutralCliffordRepEven a (chiralProjectorPlus x)) = 0
    obtain ⟨y, hy⟩ := neutralCliffordRepEven_mem_plus a (chiralProjectorPlus x)
      (LinearMap.mem_range_self _ x)
    rw [← hy]
    exact DFunLike.congr_fun chiralProjectors_minus_mul_plus y

section ComplexExterior

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Four-degree Peirce coordinates for all operators on the literal complex exterior algebra. -/
def exteriorDegreeCornerEquiv :
    Module.End ℂ (ExteriorAlgebra ℂ V) ≃ₗ[ℂ]
      cornerSpace (K := ℂ) (degreeProjector (V := V)) :=
  cornerEquiv degreeProjector degreeProjectorsComplete

/-- Unlike a cyclic sector shift, an actual exterior creation operator is nilpotent. -/
theorem exterior_creation_square_zero (v : V) :
    (LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ v))^2 =
      (0 : Module.End ℂ (ExteriorAlgebra ℂ V)) := by
  apply LinearMap.ext
  intro x
  change ExteriorAlgebra.ι ℂ v * (ExteriorAlgebra.ι ℂ v * x) = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

end ComplexExterior

/-- The pre-existing finite Lorentzian Hodge operator has square minus identity. -/
theorem hodge_operator_square :
    hodgeStarLinear * hodgeStarLinear = -(1 : Module.End ℂ TwoFormC) :=
  hodgeStarLinear_square

/-- Its fourth-order Fourier resolution recovers only the existing two Hodge sectors. -/
theorem hodge_fourier_projectors :
    projector hodgeStarLinear 0 = 0 ∧
      projector hodgeStarLinear 1 = selfDualPartLinear ∧
      projector hodgeStarLinear 2 = 0 ∧
      projector hodgeStarLinear 3 = antiSelfDualPartLinear := by
  rcases square_neg_one_projectors hodgeStarLinear hodge_operator_square with
    ⟨h0,h1,h2,h3⟩
  refine ⟨h0, ?_, h2, ?_⟩
  · rw [h1]
    apply LinearMap.ext
    intro x
    funext i
    simp [selfDualPartLinear_apply, selfDualPart, hodgeStarLinear_apply]
    ring
  · rw [h3]
    apply LinearMap.ext
    intro x
    funext i
    simp [antiSelfDualPartLinear_apply, antiSelfDualPart, hodgeStarLinear_apply]
    ring

/-- A square-minus-one Hodge action cannot be relabeled as the exterior degree phase. -/
theorem degree_phase_not_square_minus_one {V : Type*} [AddCommGroup V] [Module ℂ V] :
    (phaseEnd : Module.End ℂ (ExteriorAlgebra ℂ V))^2 ≠ -1 :=
  phaseEnd_square_ne_neg_one

section NativeCliffordProducts

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Native Clifford-to-exterior transport keeps the contraction correction.
Since associated(-Q)=-associated(Q), this is the scalar-plus-wedge formula. -/
theorem clifford_product_exterior_readout (Q : QuadraticForm ℝ V) (u v : V) :
    CliffordAlgebra.equivExterior Q
        (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) =
      ExteriorAlgebra.ι ℝ u * ExteriorAlgebra.ι ℝ v -
        algebraMap ℝ _ ((QuadraticMap.associated (-Q)) u v) := by
  change CliffordAlgebra.changeForm
      (CliffordAlgebra.changeForm.associated_neg_proof (Q := Q))
      (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) = _
  exact CliffordAlgebra.changeForm_ι_mul_ι _ u v

/-- A scalar-plus-vector paravector has the stated interval without any invented determinant. -/
theorem clifford_paravector_interval (Q : QuadraticForm ℝ V) (t : ℝ) (v : V) :
    (algebraMap ℝ (CliffordAlgebra Q) t + CliffordAlgebra.ι Q v) *
      (algebraMap ℝ (CliffordAlgebra Q) t - CliffordAlgebra.ι Q v) =
        algebraMap ℝ (CliffordAlgebra Q) (t^2 - Q v) := by
  let r := algebraMap ℝ (CliffordAlgebra Q) t
  let x := CliffordAlgebra.ι Q v
  have hc : r*x = x*r := Algebra.commutes t x
  change (r+x)*(r-x) = _
  calc
    _ = r*r + (x*r-r*x) - x*x := by noncomm_ring
    _ = r*r - x*x := by rw [hc, sub_self, add_zero]
    _ = algebraMap ℝ (CliffordAlgebra Q) (t^2-Q v) := by
      dsimp [r,x]
      rw [CliffordAlgebra.ι_sq_scalar, ← map_mul, ← map_sub]
      simp only [pow_two]

end NativeCliffordProducts

end InfoGeometry.Canonical.ExteriorCyclotomicPeirceBridge
