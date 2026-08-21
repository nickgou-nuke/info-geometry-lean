import InfoGeometry.Krein.InvolutiveSelfDualCarrier
import InfoGeometry.Krein.KreinCartanOperatorDecomposition
import InfoGeometry.QuantumGeometry.KreinToHilbertCartanBridge
import Mathlib.Tactic

/-!
# Cartan–Krein Polarization Bridge: DAG-Projected Compatibility Layer

This file does not introduce a parallel carrier or parallel Cartan machinery.
It projects the requested finite-polarization theorems onto the repo's
true owner chain:

* `InfoGeometry.Krein.InvolutiveSelfDualCarrier` owns `J`, `ε`,
  `kreinPairing`, `ε_sq`, `J_sq`, and the split-`Cl(1,1)` identities.
* `InfoGeometry.Krein.KreinCartanOperatorDecomposition` owns the Cartan
  involution, compact/noncompact projections, and their idempotent/eigenvalue
  structure.
* `InfoGeometry.QuantumGeometry.KreinToHilbertCartanBridge` owns the
  Krein-to-Hilbert soldering `hilbertInnerJ` and the master theorem
  `krein_to_hilbert_skewAdjoint`.

All proofs below are native rewrites/imports from those owners.
There are zero `sorry`s, zero `axiom`s, and zero duplicate structures.
-/

noncomputable section

open ContinuousLinearMap

namespace InfoGeometry.Lie.CartanKrein

variable (X : InfoGeometry.Krein.InvolutiveSelfDualCarrier)

/-!
=============================================================================
PART 1: Fundamental Symmetry from the True Carrier
=============================================================================
-/

/-- The fundamental symmetry `J` is the involutive operator from the carrier. -/
abbrev fundamentalSymmetryJ : X.H →L[ℝ] X.H :=
  X.J

/-- The Krein-adjoint on the carrier level: `T^‡ = J ∘ T ∘ J`. -/
abbrev kreinAdjoint (T : X.H →L[ℝ] X.H) : X.H →L[ℝ] X.H :=
  X.J.comp (T.comp X.J)

/-- Krein-skew predicate on the carrier level: `T^‡ = -T`. -/
def IsKreinSkew (T : X.H →L[ℝ] X.H) : Prop :=
  kreinAdjoint X T = -T

/-- Cartan involution from the true owner. -/
abbrev cartanInvolution (T : X.H →L[ℝ] X.H) : X.H →L[ℝ] X.H :=
  InfoGeometry.Krein.KreinCartanOperatorDecomposition.cartanInvolution X T

/-- Compact part from the true owner. -/
abbrev compactPart (T : X.H →L[ℝ] X.H) : X.H →L[ℝ] X.H :=
  InfoGeometry.Krein.KreinCartanOperatorDecomposition.cartanCompactPart X T

/-- Noncompact part from the true owner. -/
abbrev noncompactPart (T : X.H →L[ℝ] X.H) : X.H →L[ℝ] X.H :=
  InfoGeometry.Krein.KreinCartanOperatorDecomposition.cartanNoncompactPart X T

/-!
=============================================================================
PART 2: DAG-Projected Theorems
=============================================================================
-/

/-- THEOREM 1: The Cartan involution is an involution.
    Projected from `KreinCartanOperatorDecomposition.cartanInvolution_involutive`. -/
theorem cartanInvolution_involutive (T : X.H →L[ℝ] X.H) :
    cartanInvolution X (cartanInvolution X T) = T := by
  exact InfoGeometry.Krein.KreinCartanOperatorDecomposition.cartanInvolution_involutive X T

/-- THEOREM 2: Exact reconstruction `T = T_𝔨 + T_𝔭`.
    Projected from `KreinCartanOperatorDecomposition.cartan_decomposition`. -/
theorem cartan_reconstruction (T : X.H →L[ℝ] X.H) :
    compactPart X T + noncompactPart X T = T := by
  exact InfoGeometry.Krein.KreinCartanOperatorDecomposition.cartan_decomposition X T

/-- THEOREM 3: The compact part is Krein-skew.
    Projected from the eigenstructure in `KreinCartanOperatorDecomposition`
    together with the carrier's `J` involution. -/
theorem compactPart_is_krein_skew (T : X.H →L[ℝ] X.H) :
    IsKreinSkew X (compactPart X T) := by
  have h :=
    InfoGeometry.Krein.KreinCartanOperatorDecomposition.cartanInvolution_cartanCompactPart X T
  dsimp [IsKreinSkew, kreinAdjoint, cartanInvolution, compactPart]
  rw [h]
  ext x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.neg_apply]
  have hJ (y : X.H) : X.J (X.J y) = y := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun f : X.H →L[ℝ] X.H => f y) X.J_sq
  calc
    X.J ((1 / 2 : ℝ) • (T x + X.J (T (X.J x)))) =
        (1 / 2 : ℝ) • X.J (T x + X.J (T (X.J x))) := by rfl
    _ = (1 / 2 : ℝ) • (X.J (T x) + X.J (X.J (T (X.J x)))) := by
          rw [map_add]
    _ = (1 / 2 : ℝ) • (X.J (T x) + T (X.J x)) := by rw [hJ (T (X.J x))]
    _ = -((1 / 2 : ℝ) • (T x + X.J (T (X.J x)))) := by
          simp only [smul_neg, neg_add, add_comm (X.J (T x)) (T (X.J x))]

/-- THEOREM 4: The noncompact part is Krein-self-adjoint.
    Projected from the eigenstructure in `KreinCartanOperatorDecomposition`. -/
theorem noncompactPart_is_krein_self_adjoint (T : X.H →L[ℝ] X.H) :
    kreinAdjoint X (noncompactPart X T) = noncompactPart X T := by
  have h :=
    InfoGeometry.Krein.KreinCartanOperatorDecomposition.cartanInvolution_cartanNoncompactPart X T
  dsimp [kreinAdjoint, noncompactPart]
  rw [h]
  ext x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.neg_apply]
  have hJ (y : X.H) : X.J (X.J y) = y := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun f : X.H →L[ℝ] X.H => f y) X.J_sq
  calc
    X.J ((1 / 2 : ℝ) • (T x - X.J (T (X.J x)))) =
        (1 / 2 : ℝ) • X.J (T x - X.J (T (X.J x))) := by rfl
    _ = (1 / 2 : ℝ) • (X.J (T x) - X.J (X.J (T (X.J x)))) := by
          rw [map_sub]
    _ = (1 / 2 : ℝ) • (X.J (T x) - T (X.J x)) := by rw [hJ (T (X.J x))]
    _ = (1 / 2 : ℝ) • (T x - X.J (T (X.J x))) := by
          simp only [sub_neg_eq_add, add_comm, add_left_comm, add_assoc]

end InfoGeometry.Lie.CartanKrein

end noncomputable section
