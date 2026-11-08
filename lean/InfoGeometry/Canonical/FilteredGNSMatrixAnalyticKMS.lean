/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ComplexTimeCorrelation
import InfoGeometry.Canonical.FiniteMappedGibbsDensityExponential
import InfoGeometry.Geometry.PrimaMateriaThermodynamics

/-!
# Analytic KMS assembly on the native represented GNS closure

All operator and analytic constructions are elaborated with an arbitrary
compatible native state family.  A mapped finite Hermitian Hamiltonian fixes
the already constructed real-time flow and entire operator orbit.  The native
vacuum supplies positivity and normalization.  Its algebraic twisted identity
then proves the KMS strip boundary; no analytic boundary is an input.

The concrete finite-seed owner specializes these declarations and discharges
the twisted premise from its proved Gibbs-colimit identity.  Keeping that
specialization separate avoids unfolding the constructed state family while
reconstructing dependent normed-space dictionaries.
-/

noncomputable section
open scoped ComplexOrder
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000
set_option autoImplicit false

namespace CStarStateColimit.Native.FilteredGNSMatrixAnalyticKMS

open FilteredStarAlgebraDirectLimit FilteredGNSRepresentedCStarClosure
open FilteredGNSVacuumReadback FilteredGNSRepresentedKMS FilteredGNSMatrixRealTime
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
open InfoGeometry.Canonical.FiniteSeedRepresentedDensityExponential
open InfoGeometry.OperatorAlgebra.ComplexTimeConjugation
open InfoGeometry.OperatorAlgebra.ComplexTimeCorrelation

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
local notation "C" => representedCStarClosure Stage sys ω
variable {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The entire orbit of the actual represented matrix generator. -/
def matrixComplexTime
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (z : ℂ) (B : C) : C :=
  alpha (matrixGenerator Stage sys ω f H hH : C) z B

/-- The native vacuum readout of that same operator orbit. -/
def matrixCorrelation
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (v : I) (A B : C) (z : ℂ) : ℂ :=
  correlation (representedVacuumFunctional Stage sys ω v)
    (matrixGenerator Stage sys ω f H hH : C) A B z

/-- The algebraic Gibbs identity required by the generic assembly.  The
concrete finite-seed specialization proves it from its actual state. -/
def matrixFunctionalTwisted
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) (v : I) : Prop :=
  ∀ X Y : C,
    representedVacuumFunctional Stage sys ω v (X * Y) =
      representedVacuumFunctional Stage sys ω v
        (Y * ((matrixDensityUnit Stage sys ω f H hH β : C) * X *
          (↑((matrixDensityUnit Stage sys ω f H hH β)⁻¹) : C)))

/-- The existing raw-density alignment converts native represented twisted
cyclicity to the mapped finite matrix density, before any specialization. -/
theorem matrixFunctionalTwisted_of_algebraic
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) (i v : I)
    (e : Matrix n n ℂ →⋆ₐ[ℂ] Stage i)
    (δraw : (AlgebraicStarDirectLimit Stage sys)ˣ)
    (hδ : δraw = Units.map
      ((algebraicStarDirectLimitOf Stage sys i).comp e).toMonoidHom
      (gibbsDensityUnit H hH β))
    (htwist : representedVacuumTwistedCyclic Stage sys ω v δraw) :
    matrixFunctionalTwisted Stage sys ω
      (representedMatrixStageMap Stage sys ω i e) H hH β v := by
  cases hδ
  change matrixFunctionalTwisted Stage sys ω
    (representedMatrixStageMap Stage sys ω i e) H hH β v at htwist
  exact htwist

theorem matrixDensityUnit_eq_exp
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    (matrixDensityUnit Stage sys ω f H hH β : C) =
      NormedSpace.exp ((-β) • (matrixGenerator Stage sys ω f H hH : C)) := by
  change f (↑(gibbsDensityUnit H hH β) : Matrix n n ℂ) = _
  rw [gibbsDensityUnit_coe]
  exact map_gibbsDensity_eq_exp f H hH β

theorem matrixDensityUnit_inv_eq_exp
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    (↑((matrixDensityUnit Stage sys ω f H hH β)⁻¹) : C) =
      NormedSpace.exp (β • (matrixGenerator Stage sys ω f H hH : C)) :=
  map_gibbsDensityUnit_inv_eq_exp f H hH β

theorem matrixComplexTime_ofReal
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (B : C) (t : ℝ) :
    matrixComplexTime Stage sys ω f H hH (t : ℂ) B =
      matrixRealTimeAut Stage sys ω f H hH t B :=
  alpha_ofReal_eq_unitary (matrixGenerator Stage sys ω f H hH) B t

theorem matrixComplexTime_analyticAt
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (B : C) (z : ℂ) :
    AnalyticAt ℂ (fun w => matrixComplexTime Stage sys ω f H hH w B) z :=
  alpha_analyticAt (matrixGenerator Stage sys ω f H hH : C) B z

theorem matrixCorrelation_analyticAt
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (v : I) (A B : C) (z : ℂ) :
    AnalyticAt ℂ (matrixCorrelation Stage sys ω f H hH v A B) z :=
  correlation_analyticAt (representedVacuumFunctional Stage sys ω v)
    (matrixGenerator Stage sys ω f H hH) A B z

theorem matrixCorrelation_lower_boundary
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (v : I) (A B : C) (t : ℝ) :
    matrixCorrelation Stage sys ω f H hH v A B (t : ℂ) =
      representedVacuumFunctional Stage sys ω v
        (A * matrixRealTimeAut Stage sys ω f H hH t B) :=
  correlation_real_boundary (representedVacuumFunctional Stage sys ω v)
    (matrixGenerator Stage sys ω f H hH) A B t

theorem matrixCorrelation_upper_boundary
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) (v : I)
    (htwist : matrixFunctionalTwisted Stage sys ω f H hH β v)
    (A B : C) (t : ℝ) :
    matrixCorrelation Stage sys ω f H hH v A B
        ((t : ℂ) + Complex.I * (β : ℂ)) =
      representedVacuumFunctional Stage sys ω v
        (matrixRealTimeAut Stage sys ω f H hH t B * A) := by
  have h := correlation_upper_boundary_of_twisted
    (representedVacuumFunctional Stage sys ω v)
    (matrixGenerator Stage sys ω f H hH)
    (matrixDensityUnit Stage sys ω f H hH β) β
    (matrixDensityUnit_eq_exp Stage sys ω f H hH β)
    (matrixDensityUnit_inv_eq_exp Stage sys ω f H hH β) htwist A B t
  change matrixCorrelation Stage sys ω f H hH v A B
      ((t : ℂ) + Complex.I * (β : ℂ)) =
    representedVacuumFunctional Stage sys ω v
      (matrixComplexTime Stage sys ω f H hH (t : ℂ) B * A) at h
  rw [matrixComplexTime_ofReal] at h
  exact h

theorem matrixCorrelation_continuousOn_closedStrip
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) (v : I) (A B : C) :
    ContinuousOn (matrixCorrelation Stage sys ω f H hH v A B)
      (InfoGeometry.Geometry.kmsClosedStrip β) :=
  correlation_continuousOn_closedStrip (representedVacuumFunctional Stage sys ω v)
    (matrixGenerator Stage sys ω f H hH) A B β

theorem matrixCorrelation_differentiableOn_openStrip
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) (v : I) (A B : C) :
    DifferentiableOn ℂ (matrixCorrelation Stage sys ω f H hH v A B)
      (InfoGeometry.Geometry.kmsOpenStrip β) :=
  correlation_differentiableOn_openStrip (representedVacuumFunctional Stage sys ω v)
    (matrixGenerator Stage sys ω f H hH) A B β

theorem matrixCorrelation_bounded_closedStrip
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) (v : I) (A B : C) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ z : ℂ, z ∈ InfoGeometry.Geometry.kmsClosedStrip β →
        ‖matrixCorrelation Stage sys ω f H hH v A B z‖ ≤ M :=
  correlation_bounded_closedStrip (representedVacuumFunctional Stage sys ω v)
    (matrixGenerator Stage sys ω f H hH) A B β

/-- All analytic, positivity, normalization, and boundary fields are proved.
The finite-seed consumer supplies the already established algebraic identity. -/
def matrixKMSState
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) (hβ : 0 < β) (v : I)
    (htwist : matrixFunctionalTwisted Stage sys ω f H hH β v) :
    InfoGeometry.Geometry.IsKMSState
      (fun t => (matrixRealTimeAut Stage sys ω f H hH t).toAlgEquiv) β where
  state := (representedVacuumFunctional Stage sys ω v).toLinearMap
  state_positive := fun a =>
    (RCLike.nonneg_iff.mp
      (representedVacuumFunctional_star_mul_self Stage sys ω v a)).1
  state_one := representedVacuumFunctional_one Stage sys ω v
  beta_pos := hβ
  boundaryFunction := matrixCorrelation Stage sys ω f H hH v
  boundaryFunction_continuous :=
    matrixCorrelation_continuousOn_closedStrip Stage sys ω f H hH β v
  boundaryFunction_holomorphic :=
    matrixCorrelation_differentiableOn_openStrip Stage sys ω f H hH β v
  lower_boundary := matrixCorrelation_lower_boundary Stage sys ω f H hH v
  upper_boundary := matrixCorrelation_upper_boundary Stage sys ω f H hH β v htwist

end CStarStateColimit.Native.FilteredGNSMatrixAnalyticKMS
