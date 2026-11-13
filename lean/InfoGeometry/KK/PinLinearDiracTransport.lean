/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FreedPinRepresentation
import InfoGeometry.KK.LinearDiracTransport
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Represented Pin transport of linear Dirac domains

The frame is the actual group homomorphism `continuousPinAction`, obtained
from represented normalized Clifford units. Its multiplication transports
domains and operators in the same order as the group action. Domain density,
closed graphs, compact resolvents, and zero-mode range sectors use the native
constructions in `LinearDiracTransport`.

For a suspended representation, anticommutation with the target vector
actions implies invariance under every source Pin element by the Clifford
generation theorem. No separate hypothesis for each Pin element is added.

Each frame is a continuous linear automorphism. Continuity in a family
parameter is proved when the represented operators vary continuously in
operator norm; the inverse continuity then follows from native Banach algebra
inversion. These are coordinate-transport results, not a construction of a
geometric Fredholm family or a differential KO pushforward.
-/

noncomputable section

namespace InfoGeometry.KK.PinLinearDiracTransport

open InfoGeometry.Clifford.FreedCliffordSuspension
open InfoGeometry.Clifford.NormalizedVectorPin
open InfoGeometry.Clifford.FreedPinRepresentation
open InfoGeometry.KK.LinearDiracTransport
open InfoGeometry.KK.RealSplitKreinLinearResolventBridge

variable {N H : Type*} [AddCommGroup N] [Module ℝ N]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Forget only the continuity proof in a bounded Clifford representation. -/
def underlyingRepresentation (Q : QuadraticForm ℝ N)
    (ρ : CliffordAlgebra Q →ₐ[ℝ] (H →L[ℝ] H)) :
    CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ H where
  __ := ContinuousLinearMap.toLinearMapRingHom.comp ρ.toRingHom
  commutes' r := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem underlyingRepresentation_apply (Q : QuadraticForm ℝ N)
    (ρ : CliffordAlgebra Q →ₐ[ℝ] (H →L[ℝ] H))
    (a : CliffordAlgebra Q) (x : H) :
    underlyingRepresentation Q ρ a x = ρ a x := rfl

section PinAction

variable (Q : QuadraticForm ℝ N)
variable (ρ : CliffordAlgebra Q →ₐ[ℝ] (H →L[ℝ] H))

/-- The represented group product acts on actual submodule domains. -/
theorem pin_domain_mul (S : Submodule ℝ H) (g h : pin Q) :
    domain (continuousPinAction Q ρ (g * h)) S =
      domain (continuousPinAction Q ρ g) (domain (continuousPinAction Q ρ h) S) :=
  domain_representation_mul (continuousPinAction Q ρ) S g h

/-- The right factor acts first on a vector in the original operator domain. -/
theorem pin_operator_mul_on_domain {S : Submodule ℝ H} (D : S →ₗ[ℝ] H)
    (g h : pin Q) (x : S) :
    operator (continuousPinAction Q ρ (g * h)) D
        (domainEquiv (continuousPinAction Q ρ (g * h)) S x) =
      operator (continuousPinAction Q ρ g) (operator (continuousPinAction Q ρ h) D)
        (domainEquiv (continuousPinAction Q ρ g)
          (domain (continuousPinAction Q ρ h) S)
          (domainEquiv (continuousPinAction Q ρ h) S x)) := by
  rw [map_mul]
  exact operator_mul_on_domain _ _ D x

/-- Dense domains and closed graphs are proved properties of each Pin transport. -/
theorem pin_domain_regular {S : Submodule ℝ H} (D : S →ₗ[ℝ] H)
    (hS : Dense (S : Set H)) (hD : IsClosed (graph D)) (g : pin Q) :
    Dense (domain (continuousPinAction Q ρ g) S : Set H) ∧
      IsClosed (graph (operator (continuousPinAction Q ρ g) D)) :=
  ⟨dense_domain _ _ hS, closed_graph _ _ hD⟩

/-- A genuine bounded projector remains idempotent after the Pin frame change. -/
theorem pin_projector_idempotent (P : H →L[ℝ] H)
    (hP : IsIdempotentElem P) (g : pin Q) :
    IsIdempotentElem ((continuousPinAction Q ρ g).conjContinuousAlgEquiv P) :=
  hP.map (continuousPinAction Q ρ g).conjContinuousAlgEquiv

/-- An actual grading involution remains involutive in the transported frame. -/
theorem pin_grading_involutive (Γ : H →L[ℝ] H)
    (hΓ : Γ * Γ = 1) (g : pin Q) :
    (continuousPinAction Q ρ g).conjContinuousAlgEquiv Γ *
      (continuousPinAction Q ρ g).conjContinuousAlgEquiv Γ = 1 := by
  rw [← map_mul, hΓ, map_one]

/-- The actual zero-mode projector sectors are linearly equivalent. -/
def pin_kernelSectorEquiv {S : Submodule ℝ H} (D : S →ₗ[ℝ] H)
    (P : H →L[ℝ] H) (g : pin Q) :
    kernelSector D P ≃ₗ[ℝ]
      kernelSector (operator (continuousPinAction Q ρ g) D)
        ((continuousPinAction Q ρ g).conjContinuousAlgEquiv P) :=
  kernelSectorEquiv (continuousPinAction Q ρ g) D P

theorem pin_kernelSector_finrank {S : Submodule ℝ H} (D : S →ₗ[ℝ] H)
    (P : H →L[ℝ] H) (g : pin Q) :
    Module.finrank ℝ (kernelSector (operator (continuousPinAction Q ρ g) D)
      ((continuousPinAction Q ρ g).conjContinuousAlgEquiv P)) =
        Module.finrank ℝ (kernelSector D P) :=
  finrank_kernelSector (continuousPinAction Q ρ g) D P

/-- Only the source zero-mode sector, not the ambient space, must be finite. -/
theorem pin_kernelSector_finiteDimensional {S : Submodule ℝ H} (D : S →ₗ[ℝ] H)
    (P : H →L[ℝ] H) [FiniteDimensional ℝ (kernelSector D P)] (g : pin Q) :
    FiniteDimensional ℝ (kernelSector (operator (continuousPinAction Q ρ g) D)
      ((continuousPinAction Q ρ g).conjContinuousAlgEquiv P)) :=
  finiteDimensional_kernelSector (continuousPinAction Q ρ g) D P

/-- The dimension difference for two transported sectors is independent of the
Pin frame. With finite chiral projectors, this is the chiral kernel formula. -/
theorem pin_kernelDifference_family {B : Type*} (g : B → pin Q)
    {S : Submodule ℝ H} (D : S →ₗ[ℝ] H) (Pplus Pminus : H →L[ℝ] H) (s t : B) :
    (Module.finrank ℝ (kernelSector (operator (continuousPinAction Q ρ (g s)) D)
      ((continuousPinAction Q ρ (g s)).conjContinuousAlgEquiv Pplus)) : ℤ) -
      (Module.finrank ℝ (kernelSector (operator (continuousPinAction Q ρ (g s)) D)
        ((continuousPinAction Q ρ (g s)).conjContinuousAlgEquiv Pminus)) : ℤ) =
    (Module.finrank ℝ (kernelSector (operator (continuousPinAction Q ρ (g t)) D)
      ((continuousPinAction Q ρ (g t)).conjContinuousAlgEquiv Pplus)) : ℤ) -
      (Module.finrank ℝ (kernelSector (operator (continuousPinAction Q ρ (g t)) D)
        ((continuousPinAction Q ρ (g t)).conjContinuousAlgEquiv Pminus)) : ℤ) :=
  chiralKernelDifference_family (fun b => continuousPinAction Q ρ (g b)) D Pplus Pminus s t

section Complete

variable [CompleteSpace H]

/-- Both actual inverse equations and compactness are transported. -/
theorem pin_resolvent_inverse {S : Submodule ℝ H} {D : S →ₗ[ℝ] H}
    (R : RealSplitKreinLinearResolventData S D)
    (hR : Function.Injective (shifted R)) (g : pin Q) :
    (∀ x : H, shifted (resolvent (continuousPinAction Q ρ g) R)
      ⟨(resolvent (continuousPinAction Q ρ g) R).resolvent x,
        (resolvent (continuousPinAction Q ρ g) R).resolvent_preserves_domain x⟩ = x) ∧
    (∀ x : domain (continuousPinAction Q ρ g) S,
      (resolvent (continuousPinAction Q ρ g) R).resolvent
        (shifted (resolvent (continuousPinAction Q ρ g) R) x) = x) ∧
    IsCompactOperator (resolvent (continuousPinAction Q ρ g) R).resolvent :=
  ⟨shifted_apply_resolvent _, resolvent_shifted _ R hR, (resolvent _ R).compact⟩

/-- Operator-norm continuity of represented units forces continuity of their
actual inverses. No topology on the abstract Pin group is required. -/
theorem continuous_pin_inverse_family {B : Type*} [TopologicalSpace B]
    (g : B → pin Q)
    (hg : Continuous (fun b => (pinRepresentation Q ρ (g b) : H →L[ℝ] H))) :
    Continuous (fun b => ((continuousPinAction Q ρ (g b)).symm : H →L[ℝ] H)) := by
  change Continuous (fun b => (↑((pinRepresentation Q ρ (g b))⁻¹) : H →L[ℝ] H))
  apply continuous_iff_continuousAt.mpr
  intro b
  simpa only [Function.comp_def, Ring.inverse_unit] using
    (NormedRing.inverse_continuousAt (pinRepresentation Q ρ (g b))).comp hg.continuousAt

/-- The conjugated bounded operator is a genuine operator-norm continuous
family whenever the represented Pin operators are operator-norm continuous. -/
theorem continuous_pin_conjugate_family {B : Type*} [TopologicalSpace B]
    (g : B → pin Q)
    (hg : Continuous (fun b => (pinRepresentation Q ρ (g b) : H →L[ℝ] H)))
    (A : H →L[ℝ] H) :
    Continuous (fun b => (continuousPinAction Q ρ (g b)).conjContinuousAlgEquiv A) := by
  change Continuous (fun b =>
    ((pinRepresentation Q ρ (g b) : H →L[ℝ] H) * A) *
      ((continuousPinAction Q ρ (g b)).symm : H →L[ℝ] H))
  exact (hg.mul continuous_const).mul (continuous_pin_inverse_family Q ρ g hg)

/-- In particular, the constructed compact resolvents form a continuous
bounded family under the same explicit norm-continuity hypothesis. -/
theorem continuous_pin_resolvent_family {B : Type*} [TopologicalSpace B]
    (g : B → pin Q)
    (hg : Continuous (fun b => (pinRepresentation Q ρ (g b) : H →L[ℝ] H)))
    {S : Submodule ℝ H} {D : S →ₗ[ℝ] H}
    (R : RealSplitKreinLinearResolventData S D) :
    Continuous (fun b => (resolvent (continuousPinAction Q ρ (g b)) R).resolvent) :=
  continuous_pin_conjugate_family Q ρ g hg R.resolvent

end Complete

end PinAction

section SuspendedAction

variable (Q : QuadraticForm ℝ N)
variable (ρ : CliffordAlgebra (positiveForm Q) →ₐ[ℝ] (H →L[ℝ] H))

/-- Target-vector oddness gives commutation with every suspended Pin frame. -/
theorem positive_pin_commutes_grading (Γ : H →L[ℝ] H)
    (hΓ : ∀ v x, Γ (ρ (CliffordAlgebra.ι (positiveForm Q) v) x) =
      -(ρ (CliffordAlgebra.ι (positiveForm Q) v) (Γ x)))
    (g : pin Q) (x : H) :
    Γ (continuousPinAction Q (positiveRepresentation Q ρ) g x) =
      continuousPinAction Q (positiveRepresentation Q ρ) g (Γ x) :=
  positivePin_preserves_grading Q (underlyingRepresentation (positiveForm Q) ρ)
    Γ.toLinearMap hΓ g x

/-- Thus the target grading is fixed by conjugation; the source Clifford
grading is not identified with it. -/
theorem positive_pin_conjugate_grading (Γ : H →L[ℝ] H)
    (hΓ : ∀ v x, Γ (ρ (CliffordAlgebra.ι (positiveForm Q) v) x) =
      -(ρ (CliffordAlgebra.ι (positiveForm Q) v) (Γ x))) (g : pin Q) :
    (continuousPinAction Q (positiveRepresentation Q ρ) g).conjContinuousAlgEquiv Γ = Γ := by
  ext x
  change continuousPinAction Q (positiveRepresentation Q ρ) g
    (Γ ((continuousPinAction Q (positiveRepresentation Q ρ) g).symm x)) = Γ x
  rw [← positive_pin_commutes_grading Q ρ Γ hΓ g]
  simp

/-- Both chiral-projector formulas are fixed by the suspended Pin action.
For involutive `Γ`, these are the usual two chiral projectors. -/
theorem positive_pin_conjugate_chiralProjectors (Γ : H →L[ℝ] H)
    (hΓ : ∀ v x, Γ (ρ (CliffordAlgebra.ι (positiveForm Q) v) x) =
      -(ρ (CliffordAlgebra.ι (positiveForm Q) v) (Γ x))) (g : pin Q) :
    (continuousPinAction Q (positiveRepresentation Q ρ) g).conjContinuousAlgEquiv
        (((2 : ℝ)⁻¹) • (1 + Γ)) = ((2 : ℝ)⁻¹) • (1 + Γ) ∧
    (continuousPinAction Q (positiveRepresentation Q ρ) g).conjContinuousAlgEquiv
        (((2 : ℝ)⁻¹) • (1 - Γ)) = ((2 : ℝ)⁻¹) • (1 - Γ) := by
  constructor
  · rw [map_smul, map_add, map_one, positive_pin_conjugate_grading Q ρ Γ hΓ g]
  · rw [map_smul, map_sub, map_one, positive_pin_conjugate_grading Q ρ Γ hΓ g]

/-- The zero-mode dimensions in the ranges of `(1 ± Γ) / 2` are invariant
under the full suspended Pin action. When `Γ` is involutive, these are its
positive and negative chiral kernel sectors. Generator oddness proves that
both formulas are fixed; involutivity is not needed for this range identity. -/
theorem positive_pin_fixed_chiralKernel_finrank {S : Submodule ℝ H}
    (D : S →ₗ[ℝ] H) (Γ : H →L[ℝ] H)
    (hΓ : ∀ v x, Γ (ρ (CliffordAlgebra.ι (positiveForm Q) v) x) =
      -(ρ (CliffordAlgebra.ι (positiveForm Q) v) (Γ x))) (g : pin Q) :
    Module.finrank ℝ (kernelSector
        (operator (continuousPinAction Q (positiveRepresentation Q ρ) g) D)
        (((2 : ℝ)⁻¹) • (1 + Γ))) =
      Module.finrank ℝ (kernelSector D (((2 : ℝ)⁻¹) • (1 + Γ))) ∧
    Module.finrank ℝ (kernelSector
        (operator (continuousPinAction Q (positiveRepresentation Q ρ) g) D)
        (((2 : ℝ)⁻¹) • (1 - Γ))) =
      Module.finrank ℝ (kernelSector D (((2 : ℝ)⁻¹) • (1 - Γ))) := by
  obtain ⟨hPlus, hMinus⟩ := positive_pin_conjugate_chiralProjectors Q ρ Γ hΓ g
  constructor
  · exact (congrArg
      (fun P : H →L[ℝ] H => Module.finrank ℝ (kernelSector
        (operator (continuousPinAction Q (positiveRepresentation Q ρ) g) D) P))
      hPlus).symm.trans
        (pin_kernelSector_finrank Q (positiveRepresentation Q ρ) D
          (((2 : ℝ)⁻¹) • (1 + Γ)) g)
  · exact (congrArg
      (fun P : H →L[ℝ] H => Module.finrank ℝ (kernelSector
        (operator (continuousPinAction Q (positiveRepresentation Q ρ) g) D) P))
      hMinus).symm.trans
        (pin_kernelSector_finrank Q (positiveRepresentation Q ρ) D
          (((2 : ℝ)⁻¹) • (1 - Γ)) g)

/-- Domain invariance is derived from the target vector actions and their
Clifford generation, including the inverse of every source Pin element. -/
theorem positive_pin_domain_eq (S : Submodule ℝ H)
    (hS : ∀ v x, x ∈ S → ρ (CliffordAlgebra.ι (positiveForm Q) v) x ∈ S)
    (g : pin Q) :
    domain (continuousPinAction Q (positiveRepresentation Q ρ) g) S = S := by
  have hp (u : pin Q) (x : H) (hx : x ∈ S) :
      continuousPinAction Q (positiveRepresentation Q ρ) u x ∈ S :=
    preserves_domain_of_vectors (positiveForm Q)
      (underlyingRepresentation (positiveForm Q) ρ) S hS
      (positiveMap Q ((u : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) x hx
  ext x
  rw [mem_domain_iff]
  constructor
  · intro hx
    simpa using hp g ((continuousPinAction Q (positiveRepresentation Q ρ) g).symm x) hx
  · intro hx
    have hi := hp g⁻¹ x hx
    rw [map_inv] at hi
    exact hi

end SuspendedAction

end InfoGeometry.KK.PinLinearDiracTransport
