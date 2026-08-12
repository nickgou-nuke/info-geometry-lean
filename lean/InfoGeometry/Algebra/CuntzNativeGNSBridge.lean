import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import InfoGeometry.Algebra.CuntzKMSState
import InfoGeometry.Algebra.CuntzKMSCondition
import InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum
import InfoGeometry.Physics.CStarCuntzTensorQuotient

/-!
# Native Mathlib GNS bridge for the Cuntz/KMS layer

The bridge is generic in a genuine positive functional on a C*-algebra.  The
current tensor-quotient `CuntzAlg` remains algebraic, so this file does not
invent a C*-algebra instance for it.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

namespace InfoGeometry.Algebra.CuntzNativeGNSBridge

open InfoGeometry.OperatorAlgebra.GNSMathlibBridge
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (φ : A →ₚ[ℂ] ℂ)

/-! `StarAlgHom` is the native Mathlib carrier for a star-preserving algebra
algebra homomorphism. The old local structure duplicated these fields. -/
abbrev CuntzStarRepresentation (n : ℕ) (B : Type*)
    [Semiring B] [StarRing B] [Algebra ℂ B] :=
  CuntzAlg n →⋆ₐ[ℂ] B

@[simp] theorem CuntzStarRepresentation.map_one
    {n : ℕ} {B : Type*} [Semiring B] [StarRing B] [Algebra ℂ B]
    (ρ : CuntzStarRepresentation n B) : ρ.toAlgHom 1 = 1 := by
  exact ρ.toAlgHom.map_one

theorem CuntzStarRepresentation.map_star
    {n : ℕ} {B : Type*} [Semiring B] [StarRing B] [Algebra ℂ B]
    (ρ : CuntzStarRepresentation n B) (x : CuntzAlg n) :
    ρ.toAlgHom (star x) = star (ρ.toAlgHom x) := by
  exact StarHomClass.map_star ρ x

/-- A positive C*-functional extending an algebraic Cuntz functional. -/
structure CuntzPositiveExtension (n : ℕ) (B : Type*)
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] where
  representation : CuntzStarRepresentation n B
  omega : CuntzAlg n →ₗ[ℂ] ℂ
  phi : B →ₚ[ℂ] ℂ
  extension : ∀ x, phi (representation.toAlgHom x) = omega x

abbrev CuntzGNSHilbertSpace := φ.GNS

noncomputable abbrev cuntzGNSRepresentation :
    A →⋆ₐ[ℂ] (φ.GNS →L[ℂ] φ.GNS) := φ.gnsStarAlgHom

noncomputable def gnsVacuum : φ.GNS :=
  InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsVacuum φ

theorem gnsVacuum_norm_sq (hφ : φ 1 = 1) :
    ‖gnsVacuum φ‖ ^ 2 = 1 := by
  have h := InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsVacuum_norm_eq_one φ hφ
  change ‖InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsVacuum φ‖ ^ 2 = 1
  nlinarith [h]

theorem gnsRepresentation_apply_vacuum (a : A) :
    cuntzGNSRepresentation φ a (gnsVacuum φ) = (φ.toPreGNS a : φ.GNS) := by
  simpa [cuntzGNSRepresentation, gnsVacuum] using
    (InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsOrbitMap_eq_gnsRepresentation_vacuum φ a).symm

theorem gns_state_expectation_recovery (a : A) :
    ⟪gnsVacuum φ, cuntzGNSRepresentation φ a (gnsVacuum φ)⟫_ℂ = φ a := by
  simpa [cuntzGNSRepresentation, gnsVacuum] using
    (InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gns_state_expectation_recovery φ a)

theorem positiveFunctional_star_mul_self_re (a : A) :
    0 ≤ (φ (star a * a)).re :=
  (Complex.nonneg_iff.mp
    (PositiveLinearMap.map_nonneg φ
      (CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr ⟨a, rfl⟩))).1

theorem positiveFunctional_star_mul_self_im (a : A) :
    (φ (star a * a)).im = 0 := by
  exact (Complex.nonneg_iff.mp
    (PositiveLinearMap.map_nonneg φ
      (CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr ⟨a, rfl⟩))).2.symm

theorem gnsVacuum_cyclic :
    DenseRange (fun a : A => cuntzGNSRepresentation φ a (gnsVacuum φ)) := by
  rw [show (fun a : A => cuntzGNSRepresentation φ a (gnsVacuum φ)) =
      fun a : A => InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsOrbitMap φ a by
    funext a
    simpa [gnsVacuum, cuntzGNSRepresentation] using
      (InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsOrbitMap_eq_gnsRepresentation_vacuum φ a).symm]
  exact InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsOrbitMap_denseRange φ

theorem represented_cuntz_expectation_recovery
    {n : ℕ} (E : CuntzPositiveExtension n A) (x : CuntzAlg n) :
    ⟪gnsVacuum E.phi,
      cuntzGNSRepresentation E.phi
        (E.representation.toAlgHom x)
        (gnsVacuum E.phi)⟫_ℂ = E.omega x := by
  calc
    ⟪gnsVacuum E.phi,
        cuntzGNSRepresentation E.phi
          (E.representation.toAlgHom x)
          (gnsVacuum E.phi)⟫_ℂ =
        E.phi (E.representation.toAlgHom x) :=
      gns_state_expectation_recovery E.phi (E.representation.toAlgHom x)
    _ = E.omega x := E.extension x

theorem represented_cuntz_expectation_recovery_of
    {n : ℕ} (ρ : CuntzStarRepresentation n A)
    (omega : CuntzAlg n →ₗ[ℂ] ℂ)
    (h_extension : ∀ x, φ (ρ.toAlgHom x) = omega x)
    (x : CuntzAlg n) :
    ⟪gnsVacuum φ,
      cuntzGNSRepresentation φ (ρ.toAlgHom x) (gnsVacuum φ)⟫_ℂ = omega x := by
  calc
    ⟪gnsVacuum φ,
        cuntzGNSRepresentation φ (ρ.toAlgHom x) (gnsVacuum φ)⟫_ℂ =
        φ (ρ.toAlgHom x) :=
      gns_state_expectation_recovery φ (ρ.toAlgHom x)
    _ = omega x := h_extension x

/-! ### Explicit representation and pullback extension -/

namespace ExplicitCStarFamily

open InfoGeometry.Physics.CStarCuntzTensorQuotient
open InfoGeometry.Topology.AlgebraicCuntzQuotient

abbrev AlgebraicCuntzSource (n : ℕ) :=
  InfoGeometry.Topology.AlgebraicCuntzQuotient.CuntzAlg ℂ (Fin n)

/-- The existing universal representation induced by a genuine Cuntz family. -/
def representation
    {A : Type*} [CStarAlgebra A] (n : ℕ)
    (F : CStarCuntzFamily A (Fin n)) :
    AlgebraicCuntzSource n →ₐ[ℂ] A :=
  F.lift

@[simp] theorem representation_S
    {A : Type*} [CStarAlgebra A] (n : ℕ)
    (F : CStarCuntzFamily A (Fin n)) (i : Fin n) :
    representation n F (S (R := ℂ) i) = F.S i := by
  exact CStarCuntzFamily.lift_S F i

@[simp] theorem representation_T
    {A : Type*} [CStarAlgebra A] (n : ℕ)
    (F : CStarCuntzFamily A (Fin n)) (i : Fin n) :
    representation n F (T (R := ℂ) i) = star (F.S i) := by
  exact CStarCuntzFamily.lift_T F i

/-- Pull a native positive functional back along the explicit representation. -/
def pulledBackFunctional
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (n : ℕ)
    (F : CStarCuntzFamily A (Fin n)) (φ : A →ₚ[ℂ] ℂ) :
    AlgebraicCuntzSource n →ₗ[ℂ] ℂ :=
  φ.toLinearMap.comp (representation n F).toLinearMap

@[simp] theorem pulledBackFunctional_apply
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (n : ℕ)
    (F : CStarCuntzFamily A (Fin n)) (φ : A →ₚ[ℂ] ℂ)
    (x : AlgebraicCuntzSource n) :
    pulledBackFunctional n F φ x = φ (representation n F x) := by
  rfl

/-- Explicit extension packet: the algebraic functional is the pullback of `φ`. -/
structure PositiveExtension
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (n : ℕ) where
  family : CStarCuntzFamily A (Fin n)
  phi : A →ₚ[ℂ] ℂ
  omega : AlgebraicCuntzSource n →ₗ[ℂ] ℂ
  extension : ∀ x, phi (representation n family x) = omega x

def pulledBackPositiveExtension
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (n : ℕ)
    (F : CStarCuntzFamily A (Fin n)) (φ : A →ₚ[ℂ] ℂ) :
    PositiveExtension (A := A) n where
  family := F
  phi := φ
  omega := pulledBackFunctional n F φ
  extension := by
    intro x
    rfl

theorem positiveExtension_omega_eq_pullback
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (n : ℕ)
    (F : CStarCuntzFamily A (Fin n)) (φ : A →ₚ[ℂ] ℂ) (x : AlgebraicCuntzSource n) :
    (pulledBackPositiveExtension (A := A) n F φ).omega x =
      φ (representation n F x) := by
  rfl

end ExplicitCStarFamily

end InfoGeometry.Algebra.CuntzNativeGNSBridge
