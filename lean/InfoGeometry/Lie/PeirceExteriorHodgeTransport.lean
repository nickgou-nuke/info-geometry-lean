import InfoGeometry.Canonical.SplitOctonionCayleyHodgeDualityBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionPeirceExteriorBridge
import InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors

noncomputable section

namespace InfoGeometry.Lie.PeirceExteriorHodgeTransport

open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge
open InfoGeometry.Lie.SplitOctonionPeirceExteriorBridge
open InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors
open InfoGeometry.Canonical.SplitOctonionCayleyHodgeDualityBridge

theorem hodgeStar_gradedChirality_anticommutes :
    hodgeStar ∘ₗ gradedChirality =
      -(gradedChirality ∘ₗ hodgeStar) := by
  apply LinearMap.ext
  intro x
  ext <;> simp [hodgeStar, gradedChirality, LinearMap.comp_apply]

noncomputable def peirceHodgeStar :
    PeirceCarrier →ₗ[ℝ] PeirceCarrier :=
  (peirceExterior3Equiv.conjAlgEquiv ℝ) hodgeStar

noncomputable def peirceGradedChirality :
    PeirceCarrier →ₗ[ℝ] PeirceCarrier :=
  (peirceExterior3Equiv.conjAlgEquiv ℝ) gradedChirality

/-- The transported particle--hole (Cayley-conjugation) involution. -/
noncomputable def peirceParticleHole :
    PeirceCarrier →ₗ[ℝ] PeirceCarrier :=
  (peirceExterior3Equiv.conjAlgEquiv ℝ) cayleyConjugation

/-- The transported middle-degree exchange used in the particle--hole factorization. -/
noncomputable def peirceMiddleDegreeExchange :
    PeirceCarrier →ₗ[ℝ] PeirceCarrier :=
  (peirceExterior3Equiv.conjAlgEquiv ℝ) middleDegreeExchange

theorem peirceHodgeStar_apply
    (x : Exterior3Coordinates) :
    peirceHodgeStar (peirceExterior3Equiv x) =
      peirceExterior3Equiv (hodgeStar x) := by
  rw [peirceHodgeStar, LinearEquiv.conjAlgEquiv_apply]
  change peirceExterior3Equiv
      (hodgeStar (peirceExterior3Equiv.symm (peirceExterior3Equiv x))) =
    peirceExterior3Equiv (hodgeStar x)
  rw [peirceExterior3Equiv.symm_apply_apply]

theorem peirceHodgeStar_apply_all
    (y : PeirceCarrier) :
    peirceHodgeStar y =
      peirceExterior3Equiv
        (hodgeStar (peirceExterior3Equiv.symm y)) := by
  rw [peirceHodgeStar, LinearEquiv.conjAlgEquiv_apply]
  rfl

theorem peirceHodgeStar_sq :
    peirceHodgeStar * peirceHodgeStar = 1 := by
  change (peirceExterior3Equiv.conjAlgEquiv ℝ) hodgeStar *
      (peirceExterior3Equiv.conjAlgEquiv ℝ) hodgeStar = 1
  rw [← map_mul, hodgeStar_sq, map_one]

theorem peirceHodgeStar_gradedChirality_anticommutes :
    peirceHodgeStar * peirceGradedChirality =
      -(peirceGradedChirality * peirceHodgeStar) := by
  change (peirceExterior3Equiv.conjAlgEquiv ℝ) hodgeStar *
      (peirceExterior3Equiv.conjAlgEquiv ℝ) gradedChirality =
    -((peirceExterior3Equiv.conjAlgEquiv ℝ) gradedChirality *
      (peirceExterior3Equiv.conjAlgEquiv ℝ) hodgeStar)
  have hcoord : hodgeStar * gradedChirality =
      -(gradedChirality * hodgeStar) := by
    simpa [Module.End.mul_eq_comp] using
      hodgeStar_gradedChirality_anticommutes
  simpa only [map_mul, map_neg] using congrArg
    (fun T : Module.End ℝ Exterior3Coordinates =>
      (peirceExterior3Equiv.conjAlgEquiv ℝ) T) hcoord

theorem peirceGradedChirality_sq :
    peirceGradedChirality * peirceGradedChirality = 1 := by
  change (peirceExterior3Equiv.conjAlgEquiv ℝ) gradedChirality *
      (peirceExterior3Equiv.conjAlgEquiv ℝ) gradedChirality = 1
  rw [← map_mul, gradedChirality_sq, map_one]

theorem peirceParticleHole_sq :
    peirceParticleHole * peirceParticleHole = 1 := by
  change (peirceExterior3Equiv.conjAlgEquiv ℝ) cayleyConjugation *
      (peirceExterior3Equiv.conjAlgEquiv ℝ) cayleyConjugation = 1
  rw [← map_mul, cayleyConjugation_sq, map_one]

theorem peirceParticleHole_eq_middleDegreeExchange_comp_hodge :
    peirceParticleHole = peirceMiddleDegreeExchange ∘ₗ peirceHodgeStar := by
  change (peirceExterior3Equiv.conjAlgEquiv ℝ) cayleyConjugation =
    (peirceExterior3Equiv.conjAlgEquiv ℝ) middleDegreeExchange ∘ₗ
      (peirceExterior3Equiv.conjAlgEquiv ℝ) hodgeStar
  rw [← Module.End.mul_eq_comp, ← map_mul,
    cayley_eq_middleExchange_comp_hodge, Module.End.mul_eq_comp]

theorem peirceParticleHole_hodgeStar_relation :
    peirceParticleHole = peirceHodgeStar ∘ₗ peirceMiddleDegreeExchange := by
  change (peirceExterior3Equiv.conjAlgEquiv ℝ) cayleyConjugation =
    (peirceExterior3Equiv.conjAlgEquiv ℝ) hodgeStar ∘ₗ
      (peirceExterior3Equiv.conjAlgEquiv ℝ) middleDegreeExchange
  rw [← Module.End.mul_eq_comp, ← map_mul,
    cayley_eq_hodge_comp_middleExchange, Module.End.mul_eq_comp]

theorem peirceHodgeStar_coordinate (x : PeirceCarrier) :
    peirceHodgeStar x =
      ![x 4, x 5, x 6, x 7, x 0, x 1, x 2, x 3] := by
  let y := peirceExterior3Equiv.symm x
  have hx : x = peirceExterior3Equiv y := by
    exact (peirceExterior3Equiv.apply_symm_apply x).symm
  rw [hx, peirceHodgeStar_apply]
  rcases y with ⟨a, b, c, d⟩
  ext i
  fin_cases i <;> simp [hodgeStar, peirceExterior3Equiv, toPeirce, fromPeirce]

/-! The coordinate formula becomes an explicit action on the ordered
Peirce frame.  These lemmas are the concrete `u_±, σ_i^±` convention bridge:
indices `0,1,2,3` are the plus sector and `4,5,6,7` the minus sector. -/

@[simp] theorem peirceHodgeStar_single (i : Fin 8) :
    peirceHodgeStar (Pi.single i 1) =
      Pi.single (i + 4) 1 := by
  rw [peirceHodgeStar_coordinate]
  fin_cases i <;> ext j <;> fin_cases j <;> simp

theorem peirceHodgeStar_projectorPP_projectorMM :
    peirceHodgeStar * projectorPP =
      projectorMM * peirceHodgeStar * projectorPP := by
  apply LinearMap.ext
  intro x
  change peirceHodgeStar (projectorPP x) =
    projectorMM (peirceHodgeStar (projectorPP x))
  rw [projectorPP_apply, projectorMM_apply,
    peirceHodgeStar_coordinate]
  simp

theorem peirceHodgeStar_projectorPM_projectorMP :
    peirceHodgeStar * projectorPM =
      projectorMP * peirceHodgeStar * projectorPM := by
  apply LinearMap.ext
  intro x
  change peirceHodgeStar (projectorPM x) =
    projectorMP (peirceHodgeStar (projectorPM x))
  rw [projectorPM_apply, peirceHodgeStar_coordinate]
  simp [projectorMP_apply]

theorem peirceHodgeStar_projectorPM_projectorMP_add_projectorMM :
    peirceHodgeStar * projectorPM =
      (projectorMP + projectorMM) * peirceHodgeStar * projectorPM := by
  apply LinearMap.ext
  intro x
  change peirceHodgeStar (projectorPM x) =
    (projectorMP + projectorMM) (peirceHodgeStar (projectorPM x))
  rw [projectorPM_apply, peirceHodgeStar_coordinate]
  simp [projectorMP_apply, projectorMM_apply]

theorem peirceHodgeStar_projectorMP_projectorPM :
    peirceHodgeStar * projectorMP =
      projectorPM * peirceHodgeStar * projectorMP := by
  apply LinearMap.ext
  intro x
  change peirceHodgeStar (projectorMP x) =
    projectorPM (peirceHodgeStar (projectorMP x))
  rw [projectorMP_apply, peirceHodgeStar_coordinate]
  simp [projectorPM_apply]

theorem peirceHodgeStar_projectorMP_projectorPP_add_projectorPM :
    peirceHodgeStar * projectorMP =
      (projectorPP + projectorPM) * peirceHodgeStar * projectorMP := by
  apply LinearMap.ext
  intro x
  change peirceHodgeStar (projectorMP x) =
    (projectorPP + projectorPM) (peirceHodgeStar (projectorMP x))
  rw [projectorMP_apply, peirceHodgeStar_coordinate]
  simp [projectorPP_apply, projectorPM_apply]

theorem peirceHodgeStar_projectorMM_projectorPP :
    peirceHodgeStar * projectorMM =
      projectorPP * peirceHodgeStar * projectorMM := by
  apply LinearMap.ext
  intro x
  change peirceHodgeStar (projectorMM x) =
    projectorPP (peirceHodgeStar (projectorMM x))
  rw [projectorMM_apply, peirceHodgeStar_coordinate,
    projectorPP_apply]
  simp

/-! Complete complementary-sector readout for the transported Hodge
operator.  The four clauses are the native Peirce realization of
`Λ⁰ ↔ Λ³` and `Λ¹ ↔ Λ²`. -/
theorem peirceHodgeStar_complementary_projectors :
    peirceHodgeStar * projectorPP = projectorMM * peirceHodgeStar * projectorPP ∧
      peirceHodgeStar * projectorPM = projectorMP * peirceHodgeStar * projectorPM ∧
      peirceHodgeStar * projectorMP = projectorPM * peirceHodgeStar * projectorMP ∧
      peirceHodgeStar * projectorMM = projectorPP * peirceHodgeStar * projectorMM := by
  exact ⟨peirceHodgeStar_projectorPP_projectorMM,
    peirceHodgeStar_projectorPM_projectorMP,
    peirceHodgeStar_projectorMP_projectorPM,
    peirceHodgeStar_projectorMM_projectorPP⟩

end InfoGeometry.Lie.PeirceExteriorHodgeTransport
