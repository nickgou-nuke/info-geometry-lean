import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# InfoGeometry.Canonical.CurrentConjugationLemmas

Concrete conjugation transport lemmas for current operators.
-/

namespace InfoGeometry.Canonical.CurrentConjugationLemmas

open Filter
open InfoGeometry.Canonical.CurrentSugawaraBridge

@[simp]
theorem conjugateEnd_zero
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V) :
    conjugateEnd U (0 : V →ₗ[𝕜] V) = 0 := by
  ext v
  simp [conjugateEnd]

@[simp]
theorem conjugateEnd_sub
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V) (A B : V →ₗ[𝕜] V) :
    conjugateEnd U (A - B) = conjugateEnd U A - conjugateEnd U B := by
  ext v
  simp [sub_eq_add_neg, conjugateEnd]

theorem conjugateEnd_commutator
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V)
    (A B : V →ₗ[𝕜] V) :
    (conjugateEnd U A).commutator (conjugateEnd U B) =
      conjugateEnd U (A.commutator B) := by
  simp [LinearMap.commutator, conjugateEnd_mul, conjugateEnd_sub]

theorem current_commutator_conjugated
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (H : CurrentHeisenbergRep 𝕜 V)
    (U : V ≃ₗ[𝕜] V)
    (m n : Int) :
    (conjugateEnd U (H.J m)).commutator
        (conjugateEnd U (H.J n)) =
      if m + n = 0 then
        (m : 𝕜) • (1 : V →ₗ[𝕜] V)
      else
        0 := by
  rw [conjugateEnd_commutator, H.comm]
  split_ifs with hmn
  · simp [conjugateEnd_smul, conjugateEnd_one]
  · simp [conjugateEnd_zero]

theorem current_trunc_conjugated
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (H : CurrentHeisenbergRep 𝕜 V)
    (U : V ≃ₗ[𝕜] V) :
    ∀ v, atTop.Eventually
      (fun l => conjugateEnd U (H.J l) v = 0) := by
  intro v
  have htr := H.trunc (U.symm v)
  refine htr.mono ?_
  intro l hl
  simp [conjugateEnd, hl]

/--
Conjugation transports the Sugawara `lgen` action modewise.
-/
theorem currentSugawara_lgen_conjugated
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (H : CurrentHeisenbergRep 𝕜 V)
    (U : V ≃ₗ[𝕜] V)
    (n : Int) :
    conjugateEnd U
      (H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n))
    =
    conjugateEnd U (H.sugawaraStressMode n) := by
  simpa [H.currentSugawaraRepresentation_lgen_apply n]

/--
Conjugation preserves the Virasoro central generator action (`cgen ↦ 1`).
-/
theorem currentSugawara_cgen_conjugated
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (H : CurrentHeisenbergRep 𝕜 V)
    (U : V ≃ₗ[𝕜] V) :
    conjugateEnd U
      (H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.cgen 𝕜))
    =
    (1 : V →ₗ[𝕜] V) := by
  simpa [H.currentSugawaraRepresentation_central, conjugateEnd_one]

/--
Conjugation transports the full Virasoro bracket law for the Sugawara
representation.
-/
theorem currentSugawaraRepresentation_bracket_conjugated
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (H : CurrentHeisenbergRep 𝕜 V)
    (U : V ≃ₗ[𝕜] V)
    (x y : VirasoroProject.VirasoroAlgebra 𝕜) :
    (conjugateEnd U (H.currentSugawaraRepresentation x)).commutator
    (conjugateEnd U (H.currentSugawaraRepresentation y))
    =
    conjugateEnd U (H.currentSugawaraRepresentation ⁅x, y⁆) := by
  rw [conjugateEnd_commutator]
  exact congrArg (conjugateEnd U)
    (H.currentSugawaraRepresentation.map_lie x y).symm

/--
Conjugation transports the Sugawara/Virasoro stress-mode commutator law.

This is the direct operator identity
`[U L_m U⁻¹, U L_n U⁻¹] = U [L_m, L_n] U⁻¹`.
-/
theorem sugawara_commutator_conjugated
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (H : CurrentHeisenbergRep 𝕜 V)
    (U : V ≃ₗ[𝕜] V)
    (m n : Int) :
    (conjugateEnd U (H.sugawaraStressMode m)).commutator
        (conjugateEnd U (H.sugawaraStressMode n)) =
      (m - n : 𝕜) • conjugateEnd U (H.sugawaraStressMode (m + n))
      +
      (if m + n = 0 then
        (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : V →ₗ[𝕜] V))
      else 0) := by
  rw [conjugateEnd_commutator, H.sugawaraStressMode_virasoroBracket]
  ext v
  by_cases hmn : m + n = 0
  · simp [conjugateEnd, hmn, sub_eq_add_neg, add_smul]
    rw [← Int.cast_smul_eq_zsmul (R := 𝕜) m (U ((H.sugawaraStressMode 0) (U.symm v)))]
    rw [← Int.cast_smul_eq_zsmul (R := 𝕜) n (U ((H.sugawaraStressMode 0) (U.symm v)))]
  · simp [conjugateEnd, hmn, sub_eq_add_neg, add_smul]
    rw [← Int.cast_smul_eq_zsmul (R := 𝕜) m (U ((H.sugawaraStressMode (m + n)) (U.symm v)))]
    rw [← Int.cast_smul_eq_zsmul (R := 𝕜) n (U ((H.sugawaraStressMode (m + n)) (U.symm v)))]

/--
Conjugated Virasoro `lgen` commutator in Sugawara form.
-/
theorem currentSugawara_lgen_commutator_conjugated
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (H : CurrentHeisenbergRep 𝕜 V)
    (U : V ≃ₗ[𝕜] V)
    (m n : Int) :
    (conjugateEnd U
      (H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m))).commutator
    (conjugateEnd U
      (H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)))
    =
    (m - n : 𝕜) • conjugateEnd U (H.sugawaraStressMode (m + n))
      +
      (if m + n = 0 then
        (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : V →ₗ[𝕜] V))
      else 0) := by
  simpa [currentSugawara_lgen_conjugated] using
    sugawara_commutator_conjugated (H := H) (U := U) m n

/--
Conjugated central/`lgen` commutator vanishes.
-/
theorem currentSugawara_cgen_lgen_commutator_conjugated
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (H : CurrentHeisenbergRep 𝕜 V)
    (U : V ≃ₗ[𝕜] V)
    (n : Int) :
    (conjugateEnd U
      (H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.cgen 𝕜))).commutator
    (conjugateEnd U
      (H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)))
    = 0 := by
  rw [currentSugawara_cgen_conjugated, currentSugawara_lgen_conjugated]
  simp [LinearMap.commutator]

/--
Swapped conjugated `lgen`/central commutator also vanishes.
-/
theorem currentSugawara_lgen_cgen_commutator_conjugated
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (H : CurrentHeisenbergRep 𝕜 V)
    (U : V ≃ₗ[𝕜] V)
    (n : Int) :
    (conjugateEnd U
      (H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n))).commutator
    (conjugateEnd U
      (H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.cgen 𝕜)))
    = 0 := by
  rw [currentSugawara_lgen_conjugated, currentSugawara_cgen_conjugated]
  simp [LinearMap.commutator]

/--
Skew-symmetry of conjugated `lgen` commutators.
-/
theorem currentSugawara_lgen_commutator_conjugated_skew
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (H : CurrentHeisenbergRep 𝕜 V)
    (U : V ≃ₗ[𝕜] V)
    (m n : Int) :
    (conjugateEnd U
      (H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m))).commutator
      (conjugateEnd U
        (H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)))
    =
    -((conjugateEnd U
      (H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n))).commutator
      (conjugateEnd U
        (H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)))) := by
  simp [LinearMap.commutator, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/--
Conjugating every current mode by a linear equivalence yields a new
`CurrentHeisenbergRep`.
-/
noncomputable def conjugatedCurrentHeisenbergRep
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (H : CurrentHeisenbergRep 𝕜 V)
    (U : V ≃ₗ[𝕜] V) :
    CurrentHeisenbergRep 𝕜 V where
  J := fun n => conjugateEnd U (H.J n)
  trunc := by
    intro v
    simpa using current_trunc_conjugated H U v
  comm := by
    intro m n
    simpa using current_commutator_conjugated H U m n

end InfoGeometry.Canonical.CurrentConjugationLemmas
