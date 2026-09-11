import InfoGeometry.Projective.QuantumGrassmannian
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.QuantumTwistor
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot

namespace InfoGeometry.Projective.Sandbox.QuantumTwistorGauge

open QuantumGrassmannian
open QuantumTwistor

variable (R : Type*) [Field R] (q : R) (u : R)

noncomputable def gaugeFree : QuantumMatrixFree R →ₐ[R] QuantumMatrixFree R :=
  FreeAlgebra.lift R (fun idx => u • freeEntry R idx.1 idx.2)

noncomputable def gaugeComp : QuantumMatrixFree R →ₐ[R] QuantumMatrixAlgebra R q :=
  (quantumMatrixQuotient R q).comp (gaugeFree R u)

theorem gaugeComp_rel : ∀ ⦃x y : QuantumMatrixFree R⦄,
    QuantumMatrixRel R q x y → gaugeComp R q u x = gaugeComp R q u y := by
  intro x y h
  cases h with
  | sameRow i j l hjl =>
      simp [gaugeComp, gaugeFree, freeEntry]
      have h0 := congrArg (fun z => u • (u • z)) (entry_sameRow R q i j l hjl)
      simp only [smul_smul] at h0
      have hs : u * (u * q) = q * (u * u) := by ring
      rw [hs] at h0
      simpa [smul_smul] using h0
  | sameColumn i k j hik =>
      simp [gaugeComp, gaugeFree, freeEntry]
      have h0 := congrArg (fun z => u • (u • z)) (entry_sameColumn R q i k j hik)
      simp only [smul_smul] at h0
      have hs : u * (u * q) = q * (u * u) := by ring
      rw [hs] at h0
      simpa [smul_smul] using h0
  | separated i k j l hik hlj =>
      simp [gaugeComp, gaugeFree, freeEntry]
      have h0 := congrArg (fun z => u • (u • z)) (entry_separated R q i k j l hik hlj)
      simp only [smul_smul] at h0
      simpa [smul_smul] using h0
  | crossing i k j l hik hjl =>
      simp [gaugeComp, gaugeFree, freeEntry]
      have h0 := congrArg (fun z => u • (u • z)) (entry_crossing R q i k j l hik hjl)
      simp only [smul_smul, smul_sub] at h0
      have hs : u * (u * (q - q⁻¹)) = (q - q⁻¹) * (u * u) := by ring
      rw [hs] at h0
      simpa [smul_smul] using h0

noncomputable def gaugeAlgHom : QuantumMatrixAlgebra R q →ₐ[R] QuantumMatrixAlgebra R q :=
  RingQuot.liftAlgHom R ⟨gaugeComp R q u, gaugeComp_rel R q u⟩

theorem gaugeAlgHom_entry (i : Fin 2) (j : Fin 4) :
    gaugeAlgHom R q u (entry R q i j) = u • entry R q i j := by
  have h : gaugeAlgHom R q u (entry R q i j) = gaugeComp R q u (freeEntry R i j) := by
    exact RingQuot.liftAlgHom_mkAlgHom_apply R (gaugeComp R q u) (gaugeComp_rel R q u) (freeEntry R i j)
  rw [h]
  change (quantumMatrixQuotient R q) ((gaugeFree R u) (freeEntry R i j)) =
    u • (quantumMatrixQuotient R q) (freeEntry R i j)
  rw [show (gaugeFree R u) (freeEntry R i j) = u • freeEntry R i j by
    simp [gaugeFree, freeEntry]]
  exact map_smul (quantumMatrixQuotient R q) u (freeEntry R i j)

theorem gaugeAlgHom_quantumMinor (p : QuantumMinorIndex) :
    gaugeAlgHom R q u (quantumMinor R q p) = (u ^ 2) • quantumMinor R q p := by
  dsimp [quantumMinor]
  simp only [map_sub, map_mul, map_smul, gaugeAlgHom_entry]
  exact scaledQuantumMinor_eq_weight_two R u q p

theorem gaugeAlgHom_mul (v : R) :
    (gaugeAlgHom R q u).comp (gaugeAlgHom R q v) = gaugeAlgHom R q (u * v) := by
  apply RingQuot.ringQuot_ext' R
  apply FreeAlgebra.hom_ext
  funext idx
  change gaugeAlgHom R q u (gaugeAlgHom R q v (entry R q idx.1 idx.2)) =
    gaugeAlgHom R q (u * v) (entry R q idx.1 idx.2)
  simp only [gaugeAlgHom_entry, map_smul, smul_smul]
  rw [mul_comm v u]

theorem gaugeAlgHom_one : gaugeAlgHom R q 1 = AlgHom.id R (QuantumMatrixAlgebra R q) := by
  apply RingQuot.ringQuot_ext' R
  apply FreeAlgebra.hom_ext
  funext idx
  change gaugeAlgHom R q 1 (entry R q idx.1 idx.2) = entry R q idx.1 idx.2
  simp only [gaugeAlgHom_entry, one_smul]

noncomputable def gaugeAlgEquiv (unit : Rˣ) :
    QuantumMatrixAlgebra R q ≃ₐ[R] QuantumMatrixAlgebra R q :=
  AlgEquiv.ofAlgHom (gaugeAlgHom R q unit) (gaugeAlgHom R q ↑unit⁻¹)
    (by simpa [gaugeAlgHom_one] using gaugeAlgHom_mul R q (u := (unit : R)) (↑unit⁻¹ : R))
    (by simpa [gaugeAlgHom_one] using gaugeAlgHom_mul R q (u := (↑unit⁻¹ : R)) (unit : R))

noncomputable def gaugeCoordinateRing : coordinateRing R q →ₐ[R] coordinateRing R q where
  toFun x := ⟨gaugeAlgHom R q u x.1, by
    rcases x with ⟨val, hval⟩
    dsimp
    induction hval using Algebra.adjoin_induction with
    | mem val h =>
      rcases h with ⟨p, rfl⟩
      rw [gaugeAlgHom_quantumMinor]
      exact (coordinateRing R q).smul_mem (quantumMinor_mem_coordinateRing R q p) (u ^ 2)
    | algebraMap r =>
      rw [AlgHom.commutes]
      exact Subalgebra.algebraMap_mem (coordinateRing R q) r
    | add a b ha hb iha ihb =>
      rw [map_add]
      exact Subalgebra.add_mem (coordinateRing R q) iha ihb
    | mul a b ha hb iha ihb =>
      rw [map_mul]
      exact Subalgebra.mul_mem (coordinateRing R q) iha ihb
  ⟩
  map_one' := Subtype.ext (map_one (gaugeAlgHom R q u))
  map_mul' x y := Subtype.ext (map_mul (gaugeAlgHom R q u) x.1 y.1)
  map_zero' := Subtype.ext (map_zero (gaugeAlgHom R q u))
  map_add' x y := Subtype.ext (map_add (gaugeAlgHom R q u) x.1 y.1)
  commutes' r := Subtype.ext (AlgHom.commutes (gaugeAlgHom R q u) r)

noncomputable def gauge_covariance (P : QuantumTwistor.QuantumPluckerGenerator (coordinateRing R q)) :
    QuantumTwistor.QuantumPluckerGenerator (coordinateRing R q) :=
  { p01 := gaugeCoordinateRing R q u P.p01
    p02 := gaugeCoordinateRing R q u P.p02
    p03 := gaugeCoordinateRing R q u P.p03
    p12 := gaugeCoordinateRing R q u P.p12
    p13 := gaugeCoordinateRing R q u P.p13
    p23 := gaugeCoordinateRing R q u P.p23 }

theorem gauge_covariance_p01 :
    (gaugeCoordinateRing R q u (QuantumTwistor.quantumPluckerMap R q).p01 : QuantumMatrixAlgebra R q) =
    (u ^ 2) • (QuantumTwistor.quantumPluckerMap R q).p01.1 := by
  exact gaugeAlgHom_quantumMinor R q u ⟨(0, 1), by decide⟩

theorem gauge_covariance_p02 :
    (gaugeCoordinateRing R q u (QuantumTwistor.quantumPluckerMap R q).p02 : QuantumMatrixAlgebra R q) =
    (u ^ 2) • (QuantumTwistor.quantumPluckerMap R q).p02.1 := by
  exact gaugeAlgHom_quantumMinor R q u ⟨(0, 2), by decide⟩

theorem gauge_covariance_p03 :
    (gaugeCoordinateRing R q u (QuantumTwistor.quantumPluckerMap R q).p03 : QuantumMatrixAlgebra R q) =
    (u ^ 2) • (QuantumTwistor.quantumPluckerMap R q).p03.1 := by
  exact gaugeAlgHom_quantumMinor R q u ⟨(0, 3), by decide⟩

theorem gauge_covariance_p12 :
    (gaugeCoordinateRing R q u (QuantumTwistor.quantumPluckerMap R q).p12 : QuantumMatrixAlgebra R q) =
    (u ^ 2) • (QuantumTwistor.quantumPluckerMap R q).p12.1 := by
  exact gaugeAlgHom_quantumMinor R q u ⟨(1, 2), by decide⟩

theorem gauge_covariance_p13 :
    (gaugeCoordinateRing R q u (QuantumTwistor.quantumPluckerMap R q).p13 : QuantumMatrixAlgebra R q) =
    (u ^ 2) • (QuantumTwistor.quantumPluckerMap R q).p13.1 := by
  exact gaugeAlgHom_quantumMinor R q u ⟨(1, 3), by decide⟩

theorem gauge_covariance_p23 :
    (gaugeCoordinateRing R q u (QuantumTwistor.quantumPluckerMap R q).p23 : QuantumMatrixAlgebra R q) =
    (u ^ 2) • (QuantumTwistor.quantumPluckerMap R q).p23.1 := by
  exact gaugeAlgHom_quantumMinor R q u ⟨(2, 3), by decide⟩

end InfoGeometry.Projective.Sandbox.QuantumTwistorGauge
