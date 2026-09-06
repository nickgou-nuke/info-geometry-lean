import InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Clifford.TowerMatrix
import InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

set_option linter.unusedSimpArgs false

/-!
# Associative endomorphism transport for the Peirce coordinate carrier

This owner packages the existing linear equivalence
`Exterior3Coordinates ≃ₗ[ℝ] PeirceCarrier` as the native Mathlib algebra
equivalence between the corresponding endomorphism algebras.  Polynomial
relations are transported through that `AlgEquiv`; this is deliberately an
associative endomorphism statement and does not identify the carrier's
endomorphism algebra with split-octonion multiplication.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitCoordinateEndAlgEquivBridge

open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix

noncomputable def transportAlgEquiv :
    Module.End ℝ Exterior3Coordinates ≃ₐ[ℝ] Module.End ℝ PeirceCarrier :=
  peirceExterior3Equiv.conjAlgEquiv ℝ

@[simp] theorem transportAlgEquiv_apply (T : Module.End ℝ Exterior3Coordinates) :
    transportAlgEquiv T =
      peirceExterior3Equiv.toLinearMap ∘ₗ T ∘ₗ peirceExterior3Equiv.symm.toLinearMap :=
  rfl

@[simp] theorem transportAlgEquiv_apply_peirce
    (T : Module.End ℝ Exterior3Coordinates) (x : Exterior3Coordinates) :
    transportAlgEquiv T (peirceExterior3Equiv x) = peirceExterior3Equiv (T x) := by
  dsimp [transportAlgEquiv]
  simp

@[simp] theorem transportAlgEquiv_apply_symm
    (T : Module.End ℝ Exterior3Coordinates) (y : PeirceCarrier) :
    transportAlgEquiv T y = peirceExterior3Equiv (T (peirceExterior3Equiv.symm y)) :=
  rfl

theorem transport_pow (T : Module.End ℝ Exterior3Coordinates) (n : ℕ) :
    transportAlgEquiv (T ^ n) = (transportAlgEquiv T) ^ n := by
  exact map_pow (transportAlgEquiv :
    Module.End ℝ Exterior3Coordinates ≃ₐ[ℝ] Module.End ℝ PeirceCarrier) T n

theorem transport_power_relation
    (T S : Module.End ℝ Exterior3Coordinates) (n : ℕ) (h : T ^ n = S) :
    (transportAlgEquiv T) ^ n = transportAlgEquiv S := by
  calc
    (transportAlgEquiv T) ^ n = transportAlgEquiv (T ^ n) :=
      (transport_pow T n).symm
    _ = transportAlgEquiv S := congrArg transportAlgEquiv h

theorem transport_aeval (p : Polynomial ℝ)
    (T : Module.End ℝ Exterior3Coordinates) :
    transportAlgEquiv (Polynomial.aeval T p) =
      Polynomial.aeval (transportAlgEquiv T) p := by
  let e : Module.End ℝ Exterior3Coordinates →+*
      Module.End ℝ PeirceCarrier := transportAlgEquiv.toRingEquiv.toRingHom
  have he : (algebraMap ℝ (Module.End ℝ PeirceCarrier)).comp (RingHom.id ℝ) =
      e.comp (algebraMap ℝ (Module.End ℝ Exterior3Coordinates)) := by
    ext c
    simp [e]
  have h := Polynomial.map_aeval_eq_aeval_map
    (φ := RingHom.id ℝ) (ψ := e) he p T
  simpa [e] using h

theorem transport_polynomial_relation
    (p : Polynomial ℝ) (T : Module.End ℝ Exterior3Coordinates)
    (h : Polynomial.aeval T p = 0) :
    Polynomial.aeval (transportAlgEquiv T) p = 0 := by
  rw [← transport_aeval p T, h]
  exact map_zero (transportAlgEquiv :
    Module.End ℝ Exterior3Coordinates ≃ₐ[ℝ] Module.End ℝ PeirceCarrier)

theorem transport_polynomial_relation_iff
    (p : Polynomial ℝ) (T : Module.End ℝ Exterior3Coordinates) :
    Polynomial.aeval (transportAlgEquiv T) p = 0 ↔
      Polynomial.aeval T p = 0 := by
  constructor
  · intro h
    have ht : transportAlgEquiv (Polynomial.aeval T p) = 0 := by
      rw [transport_aeval]
      exact h
    exact (transportAlgEquiv.injective (by simpa using ht))
  · exact transport_polynomial_relation p T

theorem transport_nPotent_iff
    (N : ℕ) (T : Module.End ℝ Exterior3Coordinates) :
    T ^ N = T ↔ (transportAlgEquiv T) ^ N = transportAlgEquiv T := by
  constructor
  · intro h
    exact transport_power_relation T T N h
  · intro h
    apply transportAlgEquiv.injective
    rw [transport_pow]
    exact h

theorem transport_nPotentZeroProjector
    (N : ℕ) (T : Module.End ℝ Exterior3Coordinates) :
    transportAlgEquiv (1 - T ^ (N - 1)) =
      1 - (transportAlgEquiv T) ^ (N - 1) := by
  rw [map_sub, map_one, transport_pow]

theorem transport_commutator (S T : Module.End ℝ Exterior3Coordinates) :
    transportAlgEquiv (S * T - T * S) =
      transportAlgEquiv S * transportAlgEquiv T -
        transportAlgEquiv T * transportAlgEquiv S := by
  rw [map_sub, map_mul, map_mul]

theorem transport_anticommutator (S T : Module.End ℝ Exterior3Coordinates) :
    transportAlgEquiv (S * T + T * S) =
      transportAlgEquiv S * transportAlgEquiv T +
        transportAlgEquiv T * transportAlgEquiv S := by
  rw [map_add, map_mul, map_mul]

theorem transport_commutator_eq_zero_iff
    (S T : Module.End ℝ Exterior3Coordinates) :
    S * T - T * S = 0 ↔
      transportAlgEquiv S * transportAlgEquiv T -
        transportAlgEquiv T * transportAlgEquiv S = 0 := by
  rw [← transport_commutator S T]
  exact transportAlgEquiv.map_eq_zero_iff.symm

theorem transport_anticommutator_eq_zero_iff
    (S T : Module.End ℝ Exterior3Coordinates) :
    S * T + T * S = 0 ↔
      transportAlgEquiv S * transportAlgEquiv T +
        transportAlgEquiv T * transportAlgEquiv S = 0 := by
  rw [← transport_anticommutator S T]
  exact transportAlgEquiv.map_eq_zero_iff.symm

theorem transport_cyclotomic_relation
    (m : ℕ) (T : Module.End ℝ Exterior3Coordinates)
    (h : Polynomial.aeval T (Polynomial.cyclotomic m ℝ) = 0) :
    Polynomial.aeval (transportAlgEquiv T) (Polynomial.cyclotomic m ℝ) = 0 :=
  transport_polynomial_relation (Polynomial.cyclotomic m ℝ) T h

theorem transport_nilpotent
    (T : Module.End ℝ Exterior3Coordinates) (n : ℕ) (h : T ^ n = 0) :
    (transportAlgEquiv T) ^ n = 0 := by
  simpa using transport_power_relation T 0 n h

theorem transport_idempotent (T : Module.End ℝ Exterior3Coordinates)
    (h : T ^ 2 = T) :
    (transportAlgEquiv T) ^ 2 = transportAlgEquiv T := by
  exact transport_power_relation T T 2 h

theorem transport_tripotent (T : Module.End ℝ Exterior3Coordinates)
    (h : T ^ 3 = T) :
    (transportAlgEquiv T) ^ 3 = transportAlgEquiv T := by
  exact transport_power_relation T T 3 h

theorem transport_involution (T : Module.End ℝ Exterior3Coordinates)
    (h : T ^ 2 = 1) :
    (transportAlgEquiv T) ^ 2 = 1 := by
  calc
    (transportAlgEquiv T) ^ 2 = transportAlgEquiv (1 : Module.End ℝ Exterior3Coordinates) :=
      transport_power_relation T 1 2 h
    _ = 1 := map_one (transportAlgEquiv :
      Module.End ℝ Exterior3Coordinates ≃ₐ[ℝ] Module.End ℝ PeirceCarrier)

theorem transport_add (S T : Module.End ℝ Exterior3Coordinates) :
    transportAlgEquiv (S + T) = transportAlgEquiv S + transportAlgEquiv T :=
  map_add (transportAlgEquiv :
    Module.End ℝ Exterior3Coordinates ≃ₐ[ℝ] Module.End ℝ PeirceCarrier) S T

theorem transport_mul (S T : Module.End ℝ Exterior3Coordinates) :
    transportAlgEquiv (S * T) = transportAlgEquiv S * transportAlgEquiv T :=
  map_mul (transportAlgEquiv :
    Module.End ℝ Exterior3Coordinates ≃ₐ[ℝ] Module.End ℝ PeirceCarrier) S T

theorem transport_one :
    transportAlgEquiv (1 : Module.End ℝ Exterior3Coordinates) = 1 :=
  map_one (transportAlgEquiv :
    Module.End ℝ Exterior3Coordinates ≃ₐ[ℝ] Module.End ℝ PeirceCarrier)

/-- 🏆 THEOREM: Carrier Kernel Equivalence under Conjugation:
    $T x = 0 \iff \Phi(T)(e(x)) = 0$. -/
theorem transport_mem_ker_iff (T : Module.End ℝ Exterior3Coordinates) (x : Exterior3Coordinates) :
    T x = 0 ↔ transportAlgEquiv T (peirceExterior3Equiv x) = 0 := by
  rw [transportAlgEquiv_apply_peirce]
  exact (peirceExterior3Equiv.map_eq_zero_iff (x := T x)).symm

/-- 🏆 THEOREM: Carrier Range Equivalence under Conjugation:
    $y \in \operatorname{range}(T) \iff e(y) \in \operatorname{range}(\Phi(T))$. -/
theorem transport_mem_range_iff (T : Module.End ℝ Exterior3Coordinates) (y : Exterior3Coordinates) :
    (∃ x, T x = y) ↔ (∃ z, transportAlgEquiv T z = peirceExterior3Equiv y) := by
  constructor
  · rintro ⟨x, rfl⟩
    use peirceExterior3Equiv x
    rw [transportAlgEquiv_apply_peirce]
  · rintro ⟨z, hz⟩
    use peirceExterior3Equiv.symm z
    rw [transportAlgEquiv_apply_symm] at hz
    exact peirceExterior3Equiv.injective hz

/-- 🏆 THEOREM: Kernel Submodule Transport:
    $e(\ker T) = \ker \Phi(T)$. -/
theorem transport_ker_map (T : Module.End ℝ Exterior3Coordinates) :
    (LinearMap.ker T).map peirceExterior3Equiv.toLinearMap =
      LinearMap.ker (transportAlgEquiv T) := by
  ext z
  simp only [Submodule.mem_map, LinearMap.mem_ker]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change transportAlgEquiv T (peirceExterior3Equiv x) = 0
    rw [transportAlgEquiv_apply_peirce, hx, map_zero]
  · intro hz
    use peirceExterior3Equiv.symm z
    constructor
    · have h : transportAlgEquiv T (peirceExterior3Equiv (peirceExterior3Equiv.symm z)) = 0 := by
        simpa using hz
      rw [transportAlgEquiv_apply_peirce] at h
      exact peirceExterior3Equiv.injective (by simpa using h)
    · exact peirceExterior3Equiv.apply_symm_apply z

/-- 🏆 THEOREM: Range Submodule Transport:
    $e(\operatorname{range} T) = \operatorname{range} \Phi(T)$. -/
theorem transport_range_map (T : Module.End ℝ Exterior3Coordinates) :
    (LinearMap.range T).map peirceExterior3Equiv.toLinearMap =
      LinearMap.range (transportAlgEquiv T) := by
  ext z
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨x, ⟨w, rfl⟩, rfl⟩
    use peirceExterior3Equiv w
    exact transportAlgEquiv_apply_peirce T w
  · rintro ⟨w, rfl⟩
    use T (peirceExterior3Equiv.symm w)
    constructor
    · exact ⟨peirceExterior3Equiv.symm w, rfl⟩
    · exact (transportAlgEquiv_apply_symm T w).symm

/-- 🏆 THEOREM: N-Potent Zero Projector Range Transport:
    $e(\operatorname{range}(I - T^{N-1})) = \operatorname{range}(I - \Phi(T)^{N-1})$. -/
theorem transport_nPotentZeroProjector_range_map
    (N : ℕ) (T : Module.End ℝ Exterior3Coordinates) :
    (LinearMap.range (1 - T ^ (N - 1))).map peirceExterior3Equiv.toLinearMap =
      LinearMap.range (1 - (transportAlgEquiv T) ^ (N - 1)) := by
  have h := transport_range_map (1 - T ^ (N - 1))
  have hproj := transport_nPotentZeroProjector N T
  rw [hproj] at h
  exact h

/-! ## Concrete three-mode matrix readout -/

noncomputable def threeModeMatrixToPeirceAlgEquiv :
    MatStage 3 ≃ₐ[ℝ] Module.End ℝ PeirceCarrier :=
  (matEquivFinPowTwo 3).trans
    (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))).symm

@[simp] theorem threeModeMatrixToPeirceAlgEquiv_apply
    (A : MatStage 3) :
    threeModeMatrixToPeirceAlgEquiv A =
      (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))).symm
        (matEquivFinPowTwo 3 A) :=
  rfl

noncomputable def peirceThreeModeCreation (k : Fin 3) :
    Module.End ℝ PeirceCarrier :=
  threeModeMatrixToPeirceAlgEquiv (jwCreation 3 k)

noncomputable def peirceThreeModeAnnihilation (k : Fin 3) :
    Module.End ℝ PeirceCarrier :=
  threeModeMatrixToPeirceAlgEquiv (jwAnnihilation 3 k)

noncomputable def peirceThreeModeHodgeDirac : Module.End ℝ PeirceCarrier :=
  ∑ k : Fin 3, (peirceThreeModeCreation k + peirceThreeModeAnnihilation k)

theorem threeMode_transport_square_zero
    (A : MatStage 3) (h : A * A = 0) :
    threeModeMatrixToPeirceAlgEquiv A *
        threeModeMatrixToPeirceAlgEquiv A = 0 := by
  rw [← map_mul, h, map_zero]

theorem threeMode_transport_anticommutator
    (A B C : MatStage 3)
    (h : A * B + B * A = C) :
    threeModeMatrixToPeirceAlgEquiv A * threeModeMatrixToPeirceAlgEquiv B +
        threeModeMatrixToPeirceAlgEquiv B * threeModeMatrixToPeirceAlgEquiv A =
      threeModeMatrixToPeirceAlgEquiv C := by
  rw [← map_mul, ← map_mul, ← map_add, h]

end InfoGeometry.Canonical.SplitCoordinateEndAlgEquivBridge
