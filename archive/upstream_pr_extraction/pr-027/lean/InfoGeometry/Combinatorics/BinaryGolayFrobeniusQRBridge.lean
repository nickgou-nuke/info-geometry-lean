import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import InfoGeometry.Combinatorics.BinaryGolayRootField
import InfoGeometry.Combinatorics.BinaryGolayCyclotomicCosets

namespace InfoGeometry.Combinatorics.BinaryGolayFrobeniusQRBridge

open BinaryCyclicGolayPolynomial
open BinaryGolayRootField
open BinaryGolayCyclotomicCosets

abbrev RootField := BinaryGolayRootField.RootField

noncomputable section

local instance : DecidableEq RootField := Classical.decEq RootField

noncomputable def generatorFrobeniusOrbit (a : RootField) : Finset RootField :=
  Finset.image (fun k : Fin 11 => a ^ (2 ^ (k : ℕ)))
    (Finset.univ : Finset (Fin 11))

noncomputable def generatorQRPowerOrbit (a : RootField) : Finset RootField :=
  Finset.image (fun r : ℕ => a ^ r) quadraticResidueCoset

def frobeniusExponent (k : Fin 11) : Fin 23 :=
  ⟨2 ^ (k : ℕ) % 23, Nat.mod_lt _ (by norm_num)⟩

theorem frobeniusExponent_injective :
    Function.Injective frobeniusExponent := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | norm_num [frobeniusExponent] at hij

theorem generatorFrobeniusOrbit_mem_generatorRoots {a : RootField}
    (ha : Polynomial.eval₂ (algebraMap F₂ RootField) a generator = 0)
    {x : RootField} (hx : x ∈ generatorFrobeniusOrbit a) :
    Polynomial.eval₂ (algebraMap F₂ RootField) x generator = 0 := by
  change x ∈ Finset.image (fun k : Fin 11 => a ^ (2 ^ (k : ℕ)))
      (Finset.univ : Finset (Fin 11)) at hx
  rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
  exact generator_root_frobenius_pow ha k

theorem frobenius_exponent_mem_quadraticResidueCoset (k : Fin 11) :
    2 ^ (k : ℕ) % 23 ∈ quadraticResidueCoset := by
  rw [← quadraticResidueCoset_eq_frobeniusOrbit]
  exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩

theorem power_eq_power_mod_twentyThree {a : RootField}
    (ha : a ^ 23 = 1) (n : ℕ) :
    a ^ n = a ^ (n % 23) := by
  have hn : n = n % 23 + 23 * (n / 23) := by omega
  rw [hn, pow_add, pow_mul, ha]
  simp

theorem generatorFrobeniusOrbit_card_of_power_injective {a : RootField}
    (ha23 : a ^ 23 = 1)
    (hp : Function.Injective (fun i : Fin 23 => a ^ (i : ℕ))) :
    (generatorFrobeniusOrbit a).card = 11 := by
  have h_inj : Function.Injective
      (fun k : Fin 11 => a ^ (2 ^ (k : ℕ))) := by
    intro i j hij
    have hi : a ^ (2 ^ (i : ℕ)) = a ^ (frobeniusExponent i : ℕ) := by
      exact power_eq_power_mod_twentyThree ha23 _
    have hj : a ^ (2 ^ (j : ℕ)) = a ^ (frobeniusExponent j : ℕ) := by
      exact power_eq_power_mod_twentyThree ha23 _
    have hpow : a ^ (frobeniusExponent i : ℕ) =
        a ^ (frobeniusExponent j : ℕ) := by
      calc
        a ^ (frobeniusExponent i : ℕ) = a ^ (2 ^ (i : ℕ)) := hi.symm
        _ = a ^ (2 ^ (j : ℕ)) := hij
        _ = a ^ (frobeniusExponent j : ℕ) := hj
    exact frobeniusExponent_injective (hp hpow)
  change (Finset.image (fun k : Fin 11 => a ^ (2 ^ (k : ℕ)))
      (Finset.univ : Finset (Fin 11))).card = 11
  rw [Finset.card_image_of_injective _ h_inj]
  simp

theorem generatorFrobeniusOrbit_eq_generatorQRPowerOrbit {a : RootField}
    (ha23 : a ^ 23 = 1) :
    generatorFrobeniusOrbit a = generatorQRPowerOrbit a := by
  ext x
  constructor
  · intro hx
    change x ∈ Finset.image (fun k : Fin 11 => a ^ (2 ^ (k : ℕ)))
        (Finset.univ : Finset (Fin 11)) at hx
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    refine Finset.mem_image.mpr ⟨2 ^ (k : ℕ) % 23,
      frobenius_exponent_mem_quadraticResidueCoset k, ?_⟩
    exact (power_eq_power_mod_twentyThree ha23 _).symm
  · intro hx
    change x ∈ Finset.image (fun r : ℕ => a ^ r) quadraticResidueCoset at hx
    rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
    rw [← quadraticResidueCoset_eq_frobeniusOrbit] at hr
    rcases Finset.mem_image.mp hr with ⟨k, hk, hkr⟩
    change a ^ r ∈ Finset.image (fun k : Fin 11 => a ^ (2 ^ (k : ℕ)))
      (Finset.univ : Finset (Fin 11))
    refine Finset.mem_image.mpr ⟨k, Finset.mem_univ k, ?_⟩
    calc
      a ^ (2 ^ (k : ℕ)) = a ^ (2 ^ (k : ℕ) % 23) :=
        power_eq_power_mod_twentyThree ha23 _
      _ = a ^ r := by rw [hkr]

theorem generatorFrobeniusOrbit_is_generator_root_orbit
    {a : RootField}
    (ha : Polynomial.eval₂ (algebraMap F₂ RootField) a generator = 0)
    (ha23 : a ^ 23 = 1) :
    ∀ x ∈ generatorQRPowerOrbit a,
      Polynomial.eval₂ (algebraMap F₂ RootField) x generator = 0 := by
  intro x hx
  apply generatorFrobeniusOrbit_mem_generatorRoots ha
  rw [generatorFrobeniusOrbit_eq_generatorQRPowerOrbit ha23]
  exact hx

theorem generator_root_at_first_four_qr_exponents {a : RootField}
    (ha : Polynomial.eval₂ (algebraMap F₂ RootField) a generator = 0)
    (ha23 : a ^ 23 = 1) (j : Fin 4) :
    Polynomial.eval₂ (algebraMap F₂ RootField)
        (a ^ ((j : ℕ) + 1)) generator = 0 := by
  apply generatorFrobeniusOrbit_is_generator_root_orbit ha ha23
  change a ^ ((j : ℕ) + 1) ∈
    Finset.image (fun r : ℕ => a ^ r) quadraticResidueCoset
  refine Finset.mem_image.mpr ⟨(j : ℕ) + 1, ?_, rfl⟩
  fin_cases j <;> decide

theorem generator_dvd_polynomial_vanishes_at_first_four_qr_roots
    {a : RootField} (ha : Polynomial.eval₂ (algebraMap F₂ RootField) a generator = 0)
    (ha23 : a ^ 23 = 1) (f : Polynomial F₂) (hdiv : generator ∣ f)
    (j : Fin 4) :
    Polynomial.eval₂ (algebraMap F₂ RootField)
        (a ^ ((j : ℕ) + 1)) f = 0 := by
  rcases hdiv with ⟨q, hq⟩
  rw [hq, Polynomial.eval₂_mul,
    generator_root_at_first_four_qr_exponents ha ha23 j, zero_mul]

end

end InfoGeometry.Combinatorics.BinaryGolayFrobeniusQRBridge
