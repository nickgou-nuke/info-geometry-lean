import Mathlib.NumberTheory.ArithmeticFunction.Defs
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
Finite Monster/Moonshine-inspired arithmetic readouts
=====================================================

This file contains finite numerical facts and a sample-class bookkeeping packet
inspired by Monster/Moonshine terminology.  It does not construct the Monster
group, prove Monstrous Moonshine, prove a modular-function theorem, or prove
thermal stability/protection of moonshine functions.
-/

open ArithmeticFunction

namespace MonsterMoonshine

/-- List of known Mersenne exponents (prime p where 2^p - 1 is prime) -/
def mersenne_exponents : List ℕ :=
  [2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127]

/-- Mersenne primes: M_p = 2^p - 1 -/
def mersenne_prime (p : ℕ) : ℕ :=
  2^p - 1

/-- The standard decimal value of the Monster group order. -/
def monsterOrder : ℕ :=
  808017424794512875886459904961710757005754368000000000

/-- The smallest nontrivial irreducible representation dimension used here. -/
def monsterMinimalRepresentationDimension : ℕ :=
  196883

/-- The number of Monster conjugacy classes. -/
def monsterConjugacyClassCount : ℕ :=
  194

/-- The stored minimal representation dimension has its displayed value. -/
theorem monster_minimal_representation_dimension :
    monsterMinimalRepresentationDimension = 196883 :=
  rfl

/-- The stored conjugacy-class count has its displayed value. -/
theorem monster_conjugacy_class_count :
    monsterConjugacyClassCount = 194 :=
  rfl

/-- The stored order constant has the displayed prime-factor product. -/
theorem monster_order_factorization :
  monsterOrder =
    2^46 * 3^20 * 5^9 * 7^6 * 11^2 * 13^3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71 := by
  native_decide

/-- Sample Mersenne-prime values that divide the stored order constant. -/
def mersenne_in_monster : List ℕ :=
  [3, 7, 31]  -- M₂, M₃, M₅

theorem mersenne_divides_monster (M_p : ℕ) (h : M_p ∈ mersenne_in_monster) :
  M_p ∣ monsterOrder := by
  simp [mersenne_in_monster] at h
  rcases h with rfl | rfl | rfl
  · native_decide
  · native_decide
  · native_decide

/-- 
A data packet for a graded-dimension sequence and coefficient sequence.
No modular-function or Moonshine theorem is asserted here.
-/
structure MoonshineModule where
  graded_dimension : ℤ → ℕ
  j_function_coeff : ℕ → ℕ

/-- First few j-function coefficients -/
def j_coeff_1 : ℕ := 196884  -- = 1 + 196883
def j_coeff_2 : ℕ := 21493760  -- = 1 + 196883 + 21296876
def j_coeff_3 : ℕ := 864299970

theorem j_coeff_1_decomp : j_coeff_1 = 1 + 196883 := by
  norm_num [j_coeff_1]

/-- 
Liouville grading on Monster conjugacy classes.

Γ = (-1)^Ω(n) where n is the class order.
-/
def monster_liouville_grading (class_order : ℕ) : ℤ :=
  if class_order = 0 then 0
  else
    let factors := Nat.factorization class_order
    let omega := factors.sum (fun _ m => m)
    (-1 : ℤ) ^ omega

/-- Sample Monster conjugacy classes -/
inductive MonsterConjugacyClass
  | oneA : MonsterConjugacyClass  -- identity
  | twoA : MonsterConjugacyClass  -- first involution
  | threeA : MonsterConjugacyClass
  | sevenA : MonsterConjugacyClass
  | thirteenA : MonsterConjugacyClass
  | nineteenA : MonsterConjugacyClass
  | twentyNineA : MonsterConjugacyClass
  | fancy : MonsterConjugacyClass  -- other 187 classes

/-- The finite sample of Monster conjugacy classes used by this file. -/
def monsterSampleClasses : List MonsterConjugacyClass :=
  [MonsterConjugacyClass.oneA, MonsterConjugacyClass.twoA, MonsterConjugacyClass.threeA,
   MonsterConjugacyClass.sevenA, MonsterConjugacyClass.thirteenA,
   MonsterConjugacyClass.nineteenA, MonsterConjugacyClass.twentyNineA,
   MonsterConjugacyClass.fancy]

def class_order : MonsterConjugacyClass → ℕ
  | MonsterConjugacyClass.oneA => 1
  | MonsterConjugacyClass.twoA => 2
  | MonsterConjugacyClass.threeA => 3
  | MonsterConjugacyClass.sevenA => 7
  | MonsterConjugacyClass.thirteenA => 13
  | MonsterConjugacyClass.nineteenA => 19
  | MonsterConjugacyClass.twentyNineA => 29
  | MonsterConjugacyClass.fancy => 0  -- varies

/-- Count bosonic Monster classes (λ = +1) -/
def count_bosonic_monster : ℕ :=
  (monsterSampleClasses.filter (fun c => monster_liouville_grading (class_order c) = 1)).length

/-- Count fermionic Monster classes (λ = -1) -/
def count_fermionic_monster : ℕ :=
  (monsterSampleClasses.filter (fun c => monster_liouville_grading (class_order c) = -1)).length

/-- Difference of the two finite sample-class counts above. -/
def witten_index_monster : ℤ :=
  (count_bosonic_monster : ℤ) - (count_fermionic_monster : ℤ)

/-- 
Declared scalar phase factor for a grade parameter.
-/
noncomputable def moonshine_modular_flow (t : ℝ) (grade : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * t * (grade : ℝ))

/-- Scalar commutativity of the Liouville-style grading and declared phase. -/
theorem monster_liouville_scalar_commutes_phase (class_order : ℕ) (t : ℝ) :
  (monster_liouville_grading class_order : ℂ) * moonshine_modular_flow t 1
  = moonshine_modular_flow t 1 * (monster_liouville_grading class_order : ℂ) := by
  rw [mul_comm]

/-- Uniform form of the same scalar commutativity identity. -/
theorem monster_liouville_scalar_commutes_phase_uniform :
  ∀ (t : ℝ) (class_order : ℕ),
  (monster_liouville_grading class_order : ℂ) * moonshine_modular_flow t 1
  = moonshine_modular_flow t 1 * (monster_liouville_grading class_order : ℂ) := by
  intro t class_order
  exact monster_liouville_scalar_commutes_phase class_order t

/-- Self-contained alias for the E8 Witten readout used in the transport theorem. -/
def witten_index_e8 : ℤ :=
  witten_index_monster

/-- Self-contained alias for the Bost-Connes Witten readout used in the transport theorem. -/
def witten_index_bost_connes : ℤ :=
  witten_index_monster

/-- The numerical Mersenne values `3`, `7`, and `31` divide the stored order
constant. -/
theorem sample_mersenne_values_divide_monster_order_constant :
  let M2 := mersenne_prime 2
  let M3 := mersenne_prime 3
  let M5 := mersenne_prime 5
  M2 = 3 ∧ M3 = 7 ∧ M5 = 31 ∧
  M2 ∣ monsterOrder ∧
  M3 ∣ monsterOrder ∧
  M5 ∣ monsterOrder := by
  simp [mersenne_prime]
  native_decide

/-- 
A pure numerical implication involving the displayed Leech-lattice constants;
no Leech lattice or Conway/Monster embedding is constructed.
-/
theorem leech_lattice_monster :
  (let leech_min_vectors := 196560
   let leech_dim := 24
   leech_min_vectors = leech_dim * 8190 ∧
   leech_min_vectors = 196560) := by
  norm_num

/-- The finite Witten-style readout is the signed difference of the two
sample-class counts.  The parameter is retained for the historical thermal
API; no thermal conservation theorem is claimed here. -/
theorem witten_index_monster_constant_in_parameter :
  ∀ β > 0,
    witten_index_monster =
      (count_bosonic_monster : ℤ) - (count_fermionic_monster : ℤ) := by
  intro β Hβ
  rfl

/-- If the two alias readouts equal the sample Monster readout, then all three
readouts are constant in the unused positive parameter. -/
theorem shared_index_readout_constant_in_parameter :
  (witten_index_e8 = witten_index_monster) →
  (witten_index_bost_connes = witten_index_monster) →
  ∃ (W : ℤ), ∀ β > 0,
    witten_index_monster = W ∧
    witten_index_e8 = W ∧
    witten_index_bost_connes = W := by
  intro hE8 hBC
  refine ⟨witten_index_monster, ?_⟩
  intro β hβ
  constructor
  · rfl
  constructor
  · rfl
  · rfl

end MonsterMoonshine
