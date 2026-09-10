import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic.FinCases
import InfoGeometry.Clifford.Spacetime
import InfoGeometry.Canonical.ChiralStokesPauliRelations

open scoped Matrix
open CliffordAlgebra
open InfoGeometry.Canonical.ChiralStokesPauliBasis
namespace InfoGeometry.Canonical.HestenesPauliEvenClifford
abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev Vec13 := InfoGeometry.Clifford.Spacetime.Vec13
noncomputable abbrev q14 : QuadraticForm ℝ Vec13 := InfoGeometry.Clifford.Spacetime.minkiQ
noncomputable abbrev ClPlus14 := CliffordAlgebra.even q14

def e0 : Vec13 := (1, 0, 0, 0)
def e1 : Vec13 := (0, 1, 0, 0)
def e2 : Vec13 := (0, 0, 1, 0)
def e3 : Vec13 := (0, 0, 0, 1)

theorem iota_anticomm_of_q_add
    {v w : Vec13}
    (hQ : q14 (v + w) = q14 v + q14 w) :
    CliffordAlgebra.ι q14 v * CliffordAlgebra.ι q14 w =
      -CliffordAlgebra.ι q14 w * CliffordAlgebra.ι q14 v := by
  have h := CliffordAlgebra.ι_sq_scalar q14 (v + w)
  rw [map_add, hQ, map_add] at h
  have hv := CliffordAlgebra.ι_sq_scalar q14 v
  have hw := CliffordAlgebra.ι_sq_scalar q14 w
  have hcross :
      CliffordAlgebra.ι q14 v * CliffordAlgebra.ι q14 w +
          CliffordAlgebra.ι q14 w * CliffordAlgebra.ι q14 v = 0 := by
    calc
      CliffordAlgebra.ι q14 v * CliffordAlgebra.ι q14 w +
          CliffordAlgebra.ι q14 w * CliffordAlgebra.ι q14 v =
          (CliffordAlgebra.ι q14 v + CliffordAlgebra.ι q14 w) *
              (CliffordAlgebra.ι q14 v + CliffordAlgebra.ι q14 w) -
            CliffordAlgebra.ι q14 v * CliffordAlgebra.ι q14 v -
            CliffordAlgebra.ι q14 w * CliffordAlgebra.ι q14 w := by
              noncomm_ring
      _ = 0 := by rw [h, hv, hw]; abel
  simpa using eq_neg_of_add_eq_zero_left hcross

theorem iota_anti_e0_e1 :
    CliffordAlgebra.ι q14 e0 * CliffordAlgebra.ι q14 e1 =
      -CliffordAlgebra.ι q14 e1 * CliffordAlgebra.ι q14 e0 := by
  apply iota_anticomm_of_q_add
  norm_num [q14, InfoGeometry.Clifford.Spacetime.minkiQ, e0, e1]

theorem iota_anti_e0_e2 :
    CliffordAlgebra.ι q14 e0 * CliffordAlgebra.ι q14 e2 =
      -CliffordAlgebra.ι q14 e2 * CliffordAlgebra.ι q14 e0 := by
  apply iota_anticomm_of_q_add
  norm_num [q14, InfoGeometry.Clifford.Spacetime.minkiQ, e0, e2]

theorem iota_anti_e0_e3 :
    CliffordAlgebra.ι q14 e0 * CliffordAlgebra.ι q14 e3 =
      -CliffordAlgebra.ι q14 e3 * CliffordAlgebra.ι q14 e0 := by
  apply iota_anticomm_of_q_add
  norm_num [q14, InfoGeometry.Clifford.Spacetime.minkiQ, e0, e3]

theorem iota_anti_e1_e2 :
    CliffordAlgebra.ι q14 e1 * CliffordAlgebra.ι q14 e2 =
      -CliffordAlgebra.ι q14 e2 * CliffordAlgebra.ι q14 e1 := by
  apply iota_anticomm_of_q_add
  norm_num [q14, InfoGeometry.Clifford.Spacetime.minkiQ, e1, e2]

theorem iota_anti_e1_e3 :
    CliffordAlgebra.ι q14 e1 * CliffordAlgebra.ι q14 e3 =
      -CliffordAlgebra.ι q14 e3 * CliffordAlgebra.ι q14 e1 := by
  apply iota_anticomm_of_q_add
  norm_num [q14, InfoGeometry.Clifford.Spacetime.minkiQ, e1, e3]

theorem iota_anti_e2_e3 :
    CliffordAlgebra.ι q14 e2 * CliffordAlgebra.ι q14 e3 =
      -CliffordAlgebra.ι q14 e3 * CliffordAlgebra.ι q14 e2 := by
  apply iota_anticomm_of_q_add
  norm_num [q14, InfoGeometry.Clifford.Spacetime.minkiQ, e2, e3]

theorem iota_sq_e0 :
    (CliffordAlgebra.ι q14 e0) * CliffordAlgebra.ι q14 e0 =
      (1 : CliffordAlgebra q14) := by
  rw [CliffordAlgebra.ι_sq_scalar]
  norm_num [q14, InfoGeometry.Clifford.Spacetime.minkiQ, e0]

theorem iota_sq_e1 :
    (CliffordAlgebra.ι q14 e1) * CliffordAlgebra.ι q14 e1 =
      (-1 : CliffordAlgebra q14) := by
  rw [CliffordAlgebra.ι_sq_scalar]
  norm_num [q14, InfoGeometry.Clifford.Spacetime.minkiQ, e1]

theorem iota_sq_e2 :
    (CliffordAlgebra.ι q14 e2) * CliffordAlgebra.ι q14 e2 =
      (-1 : CliffordAlgebra q14) := by
  rw [CliffordAlgebra.ι_sq_scalar]
  norm_num [q14, InfoGeometry.Clifford.Spacetime.minkiQ, e2]

theorem iota_sq_e3 :
    (CliffordAlgebra.ι q14 e3) * CliffordAlgebra.ι q14 e3 =
      (-1 : CliffordAlgebra q14) := by
  rw [CliffordAlgebra.ι_sq_scalar]
  norm_num [q14, InfoGeometry.Clifford.Spacetime.minkiQ, e3]

theorem vec13_decomposition (v : Vec13) :
    v = v.1 • e0 + v.2.1 • e1 + v.2.2.1 • e2 + v.2.2.2 • e3 := by
  rcases v with ⟨t, x, y, z⟩
  ext <;> simp [e0, e1, e2, e3]

def vecBasis : Fin 4 → Vec13
  | 0 => e0
  | 1 => e1
  | 2 => e2
  | 3 => e3

noncomputable def evenPair (i j : Fin 4) : ClPlus14 :=
  (CliffordAlgebra.even.ι q14).bilin (vecBasis i) (vecBasis j)

noncomputable def evenBilin (v w : Vec13) : ClPlus14 :=
  (CliffordAlgebra.even.ι q14).bilin v w

@[simp] theorem evenPair_coe (i j : Fin 4) :
    (evenPair i j : CliffordAlgebra q14) =
      CliffordAlgebra.ι q14 (vecBasis i) * CliffordAlgebra.ι q14 (vecBasis j) :=
  rfl

@[simp] theorem evenBilin_coe (v w : Vec13) :
    (evenBilin v w : CliffordAlgebra q14) =
      CliffordAlgebra.ι q14 v * CliffordAlgebra.ι q14 w :=
  rfl

theorem evenBilin_swap_of_q_add
    {v w : Vec13}
    (hQ : q14 (v + w) = q14 v + q14 w) :
    evenBilin v w = -evenBilin w v := by
  apply Subtype.ext
  change CliffordAlgebra.ι q14 v * CliffordAlgebra.ι q14 w =
    -(CliffordAlgebra.ι q14 w * CliffordAlgebra.ι q14 v)
  simpa only [neg_mul] using iota_anticomm_of_q_add hQ

theorem evenBilin_square (v : Vec13) :
    evenBilin v v = q14 v • (1 : ClPlus14) := by
  apply Subtype.ext
  change CliffordAlgebra.ι q14 v * CliffordAlgebra.ι q14 v =
    q14 v • (1 : CliffordAlgebra q14)
  rw [CliffordAlgebra.ι_sq_scalar]
  simp [Algebra.algebraMap_eq_smul_one]

theorem evenPair_square (i : Fin 4) :
    evenPair i i = q14 (vecBasis i) • (1 : ClPlus14) := by
  exact evenBilin_square (vecBasis i)

theorem evenPair_swap (i j : Fin 4)
    (hQ : q14 (vecBasis i + vecBasis j) =
      q14 (vecBasis i) + q14 (vecBasis j)) :
    evenPair i j = -evenPair j i := by
  exact evenBilin_swap_of_q_add hQ

noncomputable def evenBasis : Fin 8 → ClPlus14
  | 0 => 1
  | 1 => evenPair 1 0
  | 2 => evenPair 2 0
  | 3 => evenPair 3 0
  | 4 => evenPair 2 1
  | 5 => evenPair 3 1
  | 6 => evenPair 3 2
  | 7 => evenPair 3 2 * evenPair 1 0

theorem evenBasis_coe (i : Fin 8) :
    (evenBasis i : CliffordAlgebra q14) =
      match i with
      | 0 => 1
      | 1 => CliffordAlgebra.ι q14 (vecBasis 1) * CliffordAlgebra.ι q14 (vecBasis 0)
      | 2 => CliffordAlgebra.ι q14 (vecBasis 2) * CliffordAlgebra.ι q14 (vecBasis 0)
      | 3 => CliffordAlgebra.ι q14 (vecBasis 3) * CliffordAlgebra.ι q14 (vecBasis 0)
      | 4 => CliffordAlgebra.ι q14 (vecBasis 2) * CliffordAlgebra.ι q14 (vecBasis 1)
      | 5 => CliffordAlgebra.ι q14 (vecBasis 3) * CliffordAlgebra.ι q14 (vecBasis 1)
      | 6 => CliffordAlgebra.ι q14 (vecBasis 3) * CliffordAlgebra.ι q14 (vecBasis 2)
      | 7 =>
          (CliffordAlgebra.ι q14 (vecBasis 3) * CliffordAlgebra.ι q14 (vecBasis 2)) *
            (CliffordAlgebra.ι q14 (vecBasis 1) * CliffordAlgebra.ι q14 (vecBasis 0) ) := by
  fin_cases i <;> rfl

def evenSpan : Submodule ℝ ClPlus14 :=
  Submodule.span ℝ (Set.range evenBasis)

theorem evenBasis_mem_evenSpan (i : Fin 8) :
    evenBasis i ∈ evenSpan :=
  Submodule.subset_span ⟨i, rfl⟩

noncomputable def cliffordGenerator : Fin 4 → CliffordAlgebra q14 :=
  fun i => CliffordAlgebra.ι q14 (vecBasis i)

noncomputable def fullCanonicalBasis : Fin 8 → CliffordAlgebra q14
  | 0 => 1
  | 1 => cliffordGenerator 1 * cliffordGenerator 0
  | 2 => cliffordGenerator 2 * cliffordGenerator 0
  | 3 => cliffordGenerator 3 * cliffordGenerator 0
  | 4 => cliffordGenerator 2 * cliffordGenerator 1
  | 5 => cliffordGenerator 3 * cliffordGenerator 1
  | 6 => cliffordGenerator 3 * cliffordGenerator 2
  | 7 => cliffordGenerator 3 * cliffordGenerator 2 *
      cliffordGenerator 1 * cliffordGenerator 0

noncomputable def fullCanonicalSpan : Submodule ℝ (CliffordAlgebra q14) :=
  Submodule.span ℝ (Set.range fullCanonicalBasis)

theorem cliffordGenerator_square (i : Fin 4) :
    cliffordGenerator i * cliffordGenerator i =
      (if i = 0 then (1 : CliffordAlgebra q14) else -1) := by
  fin_cases i
  · simpa [cliffordGenerator, vecBasis] using iota_sq_e0
  · simpa [cliffordGenerator, vecBasis] using iota_sq_e1
  · simpa [cliffordGenerator, vecBasis] using iota_sq_e2
  · simpa [cliffordGenerator, vecBasis] using iota_sq_e3

theorem cliffordGenerator_anticommute
    (i j : Fin 4) (hij : i < j) :
    cliffordGenerator i * cliffordGenerator j =
      -(cliffordGenerator j * cliffordGenerator i) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [cliffordGenerator, vecBasis,
      iota_anti_e0_e1, iota_anti_e0_e2, iota_anti_e0_e3,
      iota_anti_e1_e2, iota_anti_e1_e3, iota_anti_e2_e3]

theorem cliffordGenerator_zero_one :
    cliffordGenerator 0 * cliffordGenerator 1 =
      -(cliffordGenerator 1 * cliffordGenerator 0) := by
  exact cliffordGenerator_anticommute 0 1 (by decide)

theorem cliffordGenerator_zero_two :
    cliffordGenerator 0 * cliffordGenerator 2 =
      -(cliffordGenerator 2 * cliffordGenerator 0) := by
  exact cliffordGenerator_anticommute 0 2 (by decide)

theorem cliffordGenerator_zero_three :
    cliffordGenerator 0 * cliffordGenerator 3 =
      -(cliffordGenerator 3 * cliffordGenerator 0) := by
  exact cliffordGenerator_anticommute 0 3 (by decide)

theorem cliffordGenerator_one_two :
    cliffordGenerator 1 * cliffordGenerator 2 =
      -(cliffordGenerator 2 * cliffordGenerator 1) := by
  exact cliffordGenerator_anticommute 1 2 (by decide)

theorem cliffordGenerator_one_three :
    cliffordGenerator 1 * cliffordGenerator 3 =
      -(cliffordGenerator 3 * cliffordGenerator 1) := by
  exact cliffordGenerator_anticommute 1 3 (by decide)

theorem cliffordGenerator_two_three :
    cliffordGenerator 2 * cliffordGenerator 3 =
      -(cliffordGenerator 3 * cliffordGenerator 2) := by
  exact cliffordGenerator_anticommute 2 3 (by decide)

theorem cliffordGenerator_zero_nested (x : CliffordAlgebra q14) :
    cliffordGenerator 0 * (cliffordGenerator 0 * x) = x := by
  rw [← mul_assoc, cliffordGenerator_square]
  simp

theorem cliffordGenerator_one_nested (x : CliffordAlgebra q14) :
    cliffordGenerator 1 * (cliffordGenerator 1 * x) = -x := by
  rw [← mul_assoc, cliffordGenerator_square]
  simp

theorem cliffordGenerator_two_nested (x : CliffordAlgebra q14) :
    cliffordGenerator 2 * (cliffordGenerator 2 * x) = -x := by
  rw [← mul_assoc, cliffordGenerator_square]
  simp

theorem cliffordGenerator_three_nested (x : CliffordAlgebra q14) :
    cliffordGenerator 3 * (cliffordGenerator 3 * x) = -x := by
  rw [← mul_assoc, cliffordGenerator_square]
  simp

theorem cliffordGenerator_zero_one_nested (x : CliffordAlgebra q14) :
    cliffordGenerator 0 * (cliffordGenerator 1 * x) =
      -(cliffordGenerator 1 * (cliffordGenerator 0 * x)) := by
  rw [← mul_assoc, cliffordGenerator_zero_one, neg_mul, mul_assoc]

theorem cliffordGenerator_zero_two_nested (x : CliffordAlgebra q14) :
    cliffordGenerator 0 * (cliffordGenerator 2 * x) =
      -(cliffordGenerator 2 * (cliffordGenerator 0 * x)) := by
  rw [← mul_assoc, cliffordGenerator_zero_two, neg_mul, mul_assoc]

theorem cliffordGenerator_zero_three_nested (x : CliffordAlgebra q14) :
    cliffordGenerator 0 * (cliffordGenerator 3 * x) =
      -(cliffordGenerator 3 * (cliffordGenerator 0 * x)) := by
  rw [← mul_assoc, cliffordGenerator_zero_three, neg_mul, mul_assoc]

theorem cliffordGenerator_one_two_nested (x : CliffordAlgebra q14) :
    cliffordGenerator 1 * (cliffordGenerator 2 * x) =
      -(cliffordGenerator 2 * (cliffordGenerator 1 * x)) := by
  rw [← mul_assoc, cliffordGenerator_one_two, neg_mul, mul_assoc]

theorem cliffordGenerator_one_three_nested (x : CliffordAlgebra q14) :
    cliffordGenerator 1 * (cliffordGenerator 3 * x) =
      -(cliffordGenerator 3 * (cliffordGenerator 1 * x)) := by
  rw [← mul_assoc, cliffordGenerator_one_three, neg_mul, mul_assoc]

theorem cliffordGenerator_two_three_nested (x : CliffordAlgebra q14) :
    cliffordGenerator 2 * (cliffordGenerator 3 * x) =
      -(cliffordGenerator 3 * (cliffordGenerator 2 * x)) := by
  rw [← mul_assoc, cliffordGenerator_two_three, neg_mul, mul_assoc]

set_option maxHeartbeats 2000000 in
theorem canonical_pair_mul_mem
    (i j : Fin 4) (k : Fin 8) :
    cliffordGenerator i * cliffordGenerator j * fullCanonicalBasis k ∈
      fullCanonicalSpan := by
  have hb : ∀ n : Fin 8, fullCanonicalBasis n ∈ fullCanonicalSpan :=
    fun n => Submodule.subset_span ⟨n, rfl⟩
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  have h4 := hb 4
  have h5 := hb 5
  have h6 := hb 6
  have h7 := hb 7
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals
    simp [fullCanonicalBasis, fullCanonicalSpan, mul_assoc,
      neg_mul, mul_neg, neg_neg,
      cliffordGenerator_square,
      cliffordGenerator_zero_one, cliffordGenerator_zero_two,
      cliffordGenerator_zero_three, cliffordGenerator_one_two,
      cliffordGenerator_one_three, cliffordGenerator_two_three,
      cliffordGenerator_one_nested,
      cliffordGenerator_two_nested, cliffordGenerator_three_nested,
      cliffordGenerator_zero_one_nested, cliffordGenerator_zero_two_nested,
      cliffordGenerator_zero_three_nested, cliffordGenerator_one_two_nested,
      cliffordGenerator_one_three_nested, cliffordGenerator_two_three_nested]
    first |
      simpa [fullCanonicalBasis, fullCanonicalSpan, mul_assoc] using h0 |
      simpa [fullCanonicalBasis, fullCanonicalSpan, mul_assoc] using h1 |
      simpa [fullCanonicalBasis, fullCanonicalSpan, mul_assoc] using h2 |
      simpa [fullCanonicalBasis, fullCanonicalSpan, mul_assoc] using h3 |
      simpa [fullCanonicalBasis, fullCanonicalSpan, mul_assoc] using h4 |
      simpa [fullCanonicalBasis, fullCanonicalSpan, mul_assoc] using h5 |
      simpa [fullCanonicalBasis, fullCanonicalSpan, mul_assoc] using h6 |
      simpa [fullCanonicalBasis, fullCanonicalSpan, mul_assoc] using h7

def vecCoord (v : Vec13) : Fin 4 → ℝ
  | 0 => v.1
  | 1 => v.2.1
  | 2 => v.2.2.1
  | 3 => v.2.2.2

theorem iota_vecCoord_decomposition (v : Vec13) :
    CliffordAlgebra.ι q14 v =
      ∑ i : Fin 4, vecCoord v i • cliffordGenerator i := by
  calc
    CliffordAlgebra.ι q14 v =
        CliffordAlgebra.ι q14
          (v.1 • e0 + v.2.1 • e1 + v.2.2.1 • e2 + v.2.2.2 • e3) := by
      exact congrArg (CliffordAlgebra.ι q14) (vec13_decomposition v)
    _ = ∑ i : Fin 4, vecCoord v i • cliffordGenerator i := by
      simp only [vecCoord, cliffordGenerator, vecBasis, Fin.sum_univ_four]
      rw [(CliffordAlgebra.ι q14).map_add,
        (CliffordAlgebra.ι q14).map_add,
        (CliffordAlgebra.ι q14).map_add,
        (CliffordAlgebra.ι q14).map_smul,
        (CliffordAlgebra.ι q14).map_smul,
        (CliffordAlgebra.ι q14).map_smul,
        (CliffordAlgebra.ι q14).map_smul]

theorem generator_pair_mem (i j : Fin 4) :
    cliffordGenerator i * cliffordGenerator j ∈ fullCanonicalSpan := by
  simpa [fullCanonicalBasis] using canonical_pair_mul_mem i j 0

theorem pair_sum_mem (a b : Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4,
      a i • (b j • (cliffordGenerator i * cliffordGenerator j))) ∈
      fullCanonicalSpan := by
  exact fullCanonicalSpan.sum_mem (fun i _ =>
    fullCanonicalSpan.sum_mem (fun j _ =>
      fullCanonicalSpan.smul_mem (a i)
        (fullCanonicalSpan.smul_mem (b j) (generator_pair_mem i j))))

theorem pair_basis_sum_mem (a b : Fin 4 → ℝ) (k : Fin 8) :
    (∑ i : Fin 4, ∑ j : Fin 4,
      a i • (b j •
        (cliffordGenerator i * cliffordGenerator j * fullCanonicalBasis k))) ∈
      fullCanonicalSpan := by
  exact fullCanonicalSpan.sum_mem (fun i _ =>
    fullCanonicalSpan.sum_mem (fun j _ =>
      fullCanonicalSpan.smul_mem (a i)
        (fullCanonicalSpan.smul_mem (b j)
          (canonical_pair_mul_mem i j k))))

theorem arbitrary_pair_mem_fullCanonicalSpan (v w : Vec13) :
    CliffordAlgebra.ι q14 v * CliffordAlgebra.ι q14 w ∈
    fullCanonicalSpan := by
    rw [iota_vecCoord_decomposition, iota_vecCoord_decomposition]
    simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
    simpa [smul_smul] using pair_sum_mem (vecCoord v) (vecCoord w)

theorem pair_mul_fullCanonicalSpan
    (v w : Vec13) {x : CliffordAlgebra q14}
    (hx : x ∈ fullCanonicalSpan) :
    CliffordAlgebra.ι q14 v * CliffordAlgebra.ι q14 w * x ∈
      fullCanonicalSpan := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨k, rfl⟩
    rw [iota_vecCoord_decomposition, iota_vecCoord_decomposition]
    simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
    simp_rw [Finset.sum_mul]
    simpa [smul_smul, mul_assoc] using pair_basis_sum_mem (vecCoord v) (vecCoord w) k
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact fullCanonicalSpan.add_mem hx hy
  · intro c x _ hx
    rw [mul_smul_comm]
    exact fullCanonicalSpan.smul_mem c hx

theorem even_mem_fullCanonicalSpan (x : ClPlus14) :
    x.1 ∈ fullCanonicalSpan := by
  induction x.1, x.2 using CliffordAlgebra.even_induction with
  | algebraMap r =>
      simpa [Algebra.algebraMap_eq_smul_one] using
        fullCanonicalSpan.smul_mem r (Submodule.subset_span ⟨0, rfl⟩)
  | add x y _ _ hx hy =>
      exact fullCanonicalSpan.add_mem hx hy
  | ι_mul_ι_mul v w x _ hx =>
      exact pair_mul_fullCanonicalSpan v w hx

def clPlusVal : ClPlus14 →ₗ[ℝ] CliffordAlgebra q14 where
  toFun x := x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem clPlusVal_injective : Function.Injective clPlusVal := by
  intro x y hxy
  exact Subtype.ext hxy

theorem clPlusVal_range_eq_fullCanonicalSpan :
    clPlusVal.range = fullCanonicalSpan := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact even_mem_fullCanonicalSpan x
  · apply Submodule.span_le.2
    rintro y ⟨i, rfl⟩
    refine ⟨evenBasis i, ?_⟩
    simpa [clPlusVal, fullCanonicalBasis, mul_assoc] using evenBasis_coe i

noncomputable def clPlusValRangeEquiv :
    ClPlus14 ≃ₗ[ℝ] ↥clPlusVal.range :=
  LinearEquiv.ofInjective clPlusVal clPlusVal_injective

noncomputable def fullSpanBasis (i : Fin 8) : ↥fullCanonicalSpan :=
  ⟨fullCanonicalBasis i, Submodule.subset_span ⟨i, rfl⟩⟩

theorem fullSpanBasis_span_top :
    Submodule.span ℝ (Set.range fullSpanBasis) = ⊤ := by
  simpa [fullSpanBasis, fullCanonicalSpan] using
    (Submodule.span_range_subtype_eq_top_iff fullCanonicalSpan
      (s := fullCanonicalBasis)
      (hs := fun i => Submodule.subset_span ⟨i, rfl⟩)).2 rfl

theorem fullCanonicalSpan_finrank_le_eight :
    Module.finrank ℝ (↥fullCanonicalSpan) ≤ 8 :=
  finrank_le_of_span_eq_top fullSpanBasis_span_top

theorem clPlus14_finrank_le_eight :
    Module.finrank ℝ ClPlus14 ≤ 8 := by
  rw [clPlusValRangeEquiv.finrank_eq]
  rw [clPlusVal_range_eq_fullCanonicalSpan]
  exact fullCanonicalSpan_finrank_le_eight

noncomputable instance clPlus14_finiteDimensional :
    FiniteDimensional ℝ ClPlus14 := by
  letI : FiniteDimensional ℝ (↥clPlusVal.range) := by
    rw [clPlusVal_range_eq_fullCanonicalSpan]
    exact FiniteDimensional.span_of_finite ℝ (Set.finite_range fullCanonicalBasis)
  exact clPlusValRangeEquiv.symm.finiteDimensional

def rho : Vec13 →ₗ[ℝ] M2C where
  toFun v :=
    (v.1 : ℂ) • (1 : M2C) +
      (v.2.1 : ℂ) • sheetFlip +
      (v.2.2.1 : ℂ) • sheetPhase +
      (v.2.2.2 : ℂ) • sheetParity
  map_add' u v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sheetFlip, sheetPhase, sheetParity] <;> ring
  map_smul' c v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sheetFlip, sheetPhase, sheetParity] <;> ring

def rhoBar : Vec13 →ₗ[ℝ] M2C where
  toFun v :=
    (v.1 : ℂ) • (1 : M2C) -
      (v.2.1 : ℂ) • sheetFlip -
      (v.2.2.1 : ℂ) • sheetPhase -
      (v.2.2.2 : ℂ) • sheetParity
  map_add' u v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sheetFlip, sheetPhase, sheetParity] <;> ring
  map_smul' c v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sheetFlip, sheetPhase, sheetParity] <;> ring

lemma rho_mul_rhoBar (v : Vec13) :
    rho v * rhoBar v = algebraMap ℝ M2C (q14 v) := by
  rcases v with ⟨t, x, y, z⟩
  have hI : (Complex.I : ℂ) ^ 2 = -1 := by norm_num [Complex.ext_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, rhoBar, q14, InfoGeometry.Clifford.Spacetime.minkiQ,
      sheetFlip, sheetPhase, sheetParity,
      Matrix.mul_apply, Fin.sum_univ_two,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
  all_goals ring_nf
  all_goals norm_num [Complex.ext_iff]
  all_goals constructor <;> ring

lemma rhoBar_mul_rho (v : Vec13) :
    rhoBar v * rho v = algebraMap ℝ M2C (q14 v) := by
  rcases v with ⟨t, x, y, z⟩
  have hI : (Complex.I : ℂ) ^ 2 = -1 := by norm_num [Complex.ext_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, rhoBar, q14, InfoGeometry.Clifford.Spacetime.minkiQ,
      sheetFlip, sheetPhase, sheetParity,
      Matrix.mul_apply, Fin.sum_univ_two,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
  all_goals ring_nf
  all_goals norm_num [Complex.ext_iff]
  all_goals constructor <;> ring

noncomputable def evenHom : EvenHom q14 M2C where
  bilin := LinearMap.mk₂ ℝ (fun v w => rho v * rhoBar w)
    (fun _ _ _ => by simp only [map_add, add_mul])
    (fun c v w => by simp only [map_smul, smul_mul_assoc])
    (fun _ _ _ => by simp only [map_add, mul_add])
    (fun c v w => by simp only [map_smul, mul_smul_comm])
  contract v := by
    change rho v * rhoBar v = _
    exact rho_mul_rhoBar v
  contract_mid v₁ v₂ v₃ := by
    change (rho v₁ * rhoBar v₂) * (rho v₂ * rhoBar v₃) =
      q14 v₂ • (rho v₁ * rhoBar v₃)
    calc
      (rho v₁ * rhoBar v₂) * (rho v₂ * rhoBar v₃) =
          rho v₁ * (rhoBar v₂ * rho v₂) * rhoBar v₃ := by noncomm_ring
      _ = rho v₁ * ((q14 v₂ : ℝ) • (1 : M2C)) * rhoBar v₃ := by
        rw [rhoBar_mul_rho]
        simp [Algebra.algebraMap_eq_smul_one]
      _ = q14 v₂ • (rho v₁ * rhoBar v₃) := by
        ext i j
        simp [Matrix.mul_apply, Fin.sum_univ_two] ; ring

noncomputable def clPlusToPauli : CliffordAlgebra.even q14 →ₐ[ℝ] M2C :=
  CliffordAlgebra.even.lift q14 evenHom

@[simp] theorem clPlusToPauli_pair (v w : Vec13) :
    clPlusToPauli ((CliffordAlgebra.even.ι q14).bilin v w) =
      rho v * rhoBar w := by
  simp [clPlusToPauli, evenHom]

@[simp] theorem clPlusToPauli_e0e0 :
    clPlusToPauli ((CliffordAlgebra.even.ι q14).bilin e0 e0) =
      (1 : M2C) := by
  rw [clPlusToPauli_pair]
  simp [e0, rho, rhoBar]

theorem finrank_M2C_real : Module.finrank ℝ M2C = 8 := by
  rw [Module.finrank_matrix]
  norm_num

noncomputable def sigma1 : ClPlus14 :=
  (CliffordAlgebra.even.ι q14).bilin e1 e0

noncomputable def sigma2 : ClPlus14 :=
  (CliffordAlgebra.even.ι q14).bilin e2 e0

noncomputable def sigma3 : ClPlus14 :=
  (CliffordAlgebra.even.ι q14).bilin e3 e0

@[simp] theorem clPlusToPauli_sigma1 :
    clPlusToPauli sigma1 = sheetFlip := by
  rw [sigma1, clPlusToPauli_pair]
  simp [e0, e1, rho, rhoBar]

@[simp] theorem clPlusToPauli_sigma2 :
    clPlusToPauli sigma2 = sheetPhase := by
  rw [sigma2, clPlusToPauli_pair]
  simp [e0, e2, rho, rhoBar]

@[simp] theorem clPlusToPauli_sigma3 :
    clPlusToPauli sigma3 = sheetParity := by
  rw [sigma3, clPlusToPauli_pair]
  simp [e0, e3, rho, rhoBar]

noncomputable def spacetimePseudoscalar : ClPlus14 :=
  sigma1 * sigma2 * sigma3

theorem clPlusToPauli_pseudoscalar :
    clPlusToPauli spacetimePseudoscalar =
      Complex.I • (1 : M2C) := by
  rw [spacetimePseudoscalar, map_mul, map_mul,
    clPlusToPauli_sigma1, clPlusToPauli_sigma2, clPlusToPauli_sigma3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, sheetPhase, sheetParity,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

@[simp] theorem clPlusToPauli_pseudoscalar_mul_sigma1 :
    clPlusToPauli (spacetimePseudoscalar * sigma1) =
      Complex.I • sheetFlip := by
  rw [map_mul, clPlusToPauli_pseudoscalar, clPlusToPauli_sigma1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply]

@[simp] theorem clPlusToPauli_pseudoscalar_mul_sigma2 :
    clPlusToPauli (spacetimePseudoscalar * sigma2) =
      Complex.I • sheetPhase := by
  rw [map_mul, clPlusToPauli_pseudoscalar, clPlusToPauli_sigma2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetPhase, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply]

@[simp] theorem clPlusToPauli_pseudoscalar_mul_sigma3 :
    clPlusToPauli (spacetimePseudoscalar * sigma3) =
      Complex.I • sheetParity := by
  rw [map_mul, clPlusToPauli_pseudoscalar, clPlusToPauli_sigma3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetParity, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply]

noncomputable def pauliPreimage (A : M2C) : ClPlus14 :=
  let a := A 0 0
  let b := A 0 1
  let c := A 1 0
  let d := A 1 1
  ((a.re + d.re) / 2) • (1 : ClPlus14) +
    ((a.im + d.im) / 2) • spacetimePseudoscalar +
    ((b.re + c.re) / 2) • sigma1 +
    ((b.im + c.im) / 2) • (spacetimePseudoscalar * sigma1) +
    ((c.im - b.im) / 2) • sigma2 +
    ((b.re - c.re) / 2) • (spacetimePseudoscalar * sigma2) +
    ((a.re - d.re) / 2) • sigma3 +
    ((a.im - d.im) / 2) • (spacetimePseudoscalar * sigma3)

theorem clPlusToPauli_pauliPreimage (A : M2C) :
    clPlusToPauli (pauliPreimage A) = A := by
  let a := A 0 0
  let b := A 0 1
  let c := A 1 0
  let d := A 1 1
  unfold pauliPreimage
  simp only [map_add, map_smul, map_one,
    clPlusToPauli_pseudoscalar,
    clPlusToPauli_sigma1, clPlusToPauli_sigma2, clPlusToPauli_sigma3,
    clPlusToPauli_pseudoscalar_mul_sigma1,
    clPlusToPauli_pseudoscalar_mul_sigma2,
    clPlusToPauli_pseudoscalar_mul_sigma3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, sheetPhase, sheetParity,
      Matrix.add_apply, Matrix.smul_apply, Complex.ext_iff] <;> ring
  all_goals simp

theorem clPlusToPauli_surjective : Function.Surjective clPlusToPauli := by
  intro A
  exact ⟨pauliPreimage A, clPlusToPauli_pauliPreimage A⟩

theorem clPlusToPauli_injective_of_source_finrank
    (h_source : Module.finrank ℝ ClPlus14 = 8) :
    Function.Injective clPlusToPauli := by
  letI : FiniteDimensional ℝ ClPlus14 :=
    FiniteDimensional.of_finrank_eq_succ (by simpa using h_source)
  have h_rank :
      Module.finrank ℝ ClPlus14 = Module.finrank ℝ M2C := by
    rw [h_source, finrank_M2C_real]
  have h_surjective :
      Function.Surjective clPlusToPauli.toLinearMap :=
    clPlusToPauli_surjective
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_rank).mpr
      h_surjective

theorem clPlus14_finrank_ge_eight :
    8 ≤ Module.finrank ℝ ClPlus14 := by
  have h_range :=
    LinearMap.finrank_range_le clPlusToPauli.toLinearMap
  have h_range_eq :
      LinearMap.range clPlusToPauli.toLinearMap = ⊤ :=
    (LinearMap.range_eq_top).2 clPlusToPauli_surjective
  have h_range_finrank :
      Module.finrank ℝ (LinearMap.range clPlusToPauli.toLinearMap) =
        Module.finrank ℝ M2C := by
    rw [h_range_eq, finrank_top]
  rw [h_range_finrank] at h_range
  simpa [finrank_M2C_real] using h_range

theorem clPlus14_finrank_eq_eight :
    Module.finrank ℝ ClPlus14 = 8 := by
  exact Nat.le_antisymm clPlus14_finrank_le_eight clPlus14_finrank_ge_eight

theorem clPlusToPauli_injective :
    Function.Injective clPlusToPauli :=
  clPlusToPauli_injective_of_source_finrank clPlus14_finrank_eq_eight

noncomputable def clPlusPauliAlgEquiv :
    ClPlus14 ≃ₐ[ℝ] M2C :=
  AlgEquiv.ofBijective clPlusToPauli
    ⟨clPlusToPauli_injective, clPlusToPauli_surjective⟩

noncomputable def chiralPlus : ClPlus14 :=
  (1 / 2 : ℝ) • (sigma1 + spacetimePseudoscalar * sigma2)

noncomputable def chiralMinus : ClPlus14 :=
  (1 / 2 : ℝ) • (sigma1 - spacetimePseudoscalar * sigma2)

noncomputable def sheetIdempotentPlus : ClPlus14 :=
  (1 / 2 : ℝ) • (1 + sigma3)

noncomputable def sheetIdempotentMinus : ClPlus14 :=
  (1 / 2 : ℝ) • (1 - sigma3)

theorem chiralPlus_sq : chiralPlus * chiralPlus = 0 := by
  apply clPlusToPauli_injective
  simp only [chiralPlus, map_mul, map_smul, map_add,
    clPlusToPauli_sigma1, clPlusToPauli_sigma2,
    clPlusToPauli_pseudoscalar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, sheetPhase, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralMinus_sq : chiralMinus * chiralMinus = 0 := by
  apply clPlusToPauli_injective
  simp only [chiralMinus, map_mul, map_smul, map_sub,
    clPlusToPauli_sigma1, clPlusToPauli_sigma2,
    clPlusToPauli_pseudoscalar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, sheetPhase, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralPlus_mul_chiralMinus :
    chiralPlus * chiralMinus = sheetIdempotentPlus := by
  apply clPlusToPauli_injective
  simp only [chiralPlus, chiralMinus, sheetIdempotentPlus,
    map_mul, map_smul, map_sub, map_add, map_one,
    clPlusToPauli_sigma1, clPlusToPauli_sigma2,
    clPlusToPauli_sigma3,
    clPlusToPauli_pseudoscalar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, sheetPhase, sheetParity, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply] ; ring

theorem chiralMinus_mul_chiralPlus :
    chiralMinus * chiralPlus = sheetIdempotentMinus := by
  apply clPlusToPauli_injective
  simp only [chiralPlus, chiralMinus, sheetIdempotentMinus,
    map_mul, map_smul, map_sub, map_add, map_one,
    clPlusToPauli_sigma1, clPlusToPauli_sigma2,
    clPlusToPauli_sigma3,
    clPlusToPauli_pseudoscalar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, sheetPhase, sheetParity, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply] ; ring
end InfoGeometry.Canonical.HestenesPauliEvenClifford
