import Mathlib
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic

noncomputable section

namespace Clifford55

open BigOperators

abbrev V55 := (Fin 5 → ℝ) × (Fin 5 → ℝ)

/-- Coordinate evaluation as a linear map on `ℝ^5`. -/
def coord5 (i : Fin 5) : (Fin 5 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Euclidean quadratic form on `ℝ^5`, built from coordinate linear maps. -/
noncomputable def Q5 : QuadraticForm ℝ (Fin 5 → ℝ) :=
  ∑ i : Fin 5, QuadraticMap.linMulLin (coord5 i) (coord5 i)

def fst55 : V55 →ₗ[ℝ] (Fin 5 → ℝ) where
  toFun v := v.1
  map_add' _ _ := rfl
  map_smul' _ _ := by ext; rfl

def snd55 : V55 →ₗ[ℝ] (Fin 5 → ℝ) where
  toFun v := v.2
  map_add' _ _ := rfl
  map_smul' _ _ := by ext; rfl

noncomputable def Q55 : QuadraticForm ℝ V55 :=
  Q5.comp fst55 - Q5.comp snd55

@[simp] theorem Q5_apply (x : Fin 5 → ℝ) :
    Q5 x = ∑ i : Fin 5, x i ^ 2 := by
  simp [Q5, QuadraticMap.linMulLin, coord5, pow_two]

@[simp] theorem Q55_apply (v : V55) :
    Q55 v = (∑ i : Fin 5, v.1 i ^ 2) - (∑ i : Fin 5, v.2 i ^ 2) := by
  simp [Q55, fst55, snd55]

abbrev Cl55 := CliffordAlgebra Q55
abbrev ι55 : V55 →ₗ[ℝ] Cl55 := CliffordAlgebra.ι Q55

abbrev LipschitzGroup55 : Subgroup Cl55ˣ := lipschitzGroup Q55
abbrev Pin55 := pinGroup Q55
abbrev Spin55 := spinGroup Q55

abbrev LipschitzGroup : Subgroup Cl55ˣ := LipschitzGroup55

abbrev pinToUnits : Pin55 →* Cl55ˣ := pinGroup.toUnits

def twisted_adj (g : Pin55) (v : V55) : Cl55 :=
  (pinToUnits g : Cl55) * ι55 v * (↑((pinToUnits g)⁻¹) : Cl55)

theorem pin_units_mem_lipschitz (g : Pin55) : pinToUnits g ∈ LipschitzGroup55 := by
  apply pinGroup.units_mem_lipschitzGroup (x := pinToUnits g)
  change (g : Cl55) ∈ pinGroup Q55
  exact g.2

def e_pos (i : Fin 5) : V55 :=
  (fun j => if j = i then 1 else 0, 0)

def f_neg (i : Fin 5) : V55 :=
  (0, fun j => if j = i then 1 else 0)

@[simp] theorem Q55_e_pos (i : Fin 5) : Q55 (e_pos i) = 1 := by
  classical
  simp [Q55_apply, e_pos]

@[simp] theorem Q55_f_neg (i : Fin 5) : Q55 (f_neg i) = -1 := by
  classical
  simp [Q55_apply, f_neg]

theorem e_pos_sq (i : Fin 5) : (ι55 (e_pos i)) ^ 2 = 1 := by
  rw [pow_two, CliffordAlgebra.ι_sq_scalar]
  rw [Q55_e_pos]
  simp

theorem f_neg_sq (i : Fin 5) : (ι55 (f_neg i)) ^ 2 = -1 := by
  rw [pow_two, CliffordAlgebra.ι_sq_scalar]
  rw [Q55_f_neg]
  simp

theorem e_pos_mul_self (i : Fin 5) : ι55 (e_pos i) * ι55 (e_pos i) = 1 := by
  simpa [pow_two] using e_pos_sq i

theorem e_pos_unit_mem_lipschitz55 (i : Fin 5) :
    ∃ u : Cl55ˣ, (u : Cl55) = ι55 (e_pos i) ∧ u ∈ LipschitzGroup55 := by
  classical
  have hQunit : IsUnit (Q55 (e_pos i)) := by
    rw [Q55_e_pos]
    exact ⟨1, rfl⟩
  let u : Cl55ˣ := (CliffordAlgebra.isUnit_ι_of_isUnit Q55 hQunit).unit
  have huval : (u : Cl55) = ι55 (e_pos i) :=
    (CliffordAlgebra.isUnit_ι_of_isUnit Q55 hQunit).unit_spec
  have hgen : u ∈ ((↑) ⁻¹' Set.range ι55 : Set Cl55ˣ) := by
    refine ⟨e_pos i, ?_⟩
    simp [huval]
  have hulip : u ∈ LipschitzGroup55 :=
    Subgroup.subset_closure hgen
  exact ⟨u, huval, by simpa [LipschitzGroup55, u] using hulip⟩

theorem e_pos_not_mem_pin55 (i : Fin 5) : ¬ ι55 (e_pos i) ∈ Pin55 := by
  intro h
  have hu := (pinGroup.mem_iff.mp h).2
  have hs : star (ι55 (e_pos i)) * ι55 (e_pos i) = (1 : Cl55) := hu.1
  have hs' : -(ι55 (e_pos i) * ι55 (e_pos i)) = (1 : Cl55) := by
    simpa [CliffordAlgebra.star_ι, mul_comm, mul_left_comm, mul_assoc] using hs
  have hx : ι55 (e_pos i) * ι55 (e_pos i) = (1 : Cl55) := by
    simpa [pow_two] using e_pos_mul_self i
  have hneg : (-1 : Cl55) = (1 : Cl55) := by
    simpa [hx] using hs'
  have h02 : (0 : Cl55) = 2 := by
    have := congrArg (fun x : Cl55 => x + 1) hneg
    norm_num at this
    exact this
  have h2 : (2 : Cl55) ≠ 0 := by
    haveI : CharZero Cl55 := Algebra.charZero_of_charZero ℝ Cl55
    exact two_ne_zero
  exact h2 h02.symm

theorem f_neg_mul_self (i : Fin 5) : ι55 (f_neg i) * ι55 (f_neg i) = -1 := by
  simpa [pow_two] using f_neg_sq i

@[simp] theorem e_pos_ortho_f_neg (i j : Fin 5) : Q55.IsOrtho (e_pos i) (f_neg j) := by
  classical
  simp [QuadraticMap.isOrtho_def, Q55_apply, e_pos, f_neg]

theorem orthogonal_anticomm (i j : Fin 5) :
    ι55 (e_pos i) * ι55 (f_neg j) + ι55 (f_neg j) * ι55 (e_pos i) = 0 := by
  have h := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (Q := Q55) (e_pos_ortho_f_neg i j)
  rw [h]
  exact neg_add_cancel _

def n_pair (i : Fin 5) : V55 := e_pos i + f_neg i

def nbar_pair (i : Fin 5) : V55 := e_pos i - f_neg i

def n_vec : V55 := n_pair 4

def n_bar_vec : V55 := nbar_pair 4

@[simp] theorem n_pair_null (i : Fin 5) : Q55 (n_pair i) = 0 := by
  classical
  simp [Q55_apply, n_pair, e_pos, f_neg]

@[simp] theorem nbar_pair_null (i : Fin 5) : Q55 (nbar_pair i) = 0 := by
  classical
  simp [Q55_apply, nbar_pair, e_pos, f_neg]

theorem n_vec_null : Q55 n_vec = 0 := by
  simpa [n_vec] using n_pair_null 4

theorem n_bar_vec_null : Q55 n_bar_vec = 0 := by
  simpa [n_bar_vec] using nbar_pair_null 4

theorem n_pair_sq_zero (i : Fin 5) : ι55 (n_pair i) * ι55 (n_pair i) = 0 := by
  rw [CliffordAlgebra.ι_sq_scalar]
  rw [n_pair_null]
  simp

theorem nbar_pair_sq_zero (i : Fin 5) : ι55 (nbar_pair i) * ι55 (nbar_pair i) = 0 := by
  rw [CliffordAlgebra.ι_sq_scalar]
  rw [nbar_pair_null]
  simp

theorem n_vec_sq_zero : ι55 n_vec * ι55 n_vec = 0 := by
  simpa [n_vec] using n_pair_sq_zero 4

theorem n_bar_vec_sq_zero : ι55 n_bar_vec * ι55 n_bar_vec = 0 := by
  simpa [n_bar_vec] using nbar_pair_sq_zero 4

@[simp] theorem Q55_n_add_nbar (i : Fin 5) : Q55 (n_pair i + nbar_pair i) = 4 := by
  classical
  simp [Q55_apply, n_pair, nbar_pair, e_pos, f_neg]
  rw [Finset.sum_eq_single i]
  · norm_num
  · intro b _ hb
    simp [hb]
  · intro h
    exact False.elim (h (Finset.mem_univ i))

theorem n_dot_nbar_clifford (i : Fin 5) :
    ι55 (n_pair i) * ι55 (nbar_pair i) + ι55 (nbar_pair i) * ι55 (n_pair i) = 4 := by
  rw [CliffordAlgebra.ι_mul_ι_add_swap]
  rw [QuadraticMap.polar, Q55_n_add_nbar, n_pair_null, nbar_pair_null]
  simpa using (map_ofNat (algebraMap ℝ Cl55) 4)

def reflect_in_e (i : Fin 5) (x : Cl55) : Cl55 :=
  - ι55 (e_pos i) * x * ι55 (e_pos i)

private theorem reflect_core {A : Type*} [Ring A] (e f : A)
    (he : e * e = 1) (hanti : e * f + f * e = 0) :
    -e * (e + f) * e = -(e - f) := by
  have hef : e * f = -(f * e) := by
    rw [← add_eq_zero_iff_eq_neg]
    exact hanti
  calc
    -e * (e + f) * e = -((e * e + e * f) * e) := by noncomm_ring
    _ = -((1 + e * f) * e) := by rw [he]
    _ = -(e + (e * f) * e) := by noncomm_ring
    _ = -(e + (-(f * e)) * e) := by rw [hef]
    _ = -(e - f) := by
      rw [neg_mul, mul_assoc, he]
      noncomm_ring

private theorem reflect_core_sub {A : Type*} [Ring A] (e f : A)
    (he : e * e = 1) (hanti : e * f + f * e = 0) :
    -e * (e - f) * e = -(e + f) := by
  have hef : e * f = -(f * e) := by
    rw [← add_eq_zero_iff_eq_neg]
    exact hanti
  calc
    -e * (e - f) * e = -((e * e - e * f) * e) := by noncomm_ring
    _ = -((1 - e * f) * e) := by rw [he]
    _ = -(e - (e * f) * e) := by noncomm_ring
    _ = -(e - (-(f * e)) * e) := by rw [hef]
    _ = -(e + f) := by
      rw [neg_mul, mul_assoc, he]
      noncomm_ring

theorem reflect_n_eq_neg_nbar (i : Fin 5) :
    reflect_in_e i (ι55 (n_pair i)) = - ι55 (nbar_pair i) := by
  dsimp [reflect_in_e, n_pair, nbar_pair]
  rw [map_add, map_sub]
  exact reflect_core (ι55 (e_pos i)) (ι55 (f_neg i)) (e_pos_mul_self i) (orthogonal_anticomm i i)

theorem reflect_nbar_eq_neg_n (i : Fin 5) :
    reflect_in_e i (ι55 (nbar_pair i)) = - ι55 (n_pair i) := by
  dsimp [reflect_in_e, n_pair, nbar_pair]
  rw [map_add, map_sub]
  exact reflect_core_sub (ι55 (e_pos i)) (ι55 (f_neg i)) (e_pos_mul_self i) (orthogonal_anticomm i i)

def n_coll : V55 := ∑ i : Fin 5, n_pair i

def nbar_coll : V55 := ∑ i : Fin 5, nbar_pair i

@[simp] theorem n_coll_null : Q55 n_coll = 0 := by
  classical
  have h : n_coll = (fun _ : Fin 5 => (1 : ℝ), fun _ : Fin 5 => (1 : ℝ)) := by
    ext i
    · simp [n_coll, n_pair, e_pos, f_neg]
      change (∑ x : Fin 5, if i = x then (1 : ℝ) else 0) = 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb.symm]
      · intro h
        exact False.elim (h (Finset.mem_univ i))
    · simp [n_coll, n_pair, e_pos, f_neg]
      change (∑ x : Fin 5, if i = x then (1 : ℝ) else 0) = 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb.symm]
      · intro h
        exact False.elim (h (Finset.mem_univ i))
  rw [h]
  simp [Q55_apply]

@[simp] theorem nbar_coll_null : Q55 nbar_coll = 0 := by
  classical
  have h : nbar_coll = (fun _ : Fin 5 => (1 : ℝ), fun _ : Fin 5 => (-1 : ℝ)) := by
    ext i
    · simp [nbar_coll, nbar_pair, e_pos, f_neg]
      change (∑ x : Fin 5, if i = x then (1 : ℝ) else 0) = 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb.symm]
      · intro h
        exact False.elim (h (Finset.mem_univ i))
    · simp [nbar_coll, nbar_pair, e_pos, f_neg]
      change (∑ x : Fin 5, - (if i = x then (1 : ℝ) else 0)) = -1
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb.symm]
      · intro h
        exact False.elim (h (Finset.mem_univ i))
  rw [h]
  simp [Q55_apply]

def R_P : Cl55 :=
  ι55 (e_pos 0) * ι55 (e_pos 1) * ι55 (e_pos 2) * ι55 (e_pos 3) * ι55 (e_pos 4)

def R_T : Cl55 :=
  ι55 (f_neg 0) * ι55 (f_neg 1) * ι55 (f_neg 2) * ι55 (f_neg 3) * ι55 (f_neg 4)

def R_PT : Cl55 := R_P * R_T

inductive TrialitySector where
  | vector | spinor | cospinor
  deriving Repr, DecidableEq

def RT_sector : TrialitySector → TrialitySector
  | TrialitySector.vector => TrialitySector.vector
  | TrialitySector.spinor => TrialitySector.cospinor
  | TrialitySector.cospinor => TrialitySector.spinor

def cl_mass_scalar (m0 ΔP ΔT : ℝ) : TrialitySector → ℝ
  | TrialitySector.vector => m0 ^ 2
  | TrialitySector.spinor => m0 ^ 2 + ΔP + ΔT
  | TrialitySector.cospinor => m0 ^ 2 + ΔP - ΔT

theorem RT_swaps_semispinors :
    RT_sector TrialitySector.spinor = TrialitySector.cospinor ∧
    RT_sector TrialitySector.cospinor = TrialitySector.spinor := by
  simp [RT_sector]

theorem all_masses_distinct (m0 ΔP ΔT : ℝ) (hT : ΔT ≠ 0) :
    cl_mass_scalar m0 ΔP ΔT TrialitySector.spinor ≠
      cl_mass_scalar m0 ΔP ΔT TrialitySector.cospinor := by
  intro h
  apply hT
  simp [cl_mass_scalar] at h
  linarith

end Clifford55

end noncomputable section
