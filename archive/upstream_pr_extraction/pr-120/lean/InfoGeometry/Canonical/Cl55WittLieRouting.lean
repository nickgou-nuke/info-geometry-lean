import InfoGeometry.Canonical.Cl55WittCAR

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55WittLieRouting

open scoped Matrix Kronecker
open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55WittCAR

def bracket (X Y : MatStage 5) : MatStage 5 := X * Y - Y * X

/-- The grade-zero matrix-unit packet obtained from a mixed Witt product. -/
def E (i j : Fin 5) : MatStage 5 :=
  creation i * annihilation j -
    (if i = j then (1 / 2 : ℝ) • (1 : MatStage 5) else 0)

theorem bracket_swap (X Y : MatStage 5) :
    bracket X Y = -bracket Y X := by
  unfold bracket
  noncomm_ring

theorem bracket_self (X : MatStage 5) :
    bracket X X = 0 := by
  unfold bracket
  simp

theorem bracket_jacobi_left (X Y Z : MatStage 5) :
    bracket (bracket X Y) Z =
      bracket X (bracket Y Z) - bracket Y (bracket X Z) := by
  unfold bracket
  noncomm_ring

theorem bracket_smul_left (r : ℝ) (X Y : MatStage 5) :
    bracket (r • X) Y = r • bracket X Y := by
  unfold bracket
  simp only [smul_sub, Matrix.smul_mul, Matrix.mul_smul]

theorem bracket_smul_right (r : ℝ) (X Y : MatStage 5) :
    bracket X (r • Y) = r • bracket X Y := by
  unfold bracket
  simp only [smul_sub, Matrix.smul_mul, Matrix.mul_smul]

theorem bracket_add_left (X₁ X₂ Y : MatStage 5) :
    bracket (X₁ + X₂) Y = bracket X₁ Y + bracket X₂ Y := by
  unfold bracket
  noncomm_ring

theorem bracket_sum_left
    {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (f : ι → MatStage 5) (Y : MatStage 5) :
    bracket (∑ i, g i • f i) Y =
      ∑ i, g i • bracket (f i) Y := by
  unfold bracket
  rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Matrix.smul_mul, Matrix.mul_smul]
  rw [← Finset.sum_sub_distrib]
  simp_rw [smul_sub]

theorem bracket_add_right (X Y₁ Y₂ : MatStage 5) :
    bracket X (Y₁ + Y₂) = bracket X Y₁ + bracket X Y₂ := by
  unfold bracket
  noncomm_ring

theorem bracket_mul_left (X Y Z : MatStage 5) :
    bracket (X * Y) Z = X * bracket Y Z + bracket X Z * Y := by
  unfold bracket
  noncomm_ring

theorem bracket_mul_right (X Y Z : MatStage 5) :
    bracket X (Y * Z) = bracket X Y * Z + Y * bracket X Z := by
  unfold bracket
  noncomm_ring

lemma rank_one_bracket
    {R : Type*} [Ring R]
    (a b c d δ ε : R)
    (hδ : ∀ x : R, δ * x = x * δ)
    (hε : ∀ x : R, ε * x = x * ε)
    (hbc : b * c = δ - c * b)
    (hda : d * a = ε - a * d)
    (hac : a * c = -(c * a))
    (hbd : b * d = -(d * b)) :
    (a * b) * (c * d) - (c * d) * (a * b) =
      δ * (a * d) - ε * (c * b) := by
  have hcancel : a * c * b * d = c * a * d * b := by
    calc
      a * c * b * d = -(c * a) * b * d := by rw [hac]
      _ = -(c * a) * (b * d) := by noncomm_ring
      _ = -(c * a) * (-(d * b)) := by rw [hbd]
      _ = c * a * d * b := by noncomm_ring
  calc
    a * b * (c * d) - c * d * (a * b) =
        a * (b * c) * d - c * (d * a) * b := by noncomm_ring
    _ = a * (δ - c * b) * d - c * (ε - a * d) * b := by rw [hbc, hda]
    _ = δ * (a * d) - ε * (c * b) := by
      simp only [sub_mul, mul_sub]
      rw [show a * (c * b) * d = a * c * b * d by noncomm_ring]
      rw [show c * (a * d) * b = c * a * d * b by noncomm_ring]
      rw [hcancel]
      rw [← hδ a, ← hε c]
      noncomm_ring

theorem creation_anticomm (i j : Fin 5) :
    creation i * creation j + creation j * creation i = 0 := by
  by_cases h : i = j
  · subst j
    rw [creation_same_site_sq i]
    simp
  · exact creation_cross_anticommute h

theorem annihilation_anticomm (i j : Fin 5) :
    annihilation i * annihilation j + annihilation j * annihilation i = 0 := by
  by_cases h : i = j
  · subst j
    rw [annihilation_same_site_sq i]
    simp
  · exact annihilation_cross_anticommute h

theorem annihilation_creation_anticomm (i j : Fin 5) :
    annihilation i * creation j + creation j * annihilation i =
      if i = j then (1 : MatStage 5) else 0 := by
  by_cases h : i = j
  · subst j
    simpa [add_comm] using creation_annihilation_same_site i
  · simpa [h] using annihilation_creation_cross_anticommute h

theorem creation_annihilation_anticomm (i j : Fin 5) :
    creation i * annihilation j + annihilation j * creation i =
      if i = j then (1 : MatStage 5) else 0 := by
  by_cases h : i = j
  · subst j
    simpa using creation_annihilation_same_site i
  · simpa [h] using creation_annihilation_cross_anticommute h

theorem E_creation (i j k : Fin 5) :
    bracket (E i j) (creation k) =
      if j = k then creation i else 0 := by
  have hac := annihilation_creation_anticomm j k
  have hcc := creation_anticomm i k
  have hac' : annihilation j * creation k =
      (if j = k then (1 : MatStage 5) else 0) -
        creation k * annihilation j := by
    exact eq_sub_of_add_eq hac
  have hcore : creation i * annihilation j * creation k -
      creation k * (creation i * annihilation j) =
        if j = k then creation i else 0 := by
    calc
      creation i * annihilation j * creation k -
          creation k * (creation i * annihilation j) =
            creation i * (annihilation j * creation k) -
              (creation k * creation i) * annihilation j := by noncomm_ring
      _ = creation i * ((if j = k then (1 : MatStage 5) else 0) -
            creation k * annihilation j) -
            (creation k * creation i) * annihilation j := by rw [hac']
      _ = (if j = k then creation i else 0) -
            (creation i * creation k + creation k * creation i) * annihilation j := by
              by_cases hjk : j = k <;> simp [hjk] <;> noncomm_ring
      _ = if j = k then creation i else 0 := by rw [hcc]; simp
  have hscalar :
      (if i = j then (1 / 2 : ℝ) • (1 : MatStage 5) else 0) * creation k -
        creation k * (if i = j then (1 / 2 : ℝ) • (1 : MatStage 5) else 0) = 0 := by
    by_cases hij : i = j <;>
      simp [hij]
  rw [E, bracket]
  calc
    (creation i * annihilation j -
        (if i = j then (1 / 2 : ℝ) • (1 : MatStage 5) else 0)) * creation k -
        creation k * (creation i * annihilation j -
          (if i = j then (1 / 2 : ℝ) • (1 : MatStage 5) else 0)) =
      (creation i * annihilation j * creation k -
          creation k * (creation i * annihilation j)) -
        ((if i = j then (1 / 2 : ℝ) • (1 : MatStage 5) else 0) * creation k -
          creation k * (if i = j then (1 / 2 : ℝ) • (1 : MatStage 5) else 0)) := by
            noncomm_ring
    _ = if j = k then creation i else 0 := by rw [hcore, hscalar]; simp

theorem E_annihilation (i j k : Fin 5) :
    bracket (E i j) (annihilation k) =
      if i = k then -annihilation j else 0 := by
  have hac := creation_annihilation_anticomm i k
  have haa := annihilation_anticomm j k
  have hac' : annihilation k * creation i =
      (if i = k then (1 : MatStage 5) else 0) -
        creation i * annihilation k := by
    exact eq_sub_of_add_eq (by simpa [add_comm] using hac)
  have hcore : creation i * annihilation j * annihilation k -
      annihilation k * (creation i * annihilation j) =
        if i = k then -annihilation j else 0 := by
    calc
      creation i * annihilation j * annihilation k -
          annihilation k * (creation i * annihilation j) =
            creation i * (annihilation j * annihilation k) -
              (annihilation k * creation i) * annihilation j := by noncomm_ring
      _ = creation i * (annihilation j * annihilation k) -
            ((if i = k then (1 : MatStage 5) else 0) -
              creation i * annihilation k) * annihilation j := by rw [hac']
      _ = (if i = k then -annihilation j else 0) +
            creation i * (annihilation j * annihilation k +
              annihilation k * annihilation j) := by
              by_cases hik : i = k <;> simp [hik] <;> noncomm_ring
      _ = if i = k then -annihilation j else 0 := by rw [haa]; simp
  have hscalar :
      (if i = j then (1 / 2 : ℝ) • (1 : MatStage 5) else 0) * annihilation k -
        annihilation k * (if i = j then (1 / 2 : ℝ) • (1 : MatStage 5) else 0) = 0 := by
    by_cases hij : i = j <;> simp [hij]
  rw [E, bracket]
  calc
    (creation i * annihilation j -
        (if i = j then (1 / 2 : ℝ) • (1 : MatStage 5) else 0)) * annihilation k -
        annihilation k * (creation i * annihilation j -
          (if i = j then (1 / 2 : ℝ) • (1 : MatStage 5) else 0)) =
      (creation i * annihilation j * annihilation k -
          annihilation k * (creation i * annihilation j)) -
        ((if i = j then (1 / 2 : ℝ) • (1 : MatStage 5) else 0) * annihilation k -
          annihilation k * (if i = j then (1 / 2 : ℝ) • (1 : MatStage 5) else 0)) := by
            noncomm_ring
    _ = if i = k then -annihilation j else 0 := by rw [hcore, hscalar]; simp

def numberOperator : MatStage 5 :=
  ∑ i : Fin 5, E i i

theorem numberOperator_creation (k : Fin 5) :
    bracket numberOperator (creation k) = creation k := by
  unfold numberOperator
  rw [show (∑ i : Fin 5, E i i) = ∑ i : Fin 5, (1 : ℝ) • E i i by simp]
  rw [bracket_sum_left]
  simp_rw [E_creation]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b hb hbk
    simp [hbk]
  · intro hk
    simp at hk

theorem numberOperator_annihilation (k : Fin 5) :
    bracket numberOperator (annihilation k) = -annihilation k := by
  unfold numberOperator
  rw [show (∑ i : Fin 5, E i i) = ∑ i : Fin 5, (1 : ℝ) • E i i by simp]
  rw [bracket_sum_left]
  simp_rw [E_annihilation]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b hb hbk
    simp [hbk]
  · intro hk
    simp at hk

theorem numberOperator_creation_quadratic (i j : Fin 5) :
    bracket numberOperator (creation i * creation j) =
      (2 : ℝ) • (creation i * creation j) := by
  rw [bracket_mul_right, numberOperator_creation,
    numberOperator_creation]
  rw [two_smul]

theorem numberOperator_annihilation_quadratic (i j : Fin 5) :
    bracket numberOperator (annihilation i * annihilation j) =
      (-2 : ℝ) • (annihilation i * annihilation j) := by
  rw [bracket_mul_right, numberOperator_annihilation,
    numberOperator_annihilation]
  have htwo (X : MatStage 5) :
      (-2 : ℝ) • X = -((2 : ℝ) • X) := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, neg_smul]
  rw [htwo, two_smul]
  simp only [neg_mul, mul_neg]
  abel

theorem numberOperator_mixed (i j : Fin 5) :
    bracket numberOperator (creation i * annihilation j) = 0 := by
  rw [bracket_mul_right, numberOperator_creation,
    numberOperator_annihilation]
  simp

theorem numberOperator_E (i j : Fin 5) :
    bracket numberOperator (E i j) = 0 := by
  unfold E
  by_cases hij : i = j
  · subst j
    simp only [eq_self, ↓reduceIte]
    change bracket numberOperator
      (creation i * annihilation i - (1 / 2 : ℝ) • (1 : MatStage 5)) = 0
    rw [sub_eq_add_neg, bracket_add_right, numberOperator_mixed]
    have hscalar :
        bracket numberOperator ((1 / 2 : ℝ) • (1 : MatStage 5)) = 0 := by
      unfold bracket
      simp
    rw [show -((1 / 2 : ℝ) • (1 : MatStage 5)) =
        (-1 : ℝ) • ((1 / 2 : ℝ) • (1 : MatStage 5)) by simp,
      bracket_smul_right, hscalar]
    simp
  · simp only [if_neg hij]
    rw [sub_zero]
    exact numberOperator_mixed i j

def numberAdjoint : MatStage 5 →ₗ[ℝ] MatStage 5 where
  toFun := bracket numberOperator
  map_add' X Y := bracket_add_right numberOperator X Y
  map_smul' c X := bracket_smul_right c numberOperator X

theorem numberAdjoint_bracket (X Y : MatStage 5) :
    numberAdjoint (bracket X Y) =
      bracket (numberAdjoint X) Y + bracket X (numberAdjoint Y) := by
  change bracket numberOperator (bracket X Y) =
    bracket (bracket numberOperator X) Y +
      bracket X (bracket numberOperator Y)
  unfold bracket
  noncomm_ring

theorem numberAdjoint_mul (X Y : MatStage 5) :
    numberAdjoint (X * Y) =
      numberAdjoint X * Y + X * numberAdjoint Y := by
  change bracket numberOperator (X * Y) =
    bracket numberOperator X * Y + X * bracket numberOperator Y
  unfold bracket
  noncomm_ring

def gradeSubmodule (k : ℤ) : Submodule ℝ (MatStage 5) :=
  LinearMap.ker (numberAdjoint - (k : ℝ) • LinearMap.id)

theorem numberOperator_mem_grade_zero :
    numberOperator ∈ gradeSubmodule 0 := by
  apply LinearMap.mem_ker.mpr
  simp [numberAdjoint, bracket]

theorem creation_mem_gradeSubmodule (i : Fin 5) :
    creation i ∈ gradeSubmodule 1 := by
  apply LinearMap.mem_ker.mpr
  simp [numberAdjoint, numberOperator_creation]

theorem annihilation_mem_gradeSubmodule (i : Fin 5) :
    annihilation i ∈ gradeSubmodule (-1) := by
  apply LinearMap.mem_ker.mpr
  simp [numberAdjoint, numberOperator_annihilation]

theorem E_mem_gradeSubmodule (i j : Fin 5) :
    E i j ∈ gradeSubmodule 0 := by
  apply LinearMap.mem_ker.mpr
  simp [numberAdjoint, numberOperator_E]

theorem creation_quadratic_mem_gradeSubmodule (i j : Fin 5) :
    creation i * creation j ∈ gradeSubmodule 2 := by
  apply LinearMap.mem_ker.mpr
  simp [numberAdjoint,
    numberOperator_creation_quadratic]

theorem annihilation_quadratic_mem_gradeSubmodule (i j : Fin 5) :
    annihilation i * annihilation j ∈ gradeSubmodule (-2) := by
  apply LinearMap.mem_ker.mpr
  simp [numberAdjoint,
    numberOperator_annihilation_quadratic]

theorem creation_E (i j k : Fin 5) :
    bracket (creation k) (E i j) =
      if j = k then -creation i else 0 := by
  rw [bracket_swap, E_creation]
  by_cases h : j = k <;> simp [h]

theorem annihilation_E (i j k : Fin 5) :
    bracket (annihilation k) (E i j) =
      if i = k then annihilation j else 0 := by
  rw [bracket_swap, E_annihilation]
  by_cases h : i = k <;> simp [h]

theorem E_bracket (i j k l : Fin 5) :
    bracket (E i j) (E k l) =
      (if j = k then E i l else 0) -
        (if i = l then E k j else 0) := by
  have hjk : annihilation j * creation k =
      (if j = k then (1 : MatStage 5) else 0) -
        creation k * annihilation j := by
    have h : annihilation j * creation k + creation k * annihilation j =
        if j = k then (1 : MatStage 5) else 0 := by
      simpa [add_comm, eq_comm] using creation_annihilation_anticomm k j
    exact eq_sub_of_add_eq h
  have hli : annihilation l * creation i =
      (if l = i then (1 : MatStage 5) else 0) -
        creation i * annihilation l := by
    have h : annihilation l * creation i + creation i * annihilation l =
        if l = i then (1 : MatStage 5) else 0 := by
      simpa [add_comm, eq_comm] using creation_annihilation_anticomm i l
    exact eq_sub_of_add_eq h
  have hci : creation i * creation k = -(creation k * creation i) := by
    exact eq_neg_of_add_eq_zero_right (by
      simpa [add_comm] using creation_anticomm i k)
  have haj : annihilation j * annihilation l =
      -(annihilation l * annihilation j) := by
    exact eq_neg_of_add_eq_zero_right (by
      simpa [add_comm] using annihilation_anticomm j l)
  have hδ : ∀ x : MatStage 5,
      (if j = k then (1 : MatStage 5) else 0) * x =
        x * (if j = k then (1 : MatStage 5) else 0) := by
    intro x
    by_cases h : j = k <;> simp [h]
  have hε : ∀ x : MatStage 5,
      (if l = i then (1 : MatStage 5) else 0) * x =
        x * (if l = i then (1 : MatStage 5) else 0) := by
    intro x
    by_cases h : l = i <;> simp [h]
  have hraw :
      bracket (creation i * annihilation j)
        (creation k * annihilation l) =
      (if j = k then (creation i * annihilation l) else 0) -
        (if l = i then (creation k * annihilation j) else 0) := by
    simpa using rank_one_bracket _ _ _ _ _ _ hδ hε hjk hli hci haj
  unfold E
  rw [show bracket
      (creation i * annihilation j -
        (if i = j then (1 / 2 : ℝ) • (1 : MatStage 5) else 0))
      (creation k * annihilation l -
        (if k = l then (1 / 2 : ℝ) • (1 : MatStage 5) else 0)) =
        bracket (creation i * annihilation j)
          (creation k * annihilation l) by
            unfold bracket
            by_cases hij : i = j <;> by_cases hkl : k = l <;>
              simp [hij, hkl, sub_mul, mul_sub] <;>
              (try noncomm_ring) <;> module]
  rw [hraw]
  by_cases h₁ : j = k <;> by_cases h₂ : i = l <;>
    simp [h₁, h₂, eq_comm]

theorem creation_bracket (i j : Fin 5) :
    bracket (creation i) (creation j) = 2 • (creation i * creation j) := by
  unfold bracket
  by_cases h : i = j
  · subst j
    rw [creation_same_site_sq]
    simp
  · have hanti := creation_cross_anticommute h
    calc
      creation i * creation j - creation j * creation i =
          creation i * creation j - (-(creation i * creation j)) := by
            rw [eq_neg_of_add_eq_zero_right hanti]
      _ = 2 • (creation i * creation j) := by
            rw [two_smul]
            abel

theorem annihilation_bracket (i j : Fin 5) :
    bracket (annihilation i) (annihilation j) = 2 •
      (annihilation i * annihilation j) := by
  unfold bracket
  by_cases h : i = j
  · subst j
    rw [annihilation_same_site_sq]
    simp
  · have hanti := annihilation_cross_anticommute h
    calc
      annihilation i * annihilation j - annihilation j * annihilation i =
          annihilation i * annihilation j - (-(annihilation i * annihilation j)) := by
            rw [eq_neg_of_add_eq_zero_right hanti]
      _ = 2 • (annihilation i * annihilation j) := by
            rw [two_smul]
            abel

theorem creation_bracket_real (i j : Fin 5) :
    bracket (creation i) (creation j) =
      (2 : ℝ) • (creation i * creation j) := by
  rw [creation_bracket]
  rw [two_smul, two_smul]

theorem annihilation_bracket_real (i j : Fin 5) :
    bracket (annihilation i) (annihilation j) =
      (2 : ℝ) • (annihilation i * annihilation j) := by
  rw [annihilation_bracket]
  rw [two_smul, two_smul]

theorem creation_annihilation_bracket (i j : Fin 5) :
    bracket (creation i) (annihilation j) = 2 • E i j := by
  have hac := creation_annihilation_anticomm i j
  unfold bracket E
  by_cases h : i = j
  · subst j
    have hac' : annihilation i * creation i =
        (1 : MatStage 5) - creation i * annihilation i := by
      have hrev : annihilation i * creation i + creation i * annihilation i =
          (1 : MatStage 5) := by
        simpa [add_comm] using hac
      exact eq_sub_of_add_eq hrev
    rw [hac']
    simp [smul_sub]
    have htwo : (2 : ℝ) • (1 : MatStage 5) = (2 : MatStage 5) := by
      rw [two_smul]
      norm_num
    have hhalf : (2⁻¹ : ℝ) • (2 : MatStage 5) = 1 := by
      rw [← htwo, smul_smul]
      norm_num
    have hmat (X : MatStage 5) : (2 : MatStage 5) * X = 2 • X := by
      calc
        (2 : MatStage 5) * X = ((1 : MatStage 5) + 1) * X := by
          norm_num
        _ = X + X := by simp [add_mul]
        _ = 2 • X := by rw [two_smul]
    rw [hhalf]
    rw [hmat]
    abel
  · have hac' : annihilation j * creation i =
        -(creation i * annihilation j) := by
      have hac0 : creation i * annihilation j + annihilation j * creation i = 0 := by
        simpa [h] using hac
      exact eq_neg_of_add_eq_zero_right hac0
    rw [hac']
    simp [h]
    noncomm_ring

theorem creation_annihilation_bracket_real (i j : Fin 5) :
    bracket (creation i) (annihilation j) = (2 : ℝ) • E i j := by
  rw [creation_annihilation_bracket]
  rw [two_smul, two_smul]

theorem annihilation_creation_bracket_real (i j : Fin 5) :
    bracket (annihilation i) (creation j) =
      -(2 : ℝ) • E j i := by
  rw [bracket_swap, creation_annihilation_bracket_real]
  exact (neg_smul (2 : ℝ) (E j i)).symm

theorem creation_quadratic_bracket_annihilation (i j k : Fin 5) :
    bracket (creation i * creation j) (annihilation k) =
      (if j = k then creation i else 0) -
        (if i = k then creation j else 0) := by
  have hprod : creation i * creation j =
      (1 / 2 : ℝ) • bracket (creation i) (creation j) := by
    rw [creation_bracket_real]
    rw [smul_smul]
    norm_num
  calc
    bracket (creation i * creation j) (annihilation k) =
        bracket ((1 / 2 : ℝ) • bracket (creation i) (creation j))
          (annihilation k) := by rw [hprod]
    _ = (1 / 2 : ℝ) • bracket (bracket (creation i) (creation j))
          (annihilation k) := by rw [bracket_smul_left]
    _ = (1 / 2 : ℝ) •
        (bracket (creation i) (bracket (creation j) (annihilation k)) -
          bracket (creation j) (bracket (creation i) (annihilation k))) := by
            rw [bracket_jacobi_left]
    _ = (if j = k then creation i else 0) -
        (if i = k then creation j else 0) := by
          rw [creation_annihilation_bracket_real,
            creation_annihilation_bracket_real,
            bracket_smul_right, bracket_smul_right,
            creation_E, creation_E]
          by_cases hik : i = k
          · by_cases hjk : j = k <;>
            simp [smul_smul, hik, hjk, eq_comm]
          · by_cases hjk : j = k <;>
            simp [smul_smul, hik, hjk, eq_comm]

/-! ### Lie-only obstruction routing

The full associative Clifford envelope contains higher words, but the ordinary
commutator closure of the Witt generators does not create them.  These are the
first native matrix proofs of that distinction at stage `Cl(5,5)`. -/

theorem creation_quadratic_bracket_creation (i j k : Fin 5) :
    bracket (creation i * creation j) (creation k) = 0 := by
  rw [bracket_mul_left, creation_bracket, creation_bracket]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  have h : creation k * creation j = -(creation j * creation k) :=
    eq_neg_of_add_eq_zero_right (creation_anticomm j k)
  rw [show creation i * creation k * creation j =
      creation i * (creation k * creation j) by rw [mul_assoc]]
  rw [h]
  noncomm_ring

theorem annihilation_quadratic_bracket_annihilation (i j k : Fin 5) :
    bracket (annihilation i * annihilation j) (annihilation k) = 0 := by
  rw [bracket_mul_left, annihilation_bracket, annihilation_bracket]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  have h : annihilation k * annihilation j =
      -(annihilation j * annihilation k) :=
    eq_neg_of_add_eq_zero_right (annihilation_anticomm j k)
  rw [show annihilation i * annihilation k * annihilation j =
      annihilation i * (annihilation k * annihilation j) by rw [mul_assoc]]
  rw [h]
  noncomm_ring

theorem creation_quadratic_bracket_creation_quadratic
    (i j k l : Fin 5) :
    bracket (creation i * creation j) (creation k * creation l) = 0 := by
  rw [bracket_mul_right, creation_quadratic_bracket_creation,
    creation_quadratic_bracket_creation]
  simp

theorem annihilation_quadratic_bracket_annihilation_quadratic
    (i j k l : Fin 5) :
    bracket (annihilation i * annihilation j)
      (annihilation k * annihilation l) = 0 := by
  rw [bracket_mul_right, annihilation_quadratic_bracket_annihilation,
    annihilation_quadratic_bracket_annihilation]
  simp

theorem annihilation_quadratic_bracket_creation (i j k : Fin 5) :
    bracket (annihilation i * annihilation j) (creation k) =
      (if j = k then annihilation i else 0) -
        (if i = k then annihilation j else 0) := by
  have hprod : annihilation i * annihilation j =
      (1 / 2 : ℝ) • bracket (annihilation i) (annihilation j) := by
    rw [annihilation_bracket_real]
    rw [smul_smul]
    norm_num
  calc
    bracket (annihilation i * annihilation j) (creation k) =
        bracket ((1 / 2 : ℝ) • bracket (annihilation i) (annihilation j))
          (creation k) := by rw [hprod]
    _ = (1 / 2 : ℝ) • bracket (bracket (annihilation i) (annihilation j))
          (creation k) := by rw [bracket_smul_left]
    _ = (1 / 2 : ℝ) •
        (bracket (annihilation i) (bracket (annihilation j) (creation k)) -
          bracket (annihilation j) (bracket (annihilation i) (creation k))) := by
            rw [bracket_jacobi_left]
    _ = (if j = k then annihilation i else 0) -
        (if i = k then annihilation j else 0) := by
            rw [annihilation_creation_bracket_real,
              annihilation_creation_bracket_real,
              bracket_smul_right, bracket_smul_right,
              annihilation_E, annihilation_E]
            by_cases hik : i = k
            · by_cases hjk : j = k <;>
                simp [smul_smul, hik, hjk, eq_comm]
            · by_cases hjk : j = k <;>
                simp [smul_smul, hik, hjk, eq_comm]

theorem annihilation_creation_reorder (i j : Fin 5) :
    annihilation i * creation j =
      (if i = j then (1 : MatStage 5) else 0) -
        creation j * annihilation i := by
  calc
    annihilation i * creation j =
        (annihilation i * creation j + creation j * annihilation i) -
          creation j * annihilation i := by noncomm_ring
    _ = (if i = j then (1 : MatStage 5) else 0) -
          creation j * annihilation i := by
      rw [annihilation_creation_anticomm]

theorem creation_annihilation_reorder (i j : Fin 5) :
    creation i * annihilation j =
      (if i = j then (1 : MatStage 5) else 0) -
        annihilation j * creation i := by
  calc
    creation i * annihilation j =
        (creation i * annihilation j + annihilation j * creation i) -
          annihilation j * creation i := by noncomm_ring
    _ = (if i = j then (1 : MatStage 5) else 0) -
          annihilation j * creation i := by
      rw [creation_annihilation_anticomm]

theorem creation_quadratic_bracket_annihilation_quadratic
    (i j k l : Fin 5) :
    bracket (creation i * creation j) (annihilation k * annihilation l) =
      (if j = k then E i l else 0) -
        (if i = k then E j l else 0) -
        (if j = l then E i k else 0) +
        (if i = l then E j k else 0) := by
  rw [bracket_mul_right,
    creation_quadratic_bracket_annihilation,
    creation_quadratic_bracket_annihilation]
  by_cases hjk : j = k <;>
    by_cases hik : i = k <;>
    by_cases hjl : j = l <;>
    by_cases hil : i = l <;>
    by_cases hkl : k = l <;>
    simp [hjk, hik, hjl, hil, hkl, eq_comm, E,
      annihilation_creation_reorder] <;>
    first
    | exact Ne.symm hjk
    | exact Ne.symm hik
    | exact Ne.symm hjl
    | exact Ne.symm hil
    | exact Ne.symm hkl
    | module

/-! ### Native Lie-generated Witt sectors

These are the submodules generated by the Witt generators and the words which
are actually produced by their ordinary commutators.  They remain in the
native `MatStage 5` carrier. -/

def wittNegTwo : Submodule ℝ (MatStage 5) :=
  Submodule.span ℝ (Set.range (fun ij : Fin 5 × Fin 5 =>
    annihilation ij.1 * annihilation ij.2))

def wittNegOne : Submodule ℝ (MatStage 5) :=
  Submodule.span ℝ (Set.range annihilation)

def wittZero : Submodule ℝ (MatStage 5) :=
  Submodule.span ℝ (Set.range (fun ij : Fin 5 × Fin 5 => E ij.1 ij.2))

theorem numberOperator_mem_wittZero :
    numberOperator ∈ wittZero := by
  unfold numberOperator
  refine Submodule.sum_mem wittZero (fun i _ => ?_)
  exact Submodule.subset_span (Set.mem_range_self (i, i))

def wittPosOne : Submodule ℝ (MatStage 5) :=
  Submodule.span ℝ (Set.range creation)

def wittPosTwo : Submodule ℝ (MatStage 5) :=
  Submodule.span ℝ (Set.range (fun ij : Fin 5 × Fin 5 =>
    creation ij.1 * creation ij.2))

def wittNegTwoOrdered : Submodule ℝ (MatStage 5) :=
  Submodule.span ℝ (Set.range (fun ij : {ij : Fin 5 × Fin 5 // ij.1 < ij.2} =>
    annihilation ij.1.1 * annihilation ij.1.2))

def wittPosTwoOrdered : Submodule ℝ (MatStage 5) :=
        Submodule.span ℝ (Set.range (fun ij : {ij : Fin 5 × Fin 5 // ij.1 < ij.2} =>
          creation ij.1.1 * creation ij.1.2))

theorem wittNegTwo_le_gradeSubmodule :
    wittNegTwo ≤ gradeSubmodule (-2) := by
  unfold wittNegTwo
  refine Submodule.span_le.2 ?_
  rintro _ ⟨ij, rfl⟩
  exact annihilation_quadratic_mem_gradeSubmodule _ _

theorem wittNegOne_le_gradeSubmodule :
    wittNegOne ≤ gradeSubmodule (-1) := by
  unfold wittNegOne
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  exact annihilation_mem_gradeSubmodule i

theorem wittZero_le_gradeSubmodule :
    wittZero ≤ gradeSubmodule 0 := by
  unfold wittZero
  refine Submodule.span_le.2 ?_
  rintro _ ⟨ij, rfl⟩
  exact E_mem_gradeSubmodule _ _

theorem wittPosOne_le_gradeSubmodule :
    wittPosOne ≤ gradeSubmodule 1 := by
  unfold wittPosOne
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  exact creation_mem_gradeSubmodule i

theorem wittPosTwo_le_gradeSubmodule :
    wittPosTwo ≤ gradeSubmodule 2 := by
  unfold wittPosTwo
  refine Submodule.span_le.2 ?_
  rintro _ ⟨ij, rfl⟩
  exact creation_quadratic_mem_gradeSubmodule _ _

theorem grade_mem_eq_zero_of_distinct
    {k l : ℤ} (hkl : (k : ℝ) ≠ (l : ℝ))
    (x : MatStage 5)
    (hxk : x ∈ gradeSubmodule k)
    (hxl : x ∈ gradeSubmodule l) :
    x = 0 := by
  have hk : numberAdjoint x = (k : ℝ) • x := by
    have h := LinearMap.mem_ker.mp hxk
    exact sub_eq_zero.mp (by simpa [gradeSubmodule] using h)
  have hl : numberAdjoint x = (l : ℝ) • x := by
    have h := LinearMap.mem_ker.mp hxl
    exact sub_eq_zero.mp (by simpa [gradeSubmodule] using h)
  have hsub : ((k : ℝ) - (l : ℝ)) • x = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr (hk.symm.trans hl)
  exact (smul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hkl)

theorem gradeSubmodule_bracket_mem
    {k l : ℤ} {X Y : MatStage 5}
    (hX : X ∈ gradeSubmodule k) (hY : Y ∈ gradeSubmodule l) :
    bracket X Y ∈ gradeSubmodule (k + l) := by
  have hk : numberAdjoint X = (k : ℝ) • X := by
    have h := LinearMap.mem_ker.mp hX
    exact sub_eq_zero.mp (by simpa [gradeSubmodule] using h)
  have hl : numberAdjoint Y = (l : ℝ) • Y := by
    have h := LinearMap.mem_ker.mp hY
    exact sub_eq_zero.mp (by simpa [gradeSubmodule] using h)
  apply LinearMap.mem_ker.mpr
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [numberAdjoint_bracket, hk, hl,
    bracket_smul_left, bracket_smul_right, Int.cast_add,
    ← add_smul, sub_self]

theorem gradeSubmodule_mul_mem
    {k l : ℤ} {X Y : MatStage 5}
    (hX : X ∈ gradeSubmodule k) (hY : Y ∈ gradeSubmodule l) :
    X * Y ∈ gradeSubmodule (k + l) := by
  have hk : numberAdjoint X = (k : ℝ) • X := by
    have h := LinearMap.mem_ker.mp hX
    exact sub_eq_zero.mp (by simpa [gradeSubmodule] using h)
  have hl : numberAdjoint Y = (l : ℝ) • Y := by
    have h := LinearMap.mem_ker.mp hY
    exact sub_eq_zero.mp (by simpa [gradeSubmodule] using h)
  apply LinearMap.mem_ker.mpr
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [numberAdjoint_mul, hk, hl, Matrix.smul_mul, Matrix.mul_smul,
    Int.cast_add, ← add_smul]
  module

theorem gradeSubmodule_anticommutator_mem
    {k l : ℤ} {X Y : MatStage 5}
    (hX : X ∈ gradeSubmodule k) (hY : Y ∈ gradeSubmodule l) :
    X * Y + Y * X ∈ gradeSubmodule (k + l) := by
  have hXY := gradeSubmodule_mul_mem hX hY
  have hYX := gradeSubmodule_mul_mem hY hX
  have hYX' : Y * X ∈ gradeSubmodule (k + l) := by
    simpa [add_comm] using hYX
  exact (gradeSubmodule (k + l)).add_mem hXY hYX'

theorem gradeSubmodule_inf_eq_bot
    {k l : ℤ} (hkl : (k : ℝ) ≠ (l : ℝ)) :
    gradeSubmodule k ⊓ gradeSubmodule l = (⊥ : Submodule ℝ (MatStage 5)) := by
  apply le_antisymm
  · intro x hx
    exact grade_mem_eq_zero_of_distinct hkl x hx.1 hx.2
  · exact bot_le

theorem submodule_inf_eq_bot_of_distinct_grades
    {P Q : Submodule ℝ (MatStage 5)}
    {k l : ℤ} (hkl : (k : ℝ) ≠ (l : ℝ))
    (hP : P ≤ gradeSubmodule k)
    (hQ : Q ≤ gradeSubmodule l) :
    P ⊓ Q = (⊥ : Submodule ℝ (MatStage 5)) := by
  apply le_antisymm
  · intro x hx
    have hxg : x ∈ gradeSubmodule k ⊓ gradeSubmodule l :=
      ⟨hP hx.1, hQ hx.2⟩
    rw [gradeSubmodule_inf_eq_bot hkl] at hxg
    exact hxg
  · exact bot_le

theorem wittPosOne_inf_wittNegOne_eq_bot :
    wittPosOne ⊓ wittNegOne = (⊥ : Submodule ℝ (MatStage 5)) := by
  apply le_antisymm
  · intro x hx
    have hxg : x ∈ gradeSubmodule 1 ⊓ gradeSubmodule (-1) := by
      exact ⟨wittPosOne_le_gradeSubmodule hx.1,
        wittNegOne_le_gradeSubmodule hx.2⟩
    rw [gradeSubmodule_inf_eq_bot (by norm_num)] at hxg
    exact hxg
  · exact bot_le

theorem wittPosTwo_inf_wittNegTwo_eq_bot :
    wittPosTwo ⊓ wittNegTwo = (⊥ : Submodule ℝ (MatStage 5)) := by
  exact submodule_inf_eq_bot_of_distinct_grades (by norm_num)
    wittPosTwo_le_gradeSubmodule wittNegTwo_le_gradeSubmodule

theorem wittZero_inf_wittPosOne_eq_bot :
    wittZero ⊓ wittPosOne = (⊥ : Submodule ℝ (MatStage 5)) := by
  exact submodule_inf_eq_bot_of_distinct_grades (by norm_num)
    wittZero_le_gradeSubmodule wittPosOne_le_gradeSubmodule

theorem wittZero_inf_wittNegOne_eq_bot :
    wittZero ⊓ wittNegOne = (⊥ : Submodule ℝ (MatStage 5)) := by
  exact submodule_inf_eq_bot_of_distinct_grades (by norm_num)
    wittZero_le_gradeSubmodule wittNegOne_le_gradeSubmodule

theorem wittPosTwo_inf_wittPosOne_eq_bot :
    wittPosTwo ⊓ wittPosOne = (⊥ : Submodule ℝ (MatStage 5)) := by
  exact submodule_inf_eq_bot_of_distinct_grades (by norm_num)
    wittPosTwo_le_gradeSubmodule wittPosOne_le_gradeSubmodule

theorem wittNegTwo_inf_wittNegOne_eq_bot :
    wittNegTwo ⊓ wittNegOne = (⊥ : Submodule ℝ (MatStage 5)) := by
  exact submodule_inf_eq_bot_of_distinct_grades (by norm_num)
    wittNegTwo_le_gradeSubmodule wittNegOne_le_gradeSubmodule

theorem wittNegTwo_le_ordered :
    wittNegTwo ≤ wittNegTwoOrdered := by
  unfold wittNegTwo
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨i, j⟩, rfl⟩
  rcases lt_trichotomy i j with hij | hij | hij
  · change annihilation i * annihilation j ∈
      Submodule.span ℝ (Set.range (fun ij : {ij : Fin 5 × Fin 5 // ij.1 < ij.2} =>
        annihilation ij.1.1 * annihilation ij.1.2))
    apply Submodule.subset_span (R := ℝ)
    exact ⟨⟨⟨i, j⟩, hij⟩, rfl⟩
  · subst j
    change annihilation i * annihilation i ∈ wittNegTwoOrdered
    rw [annihilation_same_site_sq]
    exact Submodule.zero_mem _
  · have hanti := annihilation_anticomm i j
    have hswap : annihilation i * annihilation j =
        -(annihilation j * annihilation i) :=
      eq_neg_of_add_eq_zero_right (by simpa [add_comm] using hanti)
    change annihilation i * annihilation j ∈ wittNegTwoOrdered
    rw [hswap]
    have hmem : annihilation j * annihilation i ∈
        Submodule.span ℝ (Set.range (fun ij : {ij : Fin 5 × Fin 5 // ij.1 < ij.2} =>
          annihilation ij.1.1 * annihilation ij.1.2)) := by
      apply Submodule.subset_span (R := ℝ)
      exact ⟨⟨⟨j, i⟩, hij⟩, rfl⟩
    change -(annihilation j * annihilation i) ∈
      Submodule.span ℝ (Set.range (fun ij : {ij : Fin 5 × Fin 5 // ij.1 < ij.2} =>
        annihilation ij.1.1 * annihilation ij.1.2))
    simpa using Submodule.smul_mem _ (-1 : ℝ) hmem

theorem wittPosTwo_le_ordered :
    wittPosTwo ≤ wittPosTwoOrdered := by
  unfold wittPosTwo
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨i, j⟩, rfl⟩
  rcases lt_trichotomy i j with hij | hij | hij
  · change creation i * creation j ∈
      Submodule.span ℝ (Set.range (fun ij : {ij : Fin 5 × Fin 5 // ij.1 < ij.2} =>
        creation ij.1.1 * creation ij.1.2))
    apply Submodule.subset_span (R := ℝ)
    exact ⟨⟨⟨i, j⟩, hij⟩, rfl⟩
  · subst j
    change creation i * creation i ∈ wittPosTwoOrdered
    rw [creation_same_site_sq]
    exact Submodule.zero_mem _
  · have hanti := creation_anticomm i j
    have hswap : creation i * creation j =
        -(creation j * creation i) :=
      eq_neg_of_add_eq_zero_right (by simpa [add_comm] using hanti)
    change creation i * creation j ∈ wittPosTwoOrdered
    rw [hswap]
    have hmem : creation j * creation i ∈
        Submodule.span ℝ (Set.range (fun ij : {ij : Fin 5 × Fin 5 // ij.1 < ij.2} =>
          creation ij.1.1 * creation ij.1.2)) := by
      apply Submodule.subset_span (R := ℝ)
      exact ⟨⟨⟨j, i⟩, hij⟩, rfl⟩
    change -(creation j * creation i) ∈
      Submodule.span ℝ (Set.range (fun ij : {ij : Fin 5 × Fin 5 // ij.1 < ij.2} =>
        creation ij.1.1 * creation ij.1.2))
    simpa using Submodule.smul_mem _ (-1 : ℝ) hmem

theorem creation_quadratic_bracket_annihilation_mem
    (i j k : Fin 5) :
    bracket (creation i * creation j) (annihilation k) ∈ wittPosOne := by
  have hc (r : Fin 5) : creation r ∈ wittPosOne :=
    Submodule.subset_span (Set.mem_range_self r)
  rw [creation_quadratic_bracket_annihilation]
  by_cases hjk : j = k
  · by_cases hik : i = k
    · simpa [hjk, hik] using wittPosOne.sub_mem (hc i) (hc j)
    · simpa [hjk, hik] using wittPosOne.sub_mem (hc i) wittPosOne.zero_mem
  · by_cases hik : i = k
    · simpa [hjk, hik] using wittPosOne.sub_mem wittPosOne.zero_mem (hc j)
    · simpa [hjk, hik] using wittPosOne.zero_mem

theorem annihilation_quadratic_bracket_creation_mem
    (i j k : Fin 5) :
    bracket (annihilation i * annihilation j) (creation k) ∈ wittNegOne := by
  have ha (r : Fin 5) : annihilation r ∈ wittNegOne :=
    Submodule.subset_span (Set.mem_range_self r)
  rw [annihilation_quadratic_bracket_creation]
  by_cases hjk : j = k
  · by_cases hik : i = k
    · simpa [hjk, hik] using wittNegOne.sub_mem (ha i) (ha j)
    · simpa [hjk, hik] using wittNegOne.sub_mem (ha i) wittNegOne.zero_mem
  · by_cases hik : i = k
    · simpa [hjk, hik] using wittNegOne.sub_mem wittNegOne.zero_mem (ha j)
    · simpa [hjk, hik] using wittNegOne.zero_mem

theorem wittPosTwo_bracket_mem_wittZero
    {X Y : MatStage 5}
    (hX : X ∈ wittPosTwo) (hY : Y ∈ wittNegTwo) :
    bracket X Y ∈ wittZero := by
  have hE (i j : Fin 5) : E i j ∈ wittZero :=
    Submodule.subset_span (Set.mem_range_self (i, j))
  have hif (p q : Fin 5) (z : MatStage 5)
      (hz : z ∈ wittZero) :
      (if p = q then z else 0) ∈ wittZero := by
    by_cases h : p = q <;> simp [h, hz]
  have hadd_left : ∀ (x₁ x₂ y : MatStage 5),
      bracket (x₁ + x₂) y = bracket x₁ y + bracket x₂ y := by
    intro x₁ x₂ y
    unfold bracket
    noncomm_ring
  have hadd_right : ∀ (x y₁ y₂ : MatStage 5),
      bracket x (y₁ + y₂) = bracket x y₁ + bracket x y₂ := by
    intro x y₁ y₂
    unfold bracket
    noncomm_ring
  refine Submodule.span_induction (p := fun X _ => bracket X Y ∈ wittZero)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨ij, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => bracket (creation ij.1 * creation ij.2) Y ∈ wittZero)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨kl, rfl⟩
      rw [creation_quadratic_bracket_annihilation_quadratic]
      exact wittZero.add_mem
        (wittZero.sub_mem
          (wittZero.sub_mem
            (hif ij.2 kl.1 (E ij.1 kl.2) (hE _ _))
            (hif ij.1 kl.1 (E ij.2 kl.2) (hE _ _)))
          (hif ij.2 kl.2 (E ij.1 kl.1) (hE _ _)))
        (hif ij.1 kl.2 (E ij.2 kl.1) (hE _ _))
    · simp [bracket]
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [hadd_right]
      exact wittZero.add_mem hy₁ hy₂
    · intro c y _ hy
      rw [bracket_smul_right]
      exact wittZero.smul_mem c hy
  · simp [bracket]
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [hadd_left]
    exact wittZero.add_mem hx₁ hx₂
  · intro c x _ hx
    rw [bracket_smul_left]
    exact wittZero.smul_mem c hx

theorem wittPosTwo_bracket_eq_zero
    {X Y : MatStage 5}
    (hX : X ∈ wittPosTwo) (hY : Y ∈ wittPosOne) :
    bracket X Y = 0 := by
  have hadd_left : ∀ (x₁ x₂ y : MatStage 5),
      bracket (x₁ + x₂) y = bracket x₁ y + bracket x₂ y := by
    intro x₁ x₂ y
    unfold bracket
    noncomm_ring
  have hadd_right : ∀ (x y₁ y₂ : MatStage 5),
      bracket x (y₁ + y₂) = bracket x y₁ + bracket x y₂ := by
    intro x y₁ y₂
    unfold bracket
    noncomm_ring
  refine Submodule.span_induction (p := fun X _ => bracket X Y = 0)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨ij, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => bracket (creation ij.1 * creation ij.2) Y = 0)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨k, rfl⟩
      exact creation_quadratic_bracket_creation ij.1 ij.2 k
    · simp [bracket]
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [hadd_right, hy₁, hy₂, add_zero]
    · intro c y _ hy
      rw [bracket_smul_right, hy, smul_zero]
  · simp [bracket]
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [hadd_left, hx₁, hx₂, add_zero]
  · intro c x _ hx
    rw [bracket_smul_left, hx, smul_zero]

theorem wittNegTwo_bracket_eq_zero
    {X Y : MatStage 5}
    (hX : X ∈ wittNegTwo) (hY : Y ∈ wittNegOne) :
    bracket X Y = 0 := by
  have hadd_left : ∀ (x₁ x₂ y : MatStage 5),
      bracket (x₁ + x₂) y = bracket x₁ y + bracket x₂ y := by
    intro x₁ x₂ y
    unfold bracket
    noncomm_ring
  have hadd_right : ∀ (x y₁ y₂ : MatStage 5),
      bracket x (y₁ + y₂) = bracket x y₁ + bracket x y₂ := by
    intro x y₁ y₂
    unfold bracket
    noncomm_ring
  refine Submodule.span_induction (p := fun X _ => bracket X Y = 0)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨ij, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => bracket (annihilation ij.1 * annihilation ij.2) Y = 0)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨k, rfl⟩
      exact annihilation_quadratic_bracket_annihilation ij.1 ij.2 k
    · simp [bracket]
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [hadd_right, hy₁, hy₂, add_zero]
    · intro c y _ hy
      rw [bracket_smul_right, hy, smul_zero]
  · simp [bracket]
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [hadd_left, hx₁, hx₂, add_zero]
  · intro c x _ hx
    rw [bracket_smul_left, hx, smul_zero]

theorem wittPosTwo_bracket_eq_zero_quadratic
    {X Y : MatStage 5}
    (hX : X ∈ wittPosTwo) (hY : Y ∈ wittPosTwo) :
    bracket X Y = 0 := by
  have hadd_left : ∀ (x₁ x₂ y : MatStage 5),
      bracket (x₁ + x₂) y = bracket x₁ y + bracket x₂ y := by
    intro x₁ x₂ y
    unfold bracket
    noncomm_ring
  have hadd_right : ∀ (x y₁ y₂ : MatStage 5),
      bracket x (y₁ + y₂) = bracket x y₁ + bracket x y₂ := by
    intro x y₁ y₂
    unfold bracket
    noncomm_ring
  refine Submodule.span_induction (p := fun X _ => bracket X Y = 0)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨ij, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => bracket (creation ij.1 * creation ij.2) Y = 0)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨kl, rfl⟩
      exact creation_quadratic_bracket_creation_quadratic
        ij.1 ij.2 kl.1 kl.2
    · simp [bracket]
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [hadd_right, hy₁, hy₂, add_zero]
    · intro c y _ hy
      rw [bracket_smul_right, hy, smul_zero]
  · simp [bracket]
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [hadd_left, hx₁, hx₂, add_zero]
  · intro c x _ hx
    rw [bracket_smul_left, hx, smul_zero]

theorem wittNegTwo_bracket_eq_zero_quadratic
    {X Y : MatStage 5}
    (hX : X ∈ wittNegTwo) (hY : Y ∈ wittNegTwo) :
    bracket X Y = 0 := by
  have hadd_left : ∀ (x₁ x₂ y : MatStage 5),
      bracket (x₁ + x₂) y = bracket x₁ y + bracket x₂ y := by
    intro x₁ x₂ y
    unfold bracket
    noncomm_ring
  have hadd_right : ∀ (x y₁ y₂ : MatStage 5),
      bracket x (y₁ + y₂) = bracket x y₁ + bracket x y₂ := by
    intro x y₁ y₂
    unfold bracket
    noncomm_ring
  refine Submodule.span_induction (p := fun X _ => bracket X Y = 0)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨ij, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => bracket (annihilation ij.1 * annihilation ij.2) Y = 0)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨kl, rfl⟩
      exact annihilation_quadratic_bracket_annihilation_quadratic
        ij.1 ij.2 kl.1 kl.2
    · simp [bracket]
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [hadd_right, hy₁, hy₂, add_zero]
    · intro c y _ hy
      rw [bracket_smul_right, hy, smul_zero]
  · simp [bracket]
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [hadd_left, hx₁, hx₂, add_zero]
  · intro c x _ hx
    rw [bracket_smul_left, hx, smul_zero]

theorem E_creation_quadratic_bracket
    (i j k l : Fin 5) :
    bracket (E i j) (creation k * creation l) =
      (if j = k then creation i * creation l else 0) -
        (if j = l then creation i * creation k else 0) := by
  rw [bracket_mul_right, E_creation, E_creation]
  by_cases hjk : j = k <;>
    by_cases hjl : j = l <;>
    by_cases hkl : k = l <;>
    simp [hjk, hjl, hkl, eq_comm, creation_anticomm] <;>
    exact eq_neg_of_add_eq_zero_right (creation_anticomm i k)

theorem wittZero_bracket_mem_wittPosTwo
    {X Y : MatStage 5}
    (hX : X ∈ wittZero) (hY : Y ∈ wittPosTwo) :
    bracket X Y ∈ wittPosTwo := by
  have hquad (i j : Fin 5) : creation i * creation j ∈ wittPosTwo := by
    exact Submodule.subset_span (Set.mem_range_self (i, j))
  have hif (i j : Fin 5) (z : MatStage 5) (hz : z ∈ wittPosTwo) :
      (if i = j then z else 0) ∈ wittPosTwo := by
    by_cases h : i = j <;> simp [h, hz]
  have hadd_left : ∀ (x₁ x₂ y : MatStage 5),
      bracket (x₁ + x₂) y = bracket x₁ y + bracket x₂ y := by
    intro x₁ x₂ y
    unfold bracket
    noncomm_ring
  have hadd_right : ∀ (x y₁ y₂ : MatStage 5),
      bracket x (y₁ + y₂) = bracket x y₁ + bracket x y₂ := by
    intro x y₁ y₂
    unfold bracket
    noncomm_ring
  refine Submodule.span_induction (p := fun X _ => bracket X Y ∈ wittPosTwo)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨ij, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => bracket (E ij.1 ij.2) Y ∈ wittPosTwo)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨kl, rfl⟩
      rw [E_creation_quadratic_bracket]
      exact wittPosTwo.sub_mem
        (hif ij.2 kl.1 (creation ij.1 * creation kl.2)
          (hquad _ _))
        (hif ij.2 kl.2 (creation ij.1 * creation kl.1)
          (hquad _ _))
    · simp [bracket]
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [hadd_right]
      exact wittPosTwo.add_mem hy₁ hy₂
    · intro c y _ hy
      rw [bracket_smul_right]
      exact wittPosTwo.smul_mem c hy
  · simp [bracket]
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [hadd_left]
    exact wittPosTwo.add_mem hx₁ hx₂
  · intro c x _ hx
    rw [bracket_smul_left]
    exact wittPosTwo.smul_mem c hx

theorem wittPosOne_bracket_wittPosTwo_eq_zero
    {X Y : MatStage 5}
    (hX : X ∈ wittPosOne) (hY : Y ∈ wittPosTwo) :
    bracket X Y = 0 := by
  rw [bracket_swap]
  rw [wittPosTwo_bracket_eq_zero hY hX]
  simp

theorem wittNegOne_bracket_wittNegTwo_eq_zero
    {X Y : MatStage 5}
    (hX : X ∈ wittNegOne) (hY : Y ∈ wittNegTwo) :
    bracket X Y = 0 := by
  rw [bracket_swap]
  rw [wittNegTwo_bracket_eq_zero hY hX]
  simp

theorem E_annihilation_quadratic_bracket
    (i j k l : Fin 5) :
    bracket (E i j) (annihilation k * annihilation l) =
      (if i = k then -(annihilation j * annihilation l) else 0) +
        (if i = l then annihilation j * annihilation k else 0) := by
  have hanti (p q : Fin 5) :
      -(annihilation p * annihilation q) +
          -(annihilation q * annihilation p) = 0 := by
    simpa [neg_add, add_comm] using congrArg Neg.neg (annihilation_anticomm p q)
  rw [bracket_mul_right, E_annihilation, E_annihilation]
  by_cases hik : i = k <;>
    by_cases hil : i = l <;>
    by_cases hkl : k = l <;>
    simp [hik, hil, hkl, eq_comm]
  all_goals
    first
    | exact hanti j l
    | exact hanti j k
    | exact eq_neg_of_add_eq_zero_right (annihilation_anticomm k j)

theorem wittZero_bracket_mem_wittNegTwo
    {X Y : MatStage 5}
    (hX : X ∈ wittZero) (hY : Y ∈ wittNegTwo) :
    bracket X Y ∈ wittNegTwo := by
  have hquad (i j : Fin 5) : annihilation i * annihilation j ∈ wittNegTwo := by
    exact Submodule.subset_span (Set.mem_range_self (i, j))
  have hif (i j : Fin 5) (z : MatStage 5) (hz : z ∈ wittNegTwo) :
      (if i = j then z else 0) ∈ wittNegTwo := by
    by_cases h : i = j <;> simp [h, hz]
  have hadd_left : ∀ (x₁ x₂ y : MatStage 5),
      bracket (x₁ + x₂) y = bracket x₁ y + bracket x₂ y := by
    intro x₁ x₂ y
    unfold bracket
    noncomm_ring
  have hadd_right : ∀ (x y₁ y₂ : MatStage 5),
      bracket x (y₁ + y₂) = bracket x y₁ + bracket x y₂ := by
    intro x y₁ y₂
    unfold bracket
    noncomm_ring
  refine Submodule.span_induction (p := fun X _ => bracket X Y ∈ wittNegTwo)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨ij, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => bracket (E ij.1 ij.2) Y ∈ wittNegTwo)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨kl, rfl⟩
      rw [E_annihilation_quadratic_bracket]
      have hleft :
          (if ij.1 = kl.1 then
              -(annihilation ij.2 * annihilation kl.2) else 0) ∈ wittNegTwo := by
        by_cases h : ij.1 = kl.1 <;> simp [h, hquad _ _]
      exact wittNegTwo.add_mem hleft
        (hif ij.1 kl.2 (annihilation ij.2 * annihilation kl.1)
          (hquad _ _))
    · simp [bracket]
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [hadd_right]
      exact wittNegTwo.add_mem hy₁ hy₂
    · intro c y _ hy
      rw [bracket_smul_right]
      exact wittNegTwo.smul_mem c hy
  · simp [bracket]
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [hadd_left]
    exact wittNegTwo.add_mem hx₁ hx₂
  · intro c x _ hx
    rw [bracket_smul_left]
    exact wittNegTwo.smul_mem c hx

theorem wittPosTwo_bracket_mem_wittPosOne
    {X Y : MatStage 5}
    (hX : X ∈ wittPosTwo) (hY : Y ∈ wittNegOne) :
    bracket X Y ∈ wittPosOne := by
  have hadd_left : ∀ (x₁ x₂ y : MatStage 5),
      bracket (x₁ + x₂) y = bracket x₁ y + bracket x₂ y := by
    intro x₁ x₂ y
    unfold bracket
    noncomm_ring
  have hadd_right : ∀ (x y₁ y₂ : MatStage 5),
      bracket x (y₁ + y₂) = bracket x y₁ + bracket x y₂ := by
    intro x y₁ y₂
    unfold bracket
    noncomm_ring
  refine Submodule.span_induction (p := fun X _ => bracket X Y ∈ wittPosOne)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨ij, rfl⟩
    rcases ij with ⟨i, j⟩
    refine Submodule.span_induction
      (p := fun Y _ => bracket (creation i * creation j) Y ∈ wittPosOne)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨k, rfl⟩
      exact creation_quadratic_bracket_annihilation_mem i j k
    · simp [bracket]
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [hadd_right]
      exact wittPosOne.add_mem hy₁ hy₂
    · intro c y _ hy
      rw [bracket_smul_right]
      exact wittPosOne.smul_mem c hy
  · simp [bracket]
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [hadd_left]
    exact wittPosOne.add_mem hx₁ hx₂
  · intro c x _ hx
    rw [bracket_smul_left]
    exact wittPosOne.smul_mem c hx

theorem wittNegTwo_bracket_mem_wittNegOne
    {X Y : MatStage 5}
    (hX : X ∈ wittNegTwo) (hY : Y ∈ wittPosOne) :
    bracket X Y ∈ wittNegOne := by
  have hadd_left : ∀ (x₁ x₂ y : MatStage 5),
      bracket (x₁ + x₂) y = bracket x₁ y + bracket x₂ y := by
    intro x₁ x₂ y
    unfold bracket
    noncomm_ring
  have hadd_right : ∀ (x y₁ y₂ : MatStage 5),
      bracket x (y₁ + y₂) = bracket x y₁ + bracket x y₂ := by
    intro x y₁ y₂
    unfold bracket
    noncomm_ring
  refine Submodule.span_induction (p := fun X _ => bracket X Y ∈ wittNegOne)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨ij, rfl⟩
    rcases ij with ⟨i, j⟩
    refine Submodule.span_induction
      (p := fun Y _ => bracket (annihilation i * annihilation j) Y ∈ wittNegOne)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨k, rfl⟩
      exact annihilation_quadratic_bracket_creation_mem i j k
    · simp [bracket]
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [hadd_right]
      exact wittNegOne.add_mem hy₁ hy₂
    · intro c y _ hy
      rw [bracket_smul_right]
      exact wittNegOne.smul_mem c hy
  · simp [bracket]
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [hadd_left]
    exact wittNegOne.add_mem hx₁ hx₂
  · intro c x _ hx
    rw [bracket_smul_left]
    exact wittNegOne.smul_mem c hx

theorem wittPosOne_bracket_mem_wittNegOne
    {X Y : MatStage 5}
    (hX : X ∈ wittPosOne) (hY : Y ∈ wittNegTwo) :
    bracket X Y ∈ wittNegOne := by
  rw [bracket_swap]
  exact wittNegOne.neg_mem
    (wittNegTwo_bracket_mem_wittNegOne hY hX)

theorem wittNegOne_bracket_mem_wittPosOne
    {X Y : MatStage 5}
    (hX : X ∈ wittNegOne) (hY : Y ∈ wittPosTwo) :
    bracket X Y ∈ wittPosOne := by
  rw [bracket_swap]
  exact wittPosOne.neg_mem
    (wittPosTwo_bracket_mem_wittPosOne hY hX)

theorem wittNegTwo_bracket_mem_wittZero
    {X Y : MatStage 5}
    (hX : X ∈ wittNegTwo) (hY : Y ∈ wittPosTwo) :
    bracket X Y ∈ wittZero := by
  rw [bracket_swap]
  exact wittZero.neg_mem
    (wittPosTwo_bracket_mem_wittZero hY hX)

theorem wittPosTwo_bracket_mem_wittPosTwo
    {X Y : MatStage 5}
    (hX : X ∈ wittPosTwo) (hY : Y ∈ wittZero) :
    bracket X Y ∈ wittPosTwo := by
  rw [bracket_swap]
  exact wittPosTwo.neg_mem
    (wittZero_bracket_mem_wittPosTwo hY hX)

theorem wittNegTwo_bracket_mem_wittNegTwo
    {X Y : MatStage 5}
    (hX : X ∈ wittNegTwo) (hY : Y ∈ wittZero) :
    bracket X Y ∈ wittNegTwo := by
  rw [bracket_swap]
  exact wittNegTwo.neg_mem
    (wittZero_bracket_mem_wittNegTwo hY hX)

theorem wittPosOne_bracket_mem_wittPosTwo
    {X Y : MatStage 5}
    (hX : X ∈ wittPosOne) (hY : Y ∈ wittPosOne) :
    bracket X Y ∈ wittPosTwo := by
  have hadd_left : ∀ (x₁ x₂ y : MatStage 5),
      bracket (x₁ + x₂) y = bracket x₁ y + bracket x₂ y := by
    intro x₁ x₂ y
    unfold bracket
    noncomm_ring
  have hadd_right : ∀ (x y₁ y₂ : MatStage 5),
      bracket x (y₁ + y₂) = bracket x y₁ + bracket x y₂ := by
    intro x y₁ y₂
    unfold bracket
    noncomm_ring
  refine Submodule.span_induction (p := fun X _ => bracket X Y ∈ wittPosTwo)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => bracket (creation i) Y ∈ wittPosTwo)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨j, rfl⟩
      rw [creation_bracket_real]
      exact wittPosTwo.smul_mem (2 : ℝ)
        (Submodule.subset_span (Set.mem_range_self (i, j)))
    · simp [bracket]
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [hadd_right]
      exact wittPosTwo.add_mem hy₁ hy₂
    · intro c y _ hy
      rw [bracket_smul_right]
      exact wittPosTwo.smul_mem c hy
  · simp [bracket]
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [hadd_left]
    exact wittPosTwo.add_mem hx₁ hx₂
  · intro c x _ hx
    rw [bracket_smul_left]
    exact wittPosTwo.smul_mem c hx

theorem wittNegOne_bracket_mem_wittNegTwo
    {X Y : MatStage 5}
    (hX : X ∈ wittNegOne) (hY : Y ∈ wittNegOne) :
    bracket X Y ∈ wittNegTwo := by
  have hadd_left : ∀ (x₁ x₂ y : MatStage 5),
      bracket (x₁ + x₂) y = bracket x₁ y + bracket x₂ y := by
    intro x₁ x₂ y
    unfold bracket
    noncomm_ring
  have hadd_right : ∀ (x y₁ y₂ : MatStage 5),
      bracket x (y₁ + y₂) = bracket x y₁ + bracket x y₂ := by
    intro x y₁ y₂
    unfold bracket
    noncomm_ring
  refine Submodule.span_induction (p := fun X _ => bracket X Y ∈ wittNegTwo)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => bracket (annihilation i) Y ∈ wittNegTwo)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨j, rfl⟩
      rw [annihilation_bracket_real]
      exact wittNegTwo.smul_mem (2 : ℝ)
        (Submodule.subset_span (Set.mem_range_self (i, j)))
    · simp [bracket]
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [hadd_right]
      exact wittNegTwo.add_mem hy₁ hy₂
    · intro c y _ hy
      rw [bracket_smul_right]
      exact wittNegTwo.smul_mem c hy
  · simp [bracket]
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [hadd_left]
    exact wittNegTwo.add_mem hx₁ hx₂
  · intro c x _ hx
    rw [bracket_smul_left]
    exact wittNegTwo.smul_mem c hx

theorem wittZero_bracket_mem_wittPosOne
    {X Y : MatStage 5}
    (hX : X ∈ wittZero) (hY : Y ∈ wittPosOne) :
    bracket X Y ∈ wittPosOne := by
  refine Submodule.span_induction (p := fun X _ => bracket X Y ∈ wittPosOne)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨⟨i, j⟩, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => bracket (E i j) Y ∈ wittPosOne)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨k, rfl⟩
      rw [E_creation]
      by_cases h : j = k
      · simpa [h] using
        (Submodule.subset_span (Set.mem_range_self i))
      · simp [h]
    · simp [bracket]
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [bracket_add_right]
      exact wittPosOne.add_mem hy₁ hy₂
    · intro c y _ hy
      rw [bracket_smul_right]
      exact wittPosOne.smul_mem c hy
  · simp [bracket]
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [bracket_add_left]
    exact wittPosOne.add_mem hx₁ hx₂
  · intro c x _ hx
    rw [bracket_smul_left]
    exact wittPosOne.smul_mem c hx

theorem wittZero_bracket_mem_wittNegOne
    {X Y : MatStage 5}
    (hX : X ∈ wittZero) (hY : Y ∈ wittNegOne) :
    bracket X Y ∈ wittNegOne := by
  refine Submodule.span_induction (p := fun X _ => bracket X Y ∈ wittNegOne)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨⟨i, j⟩, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => bracket (E i j) Y ∈ wittNegOne)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨k, rfl⟩
      rw [E_annihilation]
      by_cases h : i = k
      · simpa [h] using wittNegOne.neg_mem
          (Submodule.subset_span (Set.mem_range_self j))
      · simp [h]
    · simp [bracket]
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [bracket_add_right]
      exact wittNegOne.add_mem hy₁ hy₂
    · intro c y _ hy
      rw [bracket_smul_right]
      exact wittNegOne.smul_mem c hy
  · simp [bracket]
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [bracket_add_left]
    exact wittNegOne.add_mem hx₁ hx₂
  · intro c x _ hx
    rw [bracket_smul_left]
    exact wittNegOne.smul_mem c hx

theorem creation_linearIndependent :
    LinearIndependent ℝ creation := by
  rw [Fintype.linearIndependent_iff]
  intro g h j
  have hcalc :
      annihilation j * (∑ i, g i • creation i) +
          (∑ i, g i • creation i) * annihilation j =
        g j • (1 : MatStage 5) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [← Finset.sum_add_distrib]
    simp_rw [← smul_add, annihilation_creation_anticomm]
    simp
  have hz : g j • (1 : MatStage 5) = 0 := by
    rw [← hcalc, h]
    simp
  exact (smul_eq_zero.mp hz).resolve_right one_ne_zero

theorem annihilation_linearIndependent :
    LinearIndependent ℝ annihilation := by
  rw [Fintype.linearIndependent_iff]
  intro g h j
  have hcalc :
      creation j * (∑ i, g i • annihilation i) +
          (∑ i, g i • annihilation i) * creation j =
        g j • (1 : MatStage 5) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [← Finset.sum_add_distrib]
    simp_rw [← smul_add, creation_annihilation_anticomm]
    simp
  have hz : g j • (1 : MatStage 5) = 0 := by
    rw [← hcalc, h]
    simp
  exact (smul_eq_zero.mp hz).resolve_right one_ne_zero

theorem wittZero_bracket_mem_wittZero
    {X Y : MatStage 5}
    (hX : X ∈ wittZero) (hY : Y ∈ wittZero) :
    bracket X Y ∈ wittZero := by
  have he (i j : Fin 5) : E i j ∈ wittZero :=
    Submodule.subset_span (Set.mem_range_self (i, j))
  have hadd_left : ∀ (x₁ x₂ y : MatStage 5),
      bracket (x₁ + x₂) y = bracket x₁ y + bracket x₂ y := by
    intro x₁ x₂ y
    rw [bracket_add_left]
  have hadd_right : ∀ (x y₁ y₂ : MatStage 5),
      bracket x (y₁ + y₂) = bracket x y₁ + bracket x y₂ := by
    intro x y₁ y₂
    rw [bracket_add_right]
  refine Submodule.span_induction (p := fun X _ => bracket X Y ∈ wittZero)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨⟨i, j⟩, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => bracket (E i j) Y ∈ wittZero)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨⟨k, l⟩, rfl⟩
      rw [E_bracket]
      by_cases hjk : j = k <;> by_cases hil : i = l
      · simpa [hjk, hil] using wittZero.sub_mem (he i l) (he k j)
      · simpa [hjk, hil] using wittZero.sub_mem (he i l) wittZero.zero_mem
      · simpa [hjk, hil] using wittZero.sub_mem wittZero.zero_mem (he k j)
      · simp [hjk, hil]
    · simp [bracket]
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [hadd_right]
      exact wittZero.add_mem hy₁ hy₂
    · intro c y _ hy
      rw [bracket_smul_right]
      exact wittZero.smul_mem c hy
  · simp [bracket]
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [hadd_left]
    exact wittZero.add_mem hx₁ hx₂
  · intro c x _ hx
    rw [bracket_smul_left]
    exact wittZero.smul_mem c hx

theorem wittPosOne_bracket_mem_wittZero
    {X Y : MatStage 5}
    (hX : X ∈ wittPosOne) (hY : Y ∈ wittNegOne) :
    bracket X Y ∈ wittZero := by
  have he (i j : Fin 5) : E i j ∈ wittZero :=
    Submodule.subset_span (Set.mem_range_self (i, j))
  refine Submodule.span_induction (p := fun X _ => bracket X Y ∈ wittZero)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => bracket (creation i) Y ∈ wittZero)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨j, rfl⟩
      rw [creation_annihilation_bracket_real]
      simpa [two_smul] using wittZero.smul_mem (2 : ℝ) (he i j)
    · simp [bracket]
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [bracket_add_right]
      exact wittZero.add_mem hy₁ hy₂
    · intro c y _ hy
      rw [bracket_smul_right]
      exact wittZero.smul_mem c hy
  · simp [bracket]
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [bracket_add_left]
    exact wittZero.add_mem hx₁ hx₂
  · intro c x _ hx
    rw [bracket_smul_left]
    exact wittZero.smul_mem c hx

theorem wittNegOne_bracket_mem_wittZero
    {X Y : MatStage 5}
    (hX : X ∈ wittNegOne) (hY : Y ∈ wittPosOne) :
    bracket X Y ∈ wittZero := by
  have he (i j : Fin 5) : E i j ∈ wittZero :=
    Submodule.subset_span (Set.mem_range_self (i, j))
  refine Submodule.span_induction (p := fun X _ => bracket X Y ∈ wittZero)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => bracket (annihilation i) Y ∈ wittZero)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨j, rfl⟩
      rw [annihilation_creation_bracket_real]
      exact wittZero.smul_mem (-2) (he j i)
    · simp [bracket]
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [bracket_add_right]
      exact wittZero.add_mem hy₁ hy₂
    · intro c y _ hy
      rw [bracket_smul_right]
      exact wittZero.smul_mem c hy
  · simp [bracket]
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [bracket_add_left]
    exact wittZero.add_mem hx₁ hx₂
  · intro c x _ hx
    rw [bracket_smul_left]
    exact wittZero.smul_mem c hx

theorem wittNegOne_finrank_le_five :
    Module.finrank ℝ wittNegOne ≤ 5 := by
  unfold wittNegOne
  calc
    Module.finrank ℝ (Submodule.span ℝ (Set.range annihilation)) ≤
        (Set.range annihilation).toFinset.card := finrank_span_le_card _
    _ = (Finset.univ.image annihilation).card := by rw [Set.toFinset_range]
    _ ≤ (Finset.univ : Finset (Fin 5)).card := Finset.card_image_le
    _ = 5 := by simp

theorem wittPosOne_finrank_le_five :
    Module.finrank ℝ wittPosOne ≤ 5 := by
  unfold wittPosOne
  calc
    Module.finrank ℝ (Submodule.span ℝ (Set.range creation)) ≤
        (Set.range creation).toFinset.card := finrank_span_le_card _
    _ = (Finset.univ.image creation).card := by rw [Set.toFinset_range]
    _ ≤ (Finset.univ : Finset (Fin 5)).card := Finset.card_image_le
    _ = 5 := by simp

theorem wittNegOne_finrank_eq_five :
    Module.finrank ℝ wittNegOne = 5 := by
  unfold wittNegOne
  rw [finrank_span_eq_card annihilation_linearIndependent]
  simp

theorem wittPosOne_finrank_eq_five :
    Module.finrank ℝ wittPosOne = 5 := by
  unfold wittPosOne
  rw [finrank_span_eq_card creation_linearIndependent]
  simp

theorem wittNegTwo_finrank_le_twentyFive :
    Module.finrank ℝ wittNegTwo ≤ 25 := by
  unfold wittNegTwo
  calc
    Module.finrank ℝ (Submodule.span ℝ
        (Set.range (fun ij : Fin 5 × Fin 5 =>
          annihilation ij.1 * annihilation ij.2))) ≤
        (Set.range (fun ij : Fin 5 × Fin 5 =>
          annihilation ij.1 * annihilation ij.2)).toFinset.card :=
      finrank_span_le_card _
    _ = (Finset.univ.image (fun ij : Fin 5 × Fin 5 =>
      annihilation ij.1 * annihilation ij.2)).card := by rw [Set.toFinset_range]
    _ ≤ (Finset.univ : Finset (Fin 5 × Fin 5)).card := Finset.card_image_le
    _ = 25 := by simp

theorem wittPosTwo_finrank_le_twentyFive :
    Module.finrank ℝ wittPosTwo ≤ 25 := by
  unfold wittPosTwo
  calc
    Module.finrank ℝ (Submodule.span ℝ
        (Set.range (fun ij : Fin 5 × Fin 5 =>
          creation ij.1 * creation ij.2))) ≤
        (Set.range (fun ij : Fin 5 × Fin 5 =>
          creation ij.1 * creation ij.2)).toFinset.card :=
      finrank_span_le_card _
    _ = (Finset.univ.image (fun ij : Fin 5 × Fin 5 =>
      creation ij.1 * creation ij.2)).card := by rw [Set.toFinset_range]
    _ ≤ (Finset.univ : Finset (Fin 5 × Fin 5)).card := Finset.card_image_le
    _ = 25 := by simp

theorem wittNegTwo_finrank_le_ten :
    Module.finrank ℝ wittNegTwo ≤ 10 := by
  apply le_trans (Submodule.finrank_mono wittNegTwo_le_ordered)
  unfold wittNegTwoOrdered
  calc
    Module.finrank ℝ (Submodule.span ℝ
        (Set.range (fun ij : {ij : Fin 5 × Fin 5 // ij.1 < ij.2} =>
          annihilation ij.1.1 * annihilation ij.1.2))) ≤
        (Set.range (fun ij : {ij : Fin 5 × Fin 5 // ij.1 < ij.2} =>
          annihilation ij.1.1 * annihilation ij.1.2)).toFinset.card :=
      finrank_span_le_card _
    _ ≤ Fintype.card {ij : Fin 5 × Fin 5 // ij.1 < ij.2} := by
      rw [Set.toFinset_range]
      exact Finset.card_image_le
    _ = 10 := by decide

theorem wittPosTwo_finrank_le_ten :
    Module.finrank ℝ wittPosTwo ≤ 10 := by
  apply le_trans (Submodule.finrank_mono wittPosTwo_le_ordered)
  unfold wittPosTwoOrdered
  calc
    Module.finrank ℝ (Submodule.span ℝ
        (Set.range (fun ij : {ij : Fin 5 × Fin 5 // ij.1 < ij.2} =>
          creation ij.1.1 * creation ij.1.2))) ≤
        (Set.range (fun ij : {ij : Fin 5 × Fin 5 // ij.1 < ij.2} =>
          creation ij.1.1 * creation ij.1.2)).toFinset.card :=
      finrank_span_le_card _
    _ ≤ Fintype.card {ij : Fin 5 × Fin 5 // ij.1 < ij.2} := by
      rw [Set.toFinset_range]
      exact Finset.card_image_le
    _ = 10 := by decide

theorem creation_quadratic_linearIndependent :
    LinearIndependent ℝ
      (fun ij : {ij : Fin 5 × Fin 5 // ij.1 < ij.2} =>
        creation ij.1.1 * creation ij.1.2) := by
  rw [Fintype.linearIndependent_iff]
  intro g h p
  have hb := congrArg (fun X => bracket X (annihilation p.1.2)) h
  dsimp at hb
  rw [bracket_sum_left] at hb
  simp_rw [creation_quadratic_bracket_annihilation] at hb
  simp [bracket] at hb
  have hterm (x : {ij : Fin 5 × Fin 5 // ij.1 < ij.2}) :
      annihilation p.1.1 *
          ((if x.1.2 = p.1.2 then creation x.1.1 else 0) -
            if x.1.1 = p.1.2 then creation x.1.2 else 0) +
        ((if x.1.2 = p.1.2 then creation x.1.1 else 0) -
            if x.1.1 = p.1.2 then creation x.1.2 else 0) *
          annihilation p.1.1 =
      (if x.1.2 = p.1.2 then
          (if x.1.1 = p.1.1 then (1 : MatStage 5) else 0) else 0) -
        (if x.1.1 = p.1.2 then
          (if x.1.2 = p.1.1 then (1 : MatStage 5) else 0) else 0) := by
    by_cases h2 : x.1.2 = p.1.2
    · by_cases h1 : x.1.1 = p.1.2
      · simp [h2, h1]
      · simp [h2, h1, annihilation_creation_anticomm, eq_comm]
    · by_cases h1 : x.1.1 = p.1.2
      · have hlt : p.1.1 < x.1.2 := by
          have hp_lt : p.1.1 < p.1.2 := p.2
          have hx_lt : x.1.1 < x.1.2 := x.2
          exact lt_trans (by simpa [h1] using hp_lt) hx_lt
        have hnot : x.1.2 ≠ p.1.1 := by
          intro h
          exact (not_lt_of_ge (by simp [h])) hlt
        have hnot' : p.1.1 ≠ x.1.2 := by
          intro h
          exact hnot h.symm
        have hac :
            annihilation p.1.1 * creation x.1.2 +
              creation x.1.2 * annihilation p.1.1 = 0 := by
          simpa [hnot'] using
            (annihilation_creation_anticomm p.1.1 x.1.2)
        simp only [h2, h1, if_false, if_true, zero_sub]
        rw [mul_neg, neg_mul, ← neg_add, hac, neg_zero]
        simp [hnot]
      · simp [h2, h1]
  have hba := congrArg
    (fun X => annihilation p.1.1 * X + X * annihilation p.1.1) hb
  dsimp at hba
  rw [Finset.sum_mul, Finset.mul_sum] at hba
  simp_rw [Matrix.smul_mul, Matrix.mul_smul] at hba
  rw [← Finset.sum_add_distrib] at hba
  simp_rw [← smul_add] at hba
  simp_rw [hterm] at hba
  have hcoeff (x : {ij : Fin 5 × Fin 5 // ij.1 < ij.2}) :
      (if x.1.2 = p.1.2 then
          (if x.1.1 = p.1.1 then (1 : MatStage 5) else 0) else 0) -
        (if x.1.1 = p.1.2 then
          (if x.1.2 = p.1.1 then (1 : MatStage 5) else 0) else 0) =
      if x = p then (1 : MatStage 5) else 0 := by
    by_cases hx : x = p
    · subst x
      have hne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
      simp [hne]
    · by_cases h2 : x.1.2 = p.1.2
      · by_cases h1 : x.1.1 = p.1.1
        · exfalso
          apply hx
          apply Subtype.ext
          exact Prod.ext h1 h2
        · have hxx : x.1.1 ≠ p.1.2 := by
            intro he
            exact (ne_of_lt x.2) (he.trans h2.symm)
          simp [h2, h1, hxx, hx]
      · by_cases h1 : x.1.1 = p.1.2
        · by_cases h0 : x.1.2 = p.1.1
          · have hrev : p.1.2 < p.1.1 := by simpa [h1, h0] using x.2
            exact False.elim ((not_lt_of_ge (le_of_lt p.2)) hrev)
          · simp [h2, h1, h0, hx]
        · simp [h2, h1, hx]
  have hsum :
      ∑ x : {ij : Fin 5 × Fin 5 // ij.1 < ij.2},
          g x •
            ((if x.1.2 = p.1.2 then
                (if x.1.1 = p.1.1 then (1 : MatStage 5) else 0) else 0) -
              (if x.1.1 = p.1.2 then
                (if x.1.2 = p.1.1 then (1 : MatStage 5) else 0) else 0)) =
        g p • (1 : MatStage 5) := by
    rw [Finset.sum_eq_single p]
    · simp [ne_of_lt p.2]
    · intro b hb hbp
      rw [hcoeff b]
      simp [hbp]
    · intro h
      simp at h
  have hba' :
      ∑ x : {ij : Fin 5 × Fin 5 // ij.1 < ij.2},
          g x •
            ((if x.1.2 = p.1.2 then
                (if x.1.1 = p.1.1 then (1 : MatStage 5) else 0) else 0) -
              (if x.1.1 = p.1.2 then
                (if x.1.2 = p.1.1 then (1 : MatStage 5) else 0) else 0)) = 0 := by
    simpa using hba
  rw [hsum] at hba'
  simpa using hba'

theorem wittPosTwoOrdered_le :
    wittPosTwoOrdered ≤ wittPosTwo := by
  unfold wittPosTwoOrdered wittPosTwo
  refine Submodule.span_le.2 ?_
  rintro _ ⟨ij, rfl⟩
  exact Submodule.subset_span (R := ℝ) ⟨(ij.1.1, ij.1.2), rfl⟩

theorem wittPosTwo_eq_ordered :
    wittPosTwo = wittPosTwoOrdered := by
  exact le_antisymm wittPosTwo_le_ordered wittPosTwoOrdered_le

theorem wittPosTwo_finrank_eq_ten :
    Module.finrank ℝ wittPosTwo = 10 := by
  rw [wittPosTwo_eq_ordered]
  unfold wittPosTwoOrdered
  rw [finrank_span_eq_card creation_quadratic_linearIndependent]
  decide

theorem annihilation_quadratic_linearIndependent :
    LinearIndependent ℝ
      (fun ij : {ij : Fin 5 × Fin 5 // ij.1 < ij.2} =>
        annihilation ij.1.1 * annihilation ij.1.2) := by
  rw [Fintype.linearIndependent_iff]
  intro g h p
  have hb := congrArg (fun X => bracket X (creation p.1.2)) h
  dsimp at hb
  rw [bracket_sum_left] at hb
  simp_rw [annihilation_quadratic_bracket_creation] at hb
  simp [bracket] at hb
  have hterm (x : {ij : Fin 5 × Fin 5 // ij.1 < ij.2}) :
      creation p.1.1 *
          ((if x.1.2 = p.1.2 then annihilation x.1.1 else 0) -
            if x.1.1 = p.1.2 then annihilation x.1.2 else 0) +
        ((if x.1.2 = p.1.2 then annihilation x.1.1 else 0) -
            if x.1.1 = p.1.2 then annihilation x.1.2 else 0) *
          creation p.1.1 =
      (if x.1.2 = p.1.2 then
          (if x.1.1 = p.1.1 then (1 : MatStage 5) else 0) else 0) -
        (if x.1.1 = p.1.2 then
          (if x.1.2 = p.1.1 then (1 : MatStage 5) else 0) else 0) := by
    by_cases h2 : x.1.2 = p.1.2
    · by_cases h1 : x.1.1 = p.1.2
      · simp [h2, h1]
      · simp [h2, h1, creation_annihilation_anticomm, eq_comm]
    · by_cases h1 : x.1.1 = p.1.2
      · have hlt : p.1.1 < x.1.2 := by
          have hp_lt : p.1.1 < p.1.2 := p.2
          have hx_lt : x.1.1 < x.1.2 := x.2
          exact lt_trans (by simpa [h1] using hp_lt) hx_lt
        have hnot : x.1.2 ≠ p.1.1 := by
          intro h
          exact (not_lt_of_ge (by simp [h])) hlt
        have hnot' : p.1.1 ≠ x.1.2 := by
          intro h
          exact hnot h.symm
        have hac :
            creation p.1.1 * annihilation x.1.2 +
              annihilation x.1.2 * creation p.1.1 = 0 := by
          simpa [hnot'] using
            (creation_annihilation_anticomm p.1.1 x.1.2)
        simp only [h2, h1, if_false, if_true, zero_sub]
        rw [mul_neg, neg_mul, ← neg_add, hac, neg_zero]
        simp [hnot]
      · simp [h2, h1]
  have hba := congrArg
    (fun X => creation p.1.1 * X + X * creation p.1.1) hb
  dsimp at hba
  rw [Finset.sum_mul, Finset.mul_sum] at hba
  simp_rw [Matrix.smul_mul, Matrix.mul_smul] at hba
  rw [← Finset.sum_add_distrib] at hba
  simp_rw [← smul_add] at hba
  simp_rw [hterm] at hba
  have hcoeff (x : {ij : Fin 5 × Fin 5 // ij.1 < ij.2}) :
      (if x.1.2 = p.1.2 then
          (if x.1.1 = p.1.1 then (1 : MatStage 5) else 0) else 0) -
        (if x.1.1 = p.1.2 then
          (if x.1.2 = p.1.1 then (1 : MatStage 5) else 0) else 0) =
      if x = p then (1 : MatStage 5) else 0 := by
    by_cases hx : x = p
    · subst x
      have hne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
      simp [hne]
    · by_cases h2 : x.1.2 = p.1.2
      · by_cases h1 : x.1.1 = p.1.1
        · exfalso
          apply hx
          apply Subtype.ext
          exact Prod.ext h1 h2
        · have hxx : x.1.1 ≠ p.1.2 := by
            intro he
            exact (ne_of_lt x.2) (he.trans h2.symm)
          simp [h2, h1, hxx, hx]
      · by_cases h1 : x.1.1 = p.1.2
        · by_cases h0 : x.1.2 = p.1.1
          · have hrev : p.1.2 < p.1.1 := by simpa [h1, h0] using x.2
            exact False.elim ((not_lt_of_ge (le_of_lt p.2)) hrev)
          · simp [h2, h1, h0, hx]
        · simp [h2, h1, hx]
  have hsum :
      ∑ x : {ij : Fin 5 × Fin 5 // ij.1 < ij.2},
          g x •
            ((if x.1.2 = p.1.2 then
                (if x.1.1 = p.1.1 then (1 : MatStage 5) else 0) else 0) -
              (if x.1.1 = p.1.2 then
                (if x.1.2 = p.1.1 then (1 : MatStage 5) else 0) else 0)) =
        g p • (1 : MatStage 5) := by
    rw [Finset.sum_eq_single p]
    · simp [ne_of_lt p.2]
    · intro b hb hbp
      rw [hcoeff b]
      simp [hbp]
    · intro h
      simp at h
  have hba' :
      ∑ x : {ij : Fin 5 × Fin 5 // ij.1 < ij.2},
          g x •
            ((if x.1.2 = p.1.2 then
                (if x.1.1 = p.1.1 then (1 : MatStage 5) else 0) else 0) -
              (if x.1.1 = p.1.2 then
                (if x.1.2 = p.1.1 then (1 : MatStage 5) else 0) else 0)) = 0 := by
    simpa using hba
  rw [hsum] at hba'
  simpa using hba'

theorem wittNegTwoOrdered_le :
    wittNegTwoOrdered ≤ wittNegTwo := by
  unfold wittNegTwoOrdered wittNegTwo
  refine Submodule.span_le.2 ?_
  rintro _ ⟨ij, rfl⟩
  exact Submodule.subset_span (R := ℝ) ⟨(ij.1.1, ij.1.2), rfl⟩

theorem wittNegTwo_eq_ordered :
    wittNegTwo = wittNegTwoOrdered := by
  exact le_antisymm wittNegTwo_le_ordered wittNegTwoOrdered_le

theorem wittNegTwo_finrank_eq_ten :
    Module.finrank ℝ wittNegTwo = 10 := by
  rw [wittNegTwo_eq_ordered]
  unfold wittNegTwoOrdered
  rw [finrank_span_eq_card annihilation_quadratic_linearIndependent]
  decide

theorem zero_packet_linearIndependent :
    LinearIndependent ℝ
      (fun ij : Fin 5 × Fin 5 => E ij.1 ij.2) := by
  rw [Fintype.linearIndependent_iff]
  intro g h p
  have hb := congrArg (fun X => bracket X (creation p.2)) h
  dsimp at hb
  rw [bracket_sum_left] at hb
  simp_rw [E_creation] at hb
  have hb' :
      ∑ x : Fin 5 × Fin 5,
          g x • (if x.2 = p.2 then creation x.1 else 0) = 0 := by
    simpa [bracket] using hb
  have hterm (x : Fin 5 × Fin 5) :
      annihilation p.1 *
          (if x.2 = p.2 then creation x.1 else 0) +
        (if x.2 = p.2 then creation x.1 else 0) *
          annihilation p.1 =
      if x = p then (1 : MatStage 5) else 0 := by
    by_cases h2 : x.2 = p.2
    · by_cases h1 : x.1 = p.1
      · have hx : x = p := Prod.ext h1 h2
        rw [hx]
        simp [annihilation_creation_anticomm]
      · have h1' : p.1 ≠ x.1 := by
          intro h
          exact h1 h.symm
        have hx : x ≠ p := by
          intro h
          exact h1 (congrArg Prod.fst h)
        simp [h2, h1', hx, annihilation_creation_anticomm]
    · have hx : x ≠ p := by
        intro h
        exact h2 (congrArg Prod.snd h)
      simp [h2, hx]
  have hba := congrArg
    (fun X => annihilation p.1 * X + X * annihilation p.1) hb'
  dsimp at hba
  rw [Finset.sum_mul, Finset.mul_sum] at hba
  simp_rw [Matrix.smul_mul, Matrix.mul_smul] at hba
  rw [← Finset.sum_add_distrib] at hba
  simp_rw [← smul_add] at hba
  simp_rw [hterm] at hba
  have hsum :
      ∑ x : Fin 5 × Fin 5,
          g x • (if x = p then (1 : MatStage 5) else 0) =
        g p • (1 : MatStage 5) := by
    rw [Finset.sum_eq_single p]
    · simp
    · intro b hb hbp
      simp [hbp]
    · intro h
      simp at h
  have hba' :
      ∑ x : Fin 5 × Fin 5,
          g x • (if x = p then (1 : MatStage 5) else 0) = 0 := by
    simpa using hba
  rw [hsum] at hba'
  simpa using hba'

theorem wittZero_finrank_eq_twentyFive :
    Module.finrank ℝ wittZero = 25 := by
  unfold wittZero
  rw [finrank_span_eq_card zero_packet_linearIndependent]
  decide

theorem wittZero_finrank_le_twentyFive :
    Module.finrank ℝ wittZero ≤ 25 := by
  unfold wittZero
  calc
    Module.finrank ℝ (Submodule.span ℝ
        (Set.range (fun ij : Fin 5 × Fin 5 => E ij.1 ij.2))) ≤
        (Set.range (fun ij : Fin 5 × Fin 5 => E ij.1 ij.2)).toFinset.card :=
      finrank_span_le_card _
    _ = (Finset.univ.image (fun ij : Fin 5 × Fin 5 => E ij.1 ij.2)).card := by
      rw [Set.toFinset_range]
    _ ≤ (Finset.univ : Finset (Fin 5 × Fin 5)).card := Finset.card_image_le
    _ = 25 := by simp

end InfoGeometry.Canonical.Cl55WittLieRouting
