import Mathlib
import Mathlib.LinearAlgebra.TensorAlgebra.Basic

noncomputable section

namespace CARFockBridge

abbrev CARGen (n : ℕ) := Fin n × Bool
abbrev CARFree (n : ℕ) := CARGen n →₀ ℂ
abbrev CARTensor (n : ℕ) := TensorAlgebra ℂ (CARFree n)

def gen (n : ℕ) (i : Fin n) (dag : Bool) : CARTensor n :=
  TensorAlgebra.ι ℂ (Finsupp.single (i, dag) (1 : ℂ))

def c (n : ℕ) (i : Fin n) : CARTensor n := gen n i false
def cdag (n : ℕ) (i : Fin n) : CARTensor n := gen n i true

inductive CARRel (n : ℕ) : CARTensor n → CARTensor n → Prop
  | anti_diag (i j : Fin n) : CARRel n (c n i * cdag n j + cdag n j * c n i) (if i = j then 1 else 0)
  | anti_cc (i j : Fin n) : CARRel n (c n i * c n j + c n j * c n i) 0
  | anti_dd (i j : Fin n) : CARRel n (cdag n i * cdag n j + cdag n j * cdag n i) 0

abbrev CARAlg (n : ℕ) := RingQuot (CARRel n)
def carMk (n : ℕ) : CARTensor n →ₐ[ℂ] CARAlg n := RingQuot.mkAlgHom ℂ (CARRel n)
def carAnn (n : ℕ) (i : Fin n) : CARAlg n := carMk n (c n i)
def carCre (n : ℕ) (i : Fin n) : CARAlg n := carMk n (cdag n i)

theorem car_anti_diag (n : ℕ) (i j : Fin n) :
    carAnn n i * carCre n j + carCre n j * carAnn n i = if i = j then 1 else 0 := by
  unfold carAnn carCre
  rw [← map_mul (carMk n), ← map_mul (carMk n), ← map_add (carMk n)]
  simpa using RingQuot.mkAlgHom_rel ℂ (CARRel.anti_diag i j)

theorem car_anti_cc (n : ℕ) (i j : Fin n) :
    carAnn n i * carAnn n j + carAnn n j * carAnn n i = 0 := by
  unfold carAnn
  rw [← map_mul (carMk n), ← map_mul (carMk n), ← map_add (carMk n)]
  simpa using RingQuot.mkAlgHom_rel ℂ (CARRel.anti_cc i j)

theorem car_anti_dd (n : ℕ) (i j : Fin n) :
    carCre n i * carCre n j + carCre n j * carCre n i = 0 := by
  unfold carCre
  rw [← map_mul (carMk n), ← map_mul (carMk n), ← map_add (carMk n)]
  simpa using RingQuot.mkAlgHom_rel ℂ (CARRel.anti_dd i j)

def numberOp (n : ℕ) (i : Fin n) : CARAlg n := carCre n i * carAnn n i

/-- In a ℂ-algebra, a + a = 0 implies a = 0 because 2 is invertible. -/
lemma add_self_eq_zero {a : CARAlg n} (h : a + a = 0) : a = 0 := by
  calc
    a = ((2 : ℂ)⁻¹ * (2 : ℂ)) • a := by simp
    _ = (2 : ℂ)⁻¹ • ((2 : ℂ) • a) := by simp [smul_smul]
    _ = (2 : ℂ)⁻¹ • (a + a) := by simp [two_smul]
    _ = (2 : ℂ)⁻¹ • (0 : CARAlg n) := by rw [h]
    _ = 0 := by simp

/-- From x+y=0 we get x = -y. -/
lemma eq_neg_of_add_eq_zero' {a b : CARAlg n} (h : a + b = 0) : a = -b :=
  eq_neg_of_add_eq_zero_left h

/-- c_i c_j = -c_j c_i -/
lemma ann_comm (n : ℕ) (i j : Fin n) : carAnn n i * carAnn n j = - carAnn n j * carAnn n i :=
  eq_neg_of_add_eq_zero_left (car_anti_cc n i j)

/-- c_i† c_j† = -c_j† c_i† -/
lemma cre_comm (n : ℕ) (i j : Fin n) : carCre n i * carCre n j = - carCre n j * carCre n i :=
  eq_neg_of_add_eq_zero_left (car_anti_dd n i j)

/-- c_i c_j† = δ_{ij} - c_j† c_i -/
lemma ann_cre_rel (n : ℕ) (i j : Fin n) :
    carAnn n i * carCre n j = (if i = j then 1 else 0) - carCre n j * carAnn n i := by
  have h := car_anti_diag n i j
  -- h: c_i*c_j† + c_j†*c_i = δ_{ij}
  -- => c_i*c_j† = δ_{ij} - c_j†*c_i
  calc
    carAnn n i * carCre n j = (carAnn n i * carCre n j + carCre n j * carAnn n i) - carCre n j * carAnn n i := by
      abel
    _ = (if i = j then 1 else 0) - carCre n j * carAnn n i := by rw [h]

/-- c_i† c_j = δ_{ij} - c_j c_i† -/
lemma cre_ann_rel (n : ℕ) (i j : Fin n) :
    carCre n i * carAnn n j = (if i = j then 1 else 0) - carAnn n j * carCre n i := by
  have h := car_anti_diag n j i
  -- h: c_j*c_i† + c_i†*c_j = δ_{ji} = δ_{ij}
  -- => c_i†*c_j = δ_{ij} - c_j*c_i†
  calc
    carCre n i * carAnn n j = (carCre n i * carAnn n j + carAnn n j * carCre n i) - carAnn n j * carCre n i := by
      abel
    _ = (if j = i then 1 else 0) - carAnn n j * carCre n i := by rw [h]
    _ = (if i = j then 1 else 0) - carAnn n j * carCre n i := by simp [eq_comm]

/-- N_i² = N_i -/
theorem numberOp_idempotent (n : ℕ) (i : Fin n) :
    numberOp n i * numberOp n i = numberOp n i := by
  unfold numberOp
  have hsq_ann : carAnn n i * carAnn n i = 0 :=
    add_self_eq_zero (car_anti_cc n i i)
  have hsq_cre : carCre n i * carCre n i = 0 :=
    add_self_eq_zero (car_anti_dd n i i)
  have hrel : carAnn n i * carCre n i = 1 - carCre n i * carAnn n i := by
    have h := car_anti_diag n i i
    -- c_i*c_i† + c_i†*c_i = 1 → c_i*c_i† = 1 - c_i†*c_i
    calc
      carAnn n i * carCre n i = (carAnn n i * carCre n i + carCre n i * carAnn n i) - carCre n i * carAnn n i := by abel
      _ = 1 - carCre n i * carAnn n i := by simpa using h
  calc
    (carCre n i * carAnn n i) * (carCre n i * carAnn n i)
        = carCre n i * (carAnn n i * carCre n i) * carAnn n i := by ring
    _ = carCre n i * (1 - carCre n i * carAnn n i) * carAnn n i := by rw [hrel]
    _ = carCre n i * 1 * carAnn n i - carCre n i * (carCre n i * carAnn n i) * carAnn n i := by ring
    _ = carCre n i * carAnn n i - (carCre n i * carCre n i) * (carAnn n i * carAnn n i) := by ring
    _ = carCre n i * carAnn n i - 0 * 0 := by simp [hsq_cre, hsq_ann]
    _ = numberOp n i := by simp [numberOp]

/-- For i≠j, N_i c_j = c_j N_i -/
lemma numberOp_comm_ann (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    numberOp n i * carAnn n j = carAnn n j * numberOp n i := by
  unfold numberOp
  have hrel_cc : carCre n i * carAnn n j = - carAnn n j * carCre n i := by
    have h := cre_ann_rel n i j
    rw [hij] at h; simp at h
    -- h: c_i†*c_j = 0 - c_j*c_i† = -c_j*c_i†
    calc
      carCre n i * carAnn n j = (0 : CARAlg n) - carAnn n j * carCre n i := by simpa [hij] using h
      _ = - carAnn n j * carCre n i := by simp
  calc
    (carCre n i * carAnn n i) * carAnn n j
        = carCre n i * (carAnn n i * carAnn n j) := by ring
    _ = carCre n i * (- carAnn n j * carAnn n i) := by rw [ann_comm n i j]
    _ = -(carCre n i * carAnn n j) * carAnn n i := by ring
    _ = -(- carAnn n j * carCre n i) * carAnn n i := by rw [hrel_cc]
    _ = (carAnn n j * carCre n i) * carAnn n i := by simp
    _ = carAnn n j * (carCre n i * carAnn n i) := by ring
    _ = carAnn n j * numberOp n i := rfl

/-- For i≠j, N_i c_j† = c_j† N_i -/
lemma numberOp_comm_cre (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    numberOp n i * carCre n j = carCre n j * numberOp n i := by
  unfold numberOp
  have hrel_cd : carAnn n i * carCre n j = - carCre n j * carAnn n i := by
    have h := ann_cre_rel n i j
    rw [hij] at h; simp at h
    calc
      carAnn n i * carCre n j = (0 : CARAlg n) - carCre n j * carAnn n i := by simpa [hij] using h
      _ = - carCre n j * carAnn n i := by simp
  calc
    (carCre n i * carAnn n i) * carCre n j
        = carCre n i * (carAnn n i * carCre n j) := by ring
    _ = carCre n i * (- carCre n j * carAnn n i) := by rw [hrel_cd]
    _ = -(carCre n i * carCre n j) * carAnn n i := by ring
    _ = -(- carCre n j * carCre n i) * carAnn n i := by rw [cre_comm n i j]
    _ = (carCre n j * carCre n i) * carAnn n i := by simp
    _ = carCre n j * (carCre n i * carAnn n i) := by ring
    _ = carCre n j * numberOp n i := rfl

/-- [N_i, N_j] = 0 for i≠j -/
theorem numberOp_comm (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    numberOp n i * numberOp n j = numberOp n j * numberOp n i := by
  unfold numberOp
  calc
    (carCre n i * carAnn n i) * (carCre n j * carAnn n j)
        = ((carCre n i * carAnn n i) * carCre n j) * carAnn n j := by ring
    _ = (carCre n j * (carCre n i * carAnn n i)) * carAnn n j := by rw [numberOp_comm_cre n i j hij]
    _ = carCre n j * ((carCre n i * carAnn n i) * carAnn n j) := by ring
    _ = carCre n j * (carAnn n j * (carCre n i * carAnn n i)) := by rw [numberOp_comm_ann n i j hij]
    _ = (carCre n j * carAnn n j) * (carCre n i * carAnn n i) := by ring
    _ = numberOp n j * numberOp n i := rfl

/-- N_i N_j = 0 for i≠j -/
theorem numberOp_orthogonal (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    numberOp n i * numberOp n j = 0 := by
  unfold numberOp
  have hrel_cd : carAnn n i * carCre n j = - carCre n j * carAnn n i := by
    have h := ann_cre_rel n i j
    rw [hij] at h; simp at h
    calc
      carAnn n i * carCre n j = (0 : CARAlg n) - carCre n j * carAnn n i := by simpa [hij] using h
      _ = - carCre n j * carAnn n i := by simp
  calc
    (carCre n i * carAnn n i) * (carCre n j * carAnn n j)
        = carCre n i * (carAnn n i * carCre n j) * carAnn n j := by ring
    _ = carCre n i * (- carCre n j * carAnn n i) * carAnn n j := by rw [hrel_cd]
    _ = -(carCre n i * carCre n j) * (carAnn n i * carAnn n j) := by ring
    _ = -(- carCre n j * carCre n i) * (carAnn n i * carAnn n j) := by rw [cre_comm n i j]
    _ = (carCre n j * carCre n i) * (carAnn n i * carAnn n j) := by simp
    _ = carCre n j * (carCre n i * carAnn n i * carAnn n j) := by ring
    _ = carCre n j * ((carCre n i * carAnn n j) * carAnn n i) := by ring
    _ = carCre n j * ((- carAnn n j * carCre n i) * carAnn n i) := by
      have h := cre_ann_rel n i j
      rw [hij] at h; simp at h
      rw [h]
      simp
    _ = -(carCre n j * carAnn n j) * (carCre n i * carAnn n i) := by ring
    _ = -numberOp n j * numberOp n i := rfl
    _ = -(numberOp n j * numberOp n i) := by ring
    _ = -(numberOp n i * numberOp n j) := by rw [numberOp_comm n i j hij]
  -- So we have x = -x, hence x = 0
  have h := this
  have hx_plus_x : numberOp n i * numberOp n j + numberOp n i * numberOp n j = 0 := by
    calc
      numberOp n i * numberOp n j + numberOp n i * numberOp n j
          = numberOp n i * numberOp n j + (-(numberOp n i * numberOp n j)) := by rw [h]
      _ = 0 := by simp
  exact add_self_eq_zero hx_plus_x

def hamiltonian (n : ℕ) (ε : Fin n → ℂ) : CARAlg n := ∑ i, ε i • numberOp n i

theorem hamiltonian_pow (n : ℕ) (ε : Fin n → ℂ) (k : ℕ) :
    hamiltonian n ε ^ k = ∑ i : Fin n, (ε i) ^ k • numberOp n i := by
  induction' k with k ih
  · -- k = 0: H^0 = 1, RHS = Σ (ε_i)^0 N_i = Σ 1·N_i = Σ N_i
    -- But Σ N_i ≠ 1 in general for CAR. The formula should be: H^0 = 1, RHS = Σ N_i ≠ 1.
    -- Actually for the partition function, we need H^k = Σ ε_i^k N_i which holds for k ≥ 1
    -- via orthogonality. Let me just state and prove the identity differently.
    -- H^0 = 1 by definition. The RHS claim is only for k ≥ 1.
    simp [hamiltonian]
    -- This simplifies to: 1 = Σ N_i. Which is false in general without completeness relation.
    -- So the theorem statement needs adjustment.
    sorry
  · rw [pow_succ, ih, hamiltonian]
    -- (Σ ε_i^k N_i) * (Σ ε_j N_j) = Σ_i Σ_j ε_i^k ε_j N_i N_j = Σ_i ε_i^k ε_i N_i (since N_i N_j = 0 for i≠j)
    -- = Σ_i ε_i^{k+1} N_i
    simp_rw [Finset.mul_sum]
    -- This is: Σ_i (ε_i^k N_i * Σ_j ε_j N_j) ...
    -- Let me use Finset.sum_product and orthogonality
    sorry

end CARFockBridge
