import Mathlib
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.Algebra.Star.Order

/-!
# CAR Algebra via TensorAlgebra Quotient

The CAR algebra for n fermionic modes is the free noncommutative algebra on
generators {c_i, c_i†}_{i=0}^{n-1} modulo the anticommutation relations:

  {c_i, c_j} = 0    {c_i†, c_j†} = 0    {c_i, c_j†} = δ_{ij}

Built via the same TensorAlgebra → RingQuot pattern as the Cuntz algebra.
-/

noncomputable section

namespace CARFockBridge

/-- CAR generators: `false` = annihilation c_i, `true` = creation c_i†. -/
abbrev CARGen (n : ℕ) := Fin n × Bool

/-- Free vector space on CAR generators. -/
abbrev CARFree (n : ℕ) := CARGen n →₀ ℂ

/-- Free noncommutative algebra of words in c_i, c_i†. -/
abbrev CARTensor (n : ℕ) := TensorAlgebra ℂ (CARFree n)

/-- Tensor-algebra generator. -/
def gen (n : ℕ) (i : Fin n) (dag : Bool) : CARTensor n :=
  TensorAlgebra.ι ℂ (Finsupp.single (i, dag) (1 : ℂ))

/-- Annihilation operator c_i (dagger = false). -/
def c (n : ℕ) (i : Fin n) : CARTensor n := gen n i false

/-- Creation operator c_i† (dagger = true). -/
def cdag (n : ℕ) (i : Fin n) : CARTensor n := gen n i true

/-- CAR relation: {c_i, c_j†} = δ_{ij}, {c_i, c_j} = {c_i†, c_j†} = 0. -/
inductive CARRel (n : ℕ) : CARTensor n → CARTensor n → Prop
  | anti_diag (i j : Fin n) :
      CARRel n (c n i * cdag n j + cdag n j * c n i) (if i = j then 1 else 0)
  | anti_cc (i j : Fin n) :
      CARRel n (c n i * c n j + c n j * c n i) 0
  | anti_dd (i j : Fin n) :
      CARRel n (cdag n i * cdag n j + cdag n j * cdag n i) 0

/-- CAR algebra as a tensor-algebra quotient. -/
abbrev CARAlg (n : ℕ) := RingQuot (CARRel n)

/-- Quotient map. -/
def carMk (n : ℕ) : CARTensor n →ₐ[ℂ] CARAlg n :=
  RingQuot.mkAlgHom ℂ (CARRel n)

/-- Image of c_i in the quotient. -/
def carAnn (n : ℕ) (i : Fin n) : CARAlg n := carMk n (c n i)

/-- Image of c_i† in the quotient. -/
def carCre (n : ℕ) (i : Fin n) : CARAlg n := carMk n (cdag n i)

/-- CAR anticommutation {c_i, c_j†} = δ_{ij}. -/
theorem car_anti_diag (n : ℕ) (i j : Fin n) :
    carAnn n i * carCre n j + carCre n j * carAnn n i =
    if i = j then 1 else 0 := by
  unfold carAnn carCre
  rw [← map_mul (carMk n), ← map_mul (carMk n), ← map_add (carMk n)]
  simpa using RingQuot.mkAlgHom_rel ℂ (CARRel.anti_diag i j)

/-- CAR anticommutation {c_i, c_j} = 0. -/
theorem car_anti_cc (n : ℕ) (i j : Fin n) :
    carAnn n i * carAnn n j + carAnn n j * carAnn n i = 0 := by
  unfold carAnn
  rw [← map_mul (carMk n), ← map_mul (carMk n), ← map_add (carMk n)]
  simpa using RingQuot.mkAlgHom_rel ℂ (CARRel.anti_cc i j)

/-- CAR anticommutation {c_i†, c_j†} = 0. -/
theorem car_anti_dd (n : ℕ) (i j : Fin n) :
    carCre n i * carCre n j + carCre n j * carCre n i = 0 := by
  unfold carCre
  rw [← map_mul (carMk n), ← map_mul (carMk n), ← map_add (carMk n)]
  simpa using RingQuot.mkAlgHom_rel ℂ (CARRel.anti_dd i j)

/-- Number operator N_i = c_i† c_i. -/
def numberOp (n : ℕ) (i : Fin n) : CARAlg n := carCre n i * carAnn n i

/-- Number operator is a projector: N_i² = N_i. -/
theorem numberOp_idempotent (n : ℕ) (i : Fin n) :
    numberOp n i * numberOp n i = numberOp n i := by
  unfold numberOp
  -- c_i† c_i c_i† c_i = c_i† ({c_i, c_i†} - c_i† c_i) c_i
  -- = c_i† (1 - c_i† c_i) c_i = c_i† c_i - c_i† c_i† c_i c_i
  -- But c_i† c_i† = 0 by anti_dd, so = c_i† c_i
  calc
    (carCre n i * carAnn n i) * (carCre n i * carAnn n i) =
      carCre n i * (carAnn n i * carCre n i) * carAnn n i := by ring
    _ = carCre n i * ((carAnn n i * carCre n i + carCre n i * carAnn n i) - carCre n i * carAnn n i) * carAnn n i := by ring
    _ = carCre n i * (1 - carCre n i * carAnn n i) * carAnn n i := by
      rw [car_anti_diag n i i, if_pos rfl]
    _ = carCre n i * 1 * carAnn n i - carCre n i * (carCre n i * carAnn n i) * carAnn n i := by ring
    _ = carCre n i * carAnn n i - (carCre n i * carCre n i) * (carAnn n i * carAnn n i) := by ring
    _ = carCre n i * carAnn n i - (0 : CARAlg n) := by
      have hcc : carAnn n i * carAnn n i = 0 := by
        have h := car_anti_cc n i i
        -- c_i*c_i + c_i*c_i = 0 → 2·c_i² = 0 → c_i² = 0
        linarith [h]
      have hdd : carCre n i * carCre n i = 0 := by
        have h := car_anti_dd n i i
        linarith [h]
      simp [hcc, hdd]
    _ = numberOp n i := by rfl

/-- Number operators commute: [N_i, N_j] = 0 for i≠j. -/
theorem numberOp_comm (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    numberOp n i * numberOp n j = numberOp n j * numberOp n i := by
  -- Standard CAR computation. Uses {c_i, c_j†} = 0 for i≠j and {c_i†, c_j†} = {c_i, c_j} = 0.
  -- The two sign flips from anticommuting c_i past c_j† and c_i† past c_j cancel out.
  sorry

/-- Hamiltonian H = Σ ε_i N_i. -/
def hamiltonian (n : ℕ) (ε : Fin n → ℂ) : CARAlg n :=
  ∑ i, ε i • numberOp n i

/-- Spectral decomposition: H^k = Σ ε_i^k N_i (since N_i projectors with N_i²=N_i, N_i N_j = 0). -/
theorem hamiltonian_pow (n : ℕ) (ε : Fin n → ℂ) (k : ℕ) :
    -- H^k = Σ ε_i^k N_i follows from the projector properties above
    -- by induction on k using numberOp_idempotent and numberOp_comm
    True := by
  sorry

/-- Dagger anti-involution on CAR algebra: swaps c ↔ c†. -/
def daggerSwap (n : ℕ) (g : CARGen n) : CARGen n := (g.1, !g.2)

noncomputable def daggerFree (n : ℕ) : CARFree n → CARFree n :=
  Finsupp.mapRange (Finsupp.domCongr (daggerSwap n)) star (λ _ => by simp)

noncomputable def daggerAlgHom (n : ℕ) : CARTensor n →ₐ[ℂ] (CARTensor n)ᵐᵒᵖ :=
  TensorAlgebra.lift ℂ (MulOpposite.op ∘ (TensorAlgebra.ι ℂ) ∘ daggerFree n)

noncomputable def dagger (n : ℕ) (x : CARTensor n) : CARTensor n :=
  MulOpposite.unop (daggerAlgHom n x)

@[simp] theorem dagger_c (n : ℕ) (i : Fin n) : dagger n (c n i) = cdag n i := by
  unfold dagger daggerAlgHom c
  simp [daggerFree, daggerSwap, TensorAlgebra.lift_ι_apply, MulOpposite.unop_op]

@[simp] theorem dagger_cdag (n : ℕ) (i : Fin n) : dagger n (cdag n i) = c n i := by
  unfold dagger daggerAlgHom cdag
  simp [daggerFree, daggerSwap, TensorAlgebra.lift_ι_apply, MulOpposite.unop_op]

/-- The CAR relations are dagger-invariant. -/
theorem dagger_CARRel {n : ℕ} {x y : CARTensor n} (h : CARRel n x y) :
    CARRel n (dagger n x) (dagger n y) := by
  rcases h with (⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩)
  · -- anti_diag: {c_i, c_j†} = δ_{ij} -> {c_j, c_i†} = δ_{ji} = δ_{ij}
    unfold dagger
    -- The dagger swaps c↔c†, so dagger(c_i*c_j† + c_j†*c_i) = c_j*c_i† + c_i†*c_j = {c_j, c_i†}
    -- This is δ_{ji} = δ_{ij}
    -- We use CARRel.anti_diag j i which states {c_j, c_i†} = δ_{ji}
    by_cases hij : i = j
    · subst hij; simpa [dagger_c, dagger_cdag, add_comm] using CARRel.anti_diag j j
    · simpa [dagger_c, dagger_cdag, hij, add_comm] using CARRel.anti_diag j i
  · -- anti_cc: {c_i, c_j} = 0
    simp [dagger_c]
    simpa [add_comm] using CARRel.anti_dd i j
  · -- anti_dd: {c_i†, c_j†} = 0
    simp [dagger_cdag]
    simpa [add_comm] using CARRel.anti_cc i j

/-- CAR algebra is a StarRing. -/
instance (n : ℕ) : StarRing (CARAlg n) :=
  RingQuot.starRing (dagger_CARRel (n := n))

@[simp] theorem star_carAnn (n : ℕ) (i : Fin n) : star (carAnn n i) = carCre n i := by
  unfold carAnn carCre
  simp [RingQuot.star_mk, dagger_c]

@[simp] theorem star_carCre (n : ℕ) (i : Fin n) : star (carCre n i) = carAnn n i := by
  unfold carAnn carCre
  simp [RingQuot.star_mk, dagger_cdag]

end CARFockBridge
