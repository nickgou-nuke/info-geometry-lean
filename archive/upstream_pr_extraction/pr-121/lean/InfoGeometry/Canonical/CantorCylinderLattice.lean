import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.RingTheory.Idempotents
import InfoGeometry.Meta.Architecture

/-!
# Cantor Cylinder Lattice

The finite Boolean lattice of Cantor cylinder sets at level `n`.

At each finite approximation level `n`, the Cantor space `{0,1}^ℕ` is partitioned
into `2ⁿ` clopen cylinder sets indexed by binary words `w ∈ {0,1}^n`.

The cylinder indicators `e_{n,w} = χ_{U_{n,w}}` are central idempotents in the
commutative algebra `C(𝒞)`. At fixed level `n`, they form a finite Boolean
lattice with:

  - `e_{n,w} ∧ e_{n,w'} = e_{n,w} · e_{n,w'}`   (product = meet for central idempotents)
  - `e_{n,w} ∨ e_{n,w'} = e_{n,w} + e_{n,w'} - e_{n,w} · e_{n,w'}`
  - Refinement: `e_{n,w} = e_{n+1,w0} ∨ e_{n+1,w1}`

Every finite Boolean lattice is automatically a `CompleteLattice`.
-/

namespace InfoGeometry.Canonical.CantorCylinderLattice

/-! ## 1. Cantor cylinder type -/

/-- The set of all level-n cylinder sets is `Set (Fin n → Bool)`.

This inherits `BooleanAlgebra` from `Set.instBooleanAlgebra`. -/
example (n : ℕ) : BooleanAlgebra (Set (Fin n → Bool)) := inferInstance

/-- The set of all level-n cylinder sets is a `CompleteLattice`. -/
example (n : ℕ) : CompleteLattice (Set (Fin n → Bool)) := inferInstance

/-! ## 2. Singleton cylinders as atoms -/

/-- The singleton cylinder set for a given binary word. -/
def cylinder (n : ℕ) (w : Fin n → Bool) : Set (Fin n → Bool) := {w}

/-- Two distinct words give disjoint cylinders. -/
theorem cylinder_disjoint {n : ℕ} {w w' : Fin n → Bool}
    (h : w ≠ w') :
    cylinder n w ⊓ cylinder n w' = ⊥ := by
  simp only [cylinder, Set.bot_eq_empty]
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  exact fun ⟨h1, h2⟩ => h (h1 ▸ h2)

/-- The union of all singleton cylinders at level n is the full set. -/
theorem cylinder_iSup_eq_top (n : ℕ) :
    ⨆ w : Fin n → Bool, cylinder n w = ⊤ := by
  ext x
  simp [cylinder, Set.mem_iUnion]

/-! ## 3. Refinement: parent-child relationship -/

/-- Extend a word of length `n` to length `n+1` by appending a bit. -/
def extendWord {n : ℕ} (w : Fin n → Bool) (b : Bool) : (Fin (n + 1) → Bool) :=
  Fin.snoc w b

/-- The left child word (appending `false`). -/
def leftChild {n : ℕ} (w : Fin n → Bool) : (Fin (n + 1) → Bool) :=
  extendWord w false

/-- The right child word (appending `true`). -/
def rightChild {n : ℕ} (w : Fin n → Bool) : (Fin (n + 1) → Bool) :=
  extendWord w true

/-- A level-(n+1) word restricts to a level-n word by dropping the last bit. -/
def truncateWord {n : ℕ} (w : (Fin (n + 1) → Bool)) : Fin n → Bool :=
  Fin.init w

@[simp] theorem truncateWord_leftChild {n : ℕ} (w : Fin n → Bool) :
    truncateWord (leftChild w) = w := by
  simp [truncateWord, leftChild, extendWord]

@[simp] theorem truncateWord_rightChild {n : ℕ} (w : Fin n → Bool) :
    truncateWord (rightChild w) = w := by
  simp [truncateWord, rightChild, extendWord]

theorem leftChild_injective {n : ℕ} :
    Function.Injective (@leftChild n) := by
  intro w₁ w₂ h
  have htrunc := congrArg truncateWord h
  simpa using htrunc

theorem rightChild_injective {n : ℕ} :
    Function.Injective (@rightChild n) := by
  intro w₁ w₂ h
  have htrunc := congrArg truncateWord h
  simpa using htrunc

@[simp] theorem leftChild_ne_rightChild {n : ℕ} (w₁ w₂ : Fin n → Bool) :
    leftChild w₁ ≠ rightChild w₂ := by
  intro h
  have hlast := congrFun h (Fin.last n)
  simp [leftChild, rightChild, extendWord] at hlast

@[simp] theorem rightChild_ne_leftChild {n : ℕ} (w₁ w₂ : Fin n → Bool) :
    rightChild w₁ ≠ leftChild w₂ := by
  intro h
  exact leftChild_ne_rightChild w₂ w₁ h.symm

/-- The parent cylinder is the union of its two children.

This is the fundamental refinement identity:
  `e_{n,w} = e_{n+1,w0} ∨ e_{n+1,w1}` -/
theorem cylinder_refinement {n : ℕ} (w : Fin n → Bool) :
    cylinder (n + 1) (leftChild w) ⊔ cylinder (n + 1) (rightChild w)
      = {v : (Fin (n + 1) → Bool) | truncateWord v = w} := by
  ext v
  constructor
  · intro hv
    rcases hv with hv | hv
    · simp [cylinder, leftChild, extendWord, truncateWord] at hv ⊢
      rw [hv]
      simp
    · simp [cylinder, rightChild, extendWord, truncateWord] at hv ⊢
      rw [hv]
      simp
  · intro hv
    simp only [Set.mem_setOf_eq, truncateWord] at hv
    have hsnoc : v = Fin.snoc (Fin.init v) (v (Fin.last n)) :=
      (Fin.snoc_init_self v).symm
    cases hlast : v (Fin.last n)
    · left
      simp [cylinder, leftChild, extendWord]
      rw [hsnoc, hv, hlast]
    · right
      simp [cylinder, rightChild, extendWord]
      rw [hsnoc, hv, hlast]

/-! ## 4. Level-n partition -/

/-- The level-n partition: the set of all singleton cylinders at level n. -/
def levelPartition (n : ℕ) : Set (Set (Fin n → Bool)) :=
  Set.range (cylinder n)

theorem cylinder_injective {n : ℕ} :
    Function.Injective (@cylinder n) := by
  intro w v h
  simpa [cylinder] using h

theorem levelPartition_natCard (n : ℕ) :
    Nat.card (levelPartition n) = 2 ^ n := by
  change Nat.card (Set.range (cylinder n)) = 2 ^ n
  rw [← Nat.card_congr
    (Equiv.ofInjective (cylinder n) (cylinder_injective (n := n)))]
  simp

/-- Every word belongs to exactly one cylinder in the partition. -/
theorem mem_unique_cylinder {n : ℕ} (v : Fin n → Bool) :
    ∃! w : Fin n → Bool, v ∈ cylinder n w := by
  exact ⟨v, rfl, fun w hw => hw.symm⟩

/-! ## 5. Idempotence of cylinder indicators -/

/-- Cylinder sets are idempotent under intersection (meet).

For central idempotents in a commutative algebra, `e² = e` translates to
`e ∩ e = e` in the set-lattice model. -/
theorem cylinder_idempotent {n : ℕ} (w : Fin n → Bool) :
    cylinder n w ⊓ cylinder n w = cylinder n w := by
  simp [cylinder]

/-- Complementarity: the complement of a cylinder is the union of all other cylinders. -/
theorem cylinder_compl {n : ℕ} (w : Fin n → Bool) :
    (cylinder n w)ᶜ = {v : Fin n → Bool | v ≠ w} := by
  ext v
  simp [cylinder]

/-! ## 6. Characteristic idempotents in the finite function algebra -/

/-- Characteristic function of a finite cylinder-sector set. -/
noncomputable def setIndicator (R : Type*) [Zero R] [One R] {n : ℕ}
    (S : Set (Fin n → Bool)) : (Fin n → Bool) → R := by
  classical
  exact fun v => if v ∈ S then 1 else 0

@[simp] theorem setIndicator_apply_mem {R : Type*} [Zero R] [One R]
    {n : ℕ} {S : Set (Fin n → Bool)} {v : Fin n → Bool} (hv : v ∈ S) :
    setIndicator R S v = 1 := by
  simp [setIndicator, hv]

@[simp] theorem setIndicator_apply_not_mem {R : Type*} [Zero R] [One R]
    {n : ℕ} {S : Set (Fin n → Bool)} {v : Fin n → Bool} (hv : v ∉ S) :
    setIndicator R S v = 0 := by
  simp [setIndicator, hv]

/-- Characteristic functions of finite sector sets are idempotents. -/
theorem setIndicator_idempotent {R : Type*} [MonoidWithZero R]
    {n : ℕ} (S : Set (Fin n → Bool)) :
    IsIdempotentElem (setIndicator R S) := by
  rw [IsIdempotentElem]
  funext v
  by_cases hv : v ∈ S <;> simp [setIndicator, hv]

/-- Meet of finite sector sets maps to multiplication of characteristic idempotents. -/
theorem setIndicator_inf_eq_mul {R : Type*} [MonoidWithZero R]
    {n : ℕ} (S T : Set (Fin n → Bool)) :
    setIndicator R (S ⊓ T) = setIndicator R S * setIndicator R T := by
  funext v
  by_cases hS : v ∈ S <;> by_cases hT : v ∈ T <;> simp [setIndicator, hS, hT]

/-- Join of finite sector sets maps to the Boolean idempotent formula `e + f - e*f`. -/
theorem setIndicator_sup_eq_add_sub_mul {R : Type*} [Ring R]
    {n : ℕ} (S T : Set (Fin n → Bool)) :
    setIndicator R (S ⊔ T) =
      setIndicator R S + setIndicator R T - setIndicator R S * setIndicator R T := by
  funext v
  by_cases hS : v ∈ S <;> by_cases hT : v ∈ T <;> simp [setIndicator, hS, hT]

/-- Complement of a finite sector set maps to `1 - e`. -/
theorem setIndicator_compl_eq_one_sub {R : Type*} [Ring R]
    {n : ℕ} (S : Set (Fin n → Bool)) :
    setIndicator R Sᶜ = 1 - setIndicator R S := by
  funext v
  by_cases hS : v ∈ S <;> simp [setIndicator, hS]

/-- Empty sector has zero characteristic idempotent. -/
@[simp] theorem setIndicator_empty {R : Type*} [Zero R] [One R]
    {n : ℕ} :
    setIndicator R (∅ : Set (Fin n → Bool)) = 0 := by
  funext v
  simp [setIndicator]

@[simp] theorem setIndicator_univ {R : Type*} [Zero R] [One R]
    {n : ℕ} :
    setIndicator R (Set.univ : Set (Fin n → Bool)) = 1 := by
  funext v
  simp [setIndicator]

/-- Disjoint sector sets have orthogonal characteristic idempotents. -/
theorem setIndicator_mul_eq_zero_of_inf_eq_bot {R : Type*} [MonoidWithZero R]
    {n : ℕ} {S T : Set (Fin n → Bool)} (h : S ⊓ T = ⊥) :
    setIndicator R S * setIndicator R T = 0 := by
  rw [← setIndicator_inf_eq_mul, h]
  simp

/-- Characteristic function of a singleton Cantor cylinder. -/
noncomputable def cylinderIndicator (R : Type*) [Zero R] [One R]
    {n : ℕ} (w : Fin n → Bool) : (Fin n → Bool) → R :=
  setIndicator R (cylinder n w)

theorem sum_cylinderIndicator_eq_one {R : Type*} [Ring R]
    {n : ℕ} :
    (∑ w : Fin n → Bool, cylinderIndicator R w) = 1 := by
  classical
  funext v
  simp [cylinderIndicator, setIndicator, cylinder]

/-- Cylinder characteristic functions are idempotents in the finite function algebra. -/
theorem cylinderIndicator_idempotent {R : Type*} [MonoidWithZero R]
    {n : ℕ} (w : Fin n → Bool) :
    IsIdempotentElem (cylinderIndicator R w) :=
  setIndicator_idempotent (R := R) (cylinder n w)

/-- Distinct Cantor cylinder idempotents are orthogonal. -/
theorem cylinderIndicator_mul_eq_zero_of_ne {R : Type*} [MonoidWithZero R]
    {n : ℕ} {w w' : Fin n → Bool} (h : w ≠ w') :
    cylinderIndicator R w * cylinderIndicator R w' = 0 := by
  exact setIndicator_mul_eq_zero_of_inf_eq_bot (R := R) (cylinder_disjoint h)

/-- Algebraic characteristic-function form of the Cantor refinement rule. -/
theorem cylinderIndicator_refinement {R : Type*} [Ring R]
    {n : ℕ} (w : Fin n → Bool) :
    setIndicator R ({v : (Fin (n + 1) → Bool) | truncateWord v = w}) =
      cylinderIndicator R (leftChild w) + cylinderIndicator R (rightChild w) := by
  have hchildren :
      cylinder (n + 1) (leftChild w) ⊓ cylinder (n + 1) (rightChild w) = ⊥ := by
    apply cylinder_disjoint
    intro h
    have hlast := congr_fun h (Fin.last n)
    simp [leftChild, rightChild, extendWord] at hlast
  calc
    setIndicator R ({v : (Fin (n + 1) → Bool) | truncateWord v = w})
        = setIndicator R
            (cylinder (n + 1) (leftChild w) ⊔ cylinder (n + 1) (rightChild w)) := by
          rw [cylinder_refinement]
    _ = setIndicator R (cylinder (n + 1) (leftChild w)) +
          setIndicator R (cylinder (n + 1) (rightChild w)) -
          setIndicator R (cylinder (n + 1) (leftChild w)) *
            setIndicator R (cylinder (n + 1) (rightChild w)) := by
          rw [setIndicator_sup_eq_add_sub_mul]
    _ = cylinderIndicator R (leftChild w) + cylinderIndicator R (rightChild w) := by
          rw [setIndicator_mul_eq_zero_of_inf_eq_bot (R := R) hchildren]
          simp [cylinderIndicator]

/- The two refined cylinder indicators form an orthogonal decomposition. -/
theorem cylinderIndicator_refinement_orthogonal_decomposition
    {R : Type*} [Ring R]
    {n : ℕ} (w : Fin n → Bool) :
    let left := cylinderIndicator R (leftChild w)
    let right := cylinderIndicator R (rightChild w)
    left * right = 0 ∧ right * left = 0 ∧
      setIndicator R {v : (Fin (n + 1) → Bool) | truncateWord v = w} =
        left + right := by
  dsimp
  have hne : leftChild w ≠ rightChild w := by
    intro h
    have hlast := congr_fun h (Fin.last n)
    simp [leftChild, rightChild, extendWord] at hlast
  have hzero :
      cylinderIndicator R (leftChild w) *
          cylinderIndicator R (rightChild w) = 0 :=
    cylinderIndicator_mul_eq_zero_of_ne hne
  have hzero' :
      cylinderIndicator R (rightChild w) *
          cylinderIndicator R (leftChild w) = 0 := by
    exact cylinderIndicator_mul_eq_zero_of_ne (Ne.symm hne)
  exact ⟨hzero, hzero', cylinderIndicator_refinement w⟩

/-! ## 7. Completeness -/

/-- The cylinder lattice at level n is a complete Boolean algebra. -/
instance completeBoolAlgebra (n : ℕ) : CompleteBooleanAlgebra (Set (Fin n → Bool)) :=
  inferInstance

end InfoGeometry.Canonical.CantorCylinderLattice
