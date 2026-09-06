import Mathlib.Tactic
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Canonical.CelikKocakCantorOperators

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.JordanWignerCelikKocakBridgeNDepth

open InfoGeometry.Canonical.CelikKocakCantorOperators
open InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace
open InfoGeometry.Clifford.Cl11TensorTower

abbrev CantorOp (n : ℕ) := FunctionSpace n →ₗ[ℂ] FunctionSpace n

/-- Product of parity signs from all coordinates strictly before `k`. -/
def prefixSign {n : ℕ} (k : ℕ) (x : CantorAddress n) : ℂ :=
  (Finset.range k).prod fun i =>
    if h : i < n then (if x ⟨i, h⟩ then (-1 : ℂ) else 1) else 1

/-- Jordan--Wigner chiral string on finite Cantor endpoint functions. -/
def cantorChiralString (n : ℕ) (k : Fin n) : CantorOp n where
  toFun f := fun x => prefixSign k.val x * f x
  map_add' := by
    intro f g
    ext x
    simp [mul_add]
  map_smul' := by
    intro c f
    ext x
    change prefixSign k.val x * (c * f x) = c * (prefixSign k.val x * f x)
    ring

/-- N-depth Cantor creation operator. -/
def cantorCreation (n : ℕ) (k : Fin n) : CantorOp n where
  toFun f := fun x => prefixSign k.val x * if x k then 0 else f (CantorAddress.flipAt k x)
  map_add' := by
    intro f g
    ext x
    by_cases hx : x k <;> simp [hx, mul_add]
  map_smul' := by
    intro c f
    ext x
    by_cases hx : x k
    · simp [hx]
    · simp [hx]
      ring

/-- N-depth Cantor annihilation operator. -/
def cantorAnnihilation (n : ℕ) (k : Fin n) : CantorOp n where
  toFun f := fun x => prefixSign k.val x * if x k then f (CantorAddress.flipAt k x) else 0
  map_add' := by
    intro f g
    ext x
    by_cases hx : x k <;> simp [hx, mul_add]
  map_smul' := by
    intro c f
    ext x
    by_cases hx : x k
    · simp [hx]
      ring
    · simp [hx]

@[simp] theorem cantorChiralString_apply {n : ℕ} (k : Fin n)
    (f : FunctionSpace n) (x : CantorAddress n) :
    cantorChiralString n k f x = prefixSign k.val x * f x :=
  rfl

@[simp] theorem cantorCreation_apply {n : ℕ} (k : Fin n)
    (f : FunctionSpace n) (x : CantorAddress n) :
    cantorCreation n k f x =
      prefixSign k.val x * if x k then 0 else f (CantorAddress.flipAt k x) :=
  rfl

@[simp] theorem cantorAnnihilation_apply {n : ℕ} (k : Fin n)
    (f : FunctionSpace n) (x : CantorAddress n) :
    cantorAnnihilation n k f x =
      prefixSign k.val x * if x k then f (CantorAddress.flipAt k x) else 0 :=
  rfl

/-- The parity string is unchanged by flipping the local site `k`. -/
theorem prefixSign_flipAt_same {n : ℕ} (k : Fin n) (x : CantorAddress n) :
    prefixSign k.val (CantorAddress.flipAt k x) = prefixSign k.val x := by
  unfold prefixSign
  refine Finset.prod_congr rfl ?_
  intro i hi
  have hik : i < k.val := by simpa using hi
  by_cases hin : i < n
  · have hne : (⟨i, hin⟩ : Fin n) ≠ k := by
      intro h
      exact Nat.ne_of_lt hik (congrArg Fin.val h)
    simp [hin, CantorAddress.flipAt_apply_ne hne]
  · simp [hin]

/-- The parity string squares to one. -/
theorem prefixSign_sq {n : ℕ} (k : ℕ) (x : CantorAddress n) :
    prefixSign k x * prefixSign k x = 1 := by
  unfold prefixSign
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one ?_
  intro i hi
  by_cases hin : i < n
  · by_cases hx : x ⟨i, hin⟩ <;> simp [hin, hx]
  · simp [hin]

/-- Creation is nilpotent. -/
theorem cantorCreation_sq_zero (n : ℕ) (k : Fin n) :
    cantorCreation n k * cantorCreation n k = 0 := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x k
  · simp [cantorCreation_apply, hx]
  · simp [cantorCreation_apply, hx]

/-- Annihilation is nilpotent. -/
theorem cantorAnnihilation_sq_zero (n : ℕ) (k : Fin n) :
    cantorAnnihilation n k * cantorAnnihilation n k = 0 := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x k
  · simp [cantorAnnihilation_apply, hx]
  · simp [cantorAnnihilation_apply, hx]

/-- Same-site CAR anticommutator on finite Cantor functions. -/
theorem cantorAnnihilation_creation_anticomm_self (n : ℕ) (k : Fin n) :
    cantorAnnihilation n k * cantorCreation n k +
      cantorCreation n k * cantorAnnihilation n k = 1 := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x k
  · have hsgn := prefixSign_flipAt_same k x
    have hsq := prefixSign_sq k.val x
    have hinv : f (CantorAddress.flipAt k (CantorAddress.flipAt k x)) = f x := by
      simpa using congrArg f (CantorAddress.flipAt_involutive k x)
    simp [cantorCreation_apply, cantorAnnihilation_apply, hx, hsgn, hinv]
    calc
      prefixSign k.val x * (prefixSign k.val x * f x)
          = (prefixSign k.val x * prefixSign k.val x) * f x := by ring
      _ = f x := by simp [hsq]
  · have hsgn := prefixSign_flipAt_same k x
    have hsq := prefixSign_sq k.val x
    have hinv : f (CantorAddress.flipAt k (CantorAddress.flipAt k x)) = f x := by
      simpa using congrArg f (CantorAddress.flipAt_involutive k x)
    simp [cantorCreation_apply, cantorAnnihilation_apply, hx, hsgn, hinv]
    calc
      prefixSign k.val x * (prefixSign k.val x * f x)
          = (prefixSign k.val x * prefixSign k.val x) * f x := by ring
      _ = f x := by simp [hsq]

/-- Depth-`n` theorem: the Cantor-side images satisfy nilpotency and same-site CAR. -/
theorem canonical_depth_n_car_wire (n : ℕ) (k : Fin n) :
    cantorCreation n k * cantorCreation n k = 0 ∧
    cantorAnnihilation n k * cantorAnnihilation n k = 0 ∧
    cantorAnnihilation n k * cantorCreation n k +
      cantorCreation n k * cantorAnnihilation n k = 1 := by
  exact ⟨cantorCreation_sq_zero n k,
    cantorAnnihilation_sq_zero n k,
    cantorAnnihilation_creation_anticomm_self n k⟩

/-- Matrix-side source creation strings preserve a fixed site under tower embedding. -/
theorem matrix_jwCreation_stable {n : ℕ} (k : Fin n) :
    matStageEmbed n (jwCreation n k) = jwCreation (n + 1) k.castSucc :=
  matStageEmbed_jwCreation (n := n) k

/-- Matrix-side source annihilation strings preserve a fixed site under tower embedding. -/
theorem matrix_jwAnnihilation_stable {n : ℕ} (k : Fin n) :
    matStageEmbed n (jwAnnihilation n k) = jwAnnihilation (n + 1) k.castSucc :=
  matStageEmbed_jwAnnihilation (n := n) k

end InfoGeometry.Canonical.JordanWignerCelikKocakBridgeNDepth
