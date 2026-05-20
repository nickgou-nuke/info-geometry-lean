import Mathlib

/-!
# InfoGeometry.Canonical.CelikKocakCantorOperators

Finite Cantor-address tilt/switch operators for the Çelik--Koçak construction.

This file formalizes the operator identities from Section 2 of the paper:

* finite Cantor addresses `V_n ≃ Fin n → Bool`,
* tilt operators `T_j`,
* switch operators `S_j`,
* involutivity and commutation/anticommutation laws.

The implementation is theorem-backed only.
-/

noncomputable section

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.CelikKocakCantorOperators

/-- Binary addresses of depth `n`. -/
abbrev CantorAddress (n : ℕ) := Fin n → Bool

/-- Complex-valued functions on the finite endpoint set `V_n`. -/
abbrev FunctionSpace (n : ℕ) := CantorAddress n → ℂ

namespace CantorAddress

variable {n : ℕ}

/-- Flip the bit at address slot `j`. -/
def flipAt (j : Fin n) (x : CantorAddress n) : CantorAddress n :=
  fun k => if k = j then ! (x k) else x k

@[simp] theorem flipAt_apply_eq (j : Fin n) (x : CantorAddress n) :
    flipAt j x j = ! (x j) := by
  simp [flipAt]

@[simp] theorem flipAt_apply_ne {j k : Fin n} (h : k ≠ j) (x : CantorAddress n) :
    flipAt j x k = x k := by
  simp [flipAt, h]

theorem flipAt_involutive (j : Fin n) (x : CantorAddress n) :
    flipAt j (flipAt j x) = x := by
  funext k
  by_cases hk : k = j <;> simp [flipAt, hk, Bool.not_not]

theorem flipAt_comm {i j : Fin n} (hij : i ≠ j) (x : CantorAddress n) :
    flipAt i (flipAt j x) = flipAt j (flipAt i x) := by
  funext k
  by_cases hk_i : k = i
  · rw [hk_i]
    by_cases hk_j : i = j
    · exact False.elim (hij hk_j)
    · simp [flipAt, hk_j]
  · by_cases hk_j : k = j
    · have hji : j ≠ i := by intro h; exact hij h.symm
      have hji' : ¬ j = i := hji
      simp [flipAt, hk_i, hk_j, hji']
    · simp [flipAt, hk_i, hk_j]

end CantorAddress

namespace FunctionSpace

variable {n : ℕ}

open CantorAddress

/-- Tilt operator `T_j`: sign on the `j`-th address sector. -/
def tilt (j : Fin n) : FunctionSpace n →ₗ[ℂ] FunctionSpace n where
  toFun f := fun x => if x j then -f x else f x
  map_add' := by
    intro f g
    ext x
    by_cases hx : x j <;> simp [hx, add_comm, add_left_comm, add_assoc]
  map_smul' := by
    intro c f
    ext x
    by_cases hx : x j <;> simp [hx]

/-- Switch operator `S_j`: flip the `j`-th address bit. -/
def switch (j : Fin n) : FunctionSpace n →ₗ[ℂ] FunctionSpace n where
  toFun f := fun x => f (CantorAddress.flipAt j x)
  map_add' := by
    intro f g
    ext x
    rfl
  map_smul' := by
    intro c f
    ext x
    rfl

@[simp] theorem tilt_apply (j : Fin n) (f : FunctionSpace n) (x : CantorAddress n) :
    tilt j f x = if x j then -f x else f x :=
  rfl

@[simp] theorem switch_apply (j : Fin n) (f : FunctionSpace n) (x : CantorAddress n) :
    switch j f x = f (CantorAddress.flipAt j x) :=
  rfl

/-- Tilt squares to the identity. -/
theorem tilt_sq (j : Fin n) :
    (tilt (n := n) j) * (tilt (n := n) j) = 1 := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;> simp [FunctionSpace.tilt, hx]

/-- Switch squares to the identity. -/
theorem switch_sq (j : Fin n) :
    (switch (n := n) j) * (switch (n := n) j) = 1 := by
  apply LinearMap.ext
  intro f
  ext x
  change f (CantorAddress.flipAt j (CantorAddress.flipAt j x)) = f x
  simpa using congrArg f (CantorAddress.flipAt_involutive j x)

/-- Tilt operators commute at distinct slots. -/
theorem tilt_comm {i j : Fin n} :
    (tilt (n := n) i) * (tilt (n := n) j)
      = (tilt (n := n) j) * (tilt (n := n) i) := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hxi : x i <;> by_cases hxj : x j <;> simp [FunctionSpace.tilt, hxi, hxj]

/-- Switch operators commute at distinct slots. -/
theorem switch_comm {i j : Fin n} (hij : i ≠ j) :
    (switch (n := n) i) * (switch (n := n) j)
      = (switch (n := n) j) * (switch (n := n) i) := by
  apply LinearMap.ext
  intro f
  ext x
  simp [FunctionSpace.switch, CantorAddress.flipAt_comm hij]

/-- Tilt and switch commute at different slots. -/
theorem tilt_switch_comm_of_ne {i j : Fin n} (hij : i ≠ j) :
    (tilt (n := n) i) * (switch (n := n) j)
      = (switch (n := n) j) * (tilt (n := n) i) := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hxi : x i <;> simp [FunctionSpace.tilt, FunctionSpace.switch,
    CantorAddress.flipAt_apply_ne hij, hxi]

/-- Tilt and switch anticommute at the same slot. -/
theorem tilt_switch_anticomm (j : Fin n) :
    (tilt (n := n) j) * (switch (n := n) j)
      = - ((switch (n := n) j) * (tilt (n := n) j)) := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;> simp [FunctionSpace.tilt, FunctionSpace.switch,
    CantorAddress.flipAt, hx]

/--
The theorem-backed finite Cantor tilt/switch system.

This is the exact algebraic core needed for the Çelik--Koçak finite
representation theorem.
-/
structure TiltSwitchSystem where
  T : Fin n → FunctionSpace n →ₗ[ℂ] FunctionSpace n
  S : Fin n → FunctionSpace n →ₗ[ℂ] FunctionSpace n
  T_sq : ∀ j, T j * T j = 1
  S_sq : ∀ j, S j * S j = 1
  T_comm : ∀ i j, T i * T j = T j * T i
  S_comm : ∀ i j, S i * S j = S j * S i
  T_S_comm_ne : ∀ i j, i ≠ j → T i * S j = S j * T i
  T_S_anticomm : ∀ j, T j * S j = - (S j * T j)

/-- Canonical tilt/switch system on finite Cantor endpoint functions. -/
def canonicalTiltSwitchSystem : TiltSwitchSystem (n := n) where
  T := tilt (n := n)
  S := switch (n := n)
  T_sq := tilt_sq (n := n)
  S_sq := switch_sq (n := n)
  T_comm := by
    intro i j
    exact tilt_comm (n := n) (i := i) (j := j)
  S_comm := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp [mul_comm]
    · exact switch_comm (n := n) hij
  T_S_comm_ne := by
    intro i j hij
    exact tilt_switch_comm_of_ne (n := n) hij
  T_S_anticomm := by
    intro j
    exact tilt_switch_anticomm (n := n) j

end FunctionSpace

/-- The canonical basis of the finite endpoint function space. -/
noncomputable def endpointBasis (n : ℕ) :
    Module.Basis (CantorAddress n) ℂ (FunctionSpace n) :=
  Pi.basisFun ℂ (CantorAddress n)

@[simp] theorem endpointBasis_apply (n : ℕ) (x : CantorAddress n) :
    endpointBasis (n := n) x = Pi.single x (1 : ℂ) := by
  simpa [endpointBasis] using (Pi.basisFun_apply (R := ℂ) (η := CantorAddress n) x)

theorem endpointBasis_repr_apply (n : ℕ) (f : FunctionSpace n) (x : CantorAddress n) :
    (endpointBasis (n := n)).repr f x = f x := by
  simpa [endpointBasis] using (Pi.basisFun_repr (R := ℂ) (η := CantorAddress n) f x)

namespace FunctionSpace

variable {n : ℕ}

/-- The local pair product `T_j * S_j`, used in the recursive Cantor/Clifford strings. -/
def pairTerm (j : ℕ) : FunctionSpace n →ₗ[ℂ] FunctionSpace n :=
  if hj : j < n then tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩ else 1

@[simp] theorem pairTerm_of_lt {j : ℕ} (hj : j < n) :
    pairTerm (n := n) j = tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩ := by
  simp [pairTerm, hj]

@[simp] theorem pairTerm_of_not_lt {j : ℕ} (hj : ¬ j < n) :
    pairTerm (n := n) j = 1 := by
  simp [pairTerm, hj]

theorem pairTerm_sq {j : ℕ} (hj : j < n) :
    pairTerm (n := n) j * pairTerm (n := n) j = - (1 : FunctionSpace n →ₗ[ℂ] FunctionSpace n) := by
  rw [pairTerm_of_lt (n := n) hj]
  calc
    (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩)
        * (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩)
      = (-(switch (n := n) ⟨j, hj⟩ * tilt (n := n) ⟨j, hj⟩))
          * (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩) := by
              rw [tilt_switch_anticomm (n := n) ⟨j, hj⟩]
    _ = - ((switch (n := n) ⟨j, hj⟩ * tilt (n := n) ⟨j, hj⟩)
          * (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩)) := by
              exact neg_mul (switch (n := n) ⟨j, hj⟩ * tilt (n := n) ⟨j, hj⟩)
                (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩)
    _ = - (switch (n := n) ⟨j, hj⟩ * ((tilt (n := n) ⟨j, hj⟩ * tilt (n := n) ⟨j, hj⟩)
            * switch (n := n) ⟨j, hj⟩)) := by
              exact congrArg Neg.neg (by
                calc
                  (switch (n := n) ⟨j, hj⟩ * tilt (n := n) ⟨j, hj⟩)
                      * (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩)
                    = switch (n := n) ⟨j, hj⟩
                        * (tilt (n := n) ⟨j, hj⟩ * (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩)) := by
                          rw [mul_assoc]
                  _ = switch (n := n) ⟨j, hj⟩
                        * ((tilt (n := n) ⟨j, hj⟩ * tilt (n := n) ⟨j, hj⟩)
                          * switch (n := n) ⟨j, hj⟩) := by
                          simp [mul_assoc]
                )
    _ = - (1 : FunctionSpace n →ₗ[ℂ] FunctionSpace n) := by
              simp [tilt_sq, switch_sq, mul_assoc]

theorem pairTerm_commute_of_ne {i j : ℕ} (hij : i ≠ j) :
    Commute (pairTerm (n := n) i) (pairTerm (n := n) j) := by
  by_cases hi : i < n
  · by_cases hj : j < n
    ·
      have hti_tj : Commute (tilt (n := n) ⟨i, hi⟩) (tilt (n := n) ⟨j, hj⟩) := by
        exact tilt_comm (n := n) (i := ⟨i, hi⟩) (j := ⟨j, hj⟩)
      have hti_sj : Commute (tilt (n := n) ⟨i, hi⟩) (switch (n := n) ⟨j, hj⟩) := by
        exact tilt_switch_comm_of_ne (n := n) (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) (by
          intro h; exact hij (congrArg Fin.val h))
      have hsi_tj : Commute (switch (n := n) ⟨i, hi⟩) (tilt (n := n) ⟨j, hj⟩) := by
        have h := tilt_switch_comm_of_ne (n := n) (i := ⟨j, hj⟩) (j := ⟨i, hi⟩) (by
          intro h; exact hij (congrArg Fin.val h.symm))
        simpa [Commute, mul_assoc] using h.symm
      have hsi_sj : Commute (switch (n := n) ⟨i, hi⟩) (switch (n := n) ⟨j, hj⟩) := by
        exact switch_comm (n := n) (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) (by
          intro h; exact hij (congrArg Fin.val h))
      have hti_pair : Commute (tilt (n := n) ⟨i, hi⟩) (pairTerm (n := n) j) := by
        simpa [pairTerm_of_lt (n := n) hj] using hti_tj.mul_right hti_sj
      have hsi_pair : Commute (switch (n := n) ⟨i, hi⟩) (pairTerm (n := n) j) := by
        simpa [pairTerm_of_lt (n := n) hj] using hsi_tj.mul_right hsi_sj
      simpa [pairTerm_of_lt (n := n) hi, pairTerm_of_lt (n := n) hj, mul_assoc] using
        (Commute.mul_left hti_pair hsi_pair)
    · simp [pairTerm, hj]
  · simp [pairTerm, hi]

end FunctionSpace

end InfoGeometry.Canonical.CelikKocakCantorOperators
