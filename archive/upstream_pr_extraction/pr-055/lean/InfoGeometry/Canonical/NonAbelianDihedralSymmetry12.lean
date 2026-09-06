import Mathlib.GroupTheory.SpecificGroups.Dihedral
import InfoGeometry.Canonical.ChiralZornFiniteSymmetry

/-!
# Dihedral relations for the chiral Zorn colour/sheet automorphisms

This file uses the existing `MulEquiv`s on `ChiralZornMatrix A`.  It records
the sheet/colour automorphism relations only.  The underlying multiplication
is the native nonassociative Peirce-routed product: same-sheet products cross
to the opposite sheet, so this file does not assert a binary superalgebra
grading or a Lie bracket.  The corresponding `ZMod 3` routing and associator
readouts are owned by `ThreeColorOperatorZ3Grading` and
`ThreeColorOperatorAssociatorGrading`.

The generated subgroup is kept as the actual closure of the two native
automorphisms; the named dihedral type below is only a separate abstract
cardinality/noncommutativity model, not an asserted equivalence with that
closure.
-/

namespace InfoGeometry.Physics.Octonion.ChiralZornMatrix

noncomputable section

variable {A : Type*} [Ring A]

abbrev R : ChiralZornMatrix A ≃* ChiralZornMatrix A := rotateMulEquiv
abbrev M : ChiralZornMatrix A ≃* ChiralZornMatrix A := reflectMulEquiv

theorem R_cubed (X : ChiralZornMatrix A) :
    R (R (R X)) = X := by
  exact rotateColor_three X

theorem M_squared (X : ChiralZornMatrix A) :
    M (M X) = X := by
  exact reflect_two X

theorem M_R_M (X : ChiralZornMatrix A) :
    M (R (M X)) = R (R X) := by
  exact reflect_rotate_reflect X

theorem M_R_M_equiv :
    (M : ChiralZornMatrix A ≃* ChiralZornMatrix A) * R * M = R ^ 2 := by
  ext X
  exact M_R_M X

theorem R_pow_three :
    (R : ChiralZornMatrix A ≃* ChiralZornMatrix A) ^ 3 = 1 := by
  ext X
  exact R_cubed X

theorem M_pow_two :
    (M : ChiralZornMatrix A ≃* ChiralZornMatrix A) ^ 2 = 1 := by
  ext X
  exact M_squared X

theorem R_inv :
    (R : ChiralZornMatrix A ≃* ChiralZornMatrix A)⁻¹ = R ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ' (R : ChiralZornMatrix A ≃* ChiralZornMatrix A) 2]
  simpa using R_pow_three (A := A)

theorem M_inv :
    (M : ChiralZornMatrix A ≃* ChiralZornMatrix A)⁻¹ = M := by
  apply inv_eq_of_mul_eq_one_right
  simpa using M_pow_two (A := A)

theorem M_conjugates_R_to_inverse :
    (M : ChiralZornMatrix A ≃* ChiralZornMatrix A) * R * M⁻¹ = R⁻¹ := by
  rw [M_inv (A := A), R_inv (A := A), M_R_M_equiv (A := A)]

theorem R_mul (X Y : ChiralZornMatrix A) :
    R (X * Y) = R X * R Y := by
  exact rotateColor_mul X Y

theorem M_mul (X Y : ChiralZornMatrix A) :
    M (X * Y) = M X * M Y := by
  exact reflect_mul X Y

/-! The relations above give a native homomorphism from the order-six
    dihedral presentation.  This is an action theorem, not yet an
    identification of its range with the closure subgroup below. -/

def rotationPower (i : ZMod 3) :
    ChiralZornMatrix A ≃* ChiralZornMatrix A := R ^ i.val

theorem rotationPower_add (i j : ZMod 3) :
    rotationPower (A := A) (i + j) =
      rotationPower i * rotationPower j := by
  have hmod : (i + j).val ≡ i.val + j.val [MOD 3] := by
    simp [Nat.ModEq, ZMod.val_add, Nat.add_mod]
  simpa [rotationPower, pow_add] using
    (pow_eq_pow_of_modEq hmod (R_pow_three (A := A)))

theorem rotationPower_sub (i j : ZMod 3) :
    rotationPower (A := A) (j - i) =
      rotationPower j * (rotationPower i)⁻¹ := by
  have hsub00 : (0 : ZMod 3) - 0 = 0 := by decide
  have hsub01 : (0 : ZMod 3) - 1 = 2 := by decide
  have hsub02 : (0 : ZMod 3) - 2 = 1 := by decide
  have hsub10 : (1 : ZMod 3) - 0 = 1 := by decide
  have hsub11 : (1 : ZMod 3) - 1 = 0 := by decide
  have hsub12 : (1 : ZMod 3) - 2 = 2 := by decide
  have hsub20 : (2 : ZMod 3) - 0 = 2 := by decide
  have hsub21 : (2 : ZMod 3) - 1 = 1 := by decide
  have hsub22 : (2 : ZMod 3) - 2 = 0 := by decide
  have hrot : (R : ChiralZornMatrix A ≃* ChiralZornMatrix A) ^ 3 = 1 :=
    R_pow_three
  have hR2inv : (R : ChiralZornMatrix A ≃* ChiralZornMatrix A) ^ 2 = R⁻¹ := by
    symm
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ']
    simpa using hrot
  have cases3 (k : ZMod 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
    fin_cases k <;> simp
  rcases cases3 i with rfl | rfl | rfl <;>
    rcases cases3 j with rfl | rfl | rfl <;>
      simp [rotationPower, hsub00, hsub01, hsub02, hsub10, hsub11,
        hsub12, hsub20, hsub21, hsub22, hrot, hR2inv, inv_pow, pow_two] <;>
      group <;> norm_num [ZMod.val] <;>
      first
      | exact hR2inv
      | calc
          R = (R⁻¹)⁻¹ := by simp
          _ = (R ^ 2)⁻¹ := by rw [hR2inv]

theorem rotationPower_mul_M (i : ZMod 3) :
    rotationPower (A := A) i * M = M * (rotationPower i)⁻¹ := by
  have hM : (M : ChiralZornMatrix A ≃* ChiralZornMatrix A) ^ 2 = 1 :=
    M_pow_two
  have hR2inv : (R : ChiralZornMatrix A ≃* ChiralZornMatrix A) ^ 2 = R⁻¹ :=
    (R_inv (A := A)).symm
  have hRM : (R : ChiralZornMatrix A ≃* ChiralZornMatrix A) * M = M * R ^ 2 := by
    calc
      R * M = M * M * (R * M) := by rw [← pow_two M, hM]; simp
      _ = M * (M * R * M) := by simp [mul_assoc]
      _ = M * R ^ 2 := by rw [M_R_M_equiv]
  have hR2M : (R : ChiralZornMatrix A ≃* ChiralZornMatrix A) ^ 2 * M = M * R := by
    calc
      R ^ 2 * M = (M * R * M) * M := by rw [M_R_M_equiv]
      _ = M * R := by
        simp only [mul_assoc]
        rw [← pow_two M, hM]
        simp
  have cases3 (k : ZMod 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
    fin_cases k <;> simp
  rcases cases3 i with rfl | rfl | rfl
  · simp [rotationPower]
  · change R * M = M * R⁻¹
    rw [R_inv]
    exact hRM
  · have hinv : ((R : ChiralZornMatrix A ≃* ChiralZornMatrix A) ^ 2)⁻¹ = R := by
      calc
        (R ^ 2)⁻¹ = (R⁻¹)⁻¹ := by rw [hR2inv]
        _ = R := by simp
    change R ^ 2 * M = M * (R ^ 2)⁻¹
    rw [hinv]
    exact hR2M

theorem M_rotationPower_M (i : ZMod 3) :
    M * rotationPower (A := A) i * M = (rotationPower i)⁻¹ := by
  have hM : (M : ChiralZornMatrix A ≃* ChiralZornMatrix A) ^ 2 = 1 := M_pow_two
  have hR2inv : (R : ChiralZornMatrix A ≃* ChiralZornMatrix A) ^ 2 = R⁻¹ :=
    (R_inv (A := A)).symm
  have cases3 (k : ZMod 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
    fin_cases k <;> simp
  rcases cases3 i with rfl | rfl | rfl
  · change M * 1 * M = (1 : ChiralZornMatrix A ≃* ChiralZornMatrix A)⁻¹
    simp only [mul_one, inv_one]
    exact hM
  · change M * R * M = R⁻¹
    calc
      M * R * M = R ^ 2 := M_R_M_equiv (A := A)
      _ = R⁻¹ := hR2inv
  · change M * R ^ 2 * M = (R ^ 2)⁻¹
    calc
      M * R ^ 2 * M = R := by
        calc
          M * R ^ 2 * M = M * (M * R * M) * M := by rw [M_R_M_equiv]
          _ = R := by
            calc
              M * (M * R * M) * M = (M * M) * R * (M * M) := by group
              _ = R := by rw [← pow_two M, hM]; simp
      _ = (R ^ 2)⁻¹ := by
        calc
          R = (R⁻¹)⁻¹ := by simp
          _ = (R ^ 2)⁻¹ := by simpa using (congrArg Inv.inv hR2inv).symm

def dihedralAction : DihedralGroup 3 →* ChiralZornMatrix A ≃* ChiralZornMatrix A where
  toFun
    | .r i => rotationPower i
    | .sr i => M * rotationPower i
  map_one' := by
    change rotationPower (A := A) 0 = 1
    simp [rotationPower]
  map_mul' := by
    intro x y
    cases x with
    | r i =>
      cases y with
      | r j =>
        simp only [DihedralGroup.r_mul_r]
        exact rotationPower_add i j
      | sr j =>
        simp only [DihedralGroup.r_mul_sr]
        change M * rotationPower (j - i) =
          rotationPower i * (M * rotationPower j)
        calc
          M * rotationPower (j - i) =
              M * (rotationPower j * (rotationPower i)⁻¹) := by
                rw [rotationPower_sub]
          _ = M * ((rotationPower i)⁻¹ * rotationPower j) := by
            congr 1
            simpa [rotationPower] using
              (Commute.pow_pow (Commute.refl R) j.val i.val).inv_right.eq
          _ = (rotationPower i * M) * rotationPower j := by
            rw [rotationPower_mul_M]
            simp [mul_assoc]
    | sr i =>
      cases y with
      | r j =>
        simp only [DihedralGroup.sr_mul_r]
        change M * rotationPower (i + j) =
          (M * rotationPower i) * rotationPower j
        rw [rotationPower_add]
        simp [mul_assoc]
      | sr j =>
        simp only [DihedralGroup.sr_mul_sr]
        change rotationPower (j - i) =
          (M * rotationPower i) * (M * rotationPower j)
        calc
          rotationPower (j - i) =
              rotationPower j * (rotationPower i)⁻¹ :=
            rotationPower_sub i j
          _ = (rotationPower i)⁻¹ * rotationPower j := by
            simpa [rotationPower] using
              (Commute.pow_pow (Commute.refl R) j.val i.val).inv_right.eq
          _ = (M * rotationPower i * M) * rotationPower j := by
            rw [M_rotationPower_M]
          _ = (M * rotationPower i) * (M * rotationPower j) := by
            simp [mul_assoc]

theorem R_ne_one [Nontrivial A] :
    R ≠ (1 : ChiralZornMatrix A ≃* ChiralZornMatrix A) := by
  intro h
  have hpoint := congrArg (fun e : ChiralZornMatrix A ≃* ChiralZornMatrix A =>
      e (firstPlus (A := A))) h
  have hcoord := congrFun
    (congrArg (fun Z : ChiralZornMatrix A => Z.sigma_plus) hpoint) 1
  simpa [R, firstPlus, rotateColor, prevColor] using hcoord

theorem M_ne_one [Nontrivial A] :
    M ≠ (1 : ChiralZornMatrix A ≃* ChiralZornMatrix A) := by
  intro h
  have hpoint := congrArg (fun e : ChiralZornMatrix A ≃* ChiralZornMatrix A =>
      e (firstPlus (A := A))) h
  have hcoord := congrFun
    (congrArg (fun Z : ChiralZornMatrix A => Z.sigma_plus) hpoint) 0
  simpa [M, firstPlus, reflect, reflectColor] using hcoord

theorem R_orderOf [Nontrivial A] :
    orderOf (R : ChiralZornMatrix A ≃* ChiralZornMatrix A) = 3 := by
  exact orderOf_eq_prime R_pow_three R_ne_one

theorem M_orderOf [Nontrivial A] :
    orderOf (M : ChiralZornMatrix A ≃* ChiralZornMatrix A) = 2 := by
  exact orderOf_eq_prime M_pow_two M_ne_one

theorem M_R_ne_R_M [Nontrivial A] :
    ¬ (∀ X : ChiralZornMatrix A, M (R X) = R (M X)) := by
  exact rotateColor_reflect_not_commute (A := A)

theorem M_mul_R_ne_R_mul_M [Nontrivial A] :
    ¬ ((M : ChiralZornMatrix A ≃* ChiralZornMatrix A) * R = R * M) := by
  intro h
  apply rotateColor_reflect_not_commute (A := A)
  intro X
  exact congrArg (fun e : ChiralZornMatrix A ≃* ChiralZornMatrix A => e X) h

/-! The native generated subgroup is recorded explicitly.  This is the
    actual subgroup of multiplication automorphisms; the declaration does
    not silently replace it by an abstract dihedral group. -/

def sheetColorSubgroup :
    Subgroup (ChiralZornMatrix A ≃* ChiralZornMatrix A) :=
  Subgroup.closure ({R, M} : Set (ChiralZornMatrix A ≃* ChiralZornMatrix A))

theorem R_mem_sheetColorSubgroup :
    R ∈ sheetColorSubgroup (A := A) := by
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem M_mem_sheetColorSubgroup :
    M ∈ sheetColorSubgroup (A := A) := by
  exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))

theorem dihedralAction_range_le_sheetColorSubgroup :
    MonoidHom.range (dihedralAction (A := A)) ≤ sheetColorSubgroup (A := A) := by
  intro g hg
  rcases hg with ⟨x, rfl⟩
  cases x with
  | r i =>
      change R ^ i.val ∈ sheetColorSubgroup (A := A)
      exact (sheetColorSubgroup (A := A)).pow_mem
        (R_mem_sheetColorSubgroup (A := A)) _
  | sr i =>
      change M * R ^ i.val ∈ sheetColorSubgroup (A := A)
      exact (sheetColorSubgroup (A := A)).mul_mem
        (M_mem_sheetColorSubgroup (A := A))
        ((sheetColorSubgroup (A := A)).pow_mem
          (R_mem_sheetColorSubgroup (A := A)) _)

theorem sheetColorSubgroup_le_dihedralAction_range :
    sheetColorSubgroup (A := A) ≤ MonoidHom.range (dihedralAction (A := A)) := by
  refine (Subgroup.closure_le _).2 ?_
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · exact ⟨.r 1, by
      change R ^ (1 : ZMod 3).val = R
      have hv : (1 : ZMod 3).val = 1 := by decide
      rw [hv]
      simp [dihedralAction, rotationPower]⟩
  · have hz' : z = M := Set.mem_singleton_iff.mp hz
    subst z
    exact ⟨.sr 0, by
      change M * R ^ (0 : ZMod 3).val = M
      have hv : (0 : ZMod 3).val = 0 := by decide
      rw [hv]
      simp [dihedralAction, rotationPower]⟩

theorem dihedralAction_range_eq_sheetColorSubgroup :
    MonoidHom.range (dihedralAction (A := A)) = sheetColorSubgroup (A := A) := by
  exact le_antisymm
    (dihedralAction_range_le_sheetColorSubgroup (A := A))
    (sheetColorSubgroup_le_dihedralAction_range (A := A))

theorem sheetColorSubgroup_noncommutative [Nontrivial A] :
    ¬ ∀ g h : sheetColorSubgroup (A := A), g * h = h * g := by
  intro h
  have hRM := h ⟨M, M_mem_sheetColorSubgroup (A := A)⟩
    ⟨R, R_mem_sheetColorSubgroup (A := A)⟩
  exact M_mul_R_ne_R_mul_M (A := A) (by simpa using hRM)

abbrev Order12DihedralModel := DihedralGroup 6

theorem order12_dihedral_model_card :
    Fintype.card Order12DihedralModel = 12 := by
  simpa [Order12DihedralModel] using (DihedralGroup.card (n := 6))

theorem order12_dihedral_model_noncommutative :
    ¬ Std.Commutative (fun x y : Order12DihedralModel => x * y) := by
  simpa [Order12DihedralModel] using
    (DihedralGroup.not_commutative (n := 6) (by decide) (by decide))

end

end InfoGeometry.Physics.Octonion.ChiralZornMatrix
