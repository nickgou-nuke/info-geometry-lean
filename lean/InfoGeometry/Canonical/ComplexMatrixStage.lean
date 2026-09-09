import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.TensorTowerColimit
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-!
# Complex finite matrix stages

This file records the complex finite-stage carrier and the coordinate form of
the successor block embedding.  It deliberately stops before declaring a
complex direct limit: the ring-hom proof and the boundary representation are
separate obligations.
-/

namespace InfoGeometry.Canonical.ComplexMatrixStage

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

abbrev Stage (n : ℕ) := Matrix (BitWord n) (BitWord n) ℂ

def bondFun (n : ℕ) (M : Stage n) : Stage (n + 1) :=
  fun v w =>
    if v ⟨n, Nat.lt_succ_self n⟩ = w ⟨n, Nat.lt_succ_self n⟩ then
      M (prefixSucc n v) (prefixSucc n w)
    else 0

theorem bondFun_extendSucc (n : ℕ) (M : Stage n)
    (u v : BitWord n) (b c : Bool) :
    bondFun n M (extendSucc n u b) (extendSucc n v c) =
      if b = c then M u v else 0 := by
  cases b <;> cases c <;>
    simp [bondFun, extendSucc, prefixSucc_extendSucc]

theorem bondFun_add (n : ℕ) (M N : Stage n) :
    bondFun n (M + N) = bondFun n M + bondFun n N := by
  ext v w
  dsimp [bondFun]
  split_ifs with h
  · rfl
  · simp

theorem bondFun_smul (n : ℕ) (c : ℂ) (M : Stage n) :
    bondFun n (c • M) = c • bondFun n M := by
  ext v w
  dsimp [bondFun]
  split_ifs with h
  · rfl
  · simp

theorem bondFun_star (n : ℕ) (M : Stage n) :
    bondFun n (star M) = star (bondFun n M) := by
  ext v w
  dsimp [bondFun, Matrix.star_apply]
  by_cases h : v ⟨n, Nat.lt_succ_self n⟩ = w ⟨n, Nat.lt_succ_self n⟩
  · simp [h]
  · have h' : w ⟨n, Nat.lt_succ_self n⟩ ≠ v ⟨n, Nat.lt_succ_self n⟩ :=
      fun hv => h hv.symm
    simp [h, h']

theorem bondFun_one (n : ℕ) :
    bondFun n (1 : Stage n) = (1 : Stage (n + 1)) := by
  ext v w
  dsimp [bondFun, Matrix.one_apply]
  by_cases hlast : v ⟨n, Nat.lt_succ_self n⟩ = w ⟨n, Nat.lt_succ_self n⟩
  · by_cases hvw : v = w
    · subst w
      simp
    · have hpref : prefixSucc n v ≠ prefixSucc n w := by
        intro h
        apply hvw
        funext i
        by_cases hi : i.1 < n
        · exact congrFun h ⟨i.1, hi⟩
        · have hi' : i.1 = n := by omega
          have hi_eq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi'
          rw [hi_eq]
          exact hlast
      simp [hvw, hpref]
  · have hvw : v ≠ w := by
      intro h
      subst w
      exact hlast rfl
    simp [hvw, hlast]

theorem bitword_sum_last_split (n : ℕ) (f : BitWord (n + 1) → ℂ) :
    ∑ u : BitWord (n + 1), f u =
      ∑ u_pref : BitWord n,
        (f (extendSucc n u_pref true) + f (extendSucc n u_pref false)) := by
  let hequiv : BitWord (n + 1) ≃ BitWord n × Bool := {
    toFun := fun w => (prefixSucc n w, w ⟨n, Nat.lt_succ_self n⟩)
    invFun := fun p => extendSucc n p.1 p.2
    left_inv := by
      intro w
      funext i
      by_cases hi : i.1 < n
      · simp [prefixSucc, extendSucc, hi]
      · have hi' : i.1 = n := by omega
        have hi_eq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi'
        rw [hi_eq]
        dsimp [extendSucc]
        rw [dif_neg (lt_irrefl n)]
    right_inv := by
      rintro ⟨w, b⟩
      apply Prod.ext
      · funext i
        exact congrFun (prefixSucc_extendSucc n w b) i
      · dsimp [extendSucc]
        rw [dif_neg (lt_irrefl n)] }
  rw [← Equiv.sum_comp hequiv.symm]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have hequiv_symm (x : BitWord n) (b : Bool) :
      hequiv.symm (x, b) = extendSucc n x b := by
    simp [hequiv]
  simp_rw [hequiv_symm]

theorem bondFun_mul (n : ℕ) (M N : Stage n) :
    bondFun n (M * N) = bondFun n M * bondFun n N := by
  ext v w
  change
    (if v ⟨n, Nat.lt_succ_self n⟩ = w ⟨n, Nat.lt_succ_self n⟩ then
        (M * N) (prefixSucc n v) (prefixSucc n w)
      else 0) =
      ∑ u : BitWord (n + 1),
        (if v ⟨n, Nat.lt_succ_self n⟩ = u ⟨n, Nat.lt_succ_self n⟩ then
            M (prefixSucc n v) (prefixSucc n u)
          else 0) *
        (if u ⟨n, Nat.lt_succ_self n⟩ = w ⟨n, Nat.lt_succ_self n⟩ then
            N (prefixSucc n u) (prefixSucc n w)
          else 0)
  rw [bitword_sum_last_split]
  cases hv : v ⟨n, Nat.lt_succ_self n⟩ <;>
    cases hw : w ⟨n, Nat.lt_succ_self n⟩ <;>
      simp [hv, hw, extendSucc, Matrix.mul_apply, prefixSucc_extendSucc]

def bond (n : ℕ) : Stage n →+* Stage (n + 1) where
  toFun := bondFun n
  map_one' := bondFun_one n
  map_mul' := bondFun_mul n
  map_zero' := by
    ext v w
    dsimp [bondFun]
    split_ifs <;> rfl
  map_add' := bondFun_add n

theorem bondMap_smul
    (m n : ℕ) (h : m ≤ n) (c : ℂ) (M : Stage m) :
    bondMap bond m n h (c • M) = c • bondMap bond m n h M := by
  induction h with
  | refl => simp [bondMap_refl]
  | @step n h ih =>
      rw [bondMap_succ bond m n h]
      change bond n (bondMap bond m n h (c • M)) =
        c • bond n (bondMap bond m n h M)
      rw [ih]
      exact bondFun_smul n c (bondMap bond m n h M)

theorem bondMap_star
    (m n : ℕ) (h : m ≤ n) (M : Stage m) :
    bondMap bond m n h (star M) = star (bondMap bond m n h M) := by
  induction h with
  | refl => simp [bondMap_refl]
  | @step n h ih =>
      rw [bondMap_succ bond m n h]
      change bond n (bondMap bond m n h (star M)) =
        star (bond n (bondMap bond m n h M))
      rw [ih]
      exact bondFun_star n (bondMap bond m n h M)

def diagonal (n : ℕ) : DiagAlg n →ₗ[ℂ] Stage n where
  toFun f := Matrix.diagonal f
  map_add' := by
    intro f g
    ext v w
    by_cases h : v = w <;> simp [Matrix.diagonal, h]
  map_smul' := by intro c f; ext v w; simp [Matrix.diagonal]

theorem bond_diagonal (n : ℕ) (f : DiagAlg n) :
    bond n (diagonal n f) = diagonal (n + 1) (diagEmbedSucc n f) := by
  ext v w
  by_cases hlast : v ⟨n, Nat.lt_succ_self n⟩ = w ⟨n, Nat.lt_succ_self n⟩
  · by_cases hvw : v = w
    · subst w
      simp [bond, bondFun, diagonal, diagEmbedSucc, prefixSucc]
    · have hpref : prefixSucc n v ≠ prefixSucc n w := by
        intro h
        apply hvw
        funext i
        by_cases hi : i.1 < n
        · exact congrFun h ⟨i.1, hi⟩
        · have hi' : i.1 = n := by omega
          have hi_eq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi'
          rw [hi_eq]
          exact hlast
      simp [bond, bondFun, diagonal, diagEmbedSucc, hvw, hpref]
  · have hvw : v ≠ w := by
      intro h
      subst w
      exact hlast rfl
    simp [bond, bondFun, diagonal, diagEmbedSucc, hlast, hvw]

/-- The diagonal successor embedding as a linear map. -/
def diagEmbedSuccLinear (n : ℕ) : DiagAlg n →ₗ[ℂ] DiagAlg (n + 1) where
  toFun := diagEmbedSucc n
  map_add' := diagEmbedSucc_add n
  map_smul' := by
    intro c f
    ext w
    rfl

/-- The finite-cylinder realization as a linear map. -/
def cylinderLinear (n : ℕ) : DiagAlg n →ₗ[ℂ] ((ℕ → Bool) → ℂ) where
  toFun := cylinder n
  map_add' := by
    intro f g
    exact cylinder_add n f g
  map_smul' := by
    intro c f
    ext b
    rfl

theorem cylinderLinear_compatible_succ (n : ℕ) :
    (cylinderLinear (n + 1)).comp (diagEmbedSuccLinear n) =
      cylinderLinear n := by
  apply LinearMap.ext
  intro f
  apply funext
  intro b
  exact congrFun (cylinder_compatible_succ n f) b

def boundaryRealization (n : ℕ) : DiagAlg n →ₗ[ℂ] ((ℕ → Bool) → ℂ) :=
  cylinderLinear n

theorem boundaryRealization_compatible (n : ℕ) :
    (boundaryRealization (n + 1)).comp (diagEmbedSuccLinear n) =
      boundaryRealization n :=
  cylinderLinear_compatible_succ n

theorem boundaryRealization_comp_iota_seq (n m : ℕ) :
    (boundaryRealization (n + m)).comp
        (_root_.iota_seq DiagAlg diagEmbedSuccLinear n m) =
      boundaryRealization n :=
  _root_.psi_comp_iota_seq DiagAlg diagEmbedSuccLinear
    ((ℕ → Bool) → ℂ) boundaryRealization boundaryRealization_compatible n m

abbrev Colimit :=
  DirectLimitSuperClosure bond

noncomputable instance colimitSMul : SMul ℂ Colimit where
  smul c :=
    DirectLimit.map
      (fun _ _ h => bondMap bond _ _ h)
      (fun _ _ h => bondMap bond _ _ h)
      (fun _ A => c • A)
      (by
        intro m n h A
        exact bondMap_smul m n h c A)

@[simp] theorem colimit_smul_mk
    (c : ℂ) (n : ℕ) (A : Stage n) :
    c • (⟦⟨n, A⟩⟧ : Colimit) =
      (⟦⟨n, c • A⟩⟧ : Colimit) := rfl

noncomputable instance colimitModule : Module ℂ Colimit where
  one_smul x := by
    induction x using DirectLimit.induction with
    | _ n A => simp [colimit_smul_mk]
  mul_smul c d x := by
    induction x using DirectLimit.induction with
    | _ n A => simp [colimit_smul_mk, mul_smul]
  smul_add c x y := by
    induction x, y using DirectLimit.induction₂ with
    | _ n A B =>
        rw [DirectLimit.add_def]
        change (⟦⟨n, c • (A + B)⟩⟧ : Colimit) =
          (⟦⟨n, c • A⟩⟧ : Colimit) +
            (⟦⟨n, c • B⟩⟧ : Colimit)
        rw [smul_add]
        exact (DirectLimit.add_def n (c • A) (c • B)).symm
  smul_zero c := by
    rw [DirectLimit.zero_def 0]
    change c • (⟦⟨0, (0 : Stage 0)⟩⟧ : Colimit) =
      (⟦⟨0, (0 : Stage 0)⟩⟧ : Colimit)
    rw [colimit_smul_mk]
    simp
  add_smul c d x := by
    induction x using DirectLimit.induction with
    | _ n A =>
        change (⟦⟨n, (c + d) • A⟩⟧ : Colimit) =
          (⟦⟨n, c • A⟩⟧ : Colimit) +
            (⟦⟨n, d • A⟩⟧ : Colimit)
        rw [add_smul]
        exact (DirectLimit.add_def n (c • A) (d • A)).symm
  zero_smul x := by
    induction x using DirectLimit.induction with
    | _ n A =>
        change (⟦⟨n, (0 : ℂ) • A⟩⟧ : Colimit) = 0
        rw [zero_smul]
        rw [DirectLimit.zero_def n]

noncomputable instance colimitAlgebra : Algebra ℂ Colimit :=
  Algebra.ofModule
    (by
      intro c x y
      induction x, y using DirectLimit.induction₂ with
      | _ n A B =>
          simp [DirectLimit.smul_def, DirectLimit.mul_def])
    (by
      intro c x y
      induction x, y using DirectLimit.induction₂ with
      | _ n A B =>
          simp [DirectLimit.smul_def, DirectLimit.mul_def])

noncomputable instance colimitStar : Star Colimit where
  star :=
    DirectLimit.map
      (fun _ _ h => bondMap bond _ _ h)
      (fun _ _ h => bondMap bond _ _ h)
      (fun _ A => star A)
      (by
        intro m n h A
        exact bondMap_star m n h A)

@[simp] theorem colimit_star_mk
    (n : ℕ) (A : Stage n) :
    star (⟦⟨n, A⟩⟧ : Colimit) =
      (⟦⟨n, star A⟩⟧ : Colimit) := rfl

noncomputable instance colimitStarRing : StarRing Colimit where
  star_involutive := by
    intro x
    induction x using DirectLimit.induction with
    | _ n A => simp [colimit_star_mk]
  star_add := by
    intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ n A B =>
        rw [DirectLimit.add_def, colimit_star_mk, colimit_star_mk,
          colimit_star_mk, DirectLimit.add_def, star_add]
  star_mul := by
    intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ n A B =>
        rw [DirectLimit.mul_def, colimit_star_mk, colimit_star_mk,
          colimit_star_mk, DirectLimit.mul_def, star_mul]

noncomputable def toColimit (n : ℕ) : Stage n →+* Colimit :=
  directLimitOf bond n

@[simp] theorem toColimit_bond (n : ℕ) (M : Stage n) :
    toColimit (n + 1) (bond n M) = toColimit n M :=
  by
    change directLimitOf bond (n + 1) (bond n M) = directLimitOf bond n M
    have hmap : bondMap bond n (n + 1) (Nat.le_succ n) = bond n := by
      simpa [bondMap_succ, bondMap_refl]
    rw [← hmap]
    exact directLimitOf_bondMap bond n (n + 1) (Nat.le_succ n) M

theorem toColimit_bondMap (m n : ℕ) (h : m ≤ n) (M : Stage m) :
    toColimit n (bondMap bond m n h M) = toColimit m M :=
  directLimitOf_bondMap bond m n h M

theorem toColimit_diagonal_compatible (n : ℕ) (f : DiagAlg n) :
    toColimit (n + 1) (diagonal (n + 1) (diagEmbedSucc n f)) =
      toColimit n (diagonal n f) := by
  rw [← bond_diagonal n f]
  exact toColimit_bond n (diagonal n f)

end InfoGeometry.Canonical.ComplexMatrixStage
