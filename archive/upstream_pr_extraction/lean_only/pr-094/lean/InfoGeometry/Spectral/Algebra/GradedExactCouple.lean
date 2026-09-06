import InfoGeometry.Spectral.Algebra.DerivedCouple

/-!
# Exact couples with explicit degree equivalences

This is the native Lean 4 form of the degree-aware exact couple used in the
CMU Spectral development.  A degree is an actual equivalence of the grading
type.  Exactness is stated componentwise as equality of Mathlib submodules.

For a derived couple the degree laws are

* `deg i' = deg i`;
* `deg j' = deg j ∘ (deg i)⁻¹`;
* `deg k' = deg k`.
-/

namespace InfoGeometry.Spectral.Algebra

universe u v

/-- A graded exact couple whose three map degrees are equivalences of indices. -/
structure GradedExactCouple
    (R : Type u) [Ring R] (I : Type v)
    (D E : I → Type u)
    [∀ p, AddCommGroup (D p)] [∀ p, AddCommGroup (E p)]
    [∀ p, Module R (D p)] [∀ p, Module R (E p)]
    (iDeg jDeg kDeg : I ≃ I) where
  i : ∀ p, D p →ₗ[R] D (iDeg p)
  j : ∀ p, D p →ₗ[R] E (jDeg p)
  k : ∀ p, E p →ₗ[R] D (kDeg p)
  exact_ij :
    ∀ p, LinearMap.ker (j (iDeg p)) =
      LinearMap.range (i p)
  exact_jk :
    ∀ p, LinearMap.ker (k (jDeg p)) =
      LinearMap.range (j p)
  exact_ki :
    ∀ p, LinearMap.ker (i (kDeg p)) =
      LinearMap.range (k p)

namespace GradedExactCouple

/-- Derivation preserves the degree of `i`. -/
def derivedIDegree {I : Type v} (iDeg : I ≃ I) : I ≃ I :=
  iDeg

/-- Derivation changes `deg j` to `deg j ∘ (deg i)⁻¹`. -/
def derivedJDegree {I : Type v}
    (iDeg jDeg : I ≃ I) : I ≃ I :=
  iDeg.symm.trans jDeg

/-- Derivation preserves the degree of `k`. -/
def derivedKDegree {I : Type v} (kDeg : I ≃ I) : I ≃ I :=
  kDeg

@[simp]
theorem derivedIDegree_apply {I : Type v}
    (iDeg : I ≃ I) (p : I) :
    derivedIDegree iDeg p = iDeg p :=
  rfl

@[simp]
theorem derivedJDegree_apply {I : Type v}
    (iDeg jDeg : I ≃ I) (p : I) :
    derivedJDegree iDeg jDeg p =
      jDeg (iDeg.symm p) :=
  rfl

@[simp]
theorem derivedKDegree_apply {I : Type v}
    (kDeg : I ≃ I) (p : I) :
    derivedKDegree kDeg p = kDeg p :=
  rfl

end GradedExactCouple

/-- The bidegree translation of the original exact-couple `i` map. -/
def shiftIEquiv : Z2 ≃ Z2 where
  toFun := shiftI
  invFun := shiftIPre
  left_inv := shiftIPre_shiftI
  right_inv := shiftI_shiftIPre

/-- The bidegree translation of the original exact-couple `k` map. -/
def shiftKEquiv : Z2 ≃ Z2 where
  toFun := shiftK
  invFun := shiftKPre
  left_inv := shiftKPre_shiftK
  right_inv := shiftK_shiftKPre

@[simp]
theorem shiftIEquiv_apply (pq : Z2) :
    shiftIEquiv pq = shiftI pq :=
  rfl

@[simp]
theorem shiftIEquiv_symm_apply (pq : Z2) :
    shiftIEquiv.symm pq = shiftIPre pq :=
  rfl

@[simp]
theorem shiftKEquiv_apply (pq : Z2) :
    shiftKEquiv pq = shiftK pq :=
  rfl

@[simp]
theorem shiftKEquiv_symm_apply (pq : Z2) :
    shiftKEquiv.symm pq = shiftKPre pq :=
  rfl

namespace ExactCouple

variable {R : Type u} [Ring R]
variable {D E : Z2 → Type u}
variable [∀ pq, AddCommGroup (D pq)] [∀ pq, AddCommGroup (E pq)]
variable [∀ pq, Module R (D pq)] [∀ pq, Module R (E pq)]

/-- The concrete bidegree exact couple as a degree-aware graded exact couple. -/
def toGradedExactCouple (C : ExactCouple R D E) :
    GradedExactCouple R Z2 D E
      shiftIEquiv (Equiv.refl Z2) shiftKEquiv where
  i := C.i
  j := C.j
  k := C.k
  exact_ij := C.exact_ij
  exact_jk := C.exact_jk
  exact_ki := C.exact_ki

@[simp]
theorem toGradedExactCouple_i
    (C : ExactCouple R D E) (pq : Z2) :
    C.toGradedExactCouple.i pq = C.i pq :=
  rfl

@[simp]
theorem toGradedExactCouple_j
    (C : ExactCouple R D E) (pq : Z2) :
    C.toGradedExactCouple.j pq = C.j pq :=
  rfl

@[simp]
theorem toGradedExactCouple_k
    (C : ExactCouple R D E) (pq : Z2) :
    C.toGradedExactCouple.k pq = C.k pq :=
  rfl

/--
The naturally graded derived `D` object.

`DerivedD C q` is the image of `i_q`, which lies in degree `shiftI q`;
therefore its component in degree `p` is indexed by `shiftIPre p`.
-/
abbrev DirectDerivedD (C : ExactCouple R D E) (p : Z2) :=
  C.DerivedD (shiftIPre p)

/--
The naturally graded derived `E` object.

`DerivedE C q` is homology in degree `shiftK q`; therefore its component in
degree `p` is indexed by `shiftKPre p`.
-/
abbrev DirectDerivedE (C : ExactCouple R D E) (p : Z2) :=
  C.DerivedE (shiftKPre p)

/-- The index equality required by the naturally graded derived `i` map. -/
theorem directDerivedI_index (p : Z2) :
    shiftI (shiftIPre p) = shiftIPre (shiftI p) :=
  (shiftI_shiftIPre p).trans (shiftIPre_shiftI p).symm

/-- The index equality required at the source of the derived `j` map. -/
theorem directDerivedJ_source_index (p : Z2) :
    shiftIPre p =
      shiftK (shiftKPre (shiftIPre p)) :=
  (shiftK_shiftKPre (shiftIPre p)).symm

/-- The index equality required at the target of the derived `k` map. -/
theorem directDerivedK_target_index (p : Z2) :
    derivedKIndex (shiftKPre p) =
      shiftIPre (shiftK p) := by
  ext <;>
    simp [derivedKIndex, shiftIPre, shiftK, shiftKPre]

/-- The degree-correct first-derived `i` map. -/
def directDerivedI (C : ExactCouple R D E) (p : Z2) :
    C.DirectDerivedD p →ₗ[R]
      C.DirectDerivedD (shiftIEquiv p) :=
  (LinearEquiv.cast
      (R := R) (M := fun q => C.DerivedD q)
      (directDerivedI_index p)).toLinearMap.comp
    (C.derivedI (shiftIPre p))

/-- The degree-correct first-derived `j` map. -/
noncomputable def directDerivedJ
    (C : ExactCouple R D E) (p : Z2) :
    C.DirectDerivedD p →ₗ[R]
      C.DirectDerivedE
        (GradedExactCouple.derivedJDegree
          shiftIEquiv (Equiv.refl Z2) p) :=
  (C.derivedJ (shiftKPre (shiftIPre p))).comp
    (LinearEquiv.cast
      (R := R) (M := fun q => C.DerivedD q)
      (directDerivedJ_source_index p)).toLinearMap

/-- The degree-correct first-derived `k` map. -/
def directDerivedK (C : ExactCouple R D E) (p : Z2) :
    C.DirectDerivedE p →ₗ[R]
      C.DirectDerivedD (shiftKEquiv p) :=
  (LinearEquiv.cast
      (R := R) (M := fun q => C.DerivedD q)
      (directDerivedK_target_index p)).toLinearMap.comp
    (C.derivedK (shiftKPre p))

@[simp]
theorem directDerivedI_apply
    (C : ExactCouple R D E) (p : Z2)
    (x : C.DirectDerivedD p) :
    C.directDerivedI p x =
      LinearEquiv.cast
        (R := R) (M := fun q => C.DerivedD q)
        (directDerivedI_index p)
        (C.derivedI (shiftIPre p) x) :=
  rfl

@[simp]
theorem directDerivedJ_apply
    (C : ExactCouple R D E) (p : Z2)
    (x : C.DirectDerivedD p) :
    C.directDerivedJ p x =
      C.derivedJ (shiftKPre (shiftIPre p))
        (LinearEquiv.cast
          (R := R) (M := fun q => C.DerivedD q)
          (directDerivedJ_source_index p) x) :=
  rfl

@[simp]
theorem directDerivedK_apply
    (C : ExactCouple R D E) (p : Z2)
    (x : C.DirectDerivedE p) :
    C.directDerivedK p x =
      LinearEquiv.cast
        (R := R) (M := fun q => C.DerivedD q)
        (directDerivedK_target_index p)
        (C.derivedK (shiftKPre p) x) :=
  rfl

/-- Source-index equality in the square relating direct and source-arrow gradings. -/
theorem directDerivedI_source_index (p : Z2) :
    shiftIPre p =
      derivedIPreIndex
        (shiftKPre (shiftIPre (shiftI p))) := by
  ext <;>
    simp [derivedIPreIndex, shiftI, shiftIPre, shiftK, shiftKPre]

/-- Canonical casts in the derived `D` family compose functorially. -/
theorem derivedD_cast_cast
    (C : ExactCouple R D E) {p q r : Z2}
    (h₁ : p = q) (h₂ : q = r) (x : C.DerivedD p) :
    LinearEquiv.cast
        (R := R) (M := fun s => C.DerivedD s) h₂
        (LinearEquiv.cast
          (R := R) (M := fun s => C.DerivedD s) h₁ x) =
      LinearEquiv.cast
        (R := R) (M := fun s => C.DerivedD s)
        (h₁.trans h₂) x := by
  subst q
  subst r
  rfl

/-- Reindexing the target of `directDerivedK` back to source-arrow grading cancels. -/
theorem directDerivedK_reindex_cancel
    (C : ExactCouple R D E) (p : Z2)
    (x : C.DirectDerivedE p) :
    LinearEquiv.cast
        (R := R) (M := fun r => C.DerivedD r)
        (directDerivedK_target_index p).symm
        (C.directDerivedK p x) =
      C.derivedK (shiftKPre p) x := by
  rw [C.directDerivedK_apply]
  apply Subtype.ext
  rw [C.derivedD_cast_cast]
  rfl

/-- Exactness of the naturally graded first-derived maps at `E₁`. -/
theorem directDerived_exact_jk
    (C : ExactCouple R D E) (p : Z2) :
    LinearMap.ker
        (C.directDerivedK
          (GradedExactCouple.derivedJDegree
            shiftIEquiv (Equiv.refl Z2) p)) =
      LinearMap.range (C.directDerivedJ p) := by
  let q := shiftKPre (shiftIPre p)
  let e :=
    LinearEquiv.cast
      (R := R) (M := fun r => C.DerivedD r)
      (directDerivedJ_source_index p)
  let ek :=
    LinearEquiv.cast
      (R := R) (M := fun r => C.DerivedD r)
      (directDerivedK_target_index (shiftIPre p))
  apply le_antisymm
  · intro x hx
    have hk : C.derivedK q x = 0 := by
      apply ek.injective
      exact hx.trans (map_zero ek).symm
    have hxRange :
        x ∈ LinearMap.range (C.derivedJ q) := by
      rw [← C.derived_exact_jk q]
      exact hk
    rcases hxRange with ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    change C.derivedJ q (e (e.symm y)) = x
    rw [e.apply_symm_apply, hy]
  · rintro x ⟨y, rfl⟩
    change
      ek
        (C.derivedK q
          (C.derivedJ q (e y))) = 0
    have hzero :=
      LinearMap.congr_fun
        (C.derivedK_comp_derivedJ q) (e y)
    rw [show C.derivedK q (C.derivedJ q (e y)) = 0 by
      simpa [LinearMap.comp_apply] using hzero]
    exact map_zero ek

/-- The derived `i` map is natural under equality reindexing. -/
theorem derivedI_cast
    (C : ExactCouple R D E) {p q : Z2}
    (h : p = q) (x : C.DerivedD p) :
    LinearEquiv.cast
        (R := R) (M := fun s => C.DerivedD s)
        (congrArg shiftI h) (C.derivedI p x) =
      C.derivedI q
        (LinearEquiv.cast
          (R := R) (M := fun s => C.DerivedD s) h x) := by
  apply Subtype.ext
  rw [C.derivedD_cast_coe]
  change
    LinearEquiv.cast
        (R := R) (M := D) (congrArg shiftI (congrArg shiftI h))
        (C.i (shiftI p) x.1) =
      C.i (shiftI q)
        (LinearEquiv.cast
          (R := R) (M := fun s => C.DerivedD s) h x).1
  calc
    _ =
        C.i (shiftI q)
          (LinearEquiv.cast
            (R := R) (M := D) (congrArg shiftI h) x.1) :=
      C.i_cast_apply (congrArg shiftI h) x.1
    _ =
        C.i (shiftI q)
          (LinearEquiv.cast
            (R := R) (M := fun s => C.DerivedD s) h x).1 := by
      rw [C.derivedD_cast_coe]

/-- The source-arrow incoming derived `i` map is natural in its page index. -/
theorem incomingDerivedI_cast
    (C : ExactCouple R D E) {p q : Z2}
    (h : p = q)
    (x : C.DerivedD (derivedIPreIndex p)) :
    LinearEquiv.cast
        (R := R) (M := fun s => C.DerivedD s)
        (congrArg shiftK h)
        (C.incomingDerivedI p x) =
      C.incomingDerivedI q
        (LinearEquiv.cast
          (R := R) (M := fun s => C.DerivedD s)
          (congrArg derivedIPreIndex h) x) := by
  change
    LinearEquiv.cast
        (R := R) (M := fun s => C.DerivedD s)
        (congrArg shiftK h)
        (LinearEquiv.cast
          (R := R) (M := fun s => C.DerivedD s)
          (shiftI_derivedIPreIndex p)
          (C.derivedI (derivedIPreIndex p) x)) =
      LinearEquiv.cast
        (R := R) (M := fun s => C.DerivedD s)
        (shiftI_derivedIPreIndex q)
        (C.derivedI (derivedIPreIndex q)
          (LinearEquiv.cast
            (R := R) (M := fun s => C.DerivedD s)
            (congrArg derivedIPreIndex h) x))
  rw [← C.derivedI_cast (congrArg derivedIPreIndex h) x]
  rw [C.derivedD_cast_cast, C.derivedD_cast_cast]

/-- The reindexing square for the first-derived `i` map commutes. -/
theorem directDerivedI_reindex_commutes
    (C : ExactCouple R D E) (p : Z2)
    (x : C.DirectDerivedD p) :
    LinearEquiv.cast
        (R := R) (M := fun r => C.DerivedD r)
        (directDerivedJ_source_index (shiftI p))
        (C.directDerivedI p x) =
      C.incomingDerivedI
        (shiftKPre (shiftIPre (shiftI p)))
        (LinearEquiv.cast
          (R := R) (M := fun r => C.DerivedD r)
          (directDerivedI_source_index p) x) := by
  change
    LinearEquiv.cast
        (R := R) (M := fun r => C.DerivedD r)
        (directDerivedJ_source_index (shiftI p))
        (LinearEquiv.cast
          (R := R) (M := fun r => C.DerivedD r)
          (directDerivedI_index p)
          (C.derivedI (shiftIPre p) x)) =
      LinearEquiv.cast
        (R := R) (M := fun r => C.DerivedD r)
        (shiftI_derivedIPreIndex
          (shiftKPre (shiftIPre (shiftI p))))
        (C.derivedI
          (derivedIPreIndex
            (shiftKPre (shiftIPre (shiftI p))))
          (LinearEquiv.cast
            (R := R) (M := fun r => C.DerivedD r)
            (directDerivedI_source_index p) x))
  rw [← C.derivedI_cast (directDerivedI_source_index p) x]
  rw [C.derivedD_cast_cast, C.derivedD_cast_cast]

/-- Exactness of the naturally graded first-derived maps at the first `D₁` vertex. -/
theorem directDerived_exact_ij
    (C : ExactCouple R D E) (p : Z2) :
    LinearMap.ker (C.directDerivedJ (shiftIEquiv p)) =
      LinearMap.range (C.directDerivedI p) := by
  let q := shiftKPre (shiftIPre (shiftI p))
  let eMid :=
    LinearEquiv.cast
      (R := R) (M := fun r => C.DerivedD r)
      (directDerivedJ_source_index (shiftI p))
  let eSrc :=
    LinearEquiv.cast
      (R := R) (M := fun r => C.DerivedD r)
      (directDerivedI_source_index p)
  apply le_antisymm
  · intro x hx
    have hj : C.derivedJ q (eMid x) = 0 := hx
    have hxRange :
        eMid x ∈
          LinearMap.range (C.incomingDerivedI q) := by
      rw [← C.derived_exact_ij q]
      exact hj
    rcases hxRange with ⟨y, hy⟩
    refine ⟨eSrc.symm y, ?_⟩
    apply eMid.injective
    rw [C.directDerivedI_reindex_commutes p (eSrc.symm y)]
    rw [eSrc.apply_symm_apply, hy]
  · rintro x ⟨y, rfl⟩
    change
      C.derivedJ q
        (eMid (C.directDerivedI p y)) = 0
    rw [C.directDerivedI_reindex_commutes p y]
    have hzero :=
      LinearMap.congr_fun
        (C.derivedJ_comp_incomingDerivedI q) (eSrc y)
    simpa [LinearMap.comp_apply] using hzero

/-- Exactness transported to the natural target of `directDerivedK`. -/
theorem incomingDerivedI_exact_directDerivedK
    (C : ExactCouple R D E) (p : Z2) :
    LinearMap.ker (C.incomingDerivedI p) =
      LinearMap.range (C.directDerivedK p) := by
  let q := shiftKPre p
  let h : shiftK q = p := shiftK_shiftKPre p
  let eSrc :=
    LinearEquiv.cast
      (R := R) (M := fun s => C.DerivedD s)
      (congrArg derivedIPreIndex h)
  let eTgt :=
    LinearEquiv.cast
      (R := R) (M := fun s => C.DerivedD s)
      (congrArg shiftK h)
  apply le_antisymm
  · intro z hz
    let a := eSrc.symm z
    have ha :
        C.incomingDerivedI (shiftK q) a = 0 := by
      apply eTgt.injective
      calc
        eTgt (C.incomingDerivedI (shiftK q) a) =
            C.incomingDerivedI p (eSrc a) :=
          C.incomingDerivedI_cast h a
        _ = C.incomingDerivedI p z := by
          rw [eSrc.apply_symm_apply]
        _ = 0 := hz
        _ = eTgt 0 := (map_zero eTgt).symm
    have haRange :
        a ∈ LinearMap.range (C.derivedK q) := by
      rw [← C.derived_exact_ki q]
      exact ha
    rcases haRange with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change eSrc (C.derivedK q x) = z
    rw [hx, eSrc.apply_symm_apply]
  · rintro z ⟨x, rfl⟩
    change
      C.incomingDerivedI p
        (eSrc (C.derivedK q x)) = 0
    rw [← C.incomingDerivedI_cast h
      (C.derivedK q x)]
    have hzero :=
      LinearMap.congr_fun
        (C.incomingDerivedI_comp_derivedK q) x
    rw [show
      C.incomingDerivedI (shiftK q)
          (C.derivedK q x) = 0 by
        simpa [LinearMap.comp_apply] using hzero]
    exact map_zero eTgt

/-- The direct and source-arrow versions of derived `i` have the same kernel. -/
theorem directDerivedI_ker_eq_incomingDerivedI
    (C : ExactCouple R D E) (p : Z2) :
    LinearMap.ker (C.directDerivedI (shiftK p)) =
      LinearMap.ker (C.incomingDerivedI p) := by
  let eDirect :=
    LinearEquiv.cast
      (R := R) (M := fun s => C.DerivedD s)
      (directDerivedI_index (shiftK p))
  let eIncoming :=
    LinearEquiv.cast
      (R := R) (M := fun s => C.DerivedD s)
      (shiftI_derivedIPreIndex p)
  apply le_antisymm
  · intro x hx
    have hraw :
        C.derivedI (shiftIPre (shiftK p)) x = 0 := by
      apply eDirect.injective
      exact hx.trans (map_zero eDirect).symm
    change
      eIncoming
        (C.derivedI (shiftIPre (shiftK p)) x) = 0
    rw [hraw]
    exact map_zero eIncoming
  · intro x hx
    have hraw :
        C.derivedI (shiftIPre (shiftK p)) x = 0 := by
      apply eIncoming.injective
      exact hx.trans (map_zero eIncoming).symm
    change
      eDirect
        (C.derivedI (shiftIPre (shiftK p)) x) = 0
    rw [hraw]
    exact map_zero eDirect

/-- Exactness of the naturally graded first-derived maps at the second `D₁` vertex. -/
theorem directDerived_exact_ki
    (C : ExactCouple R D E) (p : Z2) :
    LinearMap.ker (C.directDerivedI (shiftKEquiv p)) =
      LinearMap.range (C.directDerivedK p) := by
  change
    LinearMap.ker (C.directDerivedI (shiftK p)) =
      LinearMap.range (C.directDerivedK p)
  rw [C.directDerivedI_ker_eq_incomingDerivedI p]
  exact C.incomingDerivedI_exact_directDerivedK p

/-- The genuine first derived graded exact couple. -/
noncomputable def firstDerivedGradedExactCouple
    (C : ExactCouple R D E) :
    GradedExactCouple R Z2
      (fun p => (C.DirectDerivedD p : Type u))
      (fun p => C.DirectDerivedE p)
      (GradedExactCouple.derivedIDegree shiftIEquiv)
      (GradedExactCouple.derivedJDegree
        shiftIEquiv (Equiv.refl Z2))
      (GradedExactCouple.derivedKDegree shiftKEquiv) where
  i := C.directDerivedI
  j := C.directDerivedJ
  k := C.directDerivedK
  exact_ij := C.directDerived_exact_ij
  exact_jk := C.directDerived_exact_jk
  exact_ki := C.directDerived_exact_ki

@[simp]
theorem firstDerivedGradedExactCouple_i
    (C : ExactCouple R D E) (p : Z2) :
    C.firstDerivedGradedExactCouple.i p =
      C.directDerivedI p :=
  rfl

@[simp]
theorem firstDerivedGradedExactCouple_j
    (C : ExactCouple R D E) (p : Z2) :
    C.firstDerivedGradedExactCouple.j p =
      C.directDerivedJ p :=
  rfl

@[simp]
theorem firstDerivedGradedExactCouple_k
    (C : ExactCouple R D E) (p : Z2) :
    C.firstDerivedGradedExactCouple.k p =
      C.directDerivedK p :=
  rfl

end ExactCouple

end InfoGeometry.Spectral.Algebra
