import InfoGeometry.Spectral.Algebra.DerivedPage
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The image component of the derived exact couple

For an exact couple `(D, E, i, j, k)`, the `D`-object of the derived couple is
the image of `i`.  The induced map `i'` is the restriction of the next `i` map
to these image submodules.
-/

namespace InfoGeometry.Spectral.Algebra

universe u

namespace ExactCouple

variable {R : Type u} [Ring R]
variable {D E : Z2 → Type u}
variable [∀ pq, AddCommGroup (D pq)] [∀ pq, AddCommGroup (E pq)]
variable [∀ pq, Module R (D pq)] [∀ pq, Module R (E pq)]

/-- The `D`-object of the derived couple: the image of the original `i`. -/
abbrev DerivedD (C : ExactCouple R D E) (pq : Z2) :=
  LinearMap.range (C.i pq)

/--
The induced map `i' : image(i_pq) → image(i_(shiftI pq))`.

An image element is already an element of `D (shiftI pq)`, so applying the next
`i` lands definitionally in the next image, with the element itself as witness.
-/
def derivedI (C : ExactCouple R D E) (pq : Z2) :
    C.DerivedD pq →ₗ[R] C.DerivedD (shiftI pq) where
  toFun x :=
    ⟨C.i (shiftI pq) x.1, ⟨x.1, rfl⟩⟩
  map_add' x y := by
    ext
    exact map_add (C.i (shiftI pq)) x.1 y.1
  map_smul' r x := by
    ext
    exact map_smul (C.i (shiftI pq)) r x.1

@[simp]
theorem derivedI_coe
    (C : ExactCouple R D E) (pq : Z2) (x : C.DerivedD pq) :
    ((C.derivedI pq x : C.DerivedD (shiftI pq)) :
      D (shiftI (shiftI pq))) =
      C.i (shiftI pq) x :=
  rfl

/-- On an explicit image representative, `i'` is the next composite of `i`. -/
@[simp]
theorem derivedI_imageRepresentative
    (C : ExactCouple R D E) (pq : Z2) (x : D pq) :
    C.derivedI pq
        ⟨C.i pq x, ⟨x, rfl⟩⟩ =
      ⟨C.i (shiftI pq) (C.i pq x), ⟨C.i pq x, rfl⟩⟩ :=
  rfl

/-- Every value of the induced `i'` lies in the next original `i`-range. -/
theorem derivedI_mem_next_range
    (C : ExactCouple R D E) (pq : Z2) (x : C.DerivedD pq) :
    C.i (shiftI pq) x ∈ LinearMap.range (C.i (shiftI pq)) :=
  ⟨x, rfl⟩

/-- The original `j` map, with codomain restricted to cycles at `shiftK pq`. -/
def jToTargetCycles (C : ExactCouple R D E) (pq : Z2) :
    D (shiftK pq) →ₗ[R] C.targetCycles pq where
  toFun x := by
    refine ⟨C.j (shiftK pq) x, ?_⟩
    have hj :
        C.j (shiftK pq) x ∈
          LinearMap.range (C.j (shiftK pq)) :=
      ⟨x, rfl⟩
    have hk :
        C.k (shiftK pq) (C.j (shiftK pq) x) = 0 := by
      change C.j (shiftK pq) x ∈
        LinearMap.ker (C.k (shiftK pq))
      rw [C.exact_jk (shiftK pq)]
      exact hj
    simp [targetCycles, differential, LinearMap.comp_apply, hk]
  map_add' x y := by
    ext
    exact map_add (C.j (shiftK pq)) x y
  map_smul' r x := by
    ext
    exact map_smul (C.j (shiftK pq)) r x

/-- The map `D_(shiftK pq) → H(E,d)` induced by `j`. -/
def jToDerivedE (C : ExactCouple R D E) (pq : Z2) :
    D (shiftK pq) →ₗ[R] C.DerivedE pq :=
  (C.targetBoundariesInCycles pq).mkQ.comp (C.jToTargetCycles pq)

/--
The kernel of `i_(shiftK pq)` is killed by the homology class of `j`.

This is the essential representative-independence argument:
`ker i = range k`, and `j (k y) = d y` is a boundary.
-/
theorem ker_i_le_ker_jToDerivedE
    (C : ExactCouple R D E) (pq : Z2) :
    LinearMap.ker (C.i (shiftK pq)) ≤
      LinearMap.ker (C.jToDerivedE pq) := by
  intro x hx
  have hxrange :
      x ∈ LinearMap.range (C.k pq) := by
    rw [← C.exact_ki pq]
    exact hx
  rcases hxrange with ⟨y, rfl⟩
  apply (Submodule.Quotient.mk_eq_zero _).2
  change C.differential pq y ∈ C.targetBoundaries pq
  exact ⟨y, rfl⟩

/-- The `j` map factored through `D / ker i`. -/
def derivedJOnQuotient (C : ExactCouple R D E) (pq : Z2) :
    D (shiftK pq) ⧸ LinearMap.ker (C.i (shiftK pq)) →ₗ[R]
      C.DerivedE pq :=
  (LinearMap.ker (C.i (shiftK pq))).liftQ
    (C.jToDerivedE pq) (C.ker_i_le_ker_jToDerivedE pq)

/--
The derived exact-couple map
`j' : range(i_(shiftK pq)) → H(E,d)`.

Mathlib's first isomorphism theorem supplies
`D / ker i ≃ range i`; no representative is chosen.
-/
noncomputable def derivedJ (C : ExactCouple R D E) (pq : Z2) :
    C.DerivedD (shiftK pq) →ₗ[R] C.DerivedE pq :=
  (C.derivedJOnQuotient pq).comp
    (C.i (shiftK pq)).quotKerEquivRange.symm.toLinearMap

/-- On an image representative, `j' (i x)` is the homology class of `j x`. -/
@[simp]
theorem derivedJ_imageRepresentative
    (C : ExactCouple R D E) (pq : Z2)
    (x : D (shiftK pq)) :
    C.derivedJ pq
        ⟨C.i (shiftK pq) x, ⟨x, rfl⟩⟩ =
      C.jToDerivedE pq x := by
  simp [derivedJ, derivedJOnQuotient]

/-- The derived `D` index receiving the map from `DerivedE C pq`. -/
def derivedKIndex (pq : Z2) : Z2 :=
  shiftIPre (shiftK (shiftK pq))

@[simp]
theorem shiftI_derivedKIndex (pq : Z2) :
    shiftI (derivedKIndex pq) = shiftK (shiftK pq) :=
  shiftI_shiftIPre _

/-- Vanishing under `j` is preserved by canonical reindexing. -/
theorem j_cast_eq_zero
    (C : ExactCouple R D E) {pq pq' : Z2}
    (h : pq = pq') (x : D pq)
    (hx : C.j pq x = 0) :
    C.j pq' (LinearEquiv.cast (R := R) (M := D) h x) = 0 := by
  subst pq'
  simpa using hx

/-- The original target `k` map, canonically reindexed to the derived `D` degree. -/
def reindexedTargetK
    (C : ExactCouple R D E) (pq : Z2) :
    E (shiftK pq) →ₗ[R] D (shiftI (derivedKIndex pq)) :=
  (LinearEquiv.cast (R := R) (M := D)
    (shiftI_derivedKIndex pq).symm).toLinearMap.comp
      (C.k (shiftK pq))

/--
The map from target cycles to the next derived `D` object.

For a cycle `x`, the equation `j (k x) = d x = 0` and exactness
`ker j = range i` put `k x` in the required image of `i`.
-/
def kTargetCyclesToDerivedD
    (C : ExactCouple R D E) (pq : Z2) :
    C.targetCycles pq →ₗ[R] C.DerivedD (derivedKIndex pq) where
  toFun x := by
    refine ⟨C.reindexedTargetK pq x.1, ?_⟩
    change C.reindexedTargetK pq x.1 ∈
      LinearMap.range (C.i (derivedKIndex pq))
    rw [← C.exact_ij (derivedKIndex pq)]
    apply C.j_cast_eq_zero (shiftI_derivedKIndex pq).symm
    exact x.2
  map_add' x y := by
    ext
    exact map_add (C.reindexedTargetK pq) x.1 y.1
  map_smul' r x := by
    ext
    exact map_smul (C.reindexedTargetK pq) r x.1

/-- Target boundaries lie in the kernel of the cycle-level derived `k` map. -/
theorem targetBoundariesInCycles_le_ker_kTargetCyclesToDerivedD
    (C : ExactCouple R D E) (pq : Z2) :
    C.targetBoundariesInCycles pq ≤
      LinearMap.ker (C.kTargetCyclesToDerivedD pq) := by
  intro x hx
  change x.1 ∈ C.targetBoundaries pq at hx
  rcases hx with ⟨y, hy⟩
  apply Subtype.ext
  change C.reindexedTargetK pq x.1 = 0
  rw [← hy]
  have hmem :
      C.j (shiftK pq) (C.k pq y) ∈
        LinearMap.range (C.j (shiftK pq)) :=
    ⟨C.k pq y, rfl⟩
  have hzero :
      C.k (shiftK pq)
        (C.j (shiftK pq) (C.k pq y)) = 0 := by
    change C.j (shiftK pq) (C.k pq y) ∈
      LinearMap.ker (C.k (shiftK pq))
    rw [C.exact_jk (shiftK pq)]
    exact hmem
  simpa [reindexedTargetK, differential, LinearMap.comp_apply, hzero] using
    (map_zero
      (LinearEquiv.cast (R := R) (M := D)
        (shiftI_derivedKIndex pq).symm))

/--
The derived exact-couple map `k'` on homology classes.

It is induced by the cycle-level `k` map because every boundary maps to zero.
-/
def derivedK (C : ExactCouple R D E) (pq : Z2) :
    C.DerivedE pq →ₗ[R] C.DerivedD (derivedKIndex pq) :=
  (C.targetBoundariesInCycles pq).liftQ
    (C.kTargetCyclesToDerivedD pq)
    (C.targetBoundariesInCycles_le_ker_kTargetCyclesToDerivedD pq)

/-- `k'` sends an explicit cycle class to the reindexed original `k` value. -/
@[simp]
theorem derivedK_targetCycleClass
    (C : ExactCouple R D E) (pq : Z2)
    (x : E (shiftK pq))
    (hx : C.differential (shiftK pq) x = 0) :
    C.derivedK pq (C.targetCycleClass pq x hx) =
      C.kTargetCyclesToDerivedD pq ⟨x, hx⟩ := by
  simp [derivedK, targetCycleClass]

/-- The derived `k` map kills the homology class induced by `j`. -/
@[simp]
theorem derivedK_jToDerivedE_eq_zero
    (C : ExactCouple R D E) (pq : Z2)
    (x : D (shiftK pq)) :
    C.derivedK pq (C.jToDerivedE pq x) = 0 := by
  apply Subtype.ext
  change C.reindexedTargetK pq (C.j (shiftK pq) x) = 0
  have hmem :
      C.j (shiftK pq) x ∈
        LinearMap.range (C.j (shiftK pq)) :=
    ⟨x, rfl⟩
  have hzero :
      C.k (shiftK pq) (C.j (shiftK pq) x) = 0 := by
    change C.j (shiftK pq) x ∈
      LinearMap.ker (C.k (shiftK pq))
    rw [C.exact_jk (shiftK pq)]
    exact hmem
  simpa [reindexedTargetK, hzero] using
    (map_zero
      (LinearEquiv.cast (R := R) (M := D)
        (shiftI_derivedKIndex pq).symm))

/-- The first derived triangle relation: `k' ∘ j' = 0`. -/
theorem derivedK_comp_derivedJ
    (C : ExactCouple R D E) (pq : Z2) :
    (C.derivedK pq).comp (C.derivedJ pq) = 0 := by
  ext x
  rcases x.2 with ⟨a, ha⟩
  have hx :
      x =
        ⟨C.i (shiftK pq) a, ⟨a, rfl⟩⟩ := by
    apply Subtype.ext
    exact ha.symm
  subst x
  simp

/-- One inclusion in derived exactness at `E'`: `range j' ≤ ker k'`. -/
theorem range_derivedJ_le_ker_derivedK
    (C : ExactCouple R D E) (pq : Z2) :
    LinearMap.range (C.derivedJ pq) ≤
      LinearMap.ker (C.derivedK pq) := by
  rw [LinearMap.range_le_ker_iff]
  exact C.derivedK_comp_derivedJ pq

/-- The reverse inclusion at the derived `E` object: `ker k' ≤ range j'`. -/
theorem ker_derivedK_le_range_derivedJ
    (C : ExactCouple R D E) (pq : Z2) :
    LinearMap.ker (C.derivedK pq) ≤
      LinearMap.range (C.derivedJ pq) := by
  intro z hz
  revert hz
  refine Submodule.Quotient.induction_on
    (C.targetBoundariesInCycles pq) z ?_
  intro x hx
  have hkDerived :
      C.kTargetCyclesToDerivedD pq x = 0 := by
    simpa [derivedK] using hx
  have hkCast :
      C.reindexedTargetK pq x.1 = 0 := by
    exact congrArg Subtype.val hkDerived
  have hk :
      C.k (shiftK pq) x.1 = 0 := by
    let e :=
      LinearEquiv.cast (R := R) (M := D)
        (shiftI_derivedKIndex pq).symm
    apply e.injective
    exact hkCast.trans (map_zero e).symm
  have hxRange :
      x.1 ∈ LinearMap.range (C.j (shiftK pq)) := by
    rw [← C.exact_jk (shiftK pq)]
    exact hk
  rcases hxRange with ⟨a, ha⟩
  let da : C.DerivedD (shiftK pq) :=
    ⟨C.i (shiftK pq) a, ⟨a, rfl⟩⟩
  refine ⟨da, ?_⟩
  rw [show C.derivedJ pq da = C.jToDerivedE pq a by
    exact C.derivedJ_imageRepresentative pq a]
  have hcycles :
      C.jToTargetCycles pq a = x := by
    apply Subtype.ext
    exact ha
  subst x
  rfl

/-- Exactness of the derived couple at `E'`: `ker k' = range j'`. -/
theorem derived_exact_jk
    (C : ExactCouple R D E) (pq : Z2) :
    LinearMap.ker (C.derivedK pq) =
      LinearMap.range (C.derivedJ pq) :=
  le_antisymm
    (C.ker_derivedK_le_range_derivedJ pq)
    (C.range_derivedJ_le_ker_derivedK pq)

/-- The derived `D` index immediately preceding the domain of `derivedJ pq`. -/
def derivedIPreIndex (pq : Z2) : Z2 :=
  shiftIPre (shiftK pq)

@[simp]
theorem shiftI_derivedIPreIndex (pq : Z2) :
    shiftI (derivedIPreIndex pq) = shiftK pq :=
  shiftI_shiftIPre _

/--
The incoming `i'` map at the `D'` vertex on which `derivedJ pq` is defined.

The only reindexing is Mathlib's canonical `LinearEquiv.cast` along the proved
bidegree equality `shiftI (derivedIPreIndex pq) = shiftK pq`.
-/
def incomingDerivedI
    (C : ExactCouple R D E) (pq : Z2) :
    C.DerivedD (derivedIPreIndex pq) →ₗ[R]
      C.DerivedD (shiftK pq) :=
  (LinearEquiv.cast
      (R := R) (M := fun r => C.DerivedD r)
      (shiftI_derivedIPreIndex pq)).toLinearMap.comp
    (C.derivedI (derivedIPreIndex pq))

@[simp]
theorem incomingDerivedI_apply
    (C : ExactCouple R D E) (pq : Z2)
    (x : C.DerivedD (derivedIPreIndex pq)) :
    C.incomingDerivedI pq x =
      LinearEquiv.cast
        (R := R) (M := fun r => C.DerivedD r)
        (shiftI_derivedIPreIndex pq)
        (C.derivedI (derivedIPreIndex pq) x) :=
  rfl

/-- Coercion from a reindexed derived `D` object is the corresponding cast in `D`. -/
theorem derivedD_cast_coe
    (C : ExactCouple R D E) {pq pq' : Z2}
    (h : pq = pq') (x : C.DerivedD pq) :
    ((LinearEquiv.cast
        (R := R) (M := fun r => C.DerivedD r) h x :
      C.DerivedD pq') : D (shiftI pq')) =
      LinearEquiv.cast
        (R := R) (M := D) (congrArg shiftI h) x.1 := by
  subst pq'
  rfl

/-- Applying `i` commutes with canonical reindexing of its source degree. -/
theorem i_cast_apply
    (C : ExactCouple R D E) {pq pq' : Z2}
    (h : pq = pq') (x : D pq) :
    LinearEquiv.cast
        (R := R) (M := D) (congrArg shiftI h)
        (C.i pq x) =
      C.i pq'
        (LinearEquiv.cast (R := R) (M := D) h x) := by
  subst pq'
  rfl

/-- The incoming derived `i` map is the next original `i` on a cast representative. -/
theorem incomingDerivedI_eq_image
    (C : ExactCouple R D E) (pq : Z2)
    (x : C.DerivedD (derivedIPreIndex pq)) :
    C.incomingDerivedI pq x =
      ⟨C.i (shiftK pq)
          (LinearEquiv.cast
            (R := R) (M := D)
            (shiftI_derivedIPreIndex pq) x.1),
        ⟨LinearEquiv.cast
            (R := R) (M := D)
            (shiftI_derivedIPreIndex pq) x.1,
          rfl⟩⟩ := by
  apply Subtype.ext
  rw [incomingDerivedI_apply, C.derivedD_cast_coe]
  exact C.i_cast_apply (shiftI_derivedIPreIndex pq) x.1

/-- The second derived triangle relation: `j' ∘ i' = 0`. -/
theorem derivedJ_comp_incomingDerivedI
    (C : ExactCouple R D E) (pq : Z2) :
    (C.derivedJ pq).comp (C.incomingDerivedI pq) = 0 := by
  ext x
  let h := shiftI_derivedIPreIndex pq
  let b : D (shiftK pq) :=
    LinearEquiv.cast (R := R) (M := D) h x.1
  have hxker :
      C.j (shiftI (derivedIPreIndex pq)) x.1 = 0 := by
    change x.1 ∈
      LinearMap.ker (C.j (shiftI (derivedIPreIndex pq)))
    rw [C.exact_ij (derivedIPreIndex pq)]
    exact x.2
  have hbker : C.j (shiftK pq) b = 0 := by
    exact C.j_cast_eq_zero h x.1 hxker
  change C.derivedJ pq (C.incomingDerivedI pq x) = 0
  rw [C.incomingDerivedI_eq_image pq x]
  rw [C.derivedJ_imageRepresentative pq b]
  change
    (C.targetBoundariesInCycles pq).mkQ
      (C.jToTargetCycles pq b) = 0
  have hcycle : C.jToTargetCycles pq b = 0 := by
    apply Subtype.ext
    exact hbker
  rw [hcycle, map_zero]

/-- One inclusion in derived exactness at `D'`: `range i' ≤ ker j'`. -/
theorem range_incomingDerivedI_le_ker_derivedJ
    (C : ExactCouple R D E) (pq : Z2) :
    LinearMap.range (C.incomingDerivedI pq) ≤
      LinearMap.ker (C.derivedJ pq) := by
  rw [LinearMap.range_le_ker_iff]
  exact C.derivedJ_comp_incomingDerivedI pq

/-- The reverse inclusion at the first derived `D` vertex. -/
theorem ker_derivedJ_le_range_incomingDerivedI
    (C : ExactCouple R D E) (pq : Z2) :
    LinearMap.ker (C.derivedJ pq) ≤
      LinearMap.range (C.incomingDerivedI pq) := by
  intro z hz
  rcases z.2 with ⟨a, ha⟩
  have hzrepr :
      z =
        ⟨C.i (shiftK pq) a, ⟨a, rfl⟩⟩ := by
    apply Subtype.ext
    exact ha.symm
  subst z
  have hjClass : C.jToDerivedE pq a = 0 := by
    simpa using hz
  have hjBoundary :
      C.jToTargetCycles pq a ∈
        C.targetBoundariesInCycles pq :=
    (Submodule.Quotient.mk_eq_zero _).1 hjClass
  change
    C.j (shiftK pq) a ∈ C.targetBoundaries pq
      at hjBoundary
  rcases hjBoundary with ⟨y, hy⟩
  have hy' :
      C.j (shiftK pq) (C.k pq y) =
        C.j (shiftK pq) a := by
    simpa [differential, LinearMap.comp_apply] using hy
  let delta : D (shiftK pq) := a - C.k pq y
  have hjdelta : C.j (shiftK pq) delta = 0 := by
    simp [delta, map_sub, hy']
  let h := shiftI_derivedIPreIndex pq
  let u : D (shiftI (derivedIPreIndex pq)) :=
    LinearEquiv.cast (R := R) (M := D) h.symm delta
  have hj_u :
      C.j (shiftI (derivedIPreIndex pq)) u = 0 := by
    exact C.j_cast_eq_zero h.symm delta hjdelta
  have huRange :
      u ∈ LinearMap.range
        (C.i (derivedIPreIndex pq)) := by
    rw [← C.exact_ij (derivedIPreIndex pq)]
    exact hj_u
  rcases huRange with ⟨c, hc⟩
  let dc : C.DerivedD (derivedIPreIndex pq) :=
    ⟨C.i (derivedIPreIndex pq) c, ⟨c, rfl⟩⟩
  refine ⟨dc, ?_⟩
  rw [C.incomingDerivedI_eq_image pq dc]
  apply Subtype.ext
  have hcast :
      LinearEquiv.cast (R := R) (M := D) h
          (C.i (derivedIPreIndex pq) c) =
        delta := by
    rw [hc]
    simp [u]
  have hik :
      C.i (shiftK pq) (C.k pq y) = 0 := by
    change C.k pq y ∈
      LinearMap.ker (C.i (shiftK pq))
    rw [C.exact_ki pq]
    exact ⟨y, rfl⟩
  change
    C.i (shiftK pq)
        (LinearEquiv.cast (R := R) (M := D) h
          (C.i (derivedIPreIndex pq) c)) =
      C.i (shiftK pq) a
  rw [hcast]
  simp [delta, map_sub, hik]

/-- Exactness at the first derived `D` vertex: `ker j' = range i'`. -/
theorem derived_exact_ij
    (C : ExactCouple R D E) (pq : Z2) :
    LinearMap.ker (C.derivedJ pq) =
      LinearMap.range (C.incomingDerivedI pq) :=
  le_antisymm
    (C.ker_derivedJ_le_range_incomingDerivedI pq)
    (C.range_incomingDerivedI_le_ker_derivedJ pq)

/-- The third derived triangle relation: `i' ∘ k' = 0`. -/
theorem incomingDerivedI_comp_derivedK
    (C : ExactCouple R D E) (pq : Z2) :
    (C.incomingDerivedI (shiftK pq)).comp
        (C.derivedK pq) = 0 := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply,
    Submodule.mkQ_apply]
  have hlift :
      C.derivedK pq (Submodule.Quotient.mk x) =
        C.kTargetCyclesToDerivedD pq x := by
    simpa [derivedK] using
      (Submodule.liftQ_apply
        (C.targetBoundariesInCycles pq)
        (C.kTargetCyclesToDerivedD pq) x)
  calc
    _ =
        ((C.incomingDerivedI (shiftK pq)
            (C.kTargetCyclesToDerivedD pq x) :
          C.DerivedD (shiftK (shiftK pq))) :
          D (shiftI (shiftK (shiftK pq)))) := by
      exact congrArg
        (fun t =>
          ((C.incomingDerivedI (shiftK pq) t :
            C.DerivedD (shiftK (shiftK pq))) :
            D (shiftI (shiftK (shiftK pq)))))
        hlift
    _ = 0 := by
      rw [C.incomingDerivedI_eq_image
        (shiftK pq) (C.kTargetCyclesToDerivedD pq x)]
      have hik :
          C.i (shiftK (shiftK pq))
            (C.k (shiftK pq) x.1) = 0 := by
        change C.k (shiftK pq) x.1 ∈
          LinearMap.ker (C.i (shiftK (shiftK pq)))
        rw [C.exact_ki (shiftK pq)]
        exact ⟨x.1, rfl⟩
      have harg :
          LinearEquiv.cast
              (R := R) (M := D)
              (shiftI_derivedIPreIndex (shiftK pq))
              (C.kTargetCyclesToDerivedD pq x).1 =
            C.k (shiftK pq) x.1 := by
        let e :=
          LinearEquiv.cast
            (R := R) (M := D)
            (shiftI_derivedKIndex pq)
        simpa [kTargetCyclesToDerivedD, reindexedTargetK, e] using
          e.apply_symm_apply (C.k (shiftK pq) x.1)
      rw [harg]
      exact hik

/-- One inclusion in exactness at the second derived `D` vertex. -/
theorem range_derivedK_le_ker_incomingDerivedI
    (C : ExactCouple R D E) (pq : Z2) :
    LinearMap.range (C.derivedK pq) ≤
      LinearMap.ker (C.incomingDerivedI (shiftK pq)) := by
  rw [LinearMap.range_le_ker_iff]
  exact C.incomingDerivedI_comp_derivedK pq

/-- The reverse inclusion at the second derived `D` vertex. -/
theorem ker_incomingDerivedI_le_range_derivedK
    (C : ExactCouple R D E) (pq : Z2) :
    LinearMap.ker (C.incomingDerivedI (shiftK pq)) ≤
      LinearMap.range (C.derivedK pq) := by
  intro z hz
  let h := shiftI_derivedKIndex pq
  let b : D (shiftK (shiftK pq)) :=
    LinearEquiv.cast (R := R) (M := D) h z.1
  have hib : C.i (shiftK (shiftK pq)) b = 0 := by
    have hformula :=
      C.incomingDerivedI_eq_image (shiftK pq) z
    have hformulaVal := congrArg Subtype.val hformula
    have hzVal := congrArg Subtype.val hz
    exact hformulaVal.symm.trans hzVal
  have hbRange :
      b ∈ LinearMap.range (C.k (shiftK pq)) := by
    rw [← C.exact_ki (shiftK pq)]
    exact hib
  rcases hbRange with ⟨x, hx⟩
  have hjz :
      C.j (shiftI (derivedKIndex pq)) z.1 = 0 := by
    change z.1 ∈
      LinearMap.ker (C.j (shiftI (derivedKIndex pq)))
    rw [C.exact_ij (derivedKIndex pq)]
    exact z.2
  have hjb :
      C.j (shiftK (shiftK pq)) b = 0 := by
    exact C.j_cast_eq_zero h z.1 hjz
  have hxCycle :
      C.differential (shiftK pq) x = 0 := by
    simp [differential, LinearMap.comp_apply, hx, hjb]
  refine
    ⟨C.targetCycleClass pq x hxCycle, ?_⟩
  rw [C.derivedK_targetCycleClass pq x hxCycle]
  apply Subtype.ext
  change
    LinearEquiv.cast (R := R) (M := D) h.symm
        (C.k (shiftK pq) x) =
      z.1
  rw [hx]
  let e :=
    LinearEquiv.cast (R := R) (M := D)
      (shiftI_derivedKIndex pq)
  simpa [reindexedTargetK, b, h, e] using
    e.symm_apply_apply z.1

/-- Exactness at the second derived `D` vertex: `ker i' = range k'`. -/
theorem derived_exact_ki
    (C : ExactCouple R D E) (pq : Z2) :
    LinearMap.ker (C.incomingDerivedI (shiftK pq)) =
      LinearMap.range (C.derivedK pq) :=
  le_antisymm
    (C.ker_incomingDerivedI_le_range_derivedK pq)
    (C.range_derivedK_le_ker_incomingDerivedI pq)

end ExactCouple

end InfoGeometry.Spectral.Algebra
