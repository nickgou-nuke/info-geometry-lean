import InfoGeometry.Spectral.Algebra.GenericDerivedPage
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The derived image object of an arbitrary graded exact couple

For a degree-aware exact couple, the derived `D` component in degree `p` is
the image of the unique `i` arrow whose target is `D p`.  The induced `i`
arrow is the restriction of the next original `i` arrow to these images.
-/

namespace InfoGeometry.Spectral.Algebra

universe u v

namespace GradedExactCouple

variable {R : Type u} [Ring R]
variable {I : Type v}
variable {D E : I → Type u}
variable [∀ p, AddCommGroup (D p)] [∀ p, AddCommGroup (E p)]
variable [∀ p, Module R (D p)] [∀ p, Module R (E p)]
variable {iDeg jDeg kDeg : I ≃ I}

/-- The original incoming `i` arrow, canonically reindexed to target `D p`. -/
def incomingI
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    D (iDeg.symm p) →ₗ[R] D p :=
  (LinearEquiv.cast
      (R := R) (M := D) (iDeg.apply_symm_apply p)).toLinearMap.comp
    (C.i (iDeg.symm p))

@[simp]
theorem incomingI_apply
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (x : D (iDeg.symm p)) :
    C.incomingI p x =
      LinearEquiv.cast
        (R := R) (M := D) (iDeg.apply_symm_apply p)
        (C.i (iDeg.symm p) x) :=
  rfl

/-- Applying an indexed `i` map commutes with canonical equality transport. -/
theorem i_cast_apply
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    {p q : I} (h : p = q) (x : D p) :
    LinearEquiv.cast
        (R := R) (M := D) (congrArg iDeg h)
        (C.i p x) =
      C.i q
        (LinearEquiv.cast (R := R) (M := D) h x) := by
  subst q
  rfl

/--
The naturally graded derived `D` object: the range of the unique incoming
`i` arrow, transported along `iDeg (iDeg.symm p) = p`.
-/
abbrev DirectDerivedD
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :=
  LinearMap.range (C.incomingI p)

/-- The incoming map at `iDeg p` is the original `i p`, up to canonical casts. -/
theorem incomingI_iDeg_mem
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (x : D p) :
    C.i p x ∈ LinearMap.range (C.incomingI (iDeg p)) := by
  let h : iDeg.symm (iDeg p) = p := iDeg.symm_apply_apply p
  let y : D (iDeg.symm (iDeg p)) :=
    LinearEquiv.cast (R := R) (M := D) h.symm x
  refine ⟨y, ?_⟩
  change
    LinearEquiv.cast
        (R := R) (M := D) (iDeg.apply_symm_apply (iDeg p))
        (C.i (iDeg.symm (iDeg p)) y) =
      C.i p x
  have hi := C.i_cast_apply h y
  simpa [y] using hi

/--
The induced map `i′ : D′ p → D′ (iDeg p)`.

An element of `D′ p` is already an element of `D p`; applying `i p` places it
in `range (i p) = D′ (iDeg p)`.
-/
def directDerivedI
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    C.DirectDerivedD p →ₗ[R]
      C.DirectDerivedD (derivedIDegree iDeg p) where
  toFun x :=
    ⟨C.i p x.1, C.incomingI_iDeg_mem p x.1⟩
  map_add' x y := by
    ext
    exact map_add (C.i p) x.1 y.1
  map_smul' r x := by
    ext
    exact map_smul (C.i p) r x.1

@[simp]
theorem directDerivedI_coe
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (x : C.DirectDerivedD p) :
    ((C.directDerivedI p x :
        C.DirectDerivedD (derivedIDegree iDeg p)) :
      D (derivedIDegree iDeg p)) =
      C.i p x.1 :=
  rfl

/-- On an explicit incoming-image representative, `i′` applies the next `i`. -/
@[simp]
theorem directDerivedI_imageRepresentative
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (x : D (iDeg.symm p)) :
    C.directDerivedI p
        ⟨C.incomingI p x, ⟨x, rfl⟩⟩ =
      ⟨C.i p (C.incomingI p x),
        C.incomingI_iDeg_mem p (C.incomingI p x)⟩ :=
  rfl

/-- Every value of `i′` lies in the next original `i` range. -/
theorem directDerivedI_mem_range
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (x : C.DirectDerivedD p) :
    C.i p x.1 ∈ LinearMap.range (C.incomingI (iDeg p)) :=
  C.incomingI_iDeg_mem p x.1

/-- The source-arrow index of the homology component receiving `j′` from `D′ p`. -/
def derivedJPageIndex
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) : I :=
  C.differentialDegree.symm (jDeg (iDeg.symm p))

@[simp]
theorem differentialDegree_derivedJPageIndex
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    C.differentialDegree (C.derivedJPageIndex p) =
      jDeg (iDeg.symm p) :=
  C.differentialDegree.apply_symm_apply _

/-- The original `j` map, with codomain restricted to the appropriate cycles. -/
def jToTargetCycles
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    D (iDeg.symm p) →ₗ[R]
      C.targetCycles (C.derivedJPageIndex p) where
  toFun x := by
    let h :=
      C.differentialDegree_derivedJPageIndex p
    let y : E (C.differentialDegree (C.derivedJPageIndex p)) :=
      LinearEquiv.cast (R := R) (M := E) h.symm
        (C.j (iDeg.symm p) x)
    refine ⟨y, ?_⟩
    have hjRange :
        C.j (iDeg.symm p) x ∈
          LinearMap.range (C.j (iDeg.symm p)) :=
      ⟨x, rfl⟩
    have hk :
        C.k (jDeg (iDeg.symm p))
            (C.j (iDeg.symm p) x) = 0 := by
      change C.j (iDeg.symm p) x ∈
        LinearMap.ker (C.k (jDeg (iDeg.symm p)))
      rw [C.exact_jk (iDeg.symm p)]
      exact hjRange
    have hd :
        C.differential (jDeg (iDeg.symm p))
            (C.j (iDeg.symm p) x) = 0 := by
      change
        C.j (kDeg (jDeg (iDeg.symm p)))
            (C.k (jDeg (iDeg.symm p))
              (C.j (iDeg.symm p) x)) = 0
      rw [hk]
      exact map_zero (C.j (kDeg (jDeg (iDeg.symm p))))
    let e :=
      LinearEquiv.cast
        (R := R) (M := E)
        (congrArg C.differentialDegree h)
    apply e.injective
    rw [C.differential_cast h y]
    change
      C.differential (jDeg (iDeg.symm p))
          (LinearEquiv.cast (R := R) (M := E) h y) =
        e 0
    rw [show
      LinearEquiv.cast (R := R) (M := E) h y =
          C.j (iDeg.symm p) x by
        simp [y]]
    rw [hd]
    exact (map_zero e).symm
  map_add' x y := by
    ext
    simp [map_add]
  map_smul' r x := by
    ext
    simp [map_smul]

@[simp]
theorem jToTargetCycles_coe
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (x : D (iDeg.symm p)) :
    (C.jToTargetCycles p x).1 =
      LinearEquiv.cast
        (R := R) (M := E)
        (C.differentialDegree_derivedJPageIndex p).symm
        (C.j (iDeg.symm p) x) :=
  by
    simp [jToTargetCycles]

/-- The original `j` map followed by the native homology quotient. -/
def jToDerivedE
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    D (iDeg.symm p) →ₗ[R] C.DirectDerivedE
      (derivedJDegree iDeg jDeg p) :=
  (C.targetBoundariesInCycles (C.derivedJPageIndex p)).mkQ.comp
    (C.jToTargetCycles p)

@[simp]
theorem jToDerivedE_apply
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (x : D (iDeg.symm p)) :
    C.jToDerivedE p x =
      Submodule.Quotient.mk (C.jToTargetCycles p x) :=
  rfl

/-- Applying an indexed `j` map commutes with canonical equality transport. -/
theorem j_cast_apply
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    {p q : I} (h : p = q) (x : D p) :
    LinearEquiv.cast
        (R := R) (M := E) (congrArg jDeg h)
        (C.j p x) =
      C.j q
        (LinearEquiv.cast (R := R) (M := D) h x) := by
  subst q
  rfl

/-- The target of the preceding `k` arrow is the source of `incomingI p`. -/
theorem kDeg_derivedJPageIndex
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    kDeg (C.derivedJPageIndex p) = iDeg.symm p := by
  apply jDeg.injective
  exact C.differentialDegree_derivedJPageIndex p

/-- The homology source used by `j′` is the source of the preceding `k` arrow. -/
theorem derivedJPageIndex_eq_kDeg_symm
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    C.derivedJPageIndex p =
      kDeg.symm (iDeg.symm p) := by
  apply kDeg.injective
  rw [C.kDeg_derivedJPageIndex]
  exact (kDeg.apply_symm_apply (iDeg.symm p)).symm

/-- The `k` arrow entering the source of `incomingI p`, canonically reindexed. -/
def incomingKToIPre
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    E (C.derivedJPageIndex p) →ₗ[R] D (iDeg.symm p) :=
  (LinearEquiv.cast
      (R := R) (M := D)
      (C.kDeg_derivedJPageIndex p)).toLinearMap.comp
    (C.k (C.derivedJPageIndex p))

/-- Exactness supplies a `k`-preimage for every element killed by the incoming `i`. -/
theorem exists_incomingKToIPre_of_incomingI_eq_zero
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (x : D (iDeg.symm p))
    (hx : C.incomingI p x = 0) :
    ∃ y : E (C.derivedJPageIndex p),
      C.incomingKToIPre p y = x := by
  let hi := iDeg.apply_symm_apply p
  have hix : C.i (iDeg.symm p) x = 0 := by
    let e := LinearEquiv.cast (R := R) (M := D) hi
    apply e.injective
    exact hx.trans (map_zero e).symm
  let q := C.derivedJPageIndex p
  let hk : kDeg q = iDeg.symm p :=
    C.kDeg_derivedJPageIndex p
  let x₀ : D (kDeg q) :=
    LinearEquiv.cast (R := R) (M := D) hk.symm x
  have hix₀ : C.i (kDeg q) x₀ = 0 := by
    let e :=
      LinearEquiv.cast (R := R) (M := D) (congrArg iDeg hk)
    apply e.injective
    rw [C.i_cast_apply hk x₀]
    change C.i (iDeg.symm p)
      (LinearEquiv.cast (R := R) (M := D) hk x₀) = e 0
    rw [show
      LinearEquiv.cast (R := R) (M := D) hk x₀ = x by
        simp [x₀]]
    rw [hix]
    exact (map_zero e).symm
  have hxRange :
      x₀ ∈ LinearMap.range (C.k q) := by
    rw [← C.exact_ki q]
    exact hix₀
  rcases hxRange with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  change
    LinearEquiv.cast (R := R) (M := D) hk (C.k q y) = x
  rw [hy]
  simp [x₀]

/--
The kernel of the incoming `i` map is killed by the homology class induced by
`j`.  This is the representative-independence theorem needed by
`LinearMap.quotKerEquivRange`.
-/
theorem ker_incomingI_le_ker_jToDerivedE
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    LinearMap.ker (C.incomingI p) ≤
      LinearMap.ker (C.jToDerivedE p) := by
  intro x hx
  rcases C.exists_incomingKToIPre_of_incomingI_eq_zero p x hx with
    ⟨y, hy⟩
  apply (Submodule.Quotient.mk_eq_zero _).2
  change
    (C.jToTargetCycles p x).1 ∈
      C.targetBoundaries (C.derivedJPageIndex p)
  refine ⟨y, ?_⟩
  change
    C.differential (C.derivedJPageIndex p) y =
      (C.jToTargetCycles p x).1
  let ht := C.differentialDegree_derivedJPageIndex p
  let et := LinearEquiv.cast (R := R) (M := E) ht
  apply et.injective
  change
    et
        (C.j (kDeg (C.derivedJPageIndex p))
          (C.k (C.derivedJPageIndex p) y)) =
      et (C.jToTargetCycles p x).1
  rw [C.jToTargetCycles_coe]
  rw [show
    et
        (LinearEquiv.cast (R := R) (M := E) ht.symm
          (C.j (iDeg.symm p) x)) =
      C.j (iDeg.symm p) x by
        exact et.apply_symm_apply (C.j (iDeg.symm p) x)]
  let hk := C.kDeg_derivedJPageIndex p
  have hy' :
      LinearEquiv.cast (R := R) (M := D) hk
          (C.k (C.derivedJPageIndex p) y) = x := by
    exact hy
  have hj :=
    C.j_cast_apply hk
      (C.k (C.derivedJPageIndex p) y)
  change
    LinearEquiv.cast (R := R) (M := E) (congrArg jDeg hk)
        (C.j (kDeg (C.derivedJPageIndex p))
          (C.k (C.derivedJPageIndex p) y)) =
      C.j (iDeg.symm p)
        (LinearEquiv.cast (R := R) (M := D) hk
          (C.k (C.derivedJPageIndex p) y)) at hj
  rw [hy'] at hj
  exact hj

/-- The map `j` factored through the quotient by the kernel of incoming `i`. -/
def directDerivedJOnQuotient
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    D (iDeg.symm p) ⧸ LinearMap.ker (C.incomingI p) →ₗ[R]
      C.DirectDerivedE (derivedJDegree iDeg jDeg p) :=
  (LinearMap.ker (C.incomingI p)).liftQ
    (C.jToDerivedE p) (C.ker_incomingI_le_ker_jToDerivedE p)

/--
The generic derived map `j′`, obtained from Mathlib's first isomorphism
theorem.  No representative of an image element is chosen.
-/
noncomputable def directDerivedJ
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    C.DirectDerivedD p →ₗ[R]
      C.DirectDerivedE (derivedJDegree iDeg jDeg p) :=
  (C.directDerivedJOnQuotient p).comp
    (C.incomingI p).quotKerEquivRange.symm.toLinearMap

/-- On an explicit incoming-image representative, `j′` is the homology class of `j`. -/
@[simp]
theorem directDerivedJ_imageRepresentative
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (x : D (iDeg.symm p)) :
    C.directDerivedJ p
        ⟨C.incomingI p x, ⟨x, rfl⟩⟩ =
      C.jToDerivedE p x := by
  change
    C.directDerivedJOnQuotient p
        ((C.incomingI p).quotKerEquivRange.symm
          ⟨C.incomingI p x, ⟨x, rfl⟩⟩) =
      C.jToDerivedE p x
  let e := (C.incomingI p).quotKerEquivRange
  have hq :
      e.symm ⟨C.incomingI p x, ⟨x, rfl⟩⟩ =
        Submodule.Quotient.mk x := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    rfl
  rw [hq]
  exact Submodule.liftQ_apply
    (LinearMap.ker (C.incomingI p))
    (C.jToDerivedE p) x

/-- Applying an indexed `k` map commutes with canonical equality transport. -/
theorem k_cast_apply
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    {p q : I} (h : p = q) (x : E p) :
    LinearEquiv.cast
        (R := R) (M := D) (congrArg kDeg h)
        (C.k p x) =
      C.k q
        (LinearEquiv.cast (R := R) (M := E) h x) := by
  subst q
  rfl

/-- A naturally indexed derived cycle, transported to its actual degree. -/
def directCycleValue
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I)
    (x : C.targetCycles (C.differentialDegree.symm p)) : E p :=
  LinearEquiv.cast
    (R := R) (M := E)
    (C.differentialDegree.apply_symm_apply p) x.1

/-- The transported value of a derived cycle remains a cycle in degree `p`. -/
theorem differential_directCycleValue_eq_zero
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I)
    (x : C.targetCycles (C.differentialDegree.symm p)) :
    C.differential p (C.directCycleValue p x) = 0 := by
  let q := C.differentialDegree.symm p
  let h : C.differentialDegree q = p :=
    C.differentialDegree.apply_symm_apply p
  have hn :=
    C.differential_cast h x.1
  change
    LinearEquiv.cast
        (R := R) (M := E) (congrArg C.differentialDegree h)
        (C.differential (C.differentialDegree q) x.1) =
      C.differential p (C.directCycleValue p x) at hn
  rw [x.2] at hn
  exact hn.symm.trans
    (map_zero
      (LinearEquiv.cast
        (R := R) (M := E)
        (congrArg C.differentialDegree h)))

/-- The `k` value of a cycle lies in the next derived `D` image. -/
theorem k_directCycleValue_mem_DirectDerivedD
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I)
    (x : C.targetCycles (C.differentialDegree.symm p)) :
    C.k p (C.directCycleValue p x) ∈
      C.DirectDerivedD (derivedKDegree kDeg p) := by
  let b : D (kDeg p) := C.k p (C.directCycleValue p x)
  let r := iDeg.symm (kDeg p)
  let hi : iDeg r = kDeg p := iDeg.apply_symm_apply (kDeg p)
  let b₀ : D (iDeg r) :=
    LinearEquiv.cast (R := R) (M := D) hi.symm b
  have hjb : C.j (kDeg p) b = 0 :=
    C.differential_directCycleValue_eq_zero p x
  have hjb₀ : C.j (iDeg r) b₀ = 0 := by
    let e :=
      LinearEquiv.cast (R := R) (M := E) (congrArg jDeg hi)
    apply e.injective
    rw [C.j_cast_apply hi b₀]
    change
      C.j (kDeg p)
          (LinearEquiv.cast (R := R) (M := D) hi b₀) =
        e 0
    rw [show
      LinearEquiv.cast (R := R) (M := D) hi b₀ = b by
        simp [b₀]]
    rw [hjb]
    exact (map_zero e).symm
  have hbRange :
      b₀ ∈ LinearMap.range (C.i r) := by
    rw [← C.exact_ij r]
    exact hjb₀
  rcases hbRange with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  change
    LinearEquiv.cast (R := R) (M := D) hi (C.i r a) = b
  rw [ha]
  simp [b₀]

/--
The original `k` map on cycles, with codomain restricted to the derived image
object.  The image condition follows from `ker j = range i`.
-/
def kTargetCyclesToDirectDerivedD
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    C.targetCycles (C.differentialDegree.symm p) →ₗ[R]
      C.DirectDerivedD (derivedKDegree kDeg p) where
  toFun x :=
    ⟨C.k p (C.directCycleValue p x),
      C.k_directCycleValue_mem_DirectDerivedD p x⟩
  map_add' x y := by
    ext
    simp [directCycleValue, map_add]
  map_smul' r x := by
    ext
    simp [directCycleValue, map_smul]

@[simp]
theorem kTargetCyclesToDirectDerivedD_coe
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I)
    (x : C.targetCycles (C.differentialDegree.symm p)) :
    (C.kTargetCyclesToDirectDerivedD p x).1 =
      C.k p (C.directCycleValue p x) :=
  rfl

/-- Incoming boundaries are killed by the cycle-level derived `k` map. -/
theorem targetBoundariesInCycles_le_ker_kTargetCyclesToDirectDerivedD
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    C.targetBoundariesInCycles (C.differentialDegree.symm p) ≤
      LinearMap.ker (C.kTargetCyclesToDirectDerivedD p) := by
  intro x hx
  let q := C.differentialDegree.symm p
  change x.1 ∈ C.targetBoundaries q at hx
  rcases hx with ⟨y, hy⟩
  apply Subtype.ext
  change C.k p (C.directCycleValue p x) = 0
  let h : C.differentialDegree q = p :=
    C.differentialDegree.apply_symm_apply p
  have hkRange :
      C.j (kDeg q) (C.k q y) ∈
        LinearMap.range (C.j (kDeg q)) :=
    ⟨C.k q y, rfl⟩
  have hk0 :
      C.k (C.differentialDegree q)
          (C.differential q y) = 0 := by
    change
      C.k (jDeg (kDeg q))
          (C.j (kDeg q) (C.k q y)) = 0
    change C.j (kDeg q) (C.k q y) ∈
      LinearMap.ker (C.k (jDeg (kDeg q)))
    rw [C.exact_jk (kDeg q)]
    exact hkRange
  have hcast :=
    C.k_cast_apply h (C.differential q y)
  have hkTransported :
      C.k p
          (LinearEquiv.cast
            (R := R) (M := E) h (C.differential q y)) = 0 := by
    rw [hk0] at hcast
    exact hcast.symm.trans
      (map_zero
        (LinearEquiv.cast
          (R := R) (M := D) (congrArg kDeg h)))
  rw [show
    C.directCycleValue p x =
        LinearEquiv.cast
          (R := R) (M := E) h (C.differential q y) by
      simp only [directCycleValue, q]
      rw [hy]]
  exact hkTransported

/--
The generic derived map `k′`, induced on homology by the cycle-level `k` map.
The descent uses Mathlib's quotient universal property.
-/
def directDerivedK
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    C.DirectDerivedE p →ₗ[R]
      C.DirectDerivedD (derivedKDegree kDeg p) :=
  (C.targetBoundariesInCycles (C.differentialDegree.symm p)).liftQ
    (C.kTargetCyclesToDirectDerivedD p)
    (C.targetBoundariesInCycles_le_ker_kTargetCyclesToDirectDerivedD p)

/-- `k′` sends a represented cycle class to the original `k` value. -/
@[simp]
theorem directDerivedK_mk
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I)
    (x : C.targetCycles (C.differentialDegree.symm p)) :
    C.directDerivedK p (Submodule.Quotient.mk x) =
      C.kTargetCyclesToDirectDerivedD p x :=
  Submodule.liftQ_apply
    (C.targetBoundariesInCycles (C.differentialDegree.symm p))
    (C.kTargetCyclesToDirectDerivedD p) x

/-- The derived `k′` map kills every homology class induced by `j`. -/
@[simp]
theorem directDerivedK_jToDerivedE_eq_zero
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (x : D (iDeg.symm p)) :
    C.directDerivedK (derivedJDegree iDeg jDeg p)
        (C.jToDerivedE p x) = 0 := by
  rw [C.jToDerivedE_apply]
  rw [C.directDerivedK_mk]
  apply Subtype.ext
  rw [C.kTargetCyclesToDirectDerivedD_coe]
  change
    C.k (jDeg (iDeg.symm p))
        (C.directCycleValue
          (jDeg (iDeg.symm p)) (C.jToTargetCycles p x)) = 0
  have hvalue :
      C.directCycleValue
          (jDeg (iDeg.symm p)) (C.jToTargetCycles p x) =
        C.j (iDeg.symm p) x := by
    let h :=
      C.differentialDegree.apply_symm_apply
        (jDeg (iDeg.symm p))
    let e := LinearEquiv.cast (R := R) (M := E) h
    change
      e
          (LinearEquiv.cast
            (R := R) (M := E)
            (C.differentialDegree_derivedJPageIndex p).symm
            (C.j (iDeg.symm p) x)) =
        C.j (iDeg.symm p) x
    exact e.apply_symm_apply (C.j (iDeg.symm p) x)
  rw [hvalue]
  change C.j (iDeg.symm p) x ∈
    LinearMap.ker (C.k (jDeg (iDeg.symm p)))
  rw [C.exact_jk (iDeg.symm p)]
  exact ⟨x, rfl⟩

/-- The first generic derived triangle relation: `k′ ∘ j′ = 0`. -/
theorem directDerivedK_comp_directDerivedJ
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    (C.directDerivedK (derivedJDegree iDeg jDeg p)).comp
        (C.directDerivedJ p) = 0 := by
  apply LinearMap.ext
  intro z
  rcases z.2 with ⟨x, hx⟩
  have hz :
      z = ⟨C.incomingI p x, ⟨x, rfl⟩⟩ := by
    apply Subtype.ext
    exact hx.symm
  subst z
  change
    C.directDerivedK (derivedJDegree iDeg jDeg p)
        (C.directDerivedJ p
          ⟨C.incomingI p x, ⟨x, rfl⟩⟩) = 0
  rw [C.directDerivedJ_imageRepresentative]
  exact C.directDerivedK_jToDerivedE_eq_zero p x

/-- One inclusion in generic derived exactness at `E′`. -/
theorem range_directDerivedJ_le_ker_directDerivedK
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    LinearMap.range (C.directDerivedJ p) ≤
      LinearMap.ker
        (C.directDerivedK (derivedJDegree iDeg jDeg p)) := by
  rw [LinearMap.range_le_ker_iff]
  exact C.directDerivedK_comp_directDerivedJ p

/-- The reverse inclusion in generic derived exactness at `E′`. -/
theorem ker_directDerivedK_le_range_directDerivedJ
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    LinearMap.ker
        (C.directDerivedK (derivedJDegree iDeg jDeg p)) ≤
      LinearMap.range (C.directDerivedJ p) := by
  intro z hz
  revert hz
  refine Submodule.Quotient.induction_on
    (C.targetBoundariesInCycles (C.derivedJPageIndex p)) z ?_
  intro x hx
  have hkDerived :
      C.kTargetCyclesToDirectDerivedD
          (derivedJDegree iDeg jDeg p) x = 0 := by
    simpa [directDerivedK] using hx
  have hk :
      C.k (jDeg (iDeg.symm p))
          (C.directCycleValue (jDeg (iDeg.symm p)) x) = 0 := by
    exact congrArg Subtype.val hkDerived
  have hxRange :
      C.directCycleValue (jDeg (iDeg.symm p)) x ∈
        LinearMap.range (C.j (iDeg.symm p)) := by
    rw [← C.exact_jk (iDeg.symm p)]
    exact hk
  rcases hxRange with ⟨a, ha⟩
  let da : C.DirectDerivedD p :=
    ⟨C.incomingI p a, ⟨a, rfl⟩⟩
  refine ⟨da, ?_⟩
  rw [show
    C.directDerivedJ p da = C.jToDerivedE p a by
      exact C.directDerivedJ_imageRepresentative p a]
  rw [C.jToDerivedE_apply]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  rw [C.jToTargetCycles_coe]
  let h :=
    C.differentialDegree.apply_symm_apply
      (jDeg (iDeg.symm p))
  let e := LinearEquiv.cast (R := R) (M := E) h
  change
    e.symm (C.j (iDeg.symm p) a) = x.1
  rw [ha]
  exact e.symm_apply_apply x.1

/-- Exactness of the generic derived couple at `E′`. -/
theorem directDerived_exact_jk
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    LinearMap.ker
        (C.directDerivedK (derivedJDegree iDeg jDeg p)) =
      LinearMap.range (C.directDerivedJ p) :=
  le_antisymm
    (C.ker_directDerivedK_le_range_directDerivedJ p)
    (C.range_directDerivedJ_le_ker_directDerivedK p)

/-- Canonical inverse transport realizes the incoming `i` arrow at `iDeg p`. -/
theorem incomingI_iDeg_cast
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (x : D p) :
    C.incomingI (iDeg p)
        (LinearEquiv.cast
          (R := R) (M := D)
          (iDeg.symm_apply_apply p).symm x) =
      C.i p x := by
  let h : iDeg.symm (iDeg p) = p := iDeg.symm_apply_apply p
  let y : D (iDeg.symm (iDeg p)) :=
    LinearEquiv.cast (R := R) (M := D) h.symm x
  change
    LinearEquiv.cast
        (R := R) (M := D) (iDeg.apply_symm_apply (iDeg p))
        (C.i (iDeg.symm (iDeg p)) y) =
      C.i p x
  have hi := C.i_cast_apply h y
  simpa [y] using hi

/-- Every element of the derived image `D′ p` is killed by the original `j p`. -/
theorem j_eq_zero_of_mem_DirectDerivedD
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (x : C.DirectDerivedD p) :
    C.j p x.1 = 0 := by
  rcases x.2 with ⟨a, ha⟩
  let r := iDeg.symm p
  let h : iDeg r = p := iDeg.apply_symm_apply p
  have hiRange :
      C.i r a ∈ LinearMap.range (C.i r) :=
    ⟨a, rfl⟩
  have hj :
      C.j (iDeg r) (C.i r a) = 0 := by
    change C.i r a ∈ LinearMap.ker (C.j (iDeg r))
    rw [C.exact_ij r]
    exact hiRange
  have hjCast := C.j_cast_apply h (C.i r a)
  rw [hj] at hjCast
  have hzero :
      C.j p
          (LinearEquiv.cast
            (R := R) (M := D) h (C.i r a)) = 0 := by
    exact hjCast.symm.trans
      (map_zero
        (LinearEquiv.cast
          (R := R) (M := E) (congrArg jDeg h)))
  change C.incomingI p a = x.1 at ha
  rw [← ha]
  exact hzero

/-- The second generic derived triangle relation: `j′ ∘ i′ = 0`. -/
theorem directDerivedJ_comp_directDerivedI
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    (C.directDerivedJ (derivedIDegree iDeg p)).comp
        (C.directDerivedI p) = 0 := by
  apply LinearMap.ext
  intro x
  let h : iDeg.symm (iDeg p) = p := iDeg.symm_apply_apply p
  let y : D (iDeg.symm (iDeg p)) :=
    LinearEquiv.cast (R := R) (M := D) h.symm x.1
  have hy :
      C.incomingI (iDeg p) y = C.i p x.1 :=
    C.incomingI_iDeg_cast p x.1
  have hrepr :
      C.directDerivedI p x =
        ⟨C.incomingI (iDeg p) y, ⟨y, rfl⟩⟩ := by
    apply Subtype.ext
    exact hy.symm
  change
    C.directDerivedJ (iDeg p) (C.directDerivedI p x) = 0
  rw [hrepr]
  rw [C.directDerivedJ_imageRepresentative]
  have hjp : C.j p x.1 = 0 :=
    C.j_eq_zero_of_mem_DirectDerivedD p x
  have hjy : C.j (iDeg.symm (iDeg p)) y = 0 := by
    let e :=
      LinearEquiv.cast
        (R := R) (M := E) (congrArg jDeg h)
    apply e.injective
    rw [C.j_cast_apply h y]
    change
      C.j p
          (LinearEquiv.cast (R := R) (M := D) h y) =
        e 0
    rw [show
      LinearEquiv.cast (R := R) (M := D) h y = x.1 by
        simp [y]]
    rw [hjp]
    exact (map_zero e).symm
  change
    (C.targetBoundariesInCycles
      (C.derivedJPageIndex (iDeg p))).mkQ
        (C.jToTargetCycles (iDeg p) y) = 0
  have hcycle :
      C.jToTargetCycles (iDeg p) y = 0 := by
    apply Subtype.ext
    rw [C.jToTargetCycles_coe]
    rw [hjy]
    exact map_zero
      (LinearEquiv.cast
        (R := R) (M := E)
        (C.differentialDegree_derivedJPageIndex (iDeg p)).symm)
  rw [hcycle, map_zero]

/-- One inclusion in generic derived exactness at the first `D′` vertex. -/
theorem range_directDerivedI_le_ker_directDerivedJ
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    LinearMap.range (C.directDerivedI p) ≤
      LinearMap.ker (C.directDerivedJ (derivedIDegree iDeg p)) := by
  rw [LinearMap.range_le_ker_iff]
  exact C.directDerivedJ_comp_directDerivedI p

/-- The reindexed incoming `i` kills every value of the preceding `k` arrow. -/
theorem incomingI_incomingKToIPre_eq_zero
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (y : E (C.derivedJPageIndex p)) :
    C.incomingI p (C.incomingKToIPre p y) = 0 := by
  let q := C.derivedJPageIndex p
  let hk : kDeg q = iDeg.symm p :=
    C.kDeg_derivedJPageIndex p
  have hik :
      C.i (kDeg q) (C.k q y) = 0 := by
    change C.k q y ∈ LinearMap.ker (C.i (kDeg q))
    rw [C.exact_ki q]
    exact ⟨y, rfl⟩
  have hiCast := C.i_cast_apply hk (C.k q y)
  rw [hik] at hiCast
  have hiPre :
      C.i (iDeg.symm p)
          (C.incomingKToIPre p y) = 0 := by
    change
      C.i (iDeg.symm p)
          (LinearEquiv.cast
            (R := R) (M := D) hk (C.k q y)) = 0
    exact hiCast.symm.trans
      (map_zero
        (LinearEquiv.cast
          (R := R) (M := D) (congrArg iDeg hk)))
  change
    LinearEquiv.cast
        (R := R) (M := D) (iDeg.apply_symm_apply p)
        (C.i (iDeg.symm p) (C.incomingKToIPre p y)) = 0
  rw [hiPre]
  exact map_zero
    (LinearEquiv.cast
      (R := R) (M := D) (iDeg.apply_symm_apply p))

/-- The cycle-level `j` of the preceding `k` value is exactly the boundary `d y`. -/
theorem jToTargetCycles_incomingKToIPre_coe
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (y : E (C.derivedJPageIndex p)) :
    (C.jToTargetCycles p (C.incomingKToIPre p y)).1 =
      C.differential (C.derivedJPageIndex p) y := by
  let q := C.derivedJPageIndex p
  let hk : kDeg q = iDeg.symm p :=
    C.kDeg_derivedJPageIndex p
  let ht : C.differentialDegree q = jDeg (iDeg.symm p) :=
    C.differentialDegree_derivedJPageIndex p
  let e := LinearEquiv.cast (R := R) (M := E) ht
  have hj := C.j_cast_apply hk (C.k q y)
  change
    e (C.j (kDeg q) (C.k q y)) =
      C.j (iDeg.symm p)
        (LinearEquiv.cast (R := R) (M := D) hk (C.k q y)) at hj
  rw [C.jToTargetCycles_coe]
  change
    e.symm
        (C.j (iDeg.symm p)
          (LinearEquiv.cast (R := R) (M := D) hk (C.k q y))) =
      C.j (kDeg q) (C.k q y)
  rw [← hj]
  exact e.symm_apply_apply (C.j (kDeg q) (C.k q y))

/-- Original exactness identifies every `j`-cycle with the derived image `D′`. -/
theorem mem_DirectDerivedD_of_j_eq_zero
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (b : D p) (hb : C.j p b = 0) :
    b ∈ C.DirectDerivedD p := by
  let r := iDeg.symm p
  let h : iDeg r = p := iDeg.apply_symm_apply p
  let b₀ : D (iDeg r) :=
    LinearEquiv.cast (R := R) (M := D) h.symm b
  have hjb₀ : C.j (iDeg r) b₀ = 0 := by
    let e :=
      LinearEquiv.cast (R := R) (M := E) (congrArg jDeg h)
    apply e.injective
    rw [C.j_cast_apply h b₀]
    change
      C.j p (LinearEquiv.cast (R := R) (M := D) h b₀) =
        e 0
    rw [show
      LinearEquiv.cast (R := R) (M := D) h b₀ = b by
        simp [b₀]]
    rw [hb]
    exact (map_zero e).symm
  have hbRange :
      b₀ ∈ LinearMap.range (C.i r) := by
    rw [← C.exact_ij r]
    exact hjb₀
  rcases hbRange with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  change
    LinearEquiv.cast (R := R) (M := D) h (C.i r a) = b
  rw [ha]
  simp [b₀]

/-- The reverse inclusion in generic derived exactness at the first `D′` vertex. -/
theorem ker_directDerivedJ_le_range_directDerivedI
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    LinearMap.ker (C.directDerivedJ (derivedIDegree iDeg p)) ≤
      LinearMap.range (C.directDerivedI p) := by
  change
    LinearMap.ker (C.directDerivedJ (iDeg p)) ≤
      LinearMap.range (C.directDerivedI p)
  intro z hz
  rcases z.2 with ⟨a, ha⟩
  have hzrepr :
      z =
        ⟨C.incomingI (iDeg p) a, ⟨a, rfl⟩⟩ := by
    apply Subtype.ext
    exact ha.symm
  subst z
  have hjClass :
      C.jToDerivedE (iDeg p) a = 0 := by
    change
      C.directDerivedJ (iDeg p)
          ⟨C.incomingI (iDeg p) a, ⟨a, rfl⟩⟩ = 0 at hz
    rw [C.directDerivedJ_imageRepresentative] at hz
    exact hz
  have hjBoundary :
      C.jToTargetCycles (iDeg p) a ∈
        C.targetBoundariesInCycles
          (C.derivedJPageIndex (iDeg p)) :=
    (Submodule.Quotient.mk_eq_zero _).1 hjClass
  change
    (C.jToTargetCycles (iDeg p) a).1 ∈
      C.targetBoundaries (C.derivedJPageIndex (iDeg p))
        at hjBoundary
  rcases hjBoundary with ⟨y, hy⟩
  let s := iDeg.symm (iDeg p)
  let h : s = p := iDeg.symm_apply_apply p
  let kpre : D s :=
    C.incomingKToIPre (iDeg p) y
  have hjCycleValues :
      (C.jToTargetCycles (iDeg p) a).1 =
        (C.jToTargetCycles (iDeg p) kpre).1 := by
    exact hy.symm.trans
      (C.jToTargetCycles_incomingKToIPre_coe
        (iDeg p) y).symm
  have hja :
      C.j s a = C.j s kpre := by
    let e :=
      LinearEquiv.cast
        (R := R) (M := E)
        (C.differentialDegree_derivedJPageIndex (iDeg p)).symm
    change e (C.j s a) = e (C.j s kpre) at hjCycleValues
    exact e.injective hjCycleValues
  let deltaS : D s := a - kpre
  have hjDeltaS : C.j s deltaS = 0 := by
    simp [deltaS, hja]
  let deltaP : D p :=
    LinearEquiv.cast (R := R) (M := D) h deltaS
  have hjDeltaP : C.j p deltaP = 0 := by
    let e :=
      LinearEquiv.cast (R := R) (M := E) (congrArg jDeg h)
    have hjCast := C.j_cast_apply h deltaS
    rw [hjDeltaS] at hjCast
    exact hjCast.symm.trans (map_zero e)
  let c : C.DirectDerivedD p :=
    ⟨deltaP, C.mem_DirectDerivedD_of_j_eq_zero p deltaP hjDeltaP⟩
  refine ⟨c, ?_⟩
  apply Subtype.ext
  change
    C.i p deltaP = C.incomingI (iDeg p) a
  have hiTransport := C.i_cast_apply h deltaS
  have hiDelta :
      C.i p deltaP =
        C.incomingI (iDeg p) deltaS := by
    exact hiTransport.symm
  rw [hiDelta]
  change
    C.incomingI (iDeg p) (a - kpre) =
      C.incomingI (iDeg p) a
  rw [map_sub]
  rw [C.incomingI_incomingKToIPre_eq_zero (iDeg p) y]
  exact sub_zero _

/-- Exactness of the generic derived couple at the first `D′` vertex. -/
theorem directDerived_exact_ij
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    LinearMap.ker (C.directDerivedJ (derivedIDegree iDeg p)) =
      LinearMap.range (C.directDerivedI p) :=
  le_antisymm
    (C.ker_directDerivedJ_le_range_directDerivedI p)
    (C.range_directDerivedI_le_ker_directDerivedJ p)

/-- A cycle expressed in its actual degree, reindexed into the homology model. -/
def directCycleOf
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (x : E p) (hx : C.differential p x = 0) :
    C.targetCycles (C.differentialDegree.symm p) := by
  let q := C.differentialDegree.symm p
  let h : C.differentialDegree q = p :=
    C.differentialDegree.apply_symm_apply p
  let x₀ : E (C.differentialDegree q) :=
    LinearEquiv.cast (R := R) (M := E) h.symm x
  refine ⟨x₀, ?_⟩
  have hdCast := C.differential_cast h x₀
  have hx₀ :
      LinearEquiv.cast (R := R) (M := E) h x₀ = x := by
    simp [x₀]
  rw [hx₀, hx] at hdCast
  let e :=
    LinearEquiv.cast
      (R := R) (M := E) (congrArg C.differentialDegree h)
  apply e.injective
  exact hdCast.trans (map_zero e).symm

@[simp]
theorem directCycleValue_directCycleOf
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (x : E p) (hx : C.differential p x = 0) :
    C.directCycleValue p (C.directCycleOf p x hx) = x := by
  let h :=
    C.differentialDegree.apply_symm_apply p
  let e := LinearEquiv.cast (R := R) (M := E) h
  change e (e.symm x) = x
  exact e.apply_symm_apply x

/-- The derived `i′` map kills the cycle-level image of `k`. -/
@[simp]
theorem directDerivedI_kTargetCyclesToDirectDerivedD_eq_zero
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I)
    (x : C.targetCycles (C.differentialDegree.symm p)) :
    C.directDerivedI (derivedKDegree kDeg p)
        (C.kTargetCyclesToDirectDerivedD p x) = 0 := by
  apply Subtype.ext
  change
    C.i (kDeg p) (C.k p (C.directCycleValue p x)) = 0
  change C.k p (C.directCycleValue p x) ∈
    LinearMap.ker (C.i (kDeg p))
  rw [C.exact_ki p]
  exact ⟨C.directCycleValue p x, rfl⟩

/-- The third generic derived triangle relation: `i′ ∘ k′ = 0`. -/
theorem directDerivedI_comp_directDerivedK
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    (C.directDerivedI (derivedKDegree kDeg p)).comp
        (C.directDerivedK p) = 0 := by
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on
    (C.targetBoundariesInCycles (C.differentialDegree.symm p))
    z ?_
  intro x
  change
    C.directDerivedI (kDeg p)
        (C.directDerivedK p (Submodule.Quotient.mk x)) = 0
  rw [C.directDerivedK_mk]
  exact C.directDerivedI_kTargetCyclesToDirectDerivedD_eq_zero p x

/-- One inclusion in exactness at the second generic derived `D′` vertex. -/
theorem range_directDerivedK_le_ker_directDerivedI
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    LinearMap.range (C.directDerivedK p) ≤
      LinearMap.ker (C.directDerivedI (derivedKDegree kDeg p)) := by
  rw [LinearMap.range_le_ker_iff]
  exact C.directDerivedI_comp_directDerivedK p

/-- The reverse inclusion at the second generic derived `D′` vertex. -/
theorem ker_directDerivedI_le_range_directDerivedK
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    LinearMap.ker (C.directDerivedI (derivedKDegree kDeg p)) ≤
      LinearMap.range (C.directDerivedK p) := by
  change
    LinearMap.ker (C.directDerivedI (kDeg p)) ≤
      LinearMap.range (C.directDerivedK p)
  intro z hz
  have hiz : C.i (kDeg p) z.1 = 0 := by
    exact congrArg Subtype.val hz
  have hzRange :
      z.1 ∈ LinearMap.range (C.k p) := by
    rw [← C.exact_ki p]
    exact hiz
  rcases hzRange with ⟨x, hx⟩
  have hjz : C.j (kDeg p) z.1 = 0 :=
    C.j_eq_zero_of_mem_DirectDerivedD (kDeg p) z
  have hxCycle : C.differential p x = 0 := by
    change C.j (kDeg p) (C.k p x) = 0
    rw [hx]
    exact hjz
  let cycle := C.directCycleOf p x hxCycle
  refine
    ⟨Submodule.Quotient.mk cycle, ?_⟩
  rw [C.directDerivedK_mk]
  apply Subtype.ext
  rw [C.kTargetCyclesToDirectDerivedD_coe]
  rw [C.directCycleValue_directCycleOf]
  exact hx

/-- Exactness at the second generic derived `D′` vertex. -/
theorem directDerived_exact_ki
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    LinearMap.ker (C.directDerivedI (derivedKDegree kDeg p)) =
      LinearMap.range (C.directDerivedK p) :=
  le_antisymm
    (C.ker_directDerivedI_le_range_directDerivedK p)
    (C.range_directDerivedK_le_ker_directDerivedI p)

/--
The genuine derived graded exact couple of an arbitrary graded exact couple.

Its objects are Mathlib range submodules and homology quotients; all three
exactness fields are supplied by the theorems proved above.
-/
noncomputable def derived
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) :
    GradedExactCouple R I
      (fun p => (C.DirectDerivedD p : Type u))
      (fun p => C.DirectDerivedE p)
      (derivedIDegree iDeg)
      (derivedJDegree iDeg jDeg)
      (derivedKDegree kDeg) where
  i := C.directDerivedI
  j := C.directDerivedJ
  k := C.directDerivedK
  exact_ij := C.directDerived_exact_ij
  exact_jk := C.directDerived_exact_jk
  exact_ki := C.directDerived_exact_ki

@[simp]
theorem derived_i
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    C.derived.i p = C.directDerivedI p :=
  rfl

@[simp]
theorem derived_j
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    C.derived.j p = C.directDerivedJ p :=
  rfl

@[simp]
theorem derived_k
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    C.derived.k p = C.directDerivedK p :=
  rfl

end GradedExactCouple

end InfoGeometry.Spectral.Algebra
