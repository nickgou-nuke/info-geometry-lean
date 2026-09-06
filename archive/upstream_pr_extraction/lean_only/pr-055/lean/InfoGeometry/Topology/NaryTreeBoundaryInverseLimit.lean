import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# The n-ary tree boundary as a native topological inverse limit

This owner packages the standard prefix-restriction inverse-limit picture for
an arbitrary alphabet `A`.  The boundary is the sequence space `ℕ → A`, and
the finite-prefix diagram consists of the spaces `Fin n → A` with restriction
along prefix truncation.

No metric completion or probabilistic interpretation is introduced here.
-/

noncomputable section

namespace InfoGeometry.Topology.NaryTreeBoundaryInverseLimit

open CategoryTheory CategoryTheory.Limits

universe u

variable {A : Type u} [TopologicalSpace A]

/-- Infinite boundary sequences over the alphabet `A`. -/
abbrev Boundary : Type u := ℕ → A

/-- Finite words of length `n` over the alphabet `A`. -/
abbrev Word (n : ℕ) : Type u := Fin n → A

/-- Restrict a longer word to a shorter prefix. -/
def prefixRestriction {m n : ℕᵒᵖ} (f : m ⟶ n) :
    Word (A := A) m.unop → Word (A := A) n.unop := fun w i =>
  w (Fin.castLE (show n.unop ≤ m.unop from leOfHom f.unop) i)

/-- The prefix diagram of finite words. -/
def prefixDiagram : ℕᵒᵖ ⥤ TopCat where
  obj n := TopCat.of (Word (A := A) n.unop)
  map f :=
    { hom' :=
        { toFun := prefixRestriction (A := A) f
          continuous_toFun := by
            apply continuous_pi
            intro i
            exact continuous_apply _ } }
  map_id n := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro w
    funext i
    rfl
  map_comp f g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro w
    funext i
    rfl

/-- The cone whose point is the boundary sequence space. -/
def prefixCone : Cone (prefixDiagram (A := A)) where
  pt := TopCat.of (Boundary (A := A))
  π :=
    { app := fun n =>
        { hom' :=
            { toFun := fun x i => x i.1
              continuous_toFun := by
                apply continuous_pi
                intro i
                exact continuous_apply _ } }
      naturality := by
        intro X Y f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        funext i
        rfl }

/-- Lift a compatible cone into the boundary sequence space. -/
def prefixLimitLift (s : Cone (prefixDiagram (A := A))) :
    s.pt ⟶ prefixCone (A := A).pt := by
  let f : s.pt → Boundary (A := A) :=
    fun x n => s.π.app (Opposite.op (n + 1)) x (Fin.last n)
  have hf : Continuous f := by
    apply continuous_pi
    intro n
    exact (continuous_apply (Fin.last n)).comp
      (s.π.app (Opposite.op (n + 1))).hom.continuous
  exact { hom' := { toFun := f, continuous_toFun := hf } }

/-- The boundary sequence cone satisfies the inverse-limit universal property. -/
def prefixConeIsLimit : IsLimit (prefixCone (A := A)) := by
  refine IsLimit.mk prefixLimitLift ?_ ?_
  · intro s j
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    funext i
    rcases j with ⟨j⟩
    cases j with
    | zero =>
        exact Fin.elim0 i
    | succ k =>
        let hki : i.1 + 1 ≤ k + 1 := Nat.succ_le_of_lt i.2
        let f : (Opposite.op (k + 1) : ℕᵒᵖ) ⟶ Opposite.op (i.1 + 1) :=
          (homOfLE hki).op
        have hn := congrArg (fun q => (ConcreteCategory.hom q) x)
          (s.π.naturality f)
        have hi := congrFun hn (Fin.last i.1)
        change (s.π.app (Opposite.op (i.1 + 1))).hom x (Fin.last i.1) =
          (s.π.app (Opposite.op (k + 1))).hom x
            (Fin.castLE hki (Fin.last i.1)) at hi
        have hcast : Fin.castLE hki (Fin.last i.1) = i := by
          apply Fin.ext
          rfl
        rw [hcast] at hi
        simpa [prefixLimitLift, prefixRestriction] using hi
  · intro s m hm
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    funext n
    have h := congrArg (fun q => (ConcreteCategory.hom q) x)
      (hm (Opposite.op (n + 1)))
    have hlast := congrFun h (Fin.last n)
    change (TopCat.Hom.hom m) x n =
      (TopCat.Hom.hom (prefixLimitLift s)) x n
    simpa [prefixLimitLift] using hlast

/-- The canonical `TopCat` isomorphism between the boundary cone and the limit. -/
noncomputable def prefixBoundaryLimitIso :
    prefixCone (A := A).pt ≅ limit (prefixDiagram (A := A)) :=
  prefixConeIsLimit (A := A).conePointUniqueUpToIso
    (limit.isLimit (prefixDiagram (A := A)))

/-- The limit projection recovers the finite prefix at each stage. -/
theorem prefixBoundaryLimitIso_hom_comp (n : ℕ) :
    prefixBoundaryLimitIso (A := A).hom ≫
        limit.π (prefixDiagram (A := A)) (Opposite.op n) =
      prefixCone (A := A).π.app (Opposite.op n) := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (prefixConeIsLimit (A := A))
    (limit.isLimit (prefixDiagram (A := A)))
    (Opposite.op n)

/-- Stagewise description of the limit homeomorphism. -/
theorem prefixBoundaryLimitIso_hom_apply (n : ℕ)
    (x : Boundary (A := A)) (i : Fin n) :
    (limit.π (prefixDiagram (A := A)) (Opposite.op n)).hom
        (prefixBoundaryLimitIso (A := A).hom x) i = x i := by
  have h := congrArg (fun q => (ConcreteCategory.hom q) x)
    (prefixBoundaryLimitIso_hom_comp (A := A) n)
  have hi := congrFun h i
  exact hi

/-! ## Symbolic head/tail structure on the boundary -/

def boundaryHead : Boundary (A := A) → A := fun x => x 0

def boundaryTail : Boundary (A := A) → Boundary (A := A) :=
  fun x n => x (n + 1)

def boundaryCons : A → Boundary (A := A) → Boundary (A := A)
  | a, _, 0 => a
  | _, x, n + 1 => x n

omit [TopologicalSpace A] in
@[simp] theorem boundaryCons_zero (a : A) (x : Boundary (A := A)) :
    boundaryCons a x 0 = a := rfl

omit [TopologicalSpace A] in
@[simp] theorem boundaryCons_succ (a : A) (x : Boundary (A := A)) (n : ℕ) :
    boundaryCons a x (n + 1) = x n := rfl

omit [TopologicalSpace A] in
theorem boundary_recursive_decomposition (x : Boundary (A := A)) :
    boundaryCons (boundaryHead x) (boundaryTail x) = x := by
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

theorem continuous_boundaryHead :
    Continuous (boundaryHead (A := A)) :=
  continuous_apply 0

theorem continuous_boundaryTail :
    Continuous (boundaryTail (A := A)) := by
  apply continuous_pi
  intro n
  exact continuous_apply (n + 1)

end InfoGeometry.Topology.NaryTreeBoundaryInverseLimit
