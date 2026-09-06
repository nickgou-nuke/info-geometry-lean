import Mathlib

/-! The inverse-limit spine of the boundary of a rooted `n`-ary tree.

Finite words are prefix projections; the infinite boundary is represented by
coherent finite words.  This owner is deliberately independent of the binary
Cantor owners and makes no claim about a colimit or a metric completion.
-/

noncomputable section

namespace InfoGeometry.Canonical.NaryTreeBoundaryInverseLimit

open CategoryTheory

abbrev NaryWord (n k : ℕ) := Fin k → Fin n
abbrev NaryBoundary (n : ℕ) := ℕ → Fin n

def naryPrefix (k n : ℕ) (x : NaryBoundary n) : NaryWord n k :=
  fun i => x i.1

def forgetLast (k n : ℕ) (w : NaryWord n (k + 1)) : NaryWord n k :=
  fun i => w ⟨i.1, Nat.lt_succ_of_lt i.2⟩

structure CoherentWords (n : ℕ) where
  word : ∀ k : ℕ, NaryWord n k
  coherent : ∀ k : ℕ, forgetLast k n (word (k + 1)) = word k

@[ext] theorem CoherentWords.ext {p q : CoherentWords n}
    (h : p.word = q.word) : p = q := by
  cases p
  cases q
  simp_all

namespace CoherentWords

instance : CoeFun (CoherentWords n) (fun _ => ∀ k : ℕ, NaryWord n k) where
  coe p := p.word

def projection (k : ℕ) (p : CoherentWords n) : NaryWord n k := p.word k

def ofBoundary (x : NaryBoundary n) : CoherentWords n where
  word := fun k => naryPrefix k n x
  coherent := by
    intro k
    funext i
    rfl

def toBoundary (p : CoherentWords n) : NaryBoundary n :=
  fun k => p.word (k + 1) ⟨k, Nat.lt_succ_self k⟩

theorem toBoundary_ofBoundary (x : NaryBoundary n) :
    toBoundary (ofBoundary x) = x := by
  funext k
  dsimp [toBoundary, ofBoundary, naryPrefix]

theorem projection_toBoundary (p : CoherentWords n) (k : ℕ) :
    naryPrefix k n (toBoundary p) = p.word k := by
  induction k with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ k ih =>
      funext i
      by_cases hi : i.1 < k
      · have hcoh := congrFun (p.coherent k) ⟨i.1, hi⟩
        have hih := congrFun ih ⟨i.1, hi⟩
        exact hih.trans hcoh.symm
      · have hi' : i.1 = k := by omega
        have hieq : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hi'
        subst i
        rfl

theorem ofBoundary_toBoundary (p : CoherentWords n) :
    ofBoundary (toBoundary p) = p := by
  apply CoherentWords.ext
  funext k
  change naryPrefix k n (toBoundary p) = p.word k
  exact projection_toBoundary p k

def equivBoundary : NaryBoundary n ≃ CoherentWords n where
  toFun := ofBoundary
  invFun := toBoundary
  left_inv := toBoundary_ofBoundary
  right_inv := ofBoundary_toBoundary

instance : TopologicalSpace (CoherentWords n) :=
  TopologicalSpace.induced (fun p : CoherentWords n => p.word) inferInstance

theorem continuous_projection (k : ℕ) :
    Continuous (projection k : CoherentWords n → NaryWord n k) := by
  change Continuous (fun p : CoherentWords n => p.word k)
  exact (continuous_apply k).comp continuous_induced_dom

theorem continuous_ofBoundary :
    Continuous (ofBoundary : NaryBoundary n → CoherentWords n) := by
  rw [continuous_induced_rng]
  change Continuous (fun x : NaryBoundary n => fun k : ℕ => naryPrefix k n x)
  exact continuous_pi fun k => by
    exact continuous_pi fun i => continuous_apply i.1

theorem continuous_toBoundary :
    Continuous (toBoundary : CoherentWords n → NaryBoundary n) := by
  exact continuous_pi fun k =>
    (continuous_apply ⟨k, Nat.lt_succ_self k⟩).comp (continuous_projection (k + 1))

def boundaryHomeomorph : NaryBoundary n ≃ₜ CoherentWords n where
  toEquiv := equivBoundary
  continuous_toFun := continuous_ofBoundary
  continuous_invFun := continuous_toBoundary

def projectionTopCatHom (k : ℕ) :
    TopCat.of (CoherentWords n) ⟶ TopCat.of (NaryWord n k) :=
  TopCat.ofHom
    { toFun := projection k
      continuous_toFun := continuous_projection k }

def forgetLastTopCatHom (k : ℕ) :
    TopCat.of (NaryWord n (k + 1)) ⟶ TopCat.of (NaryWord n k) :=
  TopCat.ofHom
    { toFun := forgetLast k n
      continuous_toFun := by
        exact continuous_pi fun i =>
          continuous_apply (⟨i.1, Nat.lt_succ_of_lt i.2⟩ : Fin (k + 1)) }

theorem projection_bonding_square (k : ℕ) :
    projectionTopCatHom (n := n) (k + 1) ≫ forgetLastTopCatHom (n := n) k =
      projectionTopCatHom (n := n) k := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app]
  change forgetLast k n (projection (k + 1) p) = projection k p
  exact p.coherent k

end CoherentWords

open CategoryTheory CategoryTheory.Limits

def naryPrefixRestriction {n : ℕ} {m k : ℕᵒᵖ} (f : m ⟶ k) :
    NaryWord n m.unop → NaryWord n k.unop := fun w i =>
  w ⟨i.1, Nat.lt_of_lt_of_le i.2 (leOfHom f.unop)⟩

def naryPrefixDiagram (n : ℕ) : ℕᵒᵖ ⥤ TopCat where
  obj k := TopCat.of (NaryWord n k.unop)
  map f := TopCat.ofHom
    { toFun := naryPrefixRestriction f
      continuous_toFun := by
        exact continuous_pi fun i => continuous_apply _ }
  map_id k := by
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
    apply congrArg w
    apply Fin.ext
    rfl

def naryPrefixCone (n : ℕ) : Cone (naryPrefixDiagram n) where
  pt := TopCat.of (NaryBoundary n)
  π :=
    { app := fun k => TopCat.ofHom
        { toFun := naryPrefix k.unop n
          continuous_toFun := by
            exact continuous_pi fun i => continuous_apply i.1 }
      naturality := by
        intro X Y f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        funext i
        rfl }

def naryPrefixLimitLift {n : ℕ} (s : Cone (naryPrefixDiagram n)) :
    s.pt ⟶ (naryPrefixCone n).pt := by
  exact { hom' :=
    { toFun := fun x k =>
        (s.π.app (Opposite.op (k + 1))).hom x ⟨k, Nat.lt_succ_self k⟩
      continuous_toFun := by
        exact continuous_pi fun k =>
          (continuous_apply (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))).comp
            (s.π.app (Opposite.op (k + 1))).hom.continuous } }

def naryPrefixConeIsLimit (n : ℕ) : IsLimit (naryPrefixCone n) := by
  refine IsLimit.mk (naryPrefixLimitLift (n := n)) ?_ ?_
  · intro s j
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    funext i
    rcases j with ⟨j⟩
    cases j with
    | zero => exact Fin.elim0 i
    | succ k =>
        let hki : i.val + 1 ≤ k + 1 := Nat.succ_le_of_lt i.isLt
        let f : (Opposite.op (k + 1) : ℕᵒᵖ) ⟶ Opposite.op (i.val + 1) :=
          (homOfLE hki).op
        have hn := congrArg (fun q => (ConcreteCategory.hom q) x)
          (s.π.naturality f)
        have hi := congrFun hn (Fin.last i.val)
        change (s.π.app (Opposite.op (i.val + 1))).hom x (Fin.last i.val) =
          (s.π.app (Opposite.op (k + 1))).hom x
            (Fin.castLE hki (Fin.last i.val)) at hi
        have hcast : Fin.castLE hki (Fin.last i.val) = i := by
          apply Fin.ext
          rfl
        rw [hcast] at hi
        simpa [naryPrefixLimitLift, naryPrefixRestriction] using hi
  · intro s m hm
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    funext k
    have h := congrArg (fun q => (ConcreteCategory.hom q) x)
      (hm (Opposite.op (k + 1)))
    have hlast := congrFun h (Fin.last k)
    change (TopCat.Hom.hom m) x k =
      (TopCat.Hom.hom (naryPrefixLimitLift s)) x k
    simpa [naryPrefixLimitLift] using hlast

noncomputable def naryTreeBoundaryLimitIso (n : ℕ) :
    (naryPrefixCone n).pt ≅ limit (naryPrefixDiagram n) :=
  (naryPrefixConeIsLimit n).conePointUniqueUpToIso (limit.isLimit _)

theorem naryTreeBoundaryLimitIso_hom_comp (n k : ℕ) :
    (naryTreeBoundaryLimitIso n).hom ≫
        limit.π (naryPrefixDiagram n) (Opposite.op k) =
      (naryPrefixCone n).π.app (Opposite.op k) := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (naryPrefixConeIsLimit n) (limit.isLimit _) (Opposite.op k)

end InfoGeometry.Canonical.NaryTreeBoundaryInverseLimit
