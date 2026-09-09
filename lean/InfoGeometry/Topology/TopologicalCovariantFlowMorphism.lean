import InfoGeometry.Topology.SymbolicLatentNoncommutativeTopologicalCovariantFlow

/-!
# Morphisms of topological covariant flows on a fixed carrier

The carrier types `X`, `A`, and `ι` are fixed in this first categorical layer.
A morphism consists of a continuous latent map and a target `StarAlgEquiv`
which jointly intertwine observables and both time actions.
-/

noncomputable section

namespace InfoGeometry.Topology

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

structure TopologicalCovariantFlowMorphism
    {S : NoncommutativeObservableSystem X A ι}
    (F G : NoncommutativeObservableTopologicalCovariantFlow S) where
  latentMap : X → X
  continuous_latentMap : Continuous latentMap
  operatorMap : A ≃⋆ₐ[ℂ] A
  operatorMap_continuous : Continuous operatorMap
  flow_natural : ∀ t x,
    latentMap (F.base.act t x) = G.base.act t (latentMap x)
  observation_natural : ∀ x i,
    (S.observable i).eval (latentMap x) =
      operatorMap ((S.observable i).eval x)
  operatorAction_natural : ∀ t a,
    operatorMap (F.base.operatorAction t a) =
      G.base.operatorAction t (operatorMap a)

namespace TopologicalCovariantFlowMorphism

variable {S : NoncommutativeObservableSystem X A ι}
  {F G H : NoncommutativeObservableTopologicalCovariantFlow S}

def id (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    TopologicalCovariantFlowMorphism F F where
  latentMap := fun x => x
  continuous_latentMap := continuous_id
  operatorMap := StarAlgEquiv.refl
  operatorMap_continuous := continuous_id
  flow_natural := by intro t x; rfl
  observation_natural := by intro x i; rfl
  operatorAction_natural := by intro t a; rfl

def comp (f : TopologicalCovariantFlowMorphism F G)
    (g : TopologicalCovariantFlowMorphism G H) :
    TopologicalCovariantFlowMorphism F H where
  latentMap := g.latentMap ∘ f.latentMap
  continuous_latentMap := g.continuous_latentMap.comp f.continuous_latentMap
  operatorMap := f.operatorMap.trans g.operatorMap
  operatorMap_continuous := by
    exact g.operatorMap_continuous.comp f.operatorMap_continuous
  flow_natural := by
    intro t x
    calc
      g.latentMap (f.latentMap (F.base.act t x)) =
          g.latentMap (G.base.act t (f.latentMap x)) :=
        congrArg g.latentMap (f.flow_natural t x)
      _ = H.base.act t (g.latentMap (f.latentMap x)) :=
        g.flow_natural t (f.latentMap x)
  observation_natural := by
    intro x i
    calc
      (S.observable i).eval (g.latentMap (f.latentMap x)) =
          g.operatorMap ((S.observable i).eval (f.latentMap x)) :=
        g.observation_natural (f.latentMap x) i
      _ = g.operatorMap (f.operatorMap ((S.observable i).eval x)) := by
        rw [f.observation_natural]
      _ = (f.operatorMap.trans g.operatorMap) ((S.observable i).eval x) :=
        rfl
  operatorAction_natural := by
    intro t a
    calc
      (f.operatorMap.trans g.operatorMap) (F.base.operatorAction t a) =
          g.operatorMap (f.operatorMap (F.base.operatorAction t a)) := rfl
      _ = g.operatorMap (G.base.operatorAction t (f.operatorMap a)) := by
        rw [f.operatorAction_natural]
      _ = H.base.operatorAction t
          (g.operatorMap (f.operatorMap a)) :=
      g.operatorAction_natural t (f.operatorMap a)

@[ext] theorem ext {f g : TopologicalCovariantFlowMorphism F G}
    (h_latent : f.latentMap = g.latentMap)
    (h_operator : f.operatorMap = g.operatorMap) :
    f = g := by
  cases f
  cases g
  cases h_latent
  cases h_operator
  rfl

theorem id_latentMap
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    (id F).latentMap = (fun x => x) := rfl

theorem comp_latentMap (f : TopologicalCovariantFlowMorphism F G)
    (g : TopologicalCovariantFlowMorphism G H) :
    (comp f g).latentMap = g.latentMap ∘ f.latentMap := rfl

theorem comp_id (f : TopologicalCovariantFlowMorphism F G) :
    comp f (id G) = f := by
  cases f
  simp only [comp, id]
  ext <;> simp [Function.comp_apply]

theorem id_comp (f : TopologicalCovariantFlowMorphism F G) :
    comp (id F) f = f := by
  cases f
  simp only [comp, id]
  ext <;> simp [Function.comp_apply]

end TopologicalCovariantFlowMorphism

end InfoGeometry.Topology
