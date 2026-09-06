import Mathlib
import InfoGeometry.Topology.SymbolicLatentSpace

/-!
# A real symbolic-latent chart for the eight chiral coefficient slots

The complex Zorn owner has a coordinate soldering map.  This file records its
real coefficient slice as a genuine symbolic-latent chart: the eight scalar
observables are the coordinate projections, so the observation map is an
embedding and its fibers are exactly singletons.
-/

namespace InfoGeometry.Topology

noncomputable section

abbrev RealChiralCoefficientSpace := Fin 8 → ℝ

def realChiralCoefficientSystem :
    FiniteSymbolicLatentSystem RealChiralCoefficientSpace (Fin 8) :=
  fun i =>
    { toFun := fun c => c i
      continuous_toFun := continuous_apply i }

@[simp] theorem realChiralCoefficientSystem_observationMap (c : RealChiralCoefficientSpace) :
    symbolicObservationMap realChiralCoefficientSystem c = c := by
  funext i
  rfl

theorem realChiralCoefficientSystem_isEmbedding :
    Topology.IsEmbedding
      (symbolicObservationMap realChiralCoefficientSystem) := by
  rw [show symbolicObservationMap realChiralCoefficientSystem = id by
    funext c
    exact realChiralCoefficientSystem_observationMap c]
  exact (Homeomorph.refl RealChiralCoefficientSpace).isEmbedding

def realChiralCoefficientChart :
    SymbolicLatentChart RealChiralCoefficientSpace (Fin 8) where
  system := realChiralCoefficientSystem
  isEmbedding := realChiralCoefficientSystem_isEmbedding

theorem realChiralCoefficientChart_solutionSet_singleton
    (c : RealChiralCoefficientSpace) :
    realChiralCoefficientSystem.solutionSet c = ({c} : Set RealChiralCoefficientSpace) := by
  ext x
  constructor
  · intro hx
    apply Set.mem_singleton_iff.mpr
    funext i
    exact hx i
  · intro hx
    rw [Set.mem_singleton_iff.mp hx]
    intro i
    rfl

def realChiralToSoldered :
    RealChiralCoefficientSpace ≃ₜ RealChiralCoefficientSpace where
  toFun c := ![
    c 0 + c 4,
    c 0 - c 4,
    c 1,
    c 5,
    c 2,
    c 6,
    c 3,
    c 7]
  invFun d := ![
    (d 0 + d 1) / 2,
    d 2,
    d 4,
    d 6,
    (d 0 - d 1) / 2,
    d 3,
    d 5,
    d 7]
  left_inv := by
    intro c
    funext i
    fin_cases i <;> simp <;> ring
  right_inv := by
    intro d
    funext i
    fin_cases i <;> simp <;> ring
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun c : RealChiralCoefficientSpace => c 0 + c 4)
      fun_prop
    · change Continuous (fun c : RealChiralCoefficientSpace => c 0 - c 4)
      fun_prop
    · change Continuous (fun c : RealChiralCoefficientSpace => c 1)
      fun_prop
    · change Continuous (fun c : RealChiralCoefficientSpace => c 5)
      fun_prop
    · change Continuous (fun c : RealChiralCoefficientSpace => c 2)
      fun_prop
    · change Continuous (fun c : RealChiralCoefficientSpace => c 6)
      fun_prop
    · change Continuous (fun c : RealChiralCoefficientSpace => c 3)
      fun_prop
    · change Continuous (fun c : RealChiralCoefficientSpace => c 7)
      fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun d : RealChiralCoefficientSpace => (d 0 + d 1) / 2)
      fun_prop
    · change Continuous (fun d : RealChiralCoefficientSpace => d 2)
      fun_prop
    · change Continuous (fun d : RealChiralCoefficientSpace => d 4)
      fun_prop
    · change Continuous (fun d : RealChiralCoefficientSpace => d 6)
      fun_prop
    · change Continuous (fun d : RealChiralCoefficientSpace => (d 0 - d 1) / 2)
      fun_prop
    · change Continuous (fun d : RealChiralCoefficientSpace => d 3)
      fun_prop
    · change Continuous (fun d : RealChiralCoefficientSpace => d 5)
      fun_prop
    · change Continuous (fun d : RealChiralCoefficientSpace => d 7)
      fun_prop

def realSolderedCoefficientSystem :
    FiniteSymbolicLatentSystem RealChiralCoefficientSpace (Fin 8) :=
  fun i =>
    { toFun := fun c => realChiralToSoldered c i
      continuous_toFun := continuous_apply i |>.comp
        realChiralToSoldered.continuous }

@[simp] theorem realSolderedCoefficientSystem_observationMap
    (c : RealChiralCoefficientSpace) :
    symbolicObservationMap realSolderedCoefficientSystem c =
      realChiralToSoldered c := by
  funext i
  rfl

theorem realSolderedCoefficientSystem_isEmbedding :
    Topology.IsEmbedding
      (symbolicObservationMap realSolderedCoefficientSystem) := by
  rw [show symbolicObservationMap realSolderedCoefficientSystem =
      realChiralToSoldered by
    funext c
    exact realSolderedCoefficientSystem_observationMap c]
  exact realChiralToSoldered.isEmbedding

def realSolderedCoefficientChart :
    SymbolicLatentChart RealChiralCoefficientSpace (Fin 8) where
  system := realSolderedCoefficientSystem
  isEmbedding := realSolderedCoefficientSystem_isEmbedding

theorem realSolderedCoefficientSystem_solutionSet_singleton
    (d : RealChiralCoefficientSpace) :
    realSolderedCoefficientSystem.solutionSet d =
      ({realChiralToSoldered.symm d} : Set RealChiralCoefficientSpace) := by
  ext x
  constructor
  · intro hx
    apply Set.mem_singleton_iff.mpr
    funext i
    have hfun : realChiralToSoldered x = d := by
      funext j
      simpa [realSolderedCoefficientSystem_observationMap] using hx j
    calc
      x i = realChiralToSoldered.symm (realChiralToSoldered x) i :=
        (congrFun (realChiralToSoldered.left_inv x) i).symm
      _ = realChiralToSoldered.symm d i :=
        congrFun (congrArg realChiralToSoldered.symm hfun) i
  · intro hx
    rw [Set.mem_singleton_iff.mp hx]
    intro i
    change realChiralToSoldered (realChiralToSoldered.symm d) i = d i
    exact congrFun (realChiralToSoldered.right_inv d) i

theorem realChiralToSoldered_solutionSet_transport
    (c : RealChiralCoefficientSpace) :
    realChiralToSoldered '' realChiralCoefficientSystem.solutionSet c =
      realSolderedCoefficientSystem.solutionSet
        (realChiralToSoldered (realChiralToSoldered c)) := by
  rw [realChiralCoefficientChart_solutionSet_singleton,
    realSolderedCoefficientSystem_solutionSet_singleton]
  simp

theorem realChiralToSoldered_observation_transport (c : RealChiralCoefficientSpace) :
    symbolicObservationMap realChiralCoefficientSystem (realChiralToSoldered c) =
      realChiralToSoldered c := by
  exact realChiralCoefficientSystem_observationMap _

def chiralToSolderedLatentMorphism :
    SymbolicLatentMorphism realChiralCoefficientSystem
      realSolderedCoefficientSystem where
  toFun := realChiralToSoldered.symm
  continuous_toFun := realChiralToSoldered.symm.continuous
  intertwines := by
    intro i c
    change realChiralToSoldered (realChiralToSoldered.symm c) i = c i
    exact congrFun (realChiralToSoldered.right_inv c) i

def solderedToChiralLatentMorphism :
    SymbolicLatentMorphism realSolderedCoefficientSystem
      realChiralCoefficientSystem where
  toFun := realChiralToSoldered
  continuous_toFun := realChiralToSoldered.continuous
  intertwines := by
    intro i c
    change realChiralToSoldered c i = realChiralToSoldered c i
    rfl

theorem chiralSoldered_quotient_map_comp_inverse :
    (SymbolicLatentMorphism.comp
      solderedToChiralLatentMorphism chiralToSolderedLatentMorphism).quotientMap =
      (fun q => q) := by
  funext q
  refine _root_.Quotient.inductionOn q ?_
  intro c
  change _root_.Quotient.mk
      (symbolicObservationalSetoid realChiralCoefficientSystem)
      (realChiralToSoldered (realChiralToSoldered.symm c)) =
    _root_.Quotient.mk (symbolicObservationalSetoid realChiralCoefficientSystem) c
  exact congrArg
    (_root_.Quotient.mk (symbolicObservationalSetoid realChiralCoefficientSystem))
    (realChiralToSoldered.right_inv c)

theorem solderedChiral_quotient_map_comp_inverse :
    (SymbolicLatentMorphism.comp
      chiralToSolderedLatentMorphism solderedToChiralLatentMorphism).quotientMap =
      (fun q => q) := by
  funext q
  refine _root_.Quotient.inductionOn q ?_
  intro c
  change _root_.Quotient.mk
      (symbolicObservationalSetoid realSolderedCoefficientSystem)
      (realChiralToSoldered.symm (realChiralToSoldered c)) =
    _root_.Quotient.mk (symbolicObservationalSetoid realSolderedCoefficientSystem) c
  exact congrArg
    (_root_.Quotient.mk (symbolicObservationalSetoid realSolderedCoefficientSystem))
    (realChiralToSoldered.left_inv c)

noncomputable def chiralSolderedObservationQuotientHomeomorph :
    _root_.Quotient (symbolicObservationalSetoid realChiralCoefficientSystem) ≃ₜ
      _root_.Quotient (symbolicObservationalSetoid realSolderedCoefficientSystem) where
  toFun := chiralToSolderedLatentMorphism.quotientMap
  invFun := solderedToChiralLatentMorphism.quotientMap
  left_inv := by
    intro q
    refine _root_.Quotient.inductionOn q ?_
    intro c
    change _root_.Quotient.mk
        (symbolicObservationalSetoid realChiralCoefficientSystem)
        (realChiralToSoldered (realChiralToSoldered.symm c)) =
      _root_.Quotient.mk (symbolicObservationalSetoid realChiralCoefficientSystem) c
    exact congrArg
      (_root_.Quotient.mk (symbolicObservationalSetoid realChiralCoefficientSystem))
      (realChiralToSoldered.right_inv c)
  right_inv := by
    intro q
    refine _root_.Quotient.inductionOn q ?_
    intro c
    change _root_.Quotient.mk
        (symbolicObservationalSetoid realSolderedCoefficientSystem)
        (realChiralToSoldered.symm (realChiralToSoldered c)) =
      _root_.Quotient.mk (symbolicObservationalSetoid realSolderedCoefficientSystem) c
    exact congrArg
      (_root_.Quotient.mk (symbolicObservationalSetoid realSolderedCoefficientSystem))
      (realChiralToSoldered.left_inv c)
  continuous_toFun :=
    SymbolicLatentMorphism.continuous_quotientMap chiralToSolderedLatentMorphism
  continuous_invFun :=
    SymbolicLatentMorphism.continuous_quotientMap solderedToChiralLatentMorphism

end
end InfoGeometry.Topology
