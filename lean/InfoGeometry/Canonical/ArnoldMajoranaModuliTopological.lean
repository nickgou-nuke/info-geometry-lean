import InfoGeometry.Canonical.ArnoldMajoranaModuli
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Topological readout of the finite Arnold--Majorana moduli quotient

The algebraic owner defines the expert-permutation quotient.  This file adds
only the induced finite product topology and the quotient projection.  It does
not assert that the quotient is a manifold, a stack, or that arbitrary network
observables descend through the permutation relation.
-/

noncomputable section

namespace InfoGeometry.Canonical.MoE

open CategoryTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

instance arnoldMajoranaNetworkSetoidInstance (n : Nat) :
    Setoid (ArnoldMajoranaNetwork n E) :=
  arnoldMajoranaNetworkSetoid n E

def expertFunctionEquiv (V : Type*) : Expert V ≃ (V → V) where
  toFun e := e.apply
  invFun f := f
  left_inv e := rfl
  right_inv f := rfl

instance expertTopologicalSpace (V : Type*) [TopologicalSpace V] :
    TopologicalSpace (Expert V) :=
  inferInstance

def moeLayerFunctionEquiv (n : Nat) (V : Type*) :
    MoELayer n V ≃ (Fin n → Expert V) where
  toFun M := M.experts
  invFun f := f
  left_inv M := rfl
  right_inv f := rfl

instance moeLayerTopologicalSpace (n : Nat) (V : Type*)
    [TopologicalSpace V] : TopologicalSpace (MoELayer n V) :=
  inferInstance

def arnoldMajoranaNetworkFunctionEquiv (n : Nat) :
    ArnoldMajoranaNetwork n E ≃
      (Fin n → (ArnoldMajoranaCarrier E → ArnoldMajoranaCarrier E)) where
  toFun N := fun e => (N.moe.experts e).apply
  invFun f := { moe := fun e => f e }
  left_inv N := by cases N; rfl
  right_inv f := rfl

instance arnoldMajoranaNetworkTopologicalSpace (n : Nat) :
    TopologicalSpace (ArnoldMajoranaNetwork n E) :=
  TopologicalSpace.induced
    (arnoldMajoranaNetworkFunctionEquiv (E := E) n).toFun inferInstance

instance arnoldMajoranaModuliTopologicalSpace (n : Nat) :
    TopologicalSpace (ArnoldMajoranaModuli n E) :=
  TopologicalSpace.coinduced
    (Quotient.mk (arnoldMajoranaNetworkSetoid n E)) inferInstance

theorem continuous_arnoldMajoranaNetworkFunctionEquiv (n : Nat) :
    Continuous
      (arnoldMajoranaNetworkFunctionEquiv (E := E) n :
      ArnoldMajoranaNetwork n E →
          (Fin n → (ArnoldMajoranaCarrier E → ArnoldMajoranaCarrier E))) :=
  continuous_induced_dom

def arnoldMajoranaModuliQuotientTopCat (n : Nat) :
    TopCat.of (ArnoldMajoranaNetwork n E) ⟶
      TopCat.of (ArnoldMajoranaModuli n E) :=
  TopCat.ofHom
    { toFun := Quotient.mk (arnoldMajoranaNetworkSetoid n E)
      continuous_toFun := continuous_coinduced_rng }

theorem arnoldMajoranaModuliQuotientTopCat_apply
    (n : Nat) (N : ArnoldMajoranaNetwork n E) :
    arnoldMajoranaModuliQuotientTopCat (E := E) n N =
      Quotient.mk (arnoldMajoranaNetworkSetoid n E) N :=
  rfl

theorem arnoldMajoranaModuliQuotient_surjective (n : Nat) :
    Function.Surjective (Quotient.mk (arnoldMajoranaNetworkSetoid n E) :
      ArnoldMajoranaNetwork n E → ArnoldMajoranaModuli n E) := by
  intro q
  exact Quotient.inductionOn q (fun N => ⟨N, rfl⟩)

def descendContinuousModuliObservable
    (n : Nat) (f : ArnoldMajoranaNetwork n E → ℝ)
    (hf : ∀ N₁ N₂, ArnoldMajoranaNetworkRel n N₁ N₂ → f N₁ = f N₂) :
    ArnoldMajoranaModuli n E → ℝ :=
  Quotient.lift f (by
    intro N₁ N₂ hN
    exact hf N₁ N₂ hN)

theorem descendContinuousModuliObservable_mk
    (n : Nat) (f : ArnoldMajoranaNetwork n E → ℝ)
    (hf : ∀ N₁ N₂, ArnoldMajoranaNetworkRel n N₁ N₂ → f N₁ = f N₂)
    (N : ArnoldMajoranaNetwork n E) :
    descendContinuousModuliObservable (E := E) n f hf
      (Quotient.mk (arnoldMajoranaNetworkSetoid n E) N) = f N :=
  rfl

theorem continuous_descendContinuousModuliObservable
    (n : Nat) (f : ArnoldMajoranaNetwork n E → ℝ)
    (hcont : Continuous f)
    (hf : ∀ N₁ N₂, ArnoldMajoranaNetworkRel n N₁ N₂ → f N₁ = f N₂) :
    Continuous (descendContinuousModuliObservable (E := E) n f hf) := by
  exact hcont.quotient_lift hf

theorem descendContinuousModuliObservable_unique
    (n : Nat) (f : ArnoldMajoranaNetwork n E → ℝ)
    (hf : ∀ N₁ N₂, ArnoldMajoranaNetworkRel n N₁ N₂ → f N₁ = f N₂)
    (g : ArnoldMajoranaModuli n E → ℝ)
    (hg : ∀ N : ArnoldMajoranaNetwork n E,
      g (Quotient.mk (arnoldMajoranaNetworkSetoid n E) N) = f N) :
    g = descendContinuousModuliObservable (E := E) n f hf := by
  funext q
  refine Quotient.inductionOn q ?_
  intro N
  rw [hg, descendContinuousModuliObservable_mk]

/-!
The following readout is deliberately finite and symmetric: it records the
sum of the norms of all expert outputs on one carrier vector.  It therefore
descends through the permutation quotient without introducing any analytic
claim about a neural-network limit.
-/

def symmetricExpertNormReadout
    (n : Nat) (v : ArnoldMajoranaCarrier E)
    (N : ArnoldMajoranaNetwork n E) : ℝ :=
  ∑ e : Fin n, ‖(N.moe.experts e).apply v‖

theorem continuous_symmetricExpertNormReadout
    (n : Nat) (v : ArnoldMajoranaCarrier E) :
    Continuous (symmetricExpertNormReadout (E := E) n v) := by
  have hcoord := continuous_arnoldMajoranaNetworkFunctionEquiv (E := E) n
  apply continuous_finset_sum Finset.univ
  intro e he
  have he' :
      Continuous (fun N =>
        (arnoldMajoranaNetworkFunctionEquiv (E := E) n N) e) :=
    (continuous_apply e).comp hcoord
  have hev :
      Continuous (fun N =>
        ((arnoldMajoranaNetworkFunctionEquiv (E := E) n N) e) v) :=
    (continuous_apply v).comp he'
  simpa [symmetricExpertNormReadout] using hev.norm

theorem symmetricExpertNormReadout_nonneg
    (n : Nat) (v : ArnoldMajoranaCarrier E)
    (N : ArnoldMajoranaNetwork n E) :
    0 ≤ symmetricExpertNormReadout (E := E) n v N := by
  exact Finset.sum_nonneg (fun e he => norm_nonneg _)

theorem symmetricExpertNormReadout_sublevel_isClosed
    (n : Nat) (v : ArnoldMajoranaCarrier E) (c : ℝ) :
    IsClosed {N : ArnoldMajoranaNetwork n E |
      symmetricExpertNormReadout (E := E) n v N ≤ c} := by
  change IsClosed
    ((symmetricExpertNormReadout (E := E) n v) ⁻¹' Set.Iic c)
  exact isClosed_Iic.preimage
    (continuous_symmetricExpertNormReadout (E := E) n v)

theorem symmetricExpertNormReadout_rel
    (n : Nat) (v : ArnoldMajoranaCarrier E) :
    ∀ N₁ N₂, ArnoldMajoranaNetworkRel n N₁ N₂ →
      symmetricExpertNormReadout (E := E) n v N₁ =
        symmetricExpertNormReadout (E := E) n v N₂ := by
  intro N₁ N₂ hrel
  rcases hrel with ⟨σ, hσ⟩
  apply Fintype.sum_equiv σ
  intro e
  simpa [symmetricExpertNormReadout] using
    congrArg (fun f : ArnoldMajoranaCarrier E → ArnoldMajoranaCarrier E =>
      ‖f v‖) (congrArg Expert.apply (hσ e))

def symmetricExpertNormReadoutOnModuli
    (n : Nat) (v : ArnoldMajoranaCarrier E) :
    ArnoldMajoranaModuli n E → ℝ :=
  descendContinuousModuliObservable (E := E) n
    (symmetricExpertNormReadout (E := E) n v)
    (symmetricExpertNormReadout_rel (E := E) n v)

theorem continuous_symmetricExpertNormReadoutOnModuli
    (n : Nat) (v : ArnoldMajoranaCarrier E) :
    Continuous (symmetricExpertNormReadoutOnModuli (E := E) n v) := by
  exact continuous_descendContinuousModuliObservable (E := E) n
    (symmetricExpertNormReadout (E := E) n v)
    (continuous_symmetricExpertNormReadout (E := E) n v)
    (symmetricExpertNormReadout_rel (E := E) n v)

theorem symmetricExpertNormReadout_levelSet_isClosed
    (n : Nat) (v : ArnoldMajoranaCarrier E) (c : ℝ) :
    IsClosed {N : ArnoldMajoranaNetwork n E |
      symmetricExpertNormReadout (E := E) n v N = c} := by
  simpa only [Set.preimage, Set.mem_setOf_eq] using
    (isClosed_singleton : IsClosed ({c} : Set ℝ)).preimage
      (continuous_symmetricExpertNormReadout (E := E) n v)

theorem symmetricExpertNormReadoutOnModuli_levelSet_isClosed
    (n : Nat) (v : ArnoldMajoranaCarrier E) (c : ℝ) :
    IsClosed {q : ArnoldMajoranaModuli n E |
      symmetricExpertNormReadoutOnModuli (E := E) n v q = c} := by
  simpa only [Set.preimage, Set.mem_setOf_eq] using
    (isClosed_singleton : IsClosed ({c} : Set ℝ)).preimage
      (continuous_symmetricExpertNormReadoutOnModuli (E := E) n v)

theorem symmetricExpertNormReadoutOnModuli_mk
    (n : Nat) (v : ArnoldMajoranaCarrier E)
    (N : ArnoldMajoranaNetwork n E) :
    symmetricExpertNormReadoutOnModuli (E := E) n v
        (Quotient.mk (arnoldMajoranaNetworkSetoid n E) N) =
      symmetricExpertNormReadout (E := E) n v N :=
  descendContinuousModuliObservable_mk (E := E) n
    (symmetricExpertNormReadout (E := E) n v)
    (symmetricExpertNormReadout_rel (E := E) n v) N

theorem symmetricExpertNormReadoutOnModuli_nonneg
    (n : Nat) (v : ArnoldMajoranaCarrier E)
    (q : ArnoldMajoranaModuli n E) :
    0 ≤ symmetricExpertNormReadoutOnModuli (E := E) n v q := by
  refine Quotient.inductionOn q ?_
  intro N
  simpa only [symmetricExpertNormReadoutOnModuli_mk] using
    symmetricExpertNormReadout_nonneg (E := E) n v N

theorem symmetricExpertNormReadoutOnModuli_sublevel_isClosed
    (n : Nat) (v : ArnoldMajoranaCarrier E) (c : ℝ) :
    IsClosed {q : ArnoldMajoranaModuli n E |
      symmetricExpertNormReadoutOnModuli (E := E) n v q ≤ c} := by
  change IsClosed
    ((symmetricExpertNormReadoutOnModuli (E := E) n v) ⁻¹' Set.Iic c)
  exact isClosed_Iic.preimage
    (continuous_symmetricExpertNormReadoutOnModuli (E := E) n v)

/-!
For finitely many probe vectors, the scalar readouts assemble into a
continuous map to the finite product `Fin m → ℝ`.  This avoids assuming a
jointly continuous evaluation map on an unrestricted function space.
-/

def symmetricExpertNormReadoutVector
    (n m : Nat) (vs : Fin m → ArnoldMajoranaCarrier E)
    (N : ArnoldMajoranaNetwork n E) : Fin m → ℝ :=
  fun k => symmetricExpertNormReadout (E := E) n (vs k) N

theorem continuous_symmetricExpertNormReadoutVector
    (n m : Nat) (vs : Fin m → ArnoldMajoranaCarrier E) :
    Continuous (symmetricExpertNormReadoutVector (E := E) n m vs) := by
  exact continuous_pi (fun k =>
    continuous_symmetricExpertNormReadout (E := E) n (vs k))

def symmetricExpertNormReadoutVectorOnModuli
    (n m : Nat) (vs : Fin m → ArnoldMajoranaCarrier E) :
    ArnoldMajoranaModuli n E → Fin m → ℝ :=
  fun q => fun k =>
    symmetricExpertNormReadoutOnModuli (E := E) n (vs k) q

theorem continuous_symmetricExpertNormReadoutVectorOnModuli
    (n m : Nat) (vs : Fin m → ArnoldMajoranaCarrier E) :
    Continuous (symmetricExpertNormReadoutVectorOnModuli (E := E) n m vs) := by
  exact continuous_pi (fun k =>
    continuous_symmetricExpertNormReadoutOnModuli (E := E) n (vs k))

theorem symmetricExpertNormReadoutVectorOnModuli_mk
    (n m : Nat) (vs : Fin m → ArnoldMajoranaCarrier E)
    (N : ArnoldMajoranaNetwork n E) :
    symmetricExpertNormReadoutVectorOnModuli (E := E) n m vs
        (Quotient.mk (arnoldMajoranaNetworkSetoid n E) N) =
      symmetricExpertNormReadoutVector (E := E) n m vs N := by
  funext k
  exact symmetricExpertNormReadoutOnModuli_mk (E := E) n (vs k) N

theorem symmetricExpertNormReadoutVectorOnModuli_fiber_isClosed
    (n m : Nat) (vs : Fin m → ArnoldMajoranaCarrier E)
    (y : Fin m → ℝ) :
    IsClosed {q : ArnoldMajoranaModuli n E |
      symmetricExpertNormReadoutVectorOnModuli (E := E) n m vs q = y} := by
  simpa only [Set.preimage, Set.mem_setOf_eq] using
    (isClosed_singleton : IsClosed ({y} : Set (Fin m → ℝ))).preimage
      (continuous_symmetricExpertNormReadoutVectorOnModuli
        (E := E) n m vs)

end InfoGeometry.Canonical.MoE
