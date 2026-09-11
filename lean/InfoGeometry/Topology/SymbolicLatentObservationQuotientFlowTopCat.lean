import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentObservationQuotientFlow
import InfoGeometry.Topology.SymbolicLatentQuotientFlowHomeomorph
import InfoGeometry.Topology.SymbolicLatentQuotientOrbitClosure

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` readout of the observational symbolic-latent quotient flow

The observational quotient already carries a descended continuous flow.  This
file exposes its time slices as categorical morphisms and homeomorphisms.  No
extra quotient-topology or dynamical property is introduced here: continuity
remains the explicit property required by the quotient-flow owner.
-/

abbrev SymbolicLatentObservationQuotientObject
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :=
  TopCat.of (SymbolicLatentObservationQuotient S)

def SymbolicLatentObservableModularFlow.observationQuotientFlowActionTopCatHom
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2)) :
    TopCat.of (ℝ × SymbolicLatentObservationQuotient S) ⟶
      TopCat.of (SymbolicLatentObservationQuotient S) :=
  TopCat.ofHom
    { toFun := fun p => descendedSymbolicLatentObservationFlow Φ p.1 p.2
      continuous_toFun := h_cont }

@[simp] theorem SymbolicLatentObservableModularFlow.observationQuotientFlowActionTopCatHom_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (p : ℝ × SymbolicLatentObservationQuotient S) :
    Φ.observationQuotientFlowActionTopCatHom h_cont p =
      descendedSymbolicLatentObservationFlow Φ p.1 p.2 :=
  rfl

def SymbolicLatentObservableModularFlow.observationQuotientFlowHomeomorph
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    SymbolicLatentObservationQuotient S ≃ₜ
      SymbolicLatentObservationQuotient S :=
  (symbolicLatentObservationQuotientFlow Φ h_cont).actHomeomorph t

@[simp] theorem SymbolicLatentObservableModularFlow.observationQuotientFlowHomeomorph_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) (q : SymbolicLatentObservationQuotient S) :
    Φ.observationQuotientFlowHomeomorph h_cont t q =
      descendedSymbolicLatentObservationFlow Φ t q :=
  rfl

def SymbolicLatentObservableModularFlow.observationQuotientFlowTopCatHom
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    TopCat.of (SymbolicLatentObservationQuotient S) ⟶
      TopCat.of (SymbolicLatentObservationQuotient S) :=
  TopCat.ofHom
    { toFun := descendedSymbolicLatentObservationFlow Φ t
      continuous_toFun := by
        exact (Φ.observationQuotientFlowHomeomorph h_cont t).continuous }

@[simp] theorem SymbolicLatentObservableModularFlow.observationQuotientFlowTopCatHom_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) (q : SymbolicLatentObservationQuotient S) :
    Φ.observationQuotientFlowTopCatHom h_cont t q =
      descendedSymbolicLatentObservationFlow Φ t q :=
  rfl

theorem SymbolicLatentObservableModularFlow.observationQuotientFlowTopCatHom_zero
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2)) :
    Φ.observationQuotientFlowTopCatHom h_cont 0 =
      𝟙 (TopCat.of (SymbolicLatentObservationQuotient S)) := by
  ext q
  change descendedSymbolicLatentObservationFlow Φ 0 q = q
  exact (symbolicLatentObservationQuotientFlow Φ h_cont).act_zero q

theorem SymbolicLatentObservableModularFlow.observationQuotientFlowTopCatHom_add
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (s t : ℝ) :
    Φ.observationQuotientFlowTopCatHom h_cont (s + t) =
      Φ.observationQuotientFlowTopCatHom h_cont s ≫
        Φ.observationQuotientFlowTopCatHom h_cont t := by
  ext q
  simpa [SymbolicLatentObservableModularFlow.observationQuotientFlowTopCatHom,
    CategoryTheory.comp_apply, add_comm] using
    (symbolicLatentObservationQuotientFlow Φ h_cont).act_add t s q

@[simp] theorem SymbolicLatentObservableModularFlow.observationQuotientFlowTopCatHom_add_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (s t : ℝ) (q : SymbolicLatentObservationQuotient S) :
    Φ.observationQuotientFlowTopCatHom h_cont (s + t) q =
      Φ.observationQuotientFlowTopCatHom h_cont t
        (Φ.observationQuotientFlowTopCatHom h_cont s q) := by
  simpa [CategoryTheory.comp_apply] using
    congrArg (fun f => f q) (Φ.observationQuotientFlowTopCatHom_add h_cont s t)

theorem SymbolicLatentObservableModularFlow.observationQuotientFlowTopCatHom_comp
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t s : ℝ) :
    Φ.observationQuotientFlowTopCatHom h_cont t ≫
      Φ.observationQuotientFlowTopCatHom h_cont s =
        Φ.observationQuotientFlowTopCatHom h_cont (t + s) := by
  simpa using (observationQuotientFlowTopCatHom_add (Φ := Φ) h_cont t s).symm

@[simp] theorem SymbolicLatentObservableModularFlow.observationQuotientFlowTopCatHom_comp_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t s : ℝ) (q : SymbolicLatentObservationQuotient S) :
    (Φ.observationQuotientFlowTopCatHom h_cont t ≫
      Φ.observationQuotientFlowTopCatHom h_cont s) q =
        Φ.observationQuotientFlowTopCatHom h_cont (t + s) q := by
  simpa [CategoryTheory.comp_apply] using
    congrArg (fun f => f q) (Φ.observationQuotientFlowTopCatHom_comp h_cont t s)

@[simp] theorem SymbolicLatentObservableModularFlow.observationQuotientFlowTopCatHom_neg_left_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) (q : SymbolicLatentObservationQuotient S) :
    Φ.observationQuotientFlowTopCatHom h_cont (-t)
        (Φ.observationQuotientFlowTopCatHom h_cont t q) = q := by
  calc
    Φ.observationQuotientFlowTopCatHom h_cont (-t)
        (Φ.observationQuotientFlowTopCatHom h_cont t q) =
      Φ.observationQuotientFlowTopCatHom h_cont 0 q := by
        simpa [CategoryTheory.comp_apply] using
          congrArg (fun f => f q)
            (Φ.observationQuotientFlowTopCatHom_comp h_cont t (-t))
    _ = q := by
      simpa using
        congrArg (fun f => f q)
          (Φ.observationQuotientFlowTopCatHom_zero h_cont)

@[simp] theorem SymbolicLatentObservableModularFlow.observationQuotientFlowTopCatHom_neg_right_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) (q : SymbolicLatentObservationQuotient S) :
    Φ.observationQuotientFlowTopCatHom h_cont t
        (Φ.observationQuotientFlowTopCatHom h_cont (-t) q) = q := by
  calc
    Φ.observationQuotientFlowTopCatHom h_cont t
        (Φ.observationQuotientFlowTopCatHom h_cont (-t) q) =
      Φ.observationQuotientFlowTopCatHom h_cont 0 q := by
        simpa [CategoryTheory.comp_apply] using
          congrArg (fun f => f q)
            (Φ.observationQuotientFlowTopCatHom_comp h_cont (-t) t)
    _ = q := by
      simpa using
        congrArg (fun f => f q)
          (Φ.observationQuotientFlowTopCatHom_zero h_cont)

theorem SymbolicLatentObservableModularFlow.observationQuotientFlowTopCatHom_isIso
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    IsIso (Φ.observationQuotientFlowTopCatHom h_cont t) := by
  exact (TopCat.isIso_iff_isHomeomorph
    (Φ.observationQuotientFlowTopCatHom h_cont t)).2
      (Φ.observationQuotientFlowHomeomorph h_cont t).isHomeomorph

theorem SymbolicLatentObservableModularFlow.observationQuotientFlow_commutes_with_projection
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) (x : X) :
    Φ.observationQuotientFlowTopCatHom h_cont t
        (symbolicLatentObservationQuotientMap S x) =
      symbolicLatentObservationQuotientMap S (Φ.act t x) :=
  descendedSymbolicLatentObservationFlow_mk Φ t x

theorem SymbolicLatentObservableModularFlow.observationQuotientFlowHomeomorph_image_orbitClosure
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) (q : SymbolicLatentObservationQuotient S) :
    Φ.observationQuotientFlowHomeomorph h_cont t ''
        (symbolicLatentObservationQuotientFlow Φ h_cont).orbitClosure q =
      (symbolicLatentObservationQuotientFlow Φ h_cont).orbitClosure
        (descendedSymbolicLatentObservationFlow Φ t q) :=
  (symbolicLatentObservationQuotientFlow Φ h_cont).actHomeomorph_image_orbitClosure t q

end InfoGeometry.Topology
