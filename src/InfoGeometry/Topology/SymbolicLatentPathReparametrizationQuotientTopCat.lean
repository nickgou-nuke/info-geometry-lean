import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathReparametrizationComposition

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Topological and categorical structure of reparametrization actions

The quotient reparametrization is a genuine continuous map for the quotient
topology, and its composition law is recorded in `TopCat`.
-/

theorem continuous_reparametrizeSymbolicLatentPathHomotopyQuotient
    {X : Type*} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization) :
    Continuous
      (reparametrizeSymbolicLatentPathHomotopyQuotient (X := X) R) := by
  have hq : Continuous (symbolicLatentPathHomotopyQuotientMap (X := X)) :=
    @continuous_quotient_mk' (SymbolicLatentPath X) _
      (symbolicLatentPathHomotopySetoid (X := X))
  have hp : Continuous
      (reparametrizeSymbolicLatentPath R :
        SymbolicLatentPath X → SymbolicLatentPath X) :=
    ContinuousMap.continuous_precomp R.parameter
  exact Continuous.quotient_lift (hq.comp hp) (by
    intro γ₀ γ₁ h
    exact @Quotient.sound (SymbolicLatentPath X)
      (symbolicLatentPathHomotopySetoid (X := X))
      (reparametrizeSymbolicLatentPath R γ₀)
      (reparametrizeSymbolicLatentPath R γ₁)
      ⟨reparametrizeSymbolicLatentPathHomotopy R h.some⟩)

noncomputable def symbolicLatentPathReparametrizationTopCatHom
    {X : Type*} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization) :
    TopCat.of (SymbolicLatentPathHomotopyQuotient (X := X)) ⟶
      TopCat.of (SymbolicLatentPathHomotopyQuotient (X := X)) :=
  TopCat.ofHom
    { toFun := reparametrizeSymbolicLatentPathHomotopyQuotient (X := X) R
      continuous_toFun :=
        continuous_reparametrizeSymbolicLatentPathHomotopyQuotient (X := X) R }

theorem symbolicLatentPathReparametrizationTopCatHom_apply
    {X : Type*} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    symbolicLatentPathReparametrizationTopCatHom R q =
      reparametrizeSymbolicLatentPathHomotopyQuotient (X := X) R q :=
  rfl

theorem symbolicLatentPathReparametrizationTopCatHom_comp
    {X : Type*} [TopologicalSpace X]
    (R S : SymbolicLatentPathReparametrization) :
    symbolicLatentPathReparametrizationTopCatHom (X := X)
        (composeSymbolicLatentPathReparametrization R S) =
      symbolicLatentPathReparametrizationTopCatHom (X := X) S ≫
        symbolicLatentPathReparametrizationTopCatHom (X := X) R := by
  ext q
  change reparametrizeSymbolicLatentPathHomotopyQuotient (X := X)
      (composeSymbolicLatentPathReparametrization R S) q =
    reparametrizeSymbolicLatentPathHomotopyQuotient (X := X) R
      (reparametrizeSymbolicLatentPathHomotopyQuotient (X := X) S q)
  exact (reparametrizeSymbolicLatentPathHomotopyQuotient_comp
    (X := X) R S q).symm

theorem symbolicLatentPathReparametrizationTopCatHom_comp_apply
    {X : Type*} [TopologicalSpace X]
    (R S : SymbolicLatentPathReparametrization)
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    symbolicLatentPathReparametrizationTopCatHom (X := X)
        (composeSymbolicLatentPathReparametrization R S) q =
      (symbolicLatentPathReparametrizationTopCatHom (X := X) S ≫
        symbolicLatentPathReparametrizationTopCatHom (X := X) R) q := by
  exact congrArg (fun h => h q)
    (symbolicLatentPathReparametrizationTopCatHom_comp
      (X := X) (R := R) (S := S))

theorem symbolicLatentPathReparametrizationTopCatHom_eq_id
    {X : Type*} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization) :
    symbolicLatentPathReparametrizationTopCatHom (X := X) R =
      𝟙 (TopCat.of (SymbolicLatentPathHomotopyQuotient (X := X))) := by
  ext q
  change reparametrizeSymbolicLatentPathHomotopyQuotient (X := X) R q = q
  exact congrFun (reparametrizeSymbolicLatentPathHomotopyQuotient_id
    (X := X) R) q

theorem symbolicLatentPathReparametrizationTopCatHom_isIso
    {X : Type*} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization) :
    IsIso (symbolicLatentPathReparametrizationTopCatHom (X := X) R) := by
  rw [symbolicLatentPathReparametrizationTopCatHom_eq_id (X := X) R]
  infer_instance

end InfoGeometry.Topology
