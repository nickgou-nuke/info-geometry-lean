/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SpectralTriple
import InfoGeometry.OperatorAlgebra.RealPhaseSpectralTriple
import InfoGeometry.KK.RealSplitKreinKasparovCycle
import InfoGeometry.KK.RealSplitKreinUnboundedCycle
import InfoGeometry.KK.RealSplitKreinBoundedTransform
import InfoGeometry.KK.CompactOperatorBridge
import InfoGeometry.KK.ClNNFredholmBridge
import InfoGeometry.KK.RealSplitKreinHilbertizationBridge
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped InnerProductSpace

/-!
# Spectral Triple to Real Split-Krein Kasparov Cycle Bridge

End-to-end bridge connecting:
1. `OperatorAlgebra.SpectralTriple` (`PhaseRealSpectralTriple`,
   `KreinPhaseRealSpectralTriple`, `RealStructureKreinCompatible`),
2. `KK.RealSplitKreinUnboundedCycle` (both via domain-level
   `DomainKreinSpectralTripleData` and via bounded `PhaseRealSpectralTriple` /
   `KreinPhaseRealSpectralTriple` on `domain := Set.univ`),
3. `KK.RealSplitKreinKasparovCycle` via both the `BUCKET 3` resolvent bounded
   transform (`RealSplitKreinBoundedTransform`) and the `BUCKET 2`
   finite-dimensional `CFC.sqrt` bounded transform (`finiteDimPhase`),
4. Read-only alignment bridges with
   `OperatorAlgebra.RealPhaseSpectralTriple`, and
5. A concrete nontrivial witness on M3.2's `SplitDoubledSpace` carrier.

### Evidence Boundaries (`BUCKET 2` vs `BUCKET 3`)
- **`BUCKET 2`**: Bounded `PhaseRealSpectralTriple` /
  `KreinPhaseRealSpectralTriple` → `RealSplitKreinUnboundedCycle A ℝ H` on
  `domain := Set.univ`; finite-dimensional `CFC.sqrt (1 + D²)` bounded transform
  to `RealSplitKreinKasparovCycle A ℝ H`; zero-shift resolvent oddness and
  Krein skew-adjointness.
- **`BUCKET 3`**: General infinite-dimensional unbounded functional calculus
  `D (1 + D²)^(-1/2)` and genuine right Hilbert/Krein `B`-module Kasparov
  products remain open (`DomainKreinSpectralTripleData` packages the dense
  closed domain, resolvent, and commutator bound into `RealSplitKreinUnboundedCycle`).
-/

noncomputable section

namespace InfoGeometry.KK.SpectralTripleKreinCycleBridge

open InfoGeometry.KK InfoGeometry.Krein InfoGeometry.Quantum
open InfoGeometry.KK.ClNNFredholmBridge
open InfoGeometry.OperatorAlgebra

section Helpers

/-- Lift a `SpectralTriple.RepresentedAlgebra` to an `ℝ`-algebra homomorphism
`A →ₐ[ℝ] EndH H` when `rep` respects real scalar multiplication. -/
def repToAlgHom
    {A H : Type*} [Ring A] [Algebra ℝ A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : SpectralTriple.RepresentedAlgebra A H)
    (hsmul : ∀ (r : ℝ) (a : A), ρ.rep (r • a) = r • ρ.rep a) :
    A →ₐ[ℝ] EndH H where
  toFun := ρ.rep
  map_one' := ρ.rep.map_one
  map_mul' := ρ.rep.map_mul
  map_zero' := ρ.rep.map_zero
  map_add' := ρ.rep.map_add
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, hsmul r 1, ρ.rep.map_one,
      Algebra.algebraMap_eq_smul_one]

/-- Scalar endomorphisms `Algebra.ofId ℝ (EndH H) b` are grading-even. -/
lemma scalarAlgHom_isEven
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    (b : ℝ) :
    KreinGradedModule.IsEven (H := H) (Algebra.ofId ℝ (EndH H) b) := by
  unfold KreinGradedModule.IsEven KreinGradedModule.gradeConj
  apply ContinuousLinearMap.ext
  intro x
  change KreinGradedModule.gradeCLM (H := H) (b • KreinGradedModule.gradeCLM (H := H) x) =
    b • x
  rw [map_smul, KreinGradedModule.gradeCLM_apply, KreinGradedModule.gradeCLM_apply,
    KreinGradedModule.grade_invol]

/-- Characterization of `KreinSpace.IsKreinSkewAdjoint` via `kreinInner`. -/
theorem isKreinSkewAdjoint_iff_kreinInner
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] (D : EndH H) :
    KreinSpace.IsKreinSkewAdjoint (H := H) D ↔
      ∀ x y : H, KreinSpace.kreinInner (H := H) (D x) y +
        KreinSpace.kreinInner (H := H) x (D y) = 0 :=
  KreinSpace.isKreinSkewAdjoint_iff D

/-- Hilbert-self-adjoint operators that anticommute with `KreinSpace.jCLM` are
Krein-skew-adjoint. -/
theorem isKreinSkewAdjoint_of_adjoint_eq_self_of_anticomm_jCLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] (D : EndH H)
    (hsa : ContinuousLinearMap.adjoint D = D)
    (hanti : (KreinSpace.jCLM (H := H)).comp D = -(D.comp (KreinSpace.jCLM (H := H)))) :
    KreinSpace.IsKreinSkewAdjoint (H := H) D :=
  (RealSplitKreinHilbertizationBridge.isKreinSkewAdjoint_of_anticommute_j D hanti).2
    (ContinuousLinearMap.isSelfAdjoint_iff'.mpr hsa)

/-- When a compact resolvent `R` has `spectralParameter = 0` (so `D R = 1 = R D`),
oddness of `D` relative to `gradeCLM` forces `R` to be odd. -/
theorem resolvent_isOdd_of_zero_shift
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    {D : EndH H} (C : SpectralTriple.CompactResolventData D)
    (hzero : C.spectralParameter = 0)
    (hD_odd : D.comp (KreinGradedModule.gradeCLM (H := H)) +
      (KreinGradedModule.gradeCLM (H := H)).comp D = 0) :
    KreinGradedModule.IsOdd (H := H) C.resolvent := by
  have hDR : D.comp C.resolvent = ContinuousLinearMap.id ℝ H := by
    simpa [hzero] using C.shift_comp_resolvent
  have hRD : C.resolvent.comp D = ContinuousLinearMap.id ℝ H := by
    simpa [hzero] using C.resolvent_comp_shift
  have hGammaD :
      (KreinGradedModule.gradeCLM (H := H)).comp D =
        -(D.comp (KreinGradedModule.gradeCLM (H := H))) :=
    eq_neg_of_add_eq_zero_right hD_odd
  have hConjDR :
      (KreinGradedModule.gradeConj (H := H) C.resolvent).comp D =
        -(ContinuousLinearMap.id ℝ H) := by
    let Γ := KreinGradedModule.gradeCLM (H := H)
    have hG2 : Γ.comp Γ = ContinuousLinearMap.id ℝ H :=
      KreinGradedModule.gradeCLM_comp_self (H := H)
    calc
      (KreinGradedModule.gradeConj (H := H) C.resolvent).comp D
          = Γ.comp (C.resolvent.comp (Γ.comp D)) := by
            simp [KreinGradedModule.gradeConj, Γ, ContinuousLinearMap.comp_assoc]
      _ = Γ.comp (C.resolvent.comp (-(D.comp Γ))) := by rw [hGammaD]
      _ = -(Γ.comp ((C.resolvent.comp D).comp Γ)) := by
            simp [ContinuousLinearMap.comp_assoc]
      _ = -(Γ.comp Γ) := by rw [hRD, ContinuousLinearMap.id_comp]
      _ = -(ContinuousLinearMap.id ℝ H) := by rw [hG2]
  calc
    KreinGradedModule.gradeConj (H := H) C.resolvent
        = (KreinGradedModule.gradeConj (H := H) C.resolvent).comp
            (ContinuousLinearMap.id ℝ H) := by
          simp
    _ = (KreinGradedModule.gradeConj (H := H) C.resolvent).comp (D.comp C.resolvent) := by
          rw [hDR]
    _ = ((KreinGradedModule.gradeConj (H := H) C.resolvent).comp D).comp C.resolvent := by
          simp only [ContinuousLinearMap.comp_assoc]
    _ = (-(ContinuousLinearMap.id ℝ H)).comp C.resolvent := by rw [hConjDR]
    _ = -C.resolvent := by simp

/-- When a compact resolvent `R` has `spectralParameter = 0` (so `D R = 1 = R D`),
Krein skew-adjointness of `D` forces `R` to be Krein-skew-adjoint. -/
theorem resolvent_isKreinSkewAdjoint_of_zero_shift
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {D : EndH H} (C : SpectralTriple.CompactResolventData D)
    (hzero : C.spectralParameter = 0)
    (hD_skew : KreinSpace.IsKreinSkewAdjoint (H := H) D) :
    KreinSpace.IsKreinSkewAdjoint (H := H) C.resolvent := by
  have hDR : D.comp C.resolvent = ContinuousLinearMap.id ℝ H := by
    simpa [hzero] using C.shift_comp_resolvent
  have hRD : C.resolvent.comp D = ContinuousLinearMap.id ℝ H := by
    simpa [hzero] using C.resolvent_comp_shift
  have hAdjDR : (KreinSpace.kreinAdjoint (H := H) C.resolvent).comp D =
      -(ContinuousLinearMap.id ℝ H) := by
    have h1 := congrArg (KreinSpace.kreinAdjoint (H := H)) hDR
    rw [KreinSpace.kreinAdjoint_comp, KreinSpace.kreinAdjoint_id, hD_skew] at h1
    have h2 : -((KreinSpace.kreinAdjoint (H := H) C.resolvent).comp D) =
        ContinuousLinearMap.id ℝ H := by
      simpa using h1
    simpa using congrArg Neg.neg h2
  unfold KreinSpace.IsKreinSkewAdjoint
  calc
    KreinSpace.kreinAdjoint (H := H) C.resolvent
        = (KreinSpace.kreinAdjoint (H := H) C.resolvent).comp
            (ContinuousLinearMap.id ℝ H) := by simp
    _ = (KreinSpace.kreinAdjoint (H := H) C.resolvent).comp (D.comp C.resolvent) := by
          rw [hDR]
    _ = ((KreinSpace.kreinAdjoint (H := H) C.resolvent).comp D).comp C.resolvent := by
          simp only [ContinuousLinearMap.comp_assoc]
    _ = (-(ContinuousLinearMap.id ℝ H)).comp C.resolvent := by rw [hAdjDR]
    _ = -C.resolvent := by simp

end Helpers

section DomainLevelBridge

/--
Domain-level Krein-compatible spectral triple data (`BUCKET 2/3` boundary).

Unlike `PhaseRealSpectralTriple` (whose `D` is bounded on `Set.univ`), this
structure allows an arbitrary dense closed `domain : Set H`, domain-level
Krein skew-adjointness, `RealStructureKreinCompatible` relative to `KreinSpace.kreinInner`,
a compact resolvent packet `RealSplitKreinResolventData`, and bounded commutator
representatives with an explicit norm bound `commutatorBound`.
-/
structure DomainKreinSpectralTripleData
    (A H : Type*)
    [NormedRing A] [NormedAlgebra ℝ A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H] where
  signs : SpectralTriple.KOSigns
  phaseAxis : SpectralTriple.PhaseAxis H
  realStructure : SpectralTriple.RealStructure H phaseAxis signs
  realStructureKreinCompatible : SpectralTriple.RealStructureKreinCompatible realStructure
  cl11 : RealSplitCl11Action H
  π : A →ₐ[ℝ] EndH H
  π_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (π a)
  domain : Set H
  D : {x // x ∈ domain} → H
  dense_domain : Dense domain
  closed_graph : IsClosed (Set.range fun x : {x // x ∈ domain} => ((x.1, D x) : H × H))
  grade_preserves_domain : ∀ ⦃x : H⦄, x ∈ domain → KreinGradedModule.gradeCLM (H := H) x ∈ domain
  π_preserves_domain : ∀ a : A, ∀ ⦃x : H⦄, x ∈ domain → (π a) x ∈ domain
  domain_smul : ∀ (r : ℝ) ⦃x : H⦄, x ∈ domain → r • x ∈ domain
  D_odd :
    ∀ x : {x // x ∈ domain},
      D ⟨KreinGradedModule.gradeCLM (H := H) x.1, grade_preserves_domain x.2⟩ =
        -(KreinGradedModule.gradeCLM (H := H) (D x))
  D_krein_skewAdj :
    ∀ x y : {x // x ∈ domain},
      KreinSpace.kreinInner (H := H) (D x) y.1 + KreinSpace.kreinInner (H := H) x.1 (D y) = 0
  resolventData : RealSplitKreinResolventData H domain D
  commutator : A → EndH H
  commutator_add : ∀ a b : A, commutator (a + b) = commutator a + commutator b
  commutator_formula :
    ∀ a : A, ∀ x : {x // x ∈ domain},
      commutator a x.1 = D ⟨(π a) x.1, π_preserves_domain a x.2⟩ - (π a) (D x)
  commutatorBound : A → ℝ
  commutator_norm_le : ∀ a : A, ‖commutator a‖ ≤ commutatorBound a

/-- Convert domain-level Krein spectral triple data into `RealSplitKreinUnboundedCycle A ℝ H`. -/
def DomainKreinSpectralTripleData.toUnboundedCycle
    {A H : Type*}
    [NormedRing A] [NormedAlgebra ℝ A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    (X : DomainKreinSpectralTripleData A H) :
    RealSplitKreinUnboundedCycle A ℝ H where
  cl11 := X.cl11
  π := X.π
  ρ := Algebra.ofId ℝ (EndH H)
  π_even := X.π_even
  ρ_even := scalarAlgHom_isEven
  domain := X.domain
  D := X.D
  dense_domain := X.dense_domain
  closed_graph := X.closed_graph
  grade_preserves_domain := X.grade_preserves_domain
  π_preserves_domain := X.π_preserves_domain
  ρ_preserves_domain := fun b x hx => by
    change b • x ∈ X.domain
    exact X.domain_smul b hx
  D_odd := X.D_odd
  D_krein_skewAdj := X.D_krein_skewAdj
  resolventData := X.resolventData
  commutator := X.commutator
  commutator_add := X.commutator_add
  commutator_formula := X.commutator_formula

end DomainLevelBridge

section PhaseRealToCycles

/--
Package a Krein-compatible `SpectralTriple.PhaseRealSpectralTriple A H`
(satisfying `RealStructureKreinCompatible T.realStructure`) as domain-level
`DomainKreinSpectralTripleData A H` on `domain := Set.univ`.
-/
def phaseRealSpectralTriple_toDomainData
    {A H : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    (T : SpectralTriple.PhaseRealSpectralTriple A H)
    (hKrein : SpectralTriple.RealStructureKreinCompatible T.realStructure)
    (hD_skew : KreinSpace.IsKreinSkewAdjoint (H := H) T.spectralGenerator.D)
    (cl11 : RealSplitCl11Action H)
    (hpi_smul : ∀ (r : ℝ) (a : A),
      T.representedAlgebra.rep (r • a) = r • T.representedAlgebra.rep a)
    (hpi_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (T.representedAlgebra.rep a))
    (hchi : T.grading.chi = KreinGradedModule.gradeCLM (H := H)) :
    DomainKreinSpectralTripleData A H where
  signs := T.signs
  phaseAxis := T.phaseAxis
  realStructure := T.realStructure
  realStructureKreinCompatible := hKrein
  cl11 := cl11
  π := repToAlgHom T.representedAlgebra hpi_smul
  π_even := hpi_even
  domain := Set.univ
  D := fun x => T.spectralGenerator.D x.1
  dense_domain := dense_univ
  closed_graph := by
    have hset :
        (Set.range fun x : {x // x ∈ (Set.univ : Set H)} =>
          ((x.1, T.spectralGenerator.D x.1) : H × H)) =
          {p : H × H | p.2 = T.spectralGenerator.D p.1} := by
      ext ⟨u, v⟩
      simp [eq_comm]
    rw [hset]
    exact isClosed_eq continuous_snd (T.spectralGenerator.D.continuous.comp continuous_fst)
  grade_preserves_domain := fun _ _ => Set.mem_univ _
  π_preserves_domain := fun _ _ _ => Set.mem_univ _
  domain_smul := fun _ _ _ => Set.mem_univ _
  D_odd := fun x => by
    have hDodd := congrArg (fun S : EndH H => S x.1) T.D_odd
    simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply, hchi] at hDodd
    exact eq_neg_of_add_eq_zero_left hDodd
  D_krein_skewAdj := fun x y =>
    (KreinSpace.isKreinSkewAdjoint_iff (H := H) T.spectralGenerator.D).mp hD_skew x.1 y.1
  resolventData :=
    { shift := T.D_compactResolvent.spectralParameter
      resolvent := T.D_compactResolvent.resolvent
      resolvent_preserves_domain := fun _ => Set.mem_univ _
      left_resolvent := fun x => by
        have h := congrArg (fun S : EndH H => S x)
          T.D_compactResolvent.shift_comp_resolvent
        simpa [ContinuousLinearMap.comp_apply, sub_apply, smul_apply,
          ContinuousLinearMap.id_apply] using h
      compact := T.D_compactResolvent.resolvent_compact }
  commutator := fun a =>
    SpectralTriple.commutator T.spectralGenerator.D (T.representedAlgebra.rep a)
  commutator_add := by
    intro a b
    apply ContinuousLinearMap.ext
    intro v
    simp [SpectralTriple.commutator, map_add]
    abel
  commutator_formula := fun a x => by
    simp [SpectralTriple.commutator, repToAlgHom]
  commutatorBound := fun a => T.lipschitz a
  commutator_norm_le := fun a => le_rfl

/-- Bridge a Krein-compatible `PhaseRealSpectralTriple A H` to
`RealSplitKreinUnboundedCycle A ℝ H`. -/
def phaseRealSpectralTriple_toUnboundedCycle
    {A H : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    (T : SpectralTriple.PhaseRealSpectralTriple A H)
    (hKrein : T.IsKreinCompatible)
    (cl11 : RealSplitCl11Action H)
    (hpi_smul : ∀ (r : ℝ) (a : A),
      T.representedAlgebra.rep (r • a) = r • T.representedAlgebra.rep a)
    (hpi_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (T.representedAlgebra.rep a))
    (hchi : T.grading.chi = KreinGradedModule.gradeCLM (H := H)) :
    RealSplitKreinUnboundedCycle A ℝ H :=
  RealSplitKreinUnboundedCycle.toUnboundedCycle T hKrein cl11 hpi_smul hpi_even hchi

/-- Same bridge when `T.signs.epsJ = 1`, automatically extracting `RealSplitCl11Action H`
from `T.phaseAxis` and `T.realStructure`. -/
def phaseRealSpectralTriple_toUnboundedCycle_autoCl11
    {A H : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    (T : SpectralTriple.PhaseRealSpectralTriple A H)
    (hKrein : T.IsKreinCompatible)
    (hepsJ : T.signs.epsJ = 1)
    (hpi_smul : ∀ (r : ℝ) (a : A),
      T.representedAlgebra.rep (r • a) = r • T.representedAlgebra.rep a)
    (hpi_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (T.representedAlgebra.rep a))
    (hchi : T.grading.chi = KreinGradedModule.gradeCLM (H := H)) :
    RealSplitKreinUnboundedCycle A ℝ H :=
  RealSplitKreinUnboundedCycle.toUnboundedCycle T hKrein
    (RealSplitKreinUnboundedCycle.realSplitCl11ActionOfPhaseReal T.phaseAxis T.realStructure hepsJ)
    hpi_smul hpi_even hchi

/-- Bridge a Krein-native `SpectralTriple.KreinPhaseRealSpectralTriple A H`
(carrying `RealStructureKreinCompatible` natively) to `RealSplitKreinUnboundedCycle A ℝ H`. -/
def kreinPhaseRealSpectralTriple_toUnboundedCycle
    {A H : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    (T : SpectralTriple.KreinPhaseRealSpectralTriple A H)
    (cl11 : RealSplitCl11Action H)
    (hpi_smul : ∀ (r : ℝ) (a : A),
      T.representedAlgebra.rep (r • a) = r • T.representedAlgebra.rep a)
    (hpi_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (T.representedAlgebra.rep a))
    (hchi : T.grading.chi = KreinGradedModule.gradeCLM (H := H)) :
    RealSplitKreinUnboundedCycle A ℝ H where
  cl11 := cl11
  π := repToAlgHom T.representedAlgebra hpi_smul
  ρ := Algebra.ofId ℝ (EndH H)
  π_even := hpi_even
  ρ_even := scalarAlgHom_isEven
  domain := Set.univ
  D := fun x => T.spectralGenerator.D x.1
  dense_domain := dense_univ
  closed_graph := by
    have hset :
        (Set.range fun x : {x // x ∈ (Set.univ : Set H)} =>
          ((x.1, T.spectralGenerator.D x.1) : H × H)) =
          {p : H × H | p.2 = T.spectralGenerator.D p.1} := by
      ext ⟨u, v⟩
      simp [eq_comm]
    rw [hset]
    exact isClosed_eq continuous_snd (T.spectralGenerator.D.continuous.comp continuous_fst)
  grade_preserves_domain := fun _ _ => Set.mem_univ _
  π_preserves_domain := fun _ _ _ => Set.mem_univ _
  ρ_preserves_domain := fun _ _ _ => Set.mem_univ _
  D_odd := fun x => by
    have hDodd := congrArg (fun S : EndH H => S x.1) T.D_odd
    simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply, hchi] at hDodd
    exact eq_neg_of_add_eq_zero_left hDodd
  D_krein_skewAdj := fun x y =>
    (KreinSpace.isKreinSkewAdjoint_iff (H := H) T.spectralGenerator.D).mp
      T.D_kreinSkewAdjoint x.1 y.1
  resolventData :=
    { shift := T.D_compactResolvent.spectralParameter
      resolvent := T.D_compactResolvent.resolvent
      resolvent_preserves_domain := fun _ => Set.mem_univ _
      left_resolvent := fun x => by
        have h := congrArg (fun S : EndH H => S x)
          T.D_compactResolvent.shift_comp_resolvent
        simpa [ContinuousLinearMap.comp_apply, sub_apply, smul_apply,
          ContinuousLinearMap.id_apply] using h
      compact := T.D_compactResolvent.resolvent_compact }
  commutator := fun a =>
    SpectralTriple.commutator T.spectralGenerator.D (T.representedAlgebra.rep a)
  commutator_add := by
    intro a b
    apply ContinuousLinearMap.ext
    intro v
    simp [SpectralTriple.commutator, map_add]
    abel
  commutator_formula := fun a x => by
    simp [SpectralTriple.commutator, repToAlgHom]

/-- Path A (`BUCKET 3` resolvent phase): lift a `PhaseRealSpectralTriple` with
`RealStructureKreinCompatible` through `RealSplitKreinUnboundedCycle` and
`RealSplitKreinBoundedTransform` to `RealSplitKreinKasparovCycle A ℝ H`. -/
def phaseRealSpectralTriple_toKasparovCycle_viaResolvent
    {A H : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    (T : SpectralTriple.PhaseRealSpectralTriple A H)
    (hKrein : T.IsKreinCompatible)
    (cl11 : RealSplitCl11Action H)
    (hpi_smul : ∀ (r : ℝ) (a : A),
      T.representedAlgebra.rep (r • a) = r • T.representedAlgebra.rep a)
    (hpi_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (T.representedAlgebra.rep a))
    (hchi : T.grading.chi = KreinGradedModule.gradeCLM (H := H))
    (hodd : KreinGradedModule.IsOdd (H := H) T.D_compactResolvent.resolvent)
    (hskew : KreinSpace.IsKreinSkewAdjoint (H := H) T.D_compactResolvent.resolvent)
    (hsq : IsCompactEnd H
      (T.D_compactResolvent.resolvent * T.D_compactResolvent.resolvent - (1 : EndH H))) :
    RealSplitKreinKasparovCycle A ℝ H :=
  RealSplitKreinBoundedTransform.toRealSplitKreinKasparovCycle
    (X := phaseRealSpectralTriple_toUnboundedCycle T hKrein cl11 hpi_smul hpi_even hchi)
    { phase_odd := hodd
      phase_krein_skewAdj := hskew
      phase_sq_one_compact := hsq }

/-- Finite-dimensional zero-shift specialization of Path A: when
`[FiniteDimensional ℝ H]` and `T.D_compactResolvent.spectralParameter = 0`,
`phase_odd`, `phase_krein_skewAdj`, and `phase_sq_one_compact` are all discharged
automatically. -/
def phaseRealSpectralTriple_toKasparovCycle_finiteDimResolvent
    {A H : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H] [FiniteDimensional ℝ H]
    (T : SpectralTriple.PhaseRealSpectralTriple A H)
    (hKrein : T.IsKreinCompatible)
    (cl11 : RealSplitCl11Action H)
    (hpi_smul : ∀ (r : ℝ) (a : A),
      T.representedAlgebra.rep (r • a) = r • T.representedAlgebra.rep a)
    (hpi_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (T.representedAlgebra.rep a))
    (hchi : T.grading.chi = KreinGradedModule.gradeCLM (H := H))
    (hzero : T.D_compactResolvent.spectralParameter = 0) :
    RealSplitKreinKasparovCycle A ℝ H :=
  phaseRealSpectralTriple_toKasparovCycle_viaResolvent T hKrein cl11 hpi_smul hpi_even hchi
    (resolvent_isOdd_of_zero_shift T.D_compactResolvent hzero
      (by simpa [SpectralTriple.DiracOdd, hchi] using T.D_odd))
    (resolvent_isKreinSkewAdjoint_of_zero_shift T.D_compactResolvent hzero hKrein.2)
    (isCompactEnd_of_finiteDimensional (H := H) _)

/-- Path B (`BUCKET 2` finite-dimensional `CFC.sqrt` bounded transform):
construct `RealSplitKreinKasparovCycle A ℝ H` with phase
`F = D (1 + D²)⁻¹/²` from a Krein-compatible `PhaseRealSpectralTriple A H`
whose `operatorStar` is `ContinuousLinearMap.adjoint`. -/
def phaseRealSpectralTriple_toKasparovCycle_cfc
    {A H : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H] [FiniteDimensional ℝ H]
    (T : SpectralTriple.PhaseRealSpectralTriple A H)
    (hKrein : T.IsKreinCompatible)
    (hstar : T.operatorStar = (inferInstance : Star (EndH H)))
    (cl11 : RealSplitCl11Action H)
    (hpi_smul : ∀ (r : ℝ) (a : A),
      T.representedAlgebra.rep (r • a) = r • T.representedAlgebra.rep a)
    (hpi_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (T.representedAlgebra.rep a))
    (hchi : T.grading.chi = KreinGradedModule.gradeCLM (H := H)) :
    RealSplitKreinKasparovCycle A ℝ H :=
  finiteDimToRealSplitKreinKasparovCycle_of_unbounded
    (X := phaseRealSpectralTriple_toUnboundedCycle T hKrein cl11 hpi_smul hpi_even hchi)
    T.spectralGenerator.D
    (fun _ => rfl)
    (by
      have hD := T.D_selfAdjoint
      rw [hstar] at hD
      exact hD)

/-- Path B (`BUCKET 2` finite-dimensional `CFC.sqrt` bounded transform) starting
from a Krein-native `KreinPhaseRealSpectralTriple A H`. -/
def kreinPhaseRealSpectralTriple_toKasparovCycle_cfc
    {A H : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H] [FiniteDimensional ℝ H]
    (T : SpectralTriple.KreinPhaseRealSpectralTriple A H)
    (hD_self : IsSelfAdjoint T.spectralGenerator.D)
    (cl11 : RealSplitCl11Action H)
    (hpi_smul : ∀ (r : ℝ) (a : A),
      T.representedAlgebra.rep (r • a) = r • T.representedAlgebra.rep a)
    (hpi_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (T.representedAlgebra.rep a))
    (hchi : T.grading.chi = KreinGradedModule.gradeCLM (H := H)) :
    RealSplitKreinKasparovCycle A ℝ H :=
  finiteDimToRealSplitKreinKasparovCycle_of_unbounded
    (X := kreinPhaseRealSpectralTriple_toUnboundedCycle T cl11 hpi_smul hpi_even hchi)
    T.spectralGenerator.D
    (fun _ => rfl)
    hD_self

@[simp] theorem phaseRealSpectralTriple_toKasparovCycle_cfc_F
    {A H : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H] [FiniteDimensional ℝ H]
    (T : SpectralTriple.PhaseRealSpectralTriple A H)
    (hKrein : T.IsKreinCompatible)
    (hstar : T.operatorStar = (inferInstance : Star (EndH H)))
    (cl11 : RealSplitCl11Action H)
    (hpi_smul : ∀ (r : ℝ) (a : A),
      T.representedAlgebra.rep (r • a) = r • T.representedAlgebra.rep a)
    (hpi_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (T.representedAlgebra.rep a))
    (hchi : T.grading.chi = KreinGradedModule.gradeCLM (H := H)) :
    (phaseRealSpectralTriple_toKasparovCycle_cfc
        T hKrein hstar cl11 hpi_smul hpi_even hchi).F =
      finiteDimPhase T.spectralGenerator.D := rfl

end PhaseRealToCycles

section RealPhaseAlignment

/-- Lift a `RealPhaseSpectralTriple.PhaseAxis` to `SpectralTriple.PhaseAxis`. -/
def ofRealPhaseAxis
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : RealPhaseSpectralTriple.PhaseAxis H) : SpectralTriple.PhaseAxis H where
  K := K.K
  K_square_neg := K.K_sq

/-- Lift a `RealPhaseSpectralTriple.PhaseRealStructure` to `SpectralTriple.RealStructure`
with `epsJ = 1`. -/
def ofRealPhaseStructure
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : RealPhaseSpectralTriple.PhaseAxis H) (J : RealPhaseSpectralTriple.PhaseRealStructure H K)
    (signs : SpectralTriple.KOSigns) (hepsJ : signs.epsJ = 1) :
    SpectralTriple.RealStructure H (ofRealPhaseAxis K) signs where
  J :=
    { val := J.J
      inv := J.J
      val_inv := J.J_square
      inv_val := J.J_square }
  J_square := by
    rw [hepsJ, one_smul]
    exact J.J_square
  J_phase_reversing := J.J_reverses_phase

/-- Extract `RealSplitCl11Action H` directly from `RealPhaseSpectralTriple.PhaseRealStructure`. -/
def realSplitCl11ActionOfRealPhase
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : RealPhaseSpectralTriple.PhaseAxis H) (J : RealPhaseSpectralTriple.PhaseRealStructure H K) :
    RealSplitCl11Action H :=
  let signs : SpectralTriple.KOSigns :=
    { epsJ := 1, epsD := 1, epsChi := 1,
      epsJ_sq := by norm_num, epsD_sq := by norm_num, epsChi_sq := by norm_num }
  RealSplitKreinUnboundedCycle.realSplitCl11ActionOfPhaseReal
    (ofRealPhaseAxis K) (ofRealPhaseStructure K J signs rfl) rfl

/-- Lift a read-only `RealPhaseSpectralTriple.PhaseRealSpectralTriple` to
`SpectralTriple.PhaseRealSpectralTriple` given the extra opposite-representation and
KO-compatibility obligations. -/
def ofRealPhaseSpectralTriple
    {A H : Type*} [Ring A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : RealPhaseSpectralTriple.PhaseRealSpectralTriple A H)
    (signs : SpectralTriple.KOSigns) (hepsJ : signs.epsJ = 1)
    (hMetric : SpectralTriple.RealStructureMetricCompatible
      (ofRealPhaseStructure T.phaseAxis T.realStructure signs hepsJ))
    (hJchi : SpectralTriple.RealStructureChiralCompatible
      (ofRealPhaseStructure T.phaseAxis T.realStructure signs hepsJ)
      (@SpectralTriple.ChiralGrading.mk H _ _ (ofRealPhaseAxis T.phaseAxis) signs
        T.grading.chi
        (by
          simpa [SpectralTriple.PhaseLinear, InfoGeometry.Geometry.PhaseErlanger.PhaseLinear,
            RealPhaseSpectralTriple.PhasePreserving, ofRealPhaseAxis] using T.grading.chi_phase_linear)
        T.grading.chi_square))
    (hDphase : SpectralTriple.PhaseLinear T.phaseAxis.K T.spectralGenerator.D)
    (hrepPhase : ∀ a : A, SpectralTriple.PhaseLinear T.phaseAxis.K (T.representedAlgebra.rep a))
    (hOrderZero : SpectralTriple.OrderZeroCondition
      { rep := T.representedAlgebra.rep }
      (ofRealPhaseStructure T.phaseAxis T.realStructure signs hepsJ))
    (hOrderOne : SpectralTriple.OrderOneCondition
      { rep := T.representedAlgebra.rep }
      (ofRealPhaseStructure T.phaseAxis T.realStructure signs hepsJ)
      { D := T.spectralGenerator.D })
    (hDodd : SpectralTriple.DiracOdd
      { D := T.spectralGenerator.D }
      (@SpectralTriple.ChiralGrading.mk H _ _ (ofRealPhaseAxis T.phaseAxis) signs
        T.grading.chi
        (by
          simpa [SpectralTriple.PhaseLinear, InfoGeometry.Geometry.PhaseErlanger.PhaseLinear,
            RealPhaseSpectralTriple.PhasePreserving, ofRealPhaseAxis] using T.grading.chi_phase_linear)
        T.grading.chi_square))
    (hJD : SpectralTriple.RealStructureDiracCompatible
      (ofRealPhaseStructure T.phaseAxis T.realStructure signs hepsJ)
      { D := T.spectralGenerator.D }) :
    SpectralTriple.PhaseRealSpectralTriple A H where
  operatorStar := (inferInstance : Star (EndH H))
  signs := signs
  phaseAxis := ofRealPhaseAxis T.phaseAxis
  realStructure := ofRealPhaseStructure T.phaseAxis T.realStructure signs hepsJ
  realStructureMetricCompatible := hMetric
  grading :=
    { chi := T.grading.chi
      chi_phase_linear := by
        simpa [SpectralTriple.PhaseLinear, InfoGeometry.Geometry.PhaseErlanger.PhaseLinear,
          RealPhaseSpectralTriple.PhasePreserving, ofRealPhaseAxis] using T.grading.chi_phase_linear
      chi_square_one := T.grading.chi_square }
  J_chi_compatible := hJchi
  spectralGenerator := { D := T.spectralGenerator.D }
  D_selfAdjoint := T.D_selfAdjoint
  D_compactResolvent :=
    { spectralParameter := T.D_compactResolvent.spectralParameter
      resolvent := T.D_compactResolvent.resolvent
      resolvent_comp_shift := T.D_compactResolvent.resolvent_comp_shift
      shift_comp_resolvent := T.D_compactResolvent.shift_comp_resolvent
      resolvent_compact := T.D_compactResolvent.resolvent_compact }
  D_phase_linear := hDphase
  representedAlgebra := { rep := T.representedAlgebra.rep }
  rep_phase_linear := hrepPhase
  orderZero := hOrderZero
  orderOne := hOrderOne
  D_odd := hDodd
  J_D_compatible := hJD
  traceBackend := T.traceBackend
  modularWeightBackend := T.modularWeightBackend
  renormalizedBackend := none

/-- Directly convert a `RealPhaseSpectralTriple.PhaseRealSpectralTriple` into
`RealSplitKreinUnboundedCycle A ℝ H`. -/
def realPhaseSpectralTriple_toUnboundedCycle
    {A H : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    (T : RealPhaseSpectralTriple.PhaseRealSpectralTriple A H)
    (cl11 : RealSplitCl11Action H)
    (hpi_smul : ∀ (r : ℝ) (a : A),
      T.representedAlgebra.rep (r • a) = r • T.representedAlgebra.rep a)
    (hpi_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (T.representedAlgebra.rep a))
    (hchi : T.grading.chi = KreinGradedModule.gradeCLM (H := H))
    (hD_odd : T.spectralGenerator.D.comp T.grading.chi +
      T.grading.chi.comp T.spectralGenerator.D = 0)
    (hD_skew : KreinSpace.IsKreinSkewAdjoint (H := H) T.spectralGenerator.D) :
    RealSplitKreinUnboundedCycle A ℝ H where
  cl11 := cl11
  π :=
    { toFun := T.representedAlgebra.rep
      map_one' := T.representedAlgebra.rep.map_one
      map_mul' := T.representedAlgebra.rep.map_mul
      map_zero' := T.representedAlgebra.rep.map_zero
      map_add' := T.representedAlgebra.rep.map_add
      commutes' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one, hpi_smul r 1, T.representedAlgebra.rep.map_one,
          Algebra.algebraMap_eq_smul_one] }
  ρ := Algebra.ofId ℝ (EndH H)
  π_even := hpi_even
  ρ_even := scalarAlgHom_isEven
  domain := Set.univ
  D := fun x => T.spectralGenerator.D x.1
  dense_domain := dense_univ
  closed_graph := by
    have hset :
        (Set.range fun x : {x // x ∈ (Set.univ : Set H)} =>
          ((x.1, T.spectralGenerator.D x.1) : H × H)) =
          {p : H × H | p.2 = T.spectralGenerator.D p.1} := by
      ext ⟨u, v⟩
      simp [eq_comm]
    rw [hset]
    exact isClosed_eq continuous_snd (T.spectralGenerator.D.continuous.comp continuous_fst)
  grade_preserves_domain := fun _ _ => Set.mem_univ _
  π_preserves_domain := fun _ _ _ => Set.mem_univ _
  ρ_preserves_domain := fun _ _ _ => Set.mem_univ _
  D_odd := fun x => by
    have hDodd := congrArg (fun S : EndH H => S x.1) hD_odd
    simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply, hchi] at hDodd
    exact eq_neg_of_add_eq_zero_left hDodd
  D_krein_skewAdj := fun x y =>
    (KreinSpace.isKreinSkewAdjoint_iff (H := H) T.spectralGenerator.D).mp hD_skew x.1 y.1
  resolventData :=
    { shift := T.D_compactResolvent.spectralParameter
      resolvent := T.D_compactResolvent.resolvent
      resolvent_preserves_domain := fun _ => Set.mem_univ _
      left_resolvent := fun x => by
        have h := congrArg (fun S : EndH H => S x)
          T.D_compactResolvent.shift_comp_resolvent
        simpa [ContinuousLinearMap.comp_apply, sub_apply, smul_apply,
          ContinuousLinearMap.id_apply] using h
      compact := T.D_compactResolvent.resolvent_compact }
  commutator := fun a =>
    RealPhaseSpectralTriple.commutator T.spectralGenerator.D (T.representedAlgebra.rep a)
  commutator_add := by
    intro a b
    apply ContinuousLinearMap.ext
    intro v
    simp [RealPhaseSpectralTriple.commutator, map_add]
    abel
  commutator_formula := fun a x => by
    simp [RealPhaseSpectralTriple.commutator]

/-- Project a `SpectralTriple.PhaseRealSpectralTriple` (with `[CompleteSpace H]`,
`epsJ = 1`, `operatorStar = ContinuousLinearMap.instStar`, and
`RealPhaseSpectralTriple.OrderOneCondition`) to
`RealPhaseSpectralTriple.PhaseRealSpectralTriple`. -/
def toRealPhaseSpectralTriple
    {A H : Type*} [Ring A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : SpectralTriple.PhaseRealSpectralTriple A H)
    (hepsJ : T.signs.epsJ = 1)
    (hstar : T.operatorStar = (inferInstance : Star (EndH H)))
    (hOrderOne : RealPhaseSpectralTriple.OrderOneCondition
      { rep := T.representedAlgebra.rep }
      { D := T.spectralGenerator.D }) :
    RealPhaseSpectralTriple.PhaseRealSpectralTriple A H where
  phaseAxis :=
    { K := T.phaseAxis.K
      K_sq := T.phaseAxis.K_square_neg }
  realStructure :=
    { J := T.realStructure.J.val
      J_square := by
        change T.realStructure.J.val.comp T.realStructure.J.val = ContinuousLinearMap.id ℝ H
        simpa [hepsJ] using T.realStructure.J_square
      J_reverses_phase := T.realStructure.J_phase_reversing }
  grading :=
    { chi := T.grading.chi
      chi_square := T.grading.chi_square_one
      chi_phase_linear := T.grading.chi_phase_linear }
  spectralGenerator := { D := T.spectralGenerator.D }
  D_selfAdjoint := by
    have hD := T.D_selfAdjoint
    rw [hstar] at hD
    exact hD
  D_compactResolvent :=
    { spectralParameter := T.D_compactResolvent.spectralParameter
      resolvent := T.D_compactResolvent.resolvent
      resolvent_comp_shift := T.D_compactResolvent.resolvent_comp_shift
      shift_comp_resolvent := T.D_compactResolvent.shift_comp_resolvent
      resolvent_compact := T.D_compactResolvent.resolvent_compact }
  representedAlgebra := { rep := T.representedAlgebra.rep }
  order_one := hOrderOne
  traceBackend := T.traceBackend
  modularWeightBackend := T.modularWeightBackend
  renormalizedBackend := none

end RealPhaseAlignment

section SplitDoubledWitness

private abbrev WitnessE2 := EuclideanSpace ℝ (Fin 2)
private abbrev WitnessH := SplitDoubledSpace WitnessE2

private def witnessRot90 : EndH WitnessE2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then -(x.ofLp 1) else x.ofLp 0)
      map_add' := fun x y => by
        apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
        ext i; fin_cases i <;> simp [add_comm]
      map_smul' := fun r x => by
        apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
        ext i; fin_cases i <;> simp }

private def witnessSwap01 : EndH WitnessE2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then x.ofLp 1 else x.ofLp 0)
      map_add' := fun x y => by
        apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
        ext i; fin_cases i <;> simp
      map_smul' := fun r x => by
        apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
        ext i; fin_cases i <;> simp }

@[simp] private lemma witnessRot90_apply (x : WitnessE2) (i : Fin 2) :
    (witnessRot90 x).ofLp i = if i = 0 then -(x.ofLp 1) else x.ofLp 0 := rfl

@[simp] private lemma witnessSwap01_apply (x : WitnessE2) (i : Fin 2) :
    (witnessSwap01 x).ofLp i = if i = 0 then x.ofLp 1 else x.ofLp 0 := rfl

private lemma witnessRot90_sq : witnessRot90 * witnessRot90 = -1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext i
  fin_cases i <;> simp [mul_apply_eq_comp]

private lemma witnessSwap01_sq : witnessSwap01 * witnessSwap01 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext i
  fin_cases i <;> simp [mul_apply_eq_comp]

private lemma witnessSwap01_rot90_anti :
    witnessSwap01.comp witnessRot90 = -(witnessRot90.comp witnessSwap01) := by
  apply ContinuousLinearMap.ext
  intro x
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext i
  fin_cases i <;> simp

private lemma witnessRot90_adjoint :
    ContinuousLinearMap.adjoint witnessRot90 = -witnessRot90 := by
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_
  simp only [neg_apply, PiLp.inner_apply, Fin.sum_univ_two, witnessRot90_apply,
    RCLike.inner_apply, conj_trivial]
  norm_num
  ring

private def witnessDiracDoubled : EndH (DoubledSpace WitnessE2) where
  toFun u := to_doubled (witnessRot90 (WithLp.snd u)) (-(witnessRot90 (WithLp.fst u)))
  map_add' u v := by
    apply DoubledSpace.ext <;> simp [map_add]
    abel
  map_smul' r u := by
    apply DoubledSpace.ext <;> simp [map_smul, smul_neg]
  cont := by
    exact (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := WitnessE2) (β := WitnessE2)).comp
      ((witnessRot90.continuous.comp
          (WithLp.continuous_snd (p := (2 : ENNReal)) (α := WitnessE2) (β := WitnessE2))).prodMk
        (continuous_neg.comp
          (witnessRot90.continuous.comp
            (WithLp.continuous_fst (p := (2 : ENNReal)) (α := WitnessE2) (β := WitnessE2)))))

@[simp] private lemma witnessDiracDoubled_apply (u : DoubledSpace WitnessE2) :
    witnessDiracDoubled u =
      to_doubled (witnessRot90 (WithLp.snd u)) (-(witnessRot90 (WithLp.fst u))) := rfl

private def witnessDirac : EndH WitnessH :=
  SplitDoubledSpace.conjEnd (E := WitnessE2) witnessDiracDoubled

private lemma witnessDirac_sq : witnessDirac * witnessDirac = 1 := by
  apply ContinuousLinearMap.ext
  intro u
  have hrot : ∀ x : WitnessE2, witnessRot90 (witnessRot90 x) = -x := fun x => by
    simpa [mul_apply_eq_comp] using congrArg (fun T : EndH WitnessE2 => T x) witnessRot90_sq
  apply SplitDoubledSpace.ext
  apply DoubledSpace.ext <;>
    simp [witnessDirac, witnessDiracDoubled, mul_apply_eq_comp, hrot]

private lemma witnessSwap01_inner (x y : WitnessE2) :
    ⟪witnessSwap01 x, witnessSwap01 y⟫_ℝ = ⟪x, y⟫_ℝ := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, witnessSwap01_apply]
  ring

private lemma witnessDirac_selfAdjoint : IsSelfAdjoint witnessDirac := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun u v => ?_
  have hR' : ∀ a b : WitnessE2, ⟪witnessRot90 a, b⟫_ℝ = -⟪a, witnessRot90 b⟫_ℝ := by
    intro a b
    rw [← ContinuousLinearMap.adjoint_inner_right, witnessRot90_adjoint, neg_apply,
      inner_neg_right]
  change ⟪witnessDiracDoubled u.toDoubled, v.toDoubled⟫_ℝ =
    ⟪u.toDoubled, witnessDiracDoubled v.toDoubled⟫_ℝ
  rw [witnessDiracDoubled_apply, witnessDiracDoubled_apply,
    WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change ⟪witnessRot90 (WithLp.snd u.toDoubled), WithLp.fst v.toDoubled⟫_ℝ +
      ⟪-(witnessRot90 (WithLp.fst u.toDoubled)), WithLp.snd v.toDoubled⟫_ℝ =
    ⟪WithLp.fst u.toDoubled, witnessRot90 (WithLp.snd v.toDoubled)⟫_ℝ +
      ⟪WithLp.snd u.toDoubled, -(witnessRot90 (WithLp.fst v.toDoubled))⟫_ℝ
  simp only [inner_neg_left, inner_neg_right, hR', neg_neg]
  ring

private lemma witnessDirac_kreinSkewAdjoint :
    KreinSpace.IsKreinSkewAdjoint (H := WitnessH) witnessDirac := by
  refine isKreinSkewAdjoint_of_adjoint_eq_self_of_anticomm_jCLM witnessDirac
    (ContinuousLinearMap.isSelfAdjoint_iff'.mp witnessDirac_selfAdjoint) ?_
  apply ContinuousLinearMap.ext
  intro u
  apply SplitDoubledSpace.ext
  apply DoubledSpace.ext <;>
    simp [SplitDoubledSpace.jCLM_eq_splitDoubledSpectralEpsilon,
      SplitDoubledSpace.splitDoubledSpectralEpsilon, witnessDirac, witnessDiracDoubled,
      spectral_epsilon]

private lemma diagSplitDoubledAlgHom_toDoubled (T : EndH WitnessE2) (u : WitnessH) :
    (diagSplitDoubledAlgHom T u).toDoubled =
      to_doubled (T (WithLp.fst u.toDoubled)) (T (WithLp.snd u.toDoubled)) := rfl

private lemma witnessDirac_toDoubled (u : WitnessH) :
    (witnessDirac u).toDoubled =
      to_doubled (witnessRot90 (WithLp.snd u.toDoubled)) (-(witnessRot90 (WithLp.fst u.toDoubled))) :=
  rfl

private lemma gradeCLM_witness_toDoubled (u : WitnessH) :
    (KreinGradedModule.gradeCLM (H := WitnessH) u).toDoubled =
      to_doubled (WithLp.snd u.toDoubled) (WithLp.fst u.toDoubled) := by
  apply DoubledSpace.ext <;>
    simp [SplitDoubledSpace.gradeCLM_eq_splitDoubledModularJ,
      SplitDoubledSpace.splitDoubledModularJ, modular_j_apply]

/-- Concrete Krein-compatible `PhaseRealSpectralTriple` on `SplitDoubledSpace (EuclideanSpace ℝ (Fin 2))`. -/
def splitDoubledWitnessSpectralTriple :
    SpectralTriple.PhaseRealSpectralTriple ℝ WitnessH where
  operatorStar := (inferInstance : Star (EndH WitnessH))
  signs :=
    { epsJ := 1, epsD := -1, epsChi := 1,
      epsJ_sq := by norm_num, epsD_sq := by norm_num, epsChi_sq := by norm_num }
  phaseAxis :=
    { K := diagSplitDoubledAlgHom witnessRot90
      K_square_neg := by
        change diagSplitDoubledAlgHom witnessRot90 * diagSplitDoubledAlgHom witnessRot90 = -1
        rw [← map_mul, witnessRot90_sq, map_neg, map_one] }
  realStructure :=
    { J :=
        { val := diagSplitDoubledAlgHom witnessSwap01
          inv := diagSplitDoubledAlgHom witnessSwap01
          val_inv := by
            change diagSplitDoubledAlgHom witnessSwap01 *
                diagSplitDoubledAlgHom witnessSwap01 = 1
            rw [← map_mul, witnessSwap01_sq, map_one]
          inv_val := by
            change diagSplitDoubledAlgHom witnessSwap01 *
                diagSplitDoubledAlgHom witnessSwap01 = 1
            rw [← map_mul, witnessSwap01_sq, map_one] }
      J_square := by
        change diagSplitDoubledAlgHom witnessSwap01 *
            diagSplitDoubledAlgHom witnessSwap01 = (1 : ℝ) • 1
        rw [← map_mul, witnessSwap01_sq, map_one, one_smul]
      J_phase_reversing := by
        change diagSplitDoubledAlgHom witnessSwap01 * diagSplitDoubledAlgHom witnessRot90 =
          -(diagSplitDoubledAlgHom witnessRot90 * diagSplitDoubledAlgHom witnessSwap01)
        rw [← map_mul, ← map_mul, ← map_neg]
        congr 1
        exact witnessSwap01_rot90_anti }
  realStructureMetricCompatible := fun x y => by
    change ⟪(diagSplitDoubledAlgHom witnessSwap01 x).toDoubled,
        (diagSplitDoubledAlgHom witnessSwap01 y).toDoubled⟫_ℝ =
      ⟪x.toDoubled, y.toDoubled⟫_ℝ
    rw [diagSplitDoubledAlgHom_toDoubled, diagSplitDoubledAlgHom_toDoubled,
      WithLp.prod_inner_apply, WithLp.prod_inner_apply]
    change ⟪witnessSwap01 (WithLp.fst x.toDoubled), witnessSwap01 (WithLp.fst y.toDoubled)⟫_ℝ +
        ⟪witnessSwap01 (WithLp.snd x.toDoubled), witnessSwap01 (WithLp.snd y.toDoubled)⟫_ℝ =
      ⟪WithLp.fst x.toDoubled, WithLp.fst y.toDoubled⟫_ℝ +
        ⟪WithLp.snd x.toDoubled, WithLp.snd y.toDoubled⟫_ℝ
    rw [witnessSwap01_inner, witnessSwap01_inner]
  grading :=
    { chi := KreinGradedModule.gradeCLM (H := WitnessH)
      chi_phase_linear := by
        change (diagSplitDoubledAlgHom witnessRot90).comp
            (KreinGradedModule.gradeCLM (H := WitnessH)) =
          (KreinGradedModule.gradeCLM (H := WitnessH)).comp
            (diagSplitDoubledAlgHom witnessRot90)
        apply ContinuousLinearMap.ext
        intro u
        apply SplitDoubledSpace.ext
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
          diagSplitDoubledAlgHom_toDoubled, gradeCLM_witness_toDoubled,
          gradeCLM_witness_toDoubled, diagSplitDoubledAlgHom_toDoubled]
        simp only [fst_to_doubled, snd_to_doubled]
      chi_square_one := KreinGradedModule.gradeCLM_comp_self (H := WitnessH) }
  J_chi_compatible := by
    change (diagSplitDoubledAlgHom witnessSwap01).comp
        (KreinGradedModule.gradeCLM (H := WitnessH)) =
      (1 : ℝ) • ((KreinGradedModule.gradeCLM (H := WitnessH)).comp
        (diagSplitDoubledAlgHom witnessSwap01))
    apply ContinuousLinearMap.ext
    intro u
    apply SplitDoubledSpace.ext
    rw [ContinuousLinearMap.comp_apply, smul_apply, one_smul,
      ContinuousLinearMap.comp_apply, diagSplitDoubledAlgHom_toDoubled,
      gradeCLM_witness_toDoubled, gradeCLM_witness_toDoubled,
      diagSplitDoubledAlgHom_toDoubled]
    simp only [fst_to_doubled, snd_to_doubled]
  spectralGenerator := { D := witnessDirac }
  D_selfAdjoint := witnessDirac_selfAdjoint
  D_compactResolvent :=
    { spectralParameter := 0
      resolvent := witnessDirac
      resolvent_comp_shift := by
        have hzero : (0 : ℝ) • ContinuousLinearMap.id ℝ WitnessH = 0 := by
          apply ContinuousLinearMap.ext; intro u; simp
        rw [hzero, sub_zero]
        exact witnessDirac_sq
      shift_comp_resolvent := by
        have hzero : (0 : ℝ) • ContinuousLinearMap.id ℝ WitnessH = 0 := by
          apply ContinuousLinearMap.ext; intro u; simp
        rw [hzero, sub_zero]
        exact witnessDirac_sq
      resolvent_compact := isCompactEnd_of_finiteDimensional (H := WitnessH) _ }
  D_phase_linear := by
    apply ContinuousLinearMap.ext
    intro u
    apply SplitDoubledSpace.ext
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      diagSplitDoubledAlgHom_toDoubled, witnessDirac_toDoubled,
      witnessDirac_toDoubled, diagSplitDoubledAlgHom_toDoubled]
    simp only [fst_to_doubled, snd_to_doubled, map_neg]
  representedAlgebra := { rep := (Algebra.ofId ℝ (EndH WitnessH)).toRingHom }
  rep_phase_linear := fun r => by
    apply ContinuousLinearMap.ext
    intro u
    change r • (diagSplitDoubledAlgHom witnessRot90 u) =
      diagSplitDoubledAlgHom witnessRot90 (r • u)
    exact (map_smul _ r u).symm
  orderZero := fun a b => by
    apply ContinuousLinearMap.ext
    intro u
    change a • ((diagSplitDoubledAlgHom witnessSwap01)
        (b • (diagSplitDoubledAlgHom witnessSwap01 u))) =
      (diagSplitDoubledAlgHom witnessSwap01)
        (b • (diagSplitDoubledAlgHom witnessSwap01 (a • u)))
    have hsq : ∀ v : WitnessH,
        diagSplitDoubledAlgHom witnessSwap01 (diagSplitDoubledAlgHom witnessSwap01 v) = v := by
      intro v
      have h1 : diagSplitDoubledAlgHom witnessSwap01 * diagSplitDoubledAlgHom witnessSwap01 = 1 := by
        rw [← map_mul, witnessSwap01_sq, map_one]
      simpa [mul_apply_eq_comp] using congrArg (fun T : EndH WitnessH => T v) h1
    simp only [map_smul, hsq, smul_comm a b]
  orderOne := fun a b => by
    apply ContinuousLinearMap.ext
    intro u
    have hcomm :
        SpectralTriple.commutator witnessDirac ((Algebra.ofId ℝ (EndH WitnessH)).toRingHom a) =
          0 := by
      apply ContinuousLinearMap.ext
      intro v
      change witnessDirac (a • v) - a • witnessDirac v = 0
      simp [map_smul]
    rw [hcomm]
    simp
  D_odd := by
    apply ContinuousLinearMap.ext
    intro u
    change witnessDirac (KreinGradedModule.gradeCLM (H := WitnessH) u) +
        KreinGradedModule.gradeCLM (H := WitnessH) (witnessDirac u) = 0
    apply SplitDoubledSpace.ext
    rw [SplitDoubledSpace.toDoubled_add, SplitDoubledSpace.toDoubled_zero,
      witnessDirac_toDoubled, gradeCLM_witness_toDoubled,
      gradeCLM_witness_toDoubled, witnessDirac_toDoubled]
    simp only [fst_to_doubled, snd_to_doubled]
    apply DoubledSpace.ext <;> simp
  J_D_compatible := by
    apply ContinuousLinearMap.ext
    intro u
    have hanti : ∀ x : WitnessE2, witnessSwap01 (witnessRot90 x) = -(witnessRot90 (witnessSwap01 x)) :=
      fun x => by
        simpa using congrArg (fun T : EndH WitnessE2 => T x) witnessSwap01_rot90_anti
    change diagSplitDoubledAlgHom witnessSwap01 (witnessDirac u) =
      (-1 : ℝ) • witnessDirac (diagSplitDoubledAlgHom witnessSwap01 u)
    rw [neg_one_smul]
    apply SplitDoubledSpace.ext
    rw [SplitDoubledSpace.toDoubled_neg,
      diagSplitDoubledAlgHom_toDoubled, witnessDirac_toDoubled,
      witnessDirac_toDoubled, diagSplitDoubledAlgHom_toDoubled]
    simp only [fst_to_doubled, snd_to_doubled, map_neg, hanti]
    apply DoubledSpace.ext <;> simp
  traceBackend := none
  modularWeightBackend := none
  renormalizedBackend := none

theorem splitDoubledWitnessSpectralTriple_isKreinCompatible :
    splitDoubledWitnessSpectralTriple.IsKreinCompatible := by
  refine ⟨fun x y => ?_, witnessDirac_kreinSkewAdjoint⟩
  change KreinSpace.kreinInner (H := DoubledSpace WitnessE2)
      (diagSplitDoubledAlgHom witnessSwap01 x).toDoubled
      (diagSplitDoubledAlgHom witnessSwap01 y).toDoubled =
    KreinSpace.kreinInner (H := DoubledSpace WitnessE2) x.toDoubled y.toDoubled
  rw [diagSplitDoubledAlgHom_toDoubled, diagSplitDoubledAlgHom_toDoubled]
  have hx : x.toDoubled = to_doubled (WithLp.fst x.toDoubled) (WithLp.snd x.toDoubled) := rfl
  have hy : y.toDoubled = to_doubled (WithLp.fst y.toDoubled) (WithLp.snd y.toDoubled) := rfl
  rw [hx, hy, kreinInner_to_doubled, kreinInner_to_doubled, witnessSwap01_inner, witnessSwap01_inner]
  simp only [fst_to_doubled, snd_to_doubled]

/-- End-to-end witness `RealSplitKreinUnboundedCycle` on `SplitDoubledSpace (EuclideanSpace ℝ (Fin 2))`. -/
def splitDoubledWitnessUnboundedCycle : RealSplitKreinUnboundedCycle ℝ ℝ WitnessH :=
  phaseRealSpectralTriple_toUnboundedCycle
    splitDoubledWitnessSpectralTriple
    splitDoubledWitnessSpectralTriple_isKreinCompatible
    (SplitDoubledSpace.splitDoubledCl11Action (E := WitnessE2))
    (fun r a => map_smul (Algebra.ofId ℝ (EndH WitnessH)) r a)
    (fun a => scalarAlgHom_isEven a)
    rfl

/-- End-to-end witness `RealSplitKreinKasparovCycle` on `SplitDoubledSpace (EuclideanSpace ℝ (Fin 2))`
via the `BUCKET 2` finite-dimensional `CFC.sqrt` bounded transform. -/
def splitDoubledWitnessKasparovCycle_cfc : RealSplitKreinKasparovCycle ℝ ℝ WitnessH :=
  phaseRealSpectralTriple_toKasparovCycle_cfc
    splitDoubledWitnessSpectralTriple
    splitDoubledWitnessSpectralTriple_isKreinCompatible
    rfl
    (SplitDoubledSpace.splitDoubledCl11Action (E := WitnessE2))
    (fun r a => map_smul (Algebra.ofId ℝ (EndH WitnessH)) r a)
    (fun a => scalarAlgHom_isEven a)
    rfl

theorem splitDoubledWitnessKasparovCycle_cfc_F_ne_zero :
    splitDoubledWitnessKasparovCycle_cfc.F ≠ 0 := by
  intro h0
  have hF : splitDoubledWitnessKasparovCycle_cfc.F = finiteDimPhase witnessDirac := rfl
  rw [hF] at h0
  obtain ⟨hL, _⟩ := finiteDimPhase_sq_add_inv_one_add_sq witnessDirac_selfAdjoint
  rw [h0, zero_mul, sub_zero, mul_one] at hL
  have hDiag : (1 + witnessDirac * witnessDirac) = (2 : ℝ) • (1 : EndH WitnessH) := by
    rw [witnessDirac_sq, ← two_smul ℝ (1 : EndH WitnessH)]
  rw [hDiag] at hL
  let u₀ : WitnessH := ⟨to_doubled (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)) 0⟩
  have hu := congrArg (fun T : EndH WitnessH => WithLp.fst (T u₀).toDoubled |>.ofLp 0) hL
  simp [u₀] at hu

end SplitDoubledWitness

end InfoGeometry.KK.SpectralTripleKreinCycleBridge
