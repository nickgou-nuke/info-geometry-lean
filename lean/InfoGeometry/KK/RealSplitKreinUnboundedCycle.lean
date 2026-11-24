/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.KK.RealSplitKreinResolvent
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.SpectralTriple

open scoped InnerProductSpace

namespace InfoGeometry.KK

open InfoGeometry.Krein

/-!
# Real Split Krein Unbounded Cycle

Primitive unbounded interface scaffold layered over the real split-`Cl(1,1)`
Krein setting.

Policy note: any surviving `complex_i` terminology elsewhere in the repository
is legacy compatibility language only. The canonical internal square-minus-one
axis is `K := J.comp eps`, derived from the split `Cl(1,1)` atom.

### Evidence Boundaries
- `BUCKET 2`: Domain-level unbounded cycle scaffold (`domain`, `D`,
  `dense_domain`, `closed_graph`, `D_odd`, `D_krein_skewAdj`, `resolventData`,
  `commutator`), bounded `PhaseRealSpectralTriple` →
  `RealSplitKreinUnboundedCycle` conversion (`toUnboundedCycle`), and
  finite-dimensional `CFC.sqrt` bounded transforms.
- `BUCKET 3`: Infinite-dimensional unbounded functional calculus for
  `D (1 + D²)^(-1/2)` and the general unbounded Kasparov product remain open
  (`BUCKET 3`).
-/

/--
Primitive unbounded real split-Krein cycle interface.

This first-pass object stores explicit domain-level data for the unbounded
operator, grading compatibility, a concrete bounded commutator representative,
and primitive resolvent control packaged as separate bounded data. It still
remains an interface scaffold rather than a full unbounded-KK calculus.
-/
structure RealSplitKreinUnboundedCycle
    (A B H : Type*)
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H] where
  cl11 : InfoGeometry.Quantum.RealSplitCl11Action H
  π : A →ₐ[ℝ] EndH H
  ρ : B →ₐ[ℝ] EndH H
  π_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (π a)
  ρ_even : ∀ b : B, KreinGradedModule.IsEven (H := H) (ρ b)
  domain : Set H
  D : {x // x ∈ domain} → H
  dense_domain : Dense domain
  closed_graph : IsClosed (Set.range fun x : {x // x ∈ domain} => ((x.1, D x) : H × H))
  grade_preserves_domain : ∀ ⦃x : H⦄, x ∈ domain → KreinGradedModule.gradeCLM (H := H) x ∈ domain
  π_preserves_domain : ∀ a : A, ∀ ⦃x : H⦄, x ∈ domain → (π a) x ∈ domain
  ρ_preserves_domain : ∀ b : B, ∀ ⦃x : H⦄, x ∈ domain → (ρ b) x ∈ domain
  D_odd :
    ∀ x : {x // x ∈ domain},
      D ⟨KreinGradedModule.gradeCLM (H := H) x.1, grade_preserves_domain x.2⟩ =
        -(KreinGradedModule.gradeCLM (H := H) (D x))
  D_krein_skewAdj :
    ∀ x y : {x // x ∈ domain},
      KreinSpace.kreinInner (H := H) (D x) y.1 + KreinSpace.kreinInner (H := H) x.1 (D y) = 0
  resolventData : RealSplitKreinResolventData H domain D
  commutator : A → EndH H
  /-- The bounded commutator representative is additive in the represented algebra.
  This compatibility is needed to evaluate the universal tensor-kernel one-forms
  on the original Dirac commutator. -/
  commutator_add : ∀ a b : A, commutator (a + b) = commutator a + commutator b
  commutator_formula :
    ∀ a : A, ∀ x : {x // x ∈ domain},
      commutator a x.1 =
        D ⟨(π a) x.1, π_preserves_domain a x.2⟩ - (π a) (D x)

namespace RealSplitKreinUnboundedCycle

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

/--
First-order regularity of the real split-Krein unbounded cycle.

This predicate records the actual analytic content owned by the interface:
dense closed domain, invariance under grading and both algebra actions,
bounded commutator representatives, and compact resolvent.
-/
def Regular
    (X : RealSplitKreinUnboundedCycle A B H) : Prop :=
  Dense X.domain ∧
    IsClosed
      (Set.range fun x : {x // x ∈ X.domain} =>
        ((x.1, X.D x) : H × H)) ∧
    (∀ ⦃x : H⦄, x ∈ X.domain →
      KreinGradedModule.gradeCLM (H := H) x ∈ X.domain) ∧
    (∀ a : A, ∀ ⦃x : H⦄, x ∈ X.domain → (X.π a) x ∈ X.domain) ∧
    (∀ b : B, ∀ ⦃x : H⦄, x ∈ X.domain → (X.ρ b) x ∈ X.domain) ∧
    (∀ a b : A, X.commutator (a + b) = X.commutator a + X.commutator b) ∧
    (∀ a : A, ∀ x : {x // x ∈ X.domain},
      X.commutator a x.1 =
        X.D ⟨(X.π a) x.1, X.π_preserves_domain a x.2⟩ -
          (X.π a) (X.D x)) ∧
    IsCompactEnd H X.resolventData.resolvent

/-- Every cycle satisfies its native first-order regularity predicate. -/
theorem regular
    (X : RealSplitKreinUnboundedCycle A B H) :
    X.Regular :=
  ⟨X.dense_domain, X.closed_graph, X.grade_preserves_domain,
    X.π_preserves_domain, X.ρ_preserves_domain, X.commutator_add, X.commutator_formula,
    X.resolventData.compact⟩

/-- The internal square-minus-one axis carried by the primitive split atom. -/
noncomputable def K
    (X : RealSplitKreinUnboundedCycle A B H) : EndH H :=
  X.cl11.K

/-- The derived axis squares to `-Id` on the unbounded primitive carrier. -/
theorem K_sq
    (X : RealSplitKreinUnboundedCycle A B H) :
    X.K.comp X.K = -(ContinuousLinearMap.id ℝ H) :=
  X.cl11.K_sq

/-- The chosen real shift for the primitive resolvent packet. -/
abbrev resolventShift
    (X : RealSplitKreinUnboundedCycle A B H) : ℝ :=
  X.resolventData.shift

/-- The bounded resolvent representative for the unbounded primitive carrier. -/
abbrev resolvent
    (X : RealSplitKreinUnboundedCycle A B H) : EndH H :=
  X.resolventData.resolvent

/-- The resolvent maps the ambient carrier back into the operator domain. -/
lemma resolvent_preserves_domain
    (X : RealSplitKreinUnboundedCycle A B H) (x : H) :
    X.resolvent x ∈ X.domain :=
  X.resolventData.resolvent_preserves_domain x

/-- The stored resolvent satisfies the left identity for `D - λ`. -/
lemma resolvent_left
    (X : RealSplitKreinUnboundedCycle A B H) (x : H) :
    X.D ⟨X.resolvent x, X.resolvent_preserves_domain x⟩ - X.resolventShift • X.resolvent x = x :=
  X.resolventData.left_resolvent x

/-- The primitive resolvent representative is compact. -/
lemma resolvent_compact
    (X : RealSplitKreinUnboundedCycle A B H) :
    IsCompactEnd H X.resolvent :=
  X.resolventData.compact

/-- The grading acts on the operator domain by primitive closure. -/
noncomputable def gradeOnDomain
    (X : RealSplitKreinUnboundedCycle A B H) :
    {x // x ∈ X.domain} → {x // x ∈ X.domain}
  | ⟨x, hx⟩ =>
      ⟨KreinGradedModule.gradeCLM (H := H) x, X.grade_preserves_domain hx⟩

/-- The `A`-action preserves the unbounded operator domain. -/
def piOnDomain
    (X : RealSplitKreinUnboundedCycle A B H) (a : A) :
    {x // x ∈ X.domain} → {x // x ∈ X.domain}
  | ⟨x, hx⟩ => ⟨(X.π a) x, X.π_preserves_domain a hx⟩

/-- The `B`-action preserves the unbounded operator domain. -/
def rhoOnDomain
    (X : RealSplitKreinUnboundedCycle A B H) (b : B) :
    {x // x ∈ X.domain} → {x // x ∈ X.domain}
  | ⟨x, hx⟩ => ⟨(X.ρ b) x, X.ρ_preserves_domain b hx⟩

lemma pi_comp_resolvent_compact
    (X : RealSplitKreinUnboundedCycle A B H) (a : A) :
    IsCompactEnd H ((X.π a).comp X.resolvent) :=
  X.resolventData.comp_left_isCompactEnd (X.π a)

lemma resolvent_comp_pi_compact
    (X : RealSplitKreinUnboundedCycle A B H) (a : A) :
    IsCompactEnd H (X.resolvent.comp (X.π a)) :=
  X.resolventData.comp_right_isCompactEnd (X.π a)

lemma rho_comp_resolvent_compact
    (X : RealSplitKreinUnboundedCycle A B H) (b : B) :
    IsCompactEnd H ((X.ρ b).comp X.resolvent) :=
  X.resolventData.comp_left_isCompactEnd (X.ρ b)

lemma resolvent_comp_rho_compact
    (X : RealSplitKreinUnboundedCycle A B H) (b : B) :
    IsCompactEnd H (X.resolvent.comp (X.ρ b)) :=
  X.resolventData.comp_right_isCompactEnd (X.ρ b)

@[simp] lemma resolvent_mem_domain
    (X : RealSplitKreinUnboundedCycle A B H) (x : H) :
    X.resolvent x ∈ X.domain :=
  X.resolvent_preserves_domain x

section SpectralTripleBridge

/-- Extract a canonical `RealSplitCl11Action H` from a `PhaseAxis` and `RealStructure`
when `signs.epsJ = 1`, setting `J := J.J.val` and `eps := J.J.val.comp K.K`. -/
noncomputable def realSplitCl11ActionOfPhaseReal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {signs : InfoGeometry.OperatorAlgebra.SpectralTriple.KOSigns}
    (K : InfoGeometry.OperatorAlgebra.SpectralTriple.PhaseAxis H)
    (J : InfoGeometry.OperatorAlgebra.SpectralTriple.RealStructure H K signs)
    (hepsJ : signs.epsJ = 1) :
    InfoGeometry.Quantum.RealSplitCl11Action H where
  eps := J.J.val.comp K.K
  J := J.J.val
  eps_sq := by
    have hJ2 : J.J.val.comp J.J.val = ContinuousLinearMap.id ℝ H := by
      simpa [hepsJ] using J.J_square
    have hanti : J.J.val.comp K.K = -(K.K.comp J.J.val) := J.J_phase_reversing
    have hK2 : K.K.comp K.K = -(ContinuousLinearMap.id ℝ H) := K.K_square_neg
    ext x
    have h1 : J.J.val (K.K x) = -(K.K (J.J.val x)) :=
      congrArg (fun T : H →L[ℝ] H => T x) hanti
    have h2 : K.K (K.K x) = -x :=
      congrArg (fun T : H →L[ℝ] H => T x) hK2
    have h3 : J.J.val (J.J.val (K.K (K.K x))) = K.K (K.K x) :=
      congrArg (fun T : H →L[ℝ] H => T (K.K (K.K x))) hJ2
    calc
      (J.J.val.comp K.K) ((J.J.val.comp K.K) x)
          = J.J.val (K.K (J.J.val (K.K x))) := rfl
      _ = J.J.val (K.K (-(K.K (J.J.val x)))) := by rw [h1]
      _ = -(J.J.val (K.K (K.K (J.J.val x)))) := by simp [map_neg]
      _ = -(J.J.val (-(J.J.val x))) := by
        have h2' : K.K (K.K (J.J.val x)) = -(J.J.val x) :=
          congrArg (fun T : H →L[ℝ] H => T (J.J.val x)) hK2
        rw [h2']
      _ = J.J.val (J.J.val x) := by simp [map_neg]
      _ = x := by
        simpa using congrArg (fun T : H →L[ℝ] H => T x) hJ2
  J_sq := by
    simpa [hepsJ] using J.J_square
  J_eps_anti := by
    have hJ2 : J.J.val.comp J.J.val = ContinuousLinearMap.id ℝ H := by
      simpa [hepsJ] using J.J_square
    have hanti : J.J.val.comp K.K = -(K.K.comp J.J.val) := J.J_phase_reversing
    ext x
    have h1 : J.J.val (K.K (J.J.val x)) = -(K.K (J.J.val (J.J.val x))) :=
      congrArg (fun T : H →L[ℝ] H => T (J.J.val x)) hanti
    have hJx : J.J.val (J.J.val x) = x := by
      simpa using congrArg (fun T : H →L[ℝ] H => T x) hJ2
    calc
      J.J.val ((J.J.val.comp K.K) x)
          = J.J.val (J.J.val (K.K x)) := rfl
      _ = K.K x := by
        simpa using congrArg (fun T : H →L[ℝ] H => T (K.K x)) hJ2
      _ = K.K (J.J.val (J.J.val x)) := by rw [hJx]
      _ = -(-(K.K (J.J.val (J.J.val x)))) := by simp
      _ = -(J.J.val (K.K (J.J.val x))) := by rw [← h1]
      _ = -((J.J.val.comp K.K) (J.J.val x)) := rfl

@[simp] theorem realSplitCl11ActionOfPhaseReal_K
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {signs : InfoGeometry.OperatorAlgebra.SpectralTriple.KOSigns}
    (K : InfoGeometry.OperatorAlgebra.SpectralTriple.PhaseAxis H)
    (J : InfoGeometry.OperatorAlgebra.SpectralTriple.RealStructure H K signs)
    (hepsJ : signs.epsJ = 1) :
    (realSplitCl11ActionOfPhaseReal K J hepsJ).K = K.K := by
  have hJ2 : J.J.val.comp J.J.val = ContinuousLinearMap.id ℝ H := by
    simpa [hepsJ] using J.J_square
  ext x
  change J.J.val (J.J.val (K.K x)) = K.K x
  simpa using congrArg (fun T : H →L[ℝ] H => T (K.K x)) hJ2

/--
Construct a `RealSplitKreinUnboundedCycle A ℝ H` from a Krein-compatible
`PhaseRealSpectralTriple A H` (with `domain := Set.univ`, `ρ := Algebra.ofId ℝ (EndH H)`).
-/
noncomputable def toUnboundedCycle
    {A H : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    (T : InfoGeometry.OperatorAlgebra.SpectralTriple.PhaseRealSpectralTriple A H)
    (hKrein : T.IsKreinCompatible)
    (cl11 : InfoGeometry.Quantum.RealSplitCl11Action H)
    (hpi_smul : ∀ (r : ℝ) (a : A),
      T.representedAlgebra.rep (r • a) = r • T.representedAlgebra.rep a)
    (hpi_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (T.representedAlgebra.rep a))
    (hchi : T.grading.chi = KreinGradedModule.gradeCLM (H := H)) :
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
  ρ_even := fun b => by
    unfold KreinGradedModule.IsEven KreinGradedModule.gradeConj
    apply ContinuousLinearMap.ext
    intro x
    change KreinGradedModule.gradeCLM (H := H)
        (b • KreinGradedModule.gradeCLM (H := H) x) = b • x
    rw [map_smul, KreinGradedModule.gradeCLM_apply, KreinGradedModule.gradeCLM_apply,
      KreinGradedModule.grade_invol]
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
    have hDodd := congrArg (fun S : H →L[ℝ] H => S x.1) T.D_odd
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      zero_apply, hchi] at hDodd
    exact eq_neg_of_add_eq_zero_left hDodd
  D_krein_skewAdj := fun x y => by
    exact (KreinSpace.isKreinSkewAdjoint_iff (H := H) T.spectralGenerator.D).mp
      hKrein.2 x.1 y.1
  resolventData :=
    { shift := T.D_compactResolvent.spectralParameter
      resolvent := T.D_compactResolvent.resolvent
      resolvent_preserves_domain := fun _ => Set.mem_univ _
      left_resolvent := fun x => by
        have h := congrArg (fun S : H →L[ℝ] H => S x)
          T.D_compactResolvent.shift_comp_resolvent
        simpa [ContinuousLinearMap.comp_apply, sub_apply,
          smul_apply, ContinuousLinearMap.id_apply] using h
      compact := T.D_compactResolvent.resolvent_compact }
  commutator := fun a =>
    InfoGeometry.OperatorAlgebra.SpectralTriple.commutator
      T.spectralGenerator.D (T.representedAlgebra.rep a)
  commutator_add := by
    intro a b
    apply ContinuousLinearMap.ext
    intro v
    simp [InfoGeometry.OperatorAlgebra.SpectralTriple.commutator, map_add]
    abel
  commutator_formula := fun a x => by
    simp [InfoGeometry.OperatorAlgebra.SpectralTriple.commutator]

end SpectralTripleBridge


lemma D_odd_on_gradeOnDomain
    (X : RealSplitKreinUnboundedCycle A B H)
    (x : {x // x ∈ X.domain}) :
    X.D (X.gradeOnDomain x) =
      -(KreinGradedModule.gradeCLM (H := H) (X.D x)) := by
  exact X.D_odd x

end RealSplitKreinUnboundedCycle

end InfoGeometry.KK
