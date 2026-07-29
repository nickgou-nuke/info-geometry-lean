import InfoGeometry.KK.RealSplitKreinResolvent

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
    X.π_preserves_domain, X.ρ_preserves_domain, X.commutator_formula,
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

end RealSplitKreinUnboundedCycle

end InfoGeometry.KK
