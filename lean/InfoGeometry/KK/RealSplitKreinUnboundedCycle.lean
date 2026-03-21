import InfoGeometry.KK.RealSplitKreinKasparovCycle

open scoped InnerProductSpace

namespace InfoGeometry.KK

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
and a concrete bounded resolvent representative. It still remains an interface
scaffold rather than a full unbounded-KK calculus.
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
  regular : Prop
  D_odd :
    ∀ x : {x // x ∈ domain},
      D ⟨KreinGradedModule.gradeCLM (H := H) x.1, grade_preserves_domain x.2⟩ =
        -(KreinGradedModule.gradeCLM (H := H) (D x))
  D_krein_skewAdj :
    ∀ x y : {x // x ∈ domain},
      KreinSpace.kreinInner (H := H) (D x) y.1 + KreinSpace.kreinInner (H := H) x.1 (D y) = 0
  resolventShift : ℝ
  resolvent : EndH H
  resolvent_preserves_domain : ∀ x : H, resolvent x ∈ domain
  resolvent_left :
    ∀ x : H,
      D ⟨resolvent x, resolvent_preserves_domain x⟩ - resolventShift • resolvent x = x
  resolvent_compact : IsCompactEnd H resolvent
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

/-- The internal square-minus-one axis carried by the primitive split atom. -/
noncomputable def K
    (X : RealSplitKreinUnboundedCycle A B H) : EndH H :=
  X.cl11.K

/-- The derived axis squares to `-Id` on the unbounded primitive carrier. -/
theorem K_sq
    (X : RealSplitKreinUnboundedCycle A B H) :
    X.K.comp X.K = -(ContinuousLinearMap.id ℝ H) :=
  X.cl11.K_sq

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

@[simp] lemma resolvent_mem_domain
    (X : RealSplitKreinUnboundedCycle A B H) (x : H) :
    X.resolvent x ∈ X.domain :=
  X.resolvent_preserves_domain x

end RealSplitKreinUnboundedCycle

end InfoGeometry.KK
