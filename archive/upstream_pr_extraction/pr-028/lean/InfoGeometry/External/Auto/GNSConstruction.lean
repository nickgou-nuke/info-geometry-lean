import Mathlib.Tactic

/-!
# GNS Construction: Gelfand-Naimark-Segal Setoid and Quotient

## Scope

This file formalizes the FINITE algebraic kernel of the GNS construction:

1. GNS ideal I_ω = {x | ω(x* x) = 0} as a left ideal
2. Equivalence relation x ~ y ↔ x−y ∈ I_ω, proved reflexive/symmetric
3. Setoid instance on the *-algebra A
4. Quotient type GNS_Space = A / ~
5. Inner product ⟨[x],[y]⟩ = ω(x* y)
6. Cyclic vector Ω = [1]
7. GNS expectation: ω(a) = ⟨Ω, π(a)Ω⟩

Transitivity, well-definedness of the inner product, and the left-ideal
property of the GNS ideal are carried explicitly as hypotheses on `State`.
For C*-algebras these follow from Cauchy-Schwarz and positivity; this file
does not pretend to prove those analytic facts from the algebraic signature.

The full C*-completion, Tomita-Takesaki modular theory, and von Neumann
algebraic double commutant are outside the scope of this algebraic file.
-/

noncomputable section

variable (𝕜 : Type*) [CommRing 𝕜] [LE 𝕜]
variable (A : Type*) [Ring A] [StarRing A] [Algebra 𝕜 A]

/-- A state on A: a positive linear functional ω: A → 𝕜 with ω(1) = 1.
    Positivity: ω(x* x) ≥ 0 for all x ∈ A.
    (The ordering on 𝕜 is via the positive cone of the underlying field.) -/
structure State where
  toFun : A →ₗ[𝕜] 𝕜
  map_one : toFun 1 = 1
  positivity : ∀ x : A, 0 ≤ toFun (star x * x)
  gnsIdeal_left_mul :
    ∀ (a x : A), toFun (star x * x) = 0 → toFun (star (a * x) * (a * x)) = 0
  gnsRel_transitive :
    ∀ {x y z : A},
      toFun (star (x - y) * (x - y)) = 0 →
      toFun (star (y - z) * (y - z)) = 0 →
      toFun (star (x - z) * (x - z)) = 0
  innerProduct_descends :
    ∀ (x₁ x₂ y₁ y₂ : A),
      toFun (star (x₁ - x₂) * (x₁ - x₂)) = 0 →
      toFun (star (y₁ - y₂) * (y₁ - y₂)) = 0 →
      toFun (star x₁ * y₁) = toFun (star x₂ * y₂)

namespace State

variable {𝕜 A}
variable (ω : State 𝕜 A)

/-- The GNS left ideal: I_ω = {x ∈ A | ω(x* x) = 0}.
    This is the set of "null vectors" under the pre-inner product B(x,y) = ω(x* y).
    The quotient A/I_ω is the GNS pre-Hilbert space. -/
def gnsIdeal (x : A) : Prop :=
  ω.toFun (star x * x) = 0

/-- The GNS equivalence relation: x ~ y ↔ ω((x−y)*(x−y)) = 0.
    Two elements are equivalent if their difference has zero norm. -/
def gnsRel (x y : A) : Prop :=
  ω.gnsIdeal (x - y)

/-- Reflexivity: x ~ x, since ω((x−x)*(x−x)) = ω(0) = 0. -/
lemma gnsRel_refl (x : A) : ω.gnsRel x x := by
  unfold gnsRel gnsIdeal
  simp

/-- Symmetry: if ω((x−y)*(x−y)) = 0 then ω((y−x)*(y−x)) = 0.
    Follows from (y−x) = −(x−y) and (−z)*(−z) = z*z. -/
lemma gnsRel_symm {x y : A} (h : ω.gnsRel x y) : ω.gnsRel y x := by
  unfold gnsRel gnsIdeal at h ⊢
  have h' : y - x = -(x - y) := by abel
  simpa only [h', star_neg, neg_mul, mul_neg, neg_neg] using h

/-- The GNS ideal is a left ideal: if ω(x* x) = 0, then for any a ∈ A,
    ω((a·x)*(a·x)) = 0. This ensures that the representation π(a)[x] = [a·x]
    is well-defined on the quotient.

    Hypothesis: in analytic GNS this follows from Cauchy-Schwarz for the
    pre-inner product. It is an explicit field of `State` here. -/
theorem gnsIdeal_is_left_ideal (a x : A) (h : ω.gnsIdeal x) : ω.gnsIdeal (a * x) := by
  exact ω.gnsIdeal_left_mul a x h

/-- Transitivity: if ω((x−y)*(x−y)) = 0 and ω((y−z)*(y−z)) = 0,
    then ω((x−z)*(x−z)) = 0.

    Proof: (x−z) = (x−y) + (y−z). By Cauchy-Schwarz,
    ω((u+v)*(u+v)) ≤ 2(ω(u*u) + ω(v*v)). With both zero, the sum is zero.

    Hypothesis: in analytic GNS this follows from Cauchy-Schwarz. It is an
    explicit field of `State` here. -/
theorem gnsRel_trans {x y z : A} (h1 : ω.gnsRel x y) (h2 : ω.gnsRel y z) : ω.gnsRel x z := by
  exact ω.gnsRel_transitive h1 h2

/-- The Setoid instance on A defined by the GNS equivalence relation.
    This enables the use of Quotient to construct the GNS space. -/
def gnsSetoid : Setoid A where
  r := ω.gnsRel
  iseqv := {
    refl := ω.gnsRel_refl
    symm := ω.gnsRel_symm
    trans := ω.gnsRel_trans
  }

/-- The GNS quotient space (pre-Hilbert space before completion).
    Elements are equivalence classes [x] = x + I_ω. -/
def gnsSpace : Type _ := Quotient ω.gnsSetoid

/-- The canonical map A → A/I_ω sending x to its equivalence class [x]. -/
def gnsMap (x : A) : ω.gnsSpace := Quotient.mk ω.gnsSetoid x

/-- The cyclic vector Ω = [1] in the GNS space. -/
def gnsVacuum : ω.gnsSpace := ω.gnsMap 1

/-- The raw pre-inner product on A: B(x,y) = ω(x* y).
    This is positive semi-definite and descends to the quotient. -/
def innerProductRaw (x y : A) : 𝕜 :=
  ω.toFun (star x * y)

/-- The inner product is well-defined on the quotient:
    if x₁ ~ x₂ and y₁ ~ y₂, then ω(x₁* y₁) = ω(x₂* y₂).

    Hypothesis: in analytic GNS this follows from Cauchy-Schwarz controlling
    cross-terms. It is an explicit field of `State` here. -/
theorem innerProduct_well_defined (x₁ x₂ y₁ y₂ : A)
    (hx : ω.gnsRel x₁ x₂) (hy : ω.gnsRel y₁ y₂) :
    ω.innerProductRaw x₁ y₁ = ω.innerProductRaw x₂ y₂ := by
  exact ω.innerProduct_descends x₁ x₂ y₁ y₂ hx hy

/-- The lifted inner product on the GNS quotient space. -/
def innerProduct (u v : ω.gnsSpace) : 𝕜 :=
  Quotient.lift₂ ω.innerProductRaw
    (by
      intro x₁ y₁ x₂ y₂ hx hy
      exact ω.innerProduct_well_defined x₁ x₂ y₁ y₂ hx hy)
    u v

/-- The GNS representation π(a) on the quotient:
    π(a)[x] = [a·x]. This is a *-representation of A on the pre-Hilbert space. -/
def representationRaw (_ω : State 𝕜 A) (a x : A) : A := a * x

/-- The representation is well-defined: if x ~ y, then a·x ~ a·y.
    This follows from the fact that I_ω is a left ideal. -/
theorem representation_well_defined (a x y : A) (h : ω.gnsRel x y) :
    ω.gnsRel (ω.representationRaw a x) (ω.representationRaw a y) := by
  unfold gnsRel gnsIdeal representationRaw
  -- a·x − a·y = a·(x−y). Then ω((a·(x−y))*(a·(x−y))) = 0
  -- because I_ω is a left ideal and x−y ∈ I_ω.
  have h_diff : a * x - a * y = a * (x - y) := (mul_sub a x y).symm
  rw [h_diff]
  exact ω.gnsIdeal_is_left_ideal a (x - y) h

/-- The lifted GNS representation π: A → End(gnsSpace). -/
def representation (a : A) : ω.gnsSpace → ω.gnsSpace :=
  Quotient.map (ω.representationRaw a) (ω.representation_well_defined a)

/-- **The GNS expectation theorem:**
    ω(a) = ⟨Ω | π(a) | Ω⟩ = ⟨[1], π(a)[1]⟩

    This is the fundamental identity of the GNS construction:
    the state value equals the vacuum expectation of the represented operator. -/
theorem gns_expectation (a : A) :
    ω.innerProduct (ω.gnsVacuum) (ω.representation a (ω.gnsVacuum)) = ω.toFun a := by
  unfold gnsVacuum gnsMap representation innerProduct
  rw [Quotient.map_mk]
  rw [Quotient.lift₂_mk]
  unfold innerProductRaw representationRaw
  simp

/-- The Tomita S-operator, recorded as documentation rather than as a theorem.
    For a faithful state, the GNS vacuum is separating, and S is
    a closable anti-linear operator. Its polar decomposition S = JΔ^{1/2}
    gives the modular conjugation J and modular operator Δ.

    This is the gateway to Tomita-Takesaki theory, KMS states,
    and the classification of Type III von Neumann factors. -/
def tomita_S_operator_description : String :=
  "S : gnsSpace -> gnsSpace, S(pi(a)Omega) = pi(a*)Omega.
   For faithful ω, S is closable and S = JΔ^{1/2} (polar decomposition).
   J is the modular conjugation (anti-unitary involution).
   Δ is the modular operator (positive, self-adjoint).
   Δ^{it} is the modular flow (the thermodynamic time evolution)."

end State
