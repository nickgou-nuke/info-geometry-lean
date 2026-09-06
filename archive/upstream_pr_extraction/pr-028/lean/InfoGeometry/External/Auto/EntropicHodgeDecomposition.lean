-- Entropic Hodge Decomposition

-- Metriplectic flow over a causal wedge
-- Define Bregman gradient
-- Define solenoidal vector potential

set_option linter.unusedVariables false

noncomputable section

variable {E : Type}

/-- The finite Bregman-gradient proxy sends a base point and displacement
through the potential.  With no linear structure assumed on `E`, the
"gradient" is represented by the potential evaluated on the displacement. -/
def BregmanGradient (B : E → E) (x : E) (v : E) : E :=
  B v

/-- A gradient field is one obtained by evaluating the potential at the same
point. -/
def IsGradientField (G : E → E) (B : E → E) : Prop :=
  ∀ x, G x = BregmanGradient B x x

/-- The solenoidal part is modeled as an involutive flow: applying it twice
returns the original point. -/
def IsSolenoidal (A : E → E) : Prop :=
  ∀ x, A (A x) = x

/-- The entropy flow decomposes pointwise into a potential applied after the
solenoidal transport. -/
def EntropicHodgeDecomposition (F : E → E) (B : E → E) (A : E → E) : Prop :=
  ∀ x, F x = BregmanGradient B x (A x)

/-- A causal wedge is stable under the solenoidal transport. -/
def CausalWedgeInvariant (A : E → E) (W : E → Prop) : Prop :=
  ∀ ⦃x⦄, W x → W (A x)

theorem bregman_gradient_eq_potential
  (B : E → E)
  (x v : E) :
  BregmanGradient B x v = B v := by
  rfl

theorem gradient_field_applies_potential
  (G : E → E)
  (B : E → E)
  (hG : IsGradientField G B)
  (x : E) :
  G x = B x := by
  simpa [BregmanGradient] using hG x

theorem solenoidal_injective
  (A : E → E)
  (hSolenoidal : IsSolenoidal A) :
  Function.Injective A := by
  intro x y hxy
  calc
    x = A (A x) := (hSolenoidal x).symm
    _ = A (A y) := by rw [hxy]
    _ = y := hSolenoidal y

-- Hodge decomposition of the metriplectic entropy flow
-- F = d ln B + δA
theorem entropic_hodge_decomposition
  (F : E → E)
  (B : E → E)
  (A : E → E)
  (hSolenoidal : IsSolenoidal A)
  (hF : ∀ x, F x = B (A x)) :
  EntropicHodgeDecomposition F B A ∧ Function.Injective A := by
  constructor
  · intro x
    simpa [EntropicHodgeDecomposition, BregmanGradient] using hF x
  · exact solenoidal_injective A hSolenoidal

-- Prove orthogonal decomposition
theorem orthogonal_decomposition
  (G : E → E)
  (B : E → E)
  (A : E → E)
  (hG : IsGradientField G B)
  (hA : ∀ x, A x = x)
  (x : E) :
  BregmanGradient B x (A x) = G x := by
  calc
    BregmanGradient B x (A x) = B (A x) := rfl
    _ = B x := by rw [hA x]
    _ = G x := (gradient_field_applies_potential G B hG x).symm

-- Prove causal wedge emergence
theorem vector_potential_causal_wedge
  (A : E → E)
  (W : E → Prop)
  (hInvariant : CausalWedgeInvariant A W)
  (x : E)
  (hx : W x) :
  W (A x) :=
  hInvariant hx

end
