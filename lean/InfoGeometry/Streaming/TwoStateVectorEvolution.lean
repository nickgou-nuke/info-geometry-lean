import InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional

/-!
# Finite two-state-vector evolution

This owner records the algebraic core of a pre/post-selected evolution. The
two boundary vectors may depend on a parameter, and regularity is required at
every parameter value at which the weak value is read. No claim about
retrocausality, measurement probabilities, or modular conjugation is encoded.
-/

noncomputable section

namespace InfoGeometry.Streaming.TwoStateVectorEvolution

open InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional

abbrev State (ι : Type*) := FiniteTwoBoundaryWeakFunctional.State ι
abbrev Operator (ι : Type*) := FiniteTwoBoundaryWeakFunctional.Operator ι

/-- A finite pre/post-selected history with a regular boundary pair at every
parameter value. The two maps are independent; identifying them with forward
and backward unitary evolution requires extra structure. -/
structure DynamicBoundaryPair (ι : Type*) [Fintype ι] (τ : Type*) where
  preAt : τ → State ι
  postAt : τ → State ι
  regular : ∀ t, pairing (postAt t) (preAt t) ≠ 0

variable {ι : Type*} [Fintype ι]
variable {τ : Type*} (p : DynamicBoundaryPair ι τ)

/-- The boundary overlap at a parameter value. -/
def overlapAt (t : τ) : ℂ :=
  pairing (p.postAt t) (p.preAt t)

@[simp] theorem overlapAt_ne (t : τ) : overlapAt p t ≠ 0 :=
  p.regular t

/-- The transition numerator at a parameter value. -/
def numeratorAt (t : τ) (A : Operator ι) : ℂ :=
  pairing (p.postAt t) (A (p.preAt t))

/-- The parameter-dependent weak value of an operator. -/
def weakValueAt (t : τ) (A : Operator ι) : ℂ :=
  numeratorAt p t A / overlapAt p t

@[simp] theorem weakValueAt_one (t : τ) :
    weakValueAt p t (1 : Operator ι) = 1 := by
  unfold weakValueAt numeratorAt overlapAt
  simp only [Module.End.one_apply]
  exact div_self (p.regular t)

theorem weakValueAt_add (t : τ) (A B : Operator ι) :
    weakValueAt p t (A + B) = weakValueAt p t A + weakValueAt p t B := by
  simp [weakValueAt, numeratorAt, overlapAt, add_div]

theorem weakValueAt_smul (t : τ) (c : ℂ) (A : Operator ι) :
    weakValueAt p t (c • A) = c * weakValueAt p t A := by
  simp only [weakValueAt, numeratorAt, overlapAt, LinearMap.smul_apply,
    pairing_smul_right]
  field_simp [overlapAt_ne p t]

/-! ### A reversible specialization -/

/-- A pair of linear equivalences supplies reversible transport on the pre- and
post-selected sides. The boundary pair remains separate data. -/
structure ReversibleTwoStateVector (ι : Type*) [Fintype ι] (τ : Type*) where
  pre₀ : State ι
  post₀ : State ι
  preEvolution : τ → State ι ≃ₗ[ℂ] State ι
  postEvolution : τ → State ι ≃ₗ[ℂ] State ι
  regular : ∀ t,
    pairing (postEvolution t (post₀)) (preEvolution t (pre₀)) ≠ 0

variable (q : ReversibleTwoStateVector ι τ)

def reversibleBoundaryPair : DynamicBoundaryPair ι τ where
  preAt t := q.preEvolution t q.pre₀
  postAt t := q.postEvolution t q.post₀
  regular := q.regular

theorem reversible_weakValue_at_one (t : τ) :
    weakValueAt (reversibleBoundaryPair q) t (1 : Operator ι) = 1 := by
  exact weakValueAt_one (reversibleBoundaryPair q) t

end InfoGeometry.Streaming.TwoStateVectorEvolution

end
