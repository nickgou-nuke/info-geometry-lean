import InfoGeometry.Clifford.Cl55RoPESplitTorusBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.CliffordRoPETorus
import InfoGeometry.LogJordanKreinCore
import InfoGeometry.Physics.LogCFTJordanShear
import InfoGeometry.Krein.CarrierTransport
import InfoGeometry.LLM.PositionalEncoding

/-!
# Unified positional-dynamics regimes

The transcript's elliptic, hyperbolic, and logarithmic/Jordan channels all have
the same algebraic interface: an additive parameter acts by multiplication.
This file fuses those laws without identifying their carriers.  The first two
are Clifford rotors; the third is the non-semisimple logarithmic cell.
-/

noncomputable section

namespace InfoGeometry.Canonical.PositionalDynamicsRegimeBridge

open InfoGeometry.Clifford.Cl55RoPESplitTorusBridge
open InfoGeometry.OperatorAlgebra.CliffordRoPETorus
open InfoGeometry.LogJordanKreinCore
open InfoGeometry.Physics.LogCFTJordanShear
open InfoGeometry.Krein
open InfoGeometry.LLM

structure AdditivePositionRepresentation (M : Type*) (G : Type*)
    [Zero G] [Add G] where
  unit : M
  mul : M → M → M
  value : G → M
  value_zero : value 0 = unit
  value_add : ∀ s t, value (s + t) = mul (value s) (value t)

/-- An additive positional representation equipped with an explicit inverse
operation and both inverse laws.  The carrier need not be commutative. -/
structure GroupPositionRepresentation (M : Type*) (G : Type*)
    [Zero G] [Add G] [Neg G] extends AdditivePositionRepresentation M G where
  inv : M → M
  inv_value : ∀ t, inv (value t) = value (-t)
  left_inverse : ∀ t, mul (inv (value t)) (value t) = unit
  right_inverse : ∀ t, mul (value t) (inv (value t)) = unit

theorem GroupPositionRepresentation.relative_position
    {M G : Type*} [Zero G] [AddCommGroup G]
    (ρ : GroupPositionRepresentation M G) (s t : G) :
    ρ.mul (ρ.value (-s)) (ρ.value t) = ρ.value (t - s) := by
  rw [← ρ.value_add (-s) t]
  simp [sub_eq_add_neg, add_comm]

/-- Constructor for the group representation layer from an additive
representation and explicit inverse witnesses.  Keeping the inverse as an
argument makes this usable for matrices, continuous maps, and abstract
algebra carriers without assuming an ambient `Group` instance. -/
def GroupPositionRepresentation.ofAdditive
    {M G : Type*} [Zero G] [AddCommGroup G]
    (ρ : AdditivePositionRepresentation M G)
    (inv : M → M)
    (hinv : ∀ t, inv (ρ.value t) = ρ.value (-t))
    (hleft : ∀ t, ρ.mul (inv (ρ.value t)) (ρ.value t) = ρ.unit)
    (hright : ∀ t, ρ.mul (ρ.value t) (inv (ρ.value t)) = ρ.unit) :
    GroupPositionRepresentation M G where
  toAdditivePositionRepresentation := ρ
  inv := inv
  inv_value := hinv
  left_inverse := hleft
  right_inverse := hright

theorem GroupPositionRepresentation.inverse_value
    {M G : Type*} [Zero G] [Add G] [Neg G]
    (ρ : GroupPositionRepresentation M G) (t : G) :
    ρ.inv (ρ.value t) = ρ.value (-t) :=
  ρ.inv_value t

/-- Time-reversible representation data when inverse values are supplied only
on the represented one-parameter family.  This is the natural interface for
explicit matrix flows whose ambient carrier is not itself a group. -/
structure TimeReversiblePositionRepresentation (M : Type*) (G : Type*)
    [Zero G] [Add G] [Neg G] extends AdditivePositionRepresentation M G where
  inverseValue : G → M
  inverseValue_eq_neg : ∀ t, inverseValue t = value (-t)
  left_inverse : ∀ t, mul (inverseValue t) (value t) = unit
  right_inverse : ∀ t, mul (value t) (inverseValue t) = unit

def TimeReversiblePositionRepresentation.ofAdditive
    {M G : Type*} [Zero G] [Add G] [Neg G]
    (ρ : AdditivePositionRepresentation M G)
    (inverseValue : G → M)
    (hinv : ∀ t, inverseValue t = ρ.value (-t))
    (hleft : ∀ t, ρ.mul (inverseValue t) (ρ.value t) = ρ.unit)
    (hright : ∀ t, ρ.mul (ρ.value t) (inverseValue t) = ρ.unit) :
    TimeReversiblePositionRepresentation M G where
  toAdditivePositionRepresentation := ρ
  inverseValue := inverseValue
  inverseValue_eq_neg := hinv
  left_inverse := hleft
  right_inverse := hright

def TimeReversiblePositionRepresentation.ofFunctionRepresentation
    {Q G : Type*} [AddCommGroup G]
    (ρ : AdditivePositionRepresentation (Q → Q) G) :
    TimeReversiblePositionRepresentation (Q → Q) G :=
  TimeReversiblePositionRepresentation.ofAdditive ρ
    (fun t => ρ.value (-t))
    (by intro t; rfl)
    (by
      intro t
      dsimp
      rw [← ρ.value_add (-t) t]
      rw [neg_add_cancel]
      exact ρ.value_zero)
    (by
      intro t
      dsimp
      rw [← ρ.value_add t (-t)]
      rw [add_neg_cancel]
      exact ρ.value_zero)

theorem TimeReversiblePositionRepresentation.relative_position
    {M G : Type*} [Zero G] [AddCommGroup G]
    (ρ : TimeReversiblePositionRepresentation M G) (s t : G) :
    ρ.mul (ρ.inverseValue s) (ρ.value t) = ρ.value (t - s) := by
  rw [ρ.inverseValue_eq_neg, ← ρ.value_add (-s) t]
  simp [sub_eq_add_neg, add_comm]

/-- Transport of a positional representation across an explicit multiplicative
equivalence of carriers.  The parameter group is unchanged; this is the
precise interface used to connect concrete realizations without identifying
their underlying types. -/
def AdditivePositionRepresentation.transport
    {M N G : Type*} [Zero G] [Add G]
    [Mul M] [Mul N]
    (ρ : AdditivePositionRepresentation M G) (e : M ≃* N) :
    AdditivePositionRepresentation N G where
  unit := e ρ.unit
  mul := fun x y => e (ρ.mul (e.symm x) (e.symm y))
  value := fun g => e (ρ.value g)
  value_zero := by
    exact congrArg e ρ.value_zero
  value_add := by
    intro s t
    simp only [MulEquiv.symm_apply_apply]
    exact congrArg e (ρ.value_add s t)

theorem AdditivePositionRepresentation.transport_value
    {M N G : Type*} [Zero G] [Add G]
    [Mul M] [Mul N]
    (ρ : AdditivePositionRepresentation M G) (e : M ≃* N) (g : G) :
    (ρ.transport e).value g = e (ρ.value g) := by
  rfl

/-- The repository's pairing-preserving Krein flows are additive positional
representations in the monoid of continuous linear endomorphisms. -/
noncomputable def CarrierTransport.toAdditivePositionRepresentation
    {X : InvolutiveSelfDualCarrier} (T : CarrierTransport X) :
    AdditivePositionRepresentation (X.H →L[ℝ] X.H) ℝ where
  unit := ContinuousLinearMap.id ℝ X.H
  mul := (·.comp ·)
  value := T.transport
  value_zero := T.transport_zero
  value_add := T.transport_add

theorem CarrierTransport.toAdditivePositionRepresentation_pairing
    {X : InvolutiveSelfDualCarrier} (T : CarrierTransport X)
    (t : ℝ) (u v : X.H) :
    X.kreinPairing
        ((toAdditivePositionRepresentation T).value t u)
        ((toAdditivePositionRepresentation T).value t v) =
      X.kreinPairing u v := by
  exact T.transport_preserves_pairing t u v

/-- A representation by endofunctions is an LLM positional encoding at each
parameter value.  The hypotheses state that the representation's carrier
multiplication is ordinary function composition. -/
def AdditivePositionRepresentation.toPositionalEncoding
    {Q G : Type*} [Zero G] [Add G]
    (ρ : AdditivePositionRepresentation (Q → Q) G)
    (g : G) : PositionalEncoding Q :=
  { encode := ρ.value g }

theorem AdditivePositionRepresentation.toPositionalEncoding_add
    {Q G : Type*} [Zero G] [Add G]
    (ρ : AdditivePositionRepresentation (Q → Q) G)
    (hcomp : ∀ f g : Q → Q, ρ.mul f g = g ∘ f)
    (s t : G) :
    ρ.toPositionalEncoding (s + t) =
      PositionalEncoding.comp
        (ρ.toPositionalEncoding s) (ρ.toPositionalEncoding t) := by
  apply PositionalEncoding.ext
  funext X
  change ρ.value (s + t) X = ρ.value t (ρ.value s X)
  rw [ρ.value_add s t]
  exact congrFun (hcomp (ρ.value s) (ρ.value t)) X

theorem TimeReversiblePositionRepresentation.relative_position_encoding
    {Q G : Type*} [Zero G] [AddCommGroup G]
    (ρ : TimeReversiblePositionRepresentation (Q → Q) G)
    (hcomp : ∀ f g : Q → Q, ρ.mul f g = g ∘ f)
    (s t : G) :
    PositionalEncoding.comp
        (ρ.toAdditivePositionRepresentation.toPositionalEncoding (-s))
        (ρ.toAdditivePositionRepresentation.toPositionalEncoding t) =
      ρ.toAdditivePositionRepresentation.toPositionalEncoding (t - s) := by
  apply PositionalEncoding.ext
  funext X
  change ρ.value t (ρ.value (-s) X) = ρ.value (t - s) X
  have hm := ρ.relative_position s t
  rw [ρ.inverseValue_eq_neg s] at hm
  have hc := hcomp (ρ.value (-s)) (ρ.value t)
  rw [hc] at hm
  exact congrFun hm X

theorem transformer_run_with_additive_position_representation
    {Q K Vh Vout ι G : Type*} [DecidableEq ι]
    [AddCommGroup Vh] [Module ℝ Vh]
    [AddCommGroup Vout] [Module ℝ Vout]
    [Zero G] [Add G] {n : ℕ}
    (B : TransformerBlock (Q := Q) (K := K) (Vh := Vh)
      (Vout := Vout) (ι := ι) n)
    (ρ : AdditivePositionRepresentation (Q → Q) G)
    (hcomp : ∀ f g : Q → Q, ρ.mul f g = g ∘ f)
    (s t : G) :
    B.runWithPositionalEncoding (ρ.toPositionalEncoding (s + t)) =
      (B.runWithPositionalEncoding (ρ.toPositionalEncoding t)) ∘
        (ρ.toPositionalEncoding s).encode := by
  rw [ρ.toPositionalEncoding_add hcomp s t]
  exact TransformerBlock.runWithPositionalEncoding_comp B
    (ρ.toPositionalEncoding s) (ρ.toPositionalEncoding t)

theorem maskedTransformer_run_with_additive_position_representation
    {Q K Vh Vout ι G : Type*} [DecidableEq ι]
    [AddCommGroup Vh] [Module ℝ Vh]
    [AddCommGroup Vout] [Module ℝ Vout]
    [Zero G] [Add G] {n : ℕ}
    (M : MaskedTransformerBlock (Q := Q) (K := K) (Vh := Vh)
      (Vout := Vout) (ι := ι) n)
    (ρ : AdditivePositionRepresentation (Q → Q) G)
    (hcomp : ∀ f g : Q → Q, ρ.mul f g = g ∘ f)
    (s t : G) :
    M.runWithPositionalEncoding (ρ.toPositionalEncoding (s + t)) =
      (M.runWithPositionalEncoding (ρ.toPositionalEncoding t)) ∘
        (ρ.toPositionalEncoding s).encode := by
  rw [ρ.toPositionalEncoding_add hcomp s t]
  exact MaskedTransformerBlock.runWithPositionalEncoding_comp M
    (ρ.toPositionalEncoding s) (ρ.toPositionalEncoding t)

noncomputable def splitRotor55_is_additivePositionRepresentation (i : Fin 5) :
    AdditivePositionRepresentation InfoGeometry.Clifford.Clifford55.Cl55 ℝ where
  unit := 1
  mul := (· * ·)
  value := splitRotor55 i
  value_zero := splitRotor55_zero i
  value_add := by
    intro s t
    exact (splitRotor55_add i s t).symm

noncomputable def hyperbolicRotor_is_additivePositionRepresentation (θ : ℝ) :
    AdditivePositionRepresentation InfoGeometry.Routing.PlanarRotation.Mat2 ℝ where
  unit := 1
  mul := (· * ·)
  value := hyperbolicRotor θ
  value_zero := hyperbolicRotor_zero θ
  value_add := by
    intro s t
    exact hyperbolicRotor_add θ s t

noncomputable def ellipticRotor_is_additivePositionRepresentation (θ : ℝ) :
    AdditivePositionRepresentation InfoGeometry.Routing.PlanarRotation.Mat2 ℝ where
  unit := 1
  mul := (· * ·)
  value := ellipticRotor θ
  value_zero := ellipticRotor_zero θ
  value_add := by
    intro s t
    exact ellipticRotor_add θ s t

noncomputable def ellipticRotor_timeReversibleRepresentation (θ : ℝ) :
    TimeReversiblePositionRepresentation
      InfoGeometry.Routing.PlanarRotation.Mat2 ℝ :=
  TimeReversiblePositionRepresentation.ofAdditive
    (ellipticRotor_is_additivePositionRepresentation θ)
    (ellipticRotor θ ∘ Neg.neg)
    (by intro t; rfl)
    (by
      intro t
      simpa [neg_add_cancel, ellipticRotor_zero θ] using
        (ellipticRotor_add θ (-t) t).symm)
    (by
      intro t
      simpa [add_neg_cancel, ellipticRotor_zero θ] using
        (ellipticRotor_add θ t (-t)).symm)

noncomputable def hyperbolicRotor_timeReversibleRepresentation (θ : ℝ) :
    TimeReversiblePositionRepresentation
      InfoGeometry.Routing.PlanarRotation.Mat2 ℝ :=
  TimeReversiblePositionRepresentation.ofAdditive
    (hyperbolicRotor_is_additivePositionRepresentation θ)
    (hyperbolicRotor θ ∘ Neg.neg)
    (by intro t; rfl)
    (by
      intro t
      simpa [neg_add_cancel, hyperbolicRotor_zero θ] using
        (hyperbolicRotor_add θ (-t) t).symm)
    (by
      intro t
      simpa [add_neg_cancel, hyperbolicRotor_zero θ] using
        (hyperbolicRotor_add θ t (-t)).symm)

theorem expJordanCell_add (Δ s t : ℝ) :
    expJordanCell (s + t) Δ = expJordanCell s Δ * expJordanCell t Δ := by
  rw [exp_jordanCell, exp_jordanCell]
  rw [exp_jordanCell]
  have hExp : Real.exp ((s + t) * Δ) = Real.exp (s * Δ) * Real.exp (t * Δ) := by
    rw [show (s + t) * Δ = s * Δ + t * Δ by ring, Real.exp_add]
  rw [hExp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ring

/-- The zero-eigenvalue Jordan exponential is genuinely polynomial in time. -/
theorem exp_nilpotent_jordanCell (t : ℝ) :
    expJordanCell t 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) + t • N := by
  simp [expJordanCell]

def hyperbolicRotorPositionalEncoding (θ t : ℝ) :
    PositionalEncoding (InfoGeometry.Routing.PlanarRotation.Mat2) :=
  { encode := fun X => hyperbolicRotor θ t * X }

def ellipticRotorPositionalEncoding (θ t : ℝ) :
    PositionalEncoding InfoGeometry.Routing.PlanarRotation.Mat2 :=
  { encode := fun X => ellipticRotor θ t * X }

theorem ellipticRotorPositionalEncoding_add (θ s t : ℝ) :
    ellipticRotorPositionalEncoding θ (s + t) =
      PositionalEncoding.comp
        (ellipticRotorPositionalEncoding θ s)
        (ellipticRotorPositionalEncoding θ t) := by
  apply PositionalEncoding.ext
  funext X
  change ellipticRotor θ (s + t) * X =
    ellipticRotor θ t * (ellipticRotor θ s * X)
  calc
    ellipticRotor θ (s + t) * X = ellipticRotor θ (t + s) * X := by
      rw [add_comm]
    _ = (ellipticRotor θ t * ellipticRotor θ s) * X := by
      rw [ellipticRotor_add θ t s]
    _ = ellipticRotor θ t * (ellipticRotor θ s * X) := by
      rw [mul_assoc]

theorem hyperbolicRotorPositionalEncoding_add (θ s t : ℝ) :
    hyperbolicRotorPositionalEncoding θ (s + t) =
      PositionalEncoding.comp
        (hyperbolicRotorPositionalEncoding θ s)
        (hyperbolicRotorPositionalEncoding θ t) := by
  apply PositionalEncoding.ext
  funext X
  change hyperbolicRotor θ (s + t) * X =
    hyperbolicRotor θ t * (hyperbolicRotor θ s * X)
  calc
    hyperbolicRotor θ (s + t) * X = hyperbolicRotor θ (t + s) * X := by
      rw [add_comm]
    _ = (hyperbolicRotor θ t * hyperbolicRotor θ s) * X := by
      rw [hyperbolicRotor_add θ t s]
    _ = hyperbolicRotor θ t * (hyperbolicRotor θ s * X) := by
      rw [mul_assoc]

def expJordanCellPositionalEncoding (Δ t : ℝ) :
    PositionalEncoding (Matrix (Fin 2) (Fin 2) ℝ) :=
  { encode := fun X => expJordanCell t Δ * X }

theorem expJordanCellPositionalEncoding_add (Δ s t : ℝ) :
    expJordanCellPositionalEncoding Δ (s + t) =
      PositionalEncoding.comp
        (expJordanCellPositionalEncoding Δ s)
        (expJordanCellPositionalEncoding Δ t) := by
  apply PositionalEncoding.ext
  funext X
  change expJordanCell (s + t) Δ * X =
    expJordanCell t Δ * (expJordanCell s Δ * X)
  calc
    expJordanCell (s + t) Δ * X = expJordanCell (t + s) Δ * X := by
      rw [add_comm]
    _ = (expJordanCell t Δ * expJordanCell s Δ) * X := by
      rw [expJordanCell_add Δ t s]
    _ = expJordanCell t Δ * (expJordanCell s Δ * X) := by
      rw [mul_assoc]

theorem expJordanCell_zeroEigenvaluePositionalEncoding (t : ℝ) :
    expJordanCellPositionalEncoding 0 t =
      { encode := fun X => ((1 : Matrix (Fin 2) (Fin 2) ℝ) + t • N) * X } := by
  apply PositionalEncoding.ext
  funext X
  change expJordanCell t 0 * X = _
  rw [exp_nilpotent_jordanCell]

noncomputable def hyperbolicRotor_functionRepresentation (θ : ℝ) :
    AdditivePositionRepresentation
      (InfoGeometry.Routing.PlanarRotation.Mat2 →
        InfoGeometry.Routing.PlanarRotation.Mat2) ℝ where
  unit := id
  mul := fun f g => g ∘ f
  value := fun t => (hyperbolicRotorPositionalEncoding θ t).encode
  value_zero := by
    funext X
    simp [hyperbolicRotorPositionalEncoding, hyperbolicRotor_zero]
  value_add := by
    intro s t
    exact congrArg (fun P => P.encode)
      (hyperbolicRotorPositionalEncoding_add θ s t)

noncomputable def ellipticRotor_functionRepresentation (θ : ℝ) :
    AdditivePositionRepresentation
      (InfoGeometry.Routing.PlanarRotation.Mat2 →
        InfoGeometry.Routing.PlanarRotation.Mat2) ℝ where
  unit := id
  mul := fun f g => g ∘ f
  value := fun t => (ellipticRotorPositionalEncoding θ t).encode
  value_zero := by
    funext X
    simp [ellipticRotorPositionalEncoding, ellipticRotor_zero]
  value_add := by
    intro s t
    exact congrArg (fun P => P.encode)
      (ellipticRotorPositionalEncoding_add θ s t)

theorem ellipticRotor_functionRepresentation_mul (θ : ℝ)
    (f g : InfoGeometry.Routing.PlanarRotation.Mat2 →
      InfoGeometry.Routing.PlanarRotation.Mat2) :
    (ellipticRotor_functionRepresentation θ).mul f g = g ∘ f := by
  rfl

theorem hyperbolicRotor_functionRepresentation_mul (θ : ℝ)
    (f g : InfoGeometry.Routing.PlanarRotation.Mat2 →
      InfoGeometry.Routing.PlanarRotation.Mat2) :
    (hyperbolicRotor_functionRepresentation θ).mul f g = g ∘ f := by
  rfl

noncomputable def expJordanCell_functionRepresentation (Δ : ℝ) :
    AdditivePositionRepresentation
      ((Matrix (Fin 2) (Fin 2) ℝ) → Matrix (Fin 2) (Fin 2) ℝ) ℝ where
  unit := id
  mul := fun f g => g ∘ f
  value := fun t => (expJordanCellPositionalEncoding Δ t).encode
  value_zero := by
    funext X
    change expJordanCell 0 Δ * X = X
    rw [exp_jordanCell]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  value_add := by
    intro s t
    exact congrArg (fun P => P.encode)
      (expJordanCellPositionalEncoding_add Δ s t)

theorem expJordanCell_functionRepresentation_mul (Δ : ℝ)
    (f g : (Matrix (Fin 2) (Fin 2) ℝ) → Matrix (Fin 2) (Fin 2) ℝ) :
    (expJordanCell_functionRepresentation Δ).mul f g = g ∘ f := by
  rfl

theorem transformer_run_hyperbolicRotor_add
    {K Vh Vout ι : Type*} [DecidableEq ι]
    [AddCommGroup Vh] [Module ℝ Vh]
    [AddCommGroup Vout] [Module ℝ Vout] {n : ℕ}
    (B : TransformerBlock
      (Q := InfoGeometry.Routing.PlanarRotation.Mat2) (K := K)
      (Vh := Vh) (Vout := Vout) (ι := ι) n) (θ s t : ℝ) :
    B.runWithPositionalEncoding
        (hyperbolicRotorPositionalEncoding θ (s + t)) =
      (B.runWithPositionalEncoding
        (hyperbolicRotorPositionalEncoding θ t)) ∘
        (hyperbolicRotorPositionalEncoding θ s).encode := by
  simpa [AdditivePositionRepresentation.toPositionalEncoding,
    hyperbolicRotor_functionRepresentation] using
    (transformer_run_with_additive_position_representation B
      (hyperbolicRotor_functionRepresentation θ)
      (hyperbolicRotor_functionRepresentation_mul θ) s t)

theorem transformer_run_expJordanCell_add
    {K Vh Vout ι : Type*} [DecidableEq ι]
    [AddCommGroup Vh] [Module ℝ Vh]
    [AddCommGroup Vout] [Module ℝ Vout] {n : ℕ}
    (B : TransformerBlock
      (Q := Matrix (Fin 2) (Fin 2) ℝ) (K := K)
      (Vh := Vh) (Vout := Vout) (ι := ι) n) (Δ s t : ℝ) :
    B.runWithPositionalEncoding
        (expJordanCellPositionalEncoding Δ (s + t)) =
      (B.runWithPositionalEncoding
        (expJordanCellPositionalEncoding Δ t)) ∘
        (expJordanCellPositionalEncoding Δ s).encode := by
  simpa [AdditivePositionRepresentation.toPositionalEncoding,
    expJordanCell_functionRepresentation] using
    (transformer_run_with_additive_position_representation B
      (expJordanCell_functionRepresentation Δ)
      (expJordanCell_functionRepresentation_mul Δ) s t)

theorem transformer_run_ellipticRotor_add
    {K Vh Vout ι : Type*} [DecidableEq ι]
    [AddCommGroup Vh] [Module ℝ Vh]
    [AddCommGroup Vout] [Module ℝ Vout] {n : ℕ}
    (B : TransformerBlock
      (Q := InfoGeometry.Routing.PlanarRotation.Mat2) (K := K)
      (Vh := Vh) (Vout := Vout) (ι := ι) n) (θ s t : ℝ) :
    B.runWithPositionalEncoding
        (ellipticRotorPositionalEncoding θ (s + t)) =
      (B.runWithPositionalEncoding
        (ellipticRotorPositionalEncoding θ t)) ∘
        (ellipticRotorPositionalEncoding θ s).encode := by
  simpa [AdditivePositionRepresentation.toPositionalEncoding,
    ellipticRotor_functionRepresentation] using
    (transformer_run_with_additive_position_representation B
      (ellipticRotor_functionRepresentation θ)
      (ellipticRotor_functionRepresentation_mul θ) s t)

theorem maskedTransformer_run_hyperbolicRotor_add
    {K Vh Vout ι : Type*} [DecidableEq ι]
    [AddCommGroup Vh] [Module ℝ Vh]
    [AddCommGroup Vout] [Module ℝ Vout] {n : ℕ}
    (M : MaskedTransformerBlock
      (Q := InfoGeometry.Routing.PlanarRotation.Mat2) (K := K)
      (Vh := Vh) (Vout := Vout) (ι := ι) n) (θ s t : ℝ) :
    M.runWithPositionalEncoding
        (hyperbolicRotorPositionalEncoding θ (s + t)) =
      (M.runWithPositionalEncoding
        (hyperbolicRotorPositionalEncoding θ t)) ∘
        (hyperbolicRotorPositionalEncoding θ s).encode := by
  simpa [AdditivePositionRepresentation.toPositionalEncoding,
    hyperbolicRotor_functionRepresentation] using
    (maskedTransformer_run_with_additive_position_representation M
      (hyperbolicRotor_functionRepresentation θ)
      (hyperbolicRotor_functionRepresentation_mul θ) s t)

theorem maskedTransformer_run_expJordanCell_add
    {K Vh Vout ι : Type*} [DecidableEq ι]
    [AddCommGroup Vh] [Module ℝ Vh]
    [AddCommGroup Vout] [Module ℝ Vout] {n : ℕ}
    (M : MaskedTransformerBlock
      (Q := Matrix (Fin 2) (Fin 2) ℝ) (K := K)
      (Vh := Vh) (Vout := Vout) (ι := ι) n) (Δ s t : ℝ) :
    M.runWithPositionalEncoding
        (expJordanCellPositionalEncoding Δ (s + t)) =
      (M.runWithPositionalEncoding
        (expJordanCellPositionalEncoding Δ t)) ∘
        (expJordanCellPositionalEncoding Δ s).encode := by
  simpa [AdditivePositionRepresentation.toPositionalEncoding,
    expJordanCell_functionRepresentation] using
    (maskedTransformer_run_with_additive_position_representation M
      (expJordanCell_functionRepresentation Δ)
      (expJordanCell_functionRepresentation_mul Δ) s t)

theorem maskedTransformer_run_ellipticRotor_add
    {K Vh Vout ι : Type*} [DecidableEq ι]
    [AddCommGroup Vh] [Module ℝ Vh]
    [AddCommGroup Vout] [Module ℝ Vout] {n : ℕ}
    (M : MaskedTransformerBlock
      (Q := InfoGeometry.Routing.PlanarRotation.Mat2) (K := K)
      (Vh := Vh) (Vout := Vout) (ι := ι) n) (θ s t : ℝ) :
    M.runWithPositionalEncoding
        (ellipticRotorPositionalEncoding θ (s + t)) =
      (M.runWithPositionalEncoding
        (ellipticRotorPositionalEncoding θ t)) ∘
        (ellipticRotorPositionalEncoding θ s).encode := by
  simpa [AdditivePositionRepresentation.toPositionalEncoding,
    ellipticRotor_functionRepresentation] using
    (maskedTransformer_run_with_additive_position_representation M
      (ellipticRotor_functionRepresentation θ)
      (ellipticRotor_functionRepresentation_mul θ) s t)

noncomputable def expJordanCell_is_additivePositionRepresentation (Δ : ℝ) :
    AdditivePositionRepresentation (Matrix (Fin 2) (Fin 2) ℝ) ℝ where
  unit := 1
  mul := (· * ·)
  value := fun t => expJordanCell t Δ
  value_zero := by
    rw [exp_jordanCell]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  value_add := by
    intro s t
    exact expJordanCell_add Δ s t

noncomputable def logCFTUnipotentShear_is_additivePositionRepresentation :
    AdditivePositionRepresentation Mat2C ℂ where
  unit := 1
  mul := (· * ·)
  value := unipotentShear
  value_zero := by
    simp [unipotentShear]
  value_add := by
    intro s t
    exact (unipotentShear_mul s t).symm

theorem logCFTUnipotentShear_is_polynomial (τ : ℂ) :
    unipotentShear τ = (1 : Mat2C) + τ • nilpotentN := by
  rfl

noncomputable def expJordanCell_timeReversibleRepresentation (Δ : ℝ) :
    TimeReversiblePositionRepresentation
      (Matrix (Fin 2) (Fin 2) ℝ) ℝ :=
  TimeReversiblePositionRepresentation.ofAdditive
    (expJordanCell_is_additivePositionRepresentation Δ)
    (fun t => expJordanCell (-t) Δ)
    (by intro t; rfl)
    (by
      intro t
      calc
        expJordanCell (-t) Δ * expJordanCell t Δ = expJordanCell 0 Δ := by
          rw [← expJordanCell_add Δ (-t) t, neg_add_cancel]
        _ = 1 := by
          rw [exp_jordanCell]
          ext i j
          fin_cases i <;> fin_cases j <;> simp)
    (by
      intro t
      calc
        expJordanCell t Δ * expJordanCell (-t) Δ = expJordanCell 0 Δ := by
          rw [← expJordanCell_add Δ t (-t), add_neg_cancel]
        _ = 1 := by
          rw [exp_jordanCell]
          ext i j
          fin_cases i <;> fin_cases j <;> simp)

noncomputable def logCFTUnipotentShear_timeReversibleRepresentation :
    TimeReversiblePositionRepresentation Mat2C ℂ :=
  TimeReversiblePositionRepresentation.ofAdditive
    logCFTUnipotentShear_is_additivePositionRepresentation
    (fun t => unipotentShear (-t))
    (by intro t; rfl)
    (by
      intro t
      simpa [unipotentShear,
        logCFTUnipotentShear_is_additivePositionRepresentation] using
        (unipotentShear_neg_mul t))
    (by
      intro t
      simpa [unipotentShear,
        logCFTUnipotentShear_is_additivePositionRepresentation] using
        (unipotentShear_mul_neg t))

theorem splitRotor55_relative_position (i : Fin 5) (s t : ℝ) :
    splitRotor55 i (-s) * splitRotor55 i t = splitRotor55 i (t - s) :=
  splitRotor55_relative i s t

theorem hyperbolicRotor_relative_position (θ s t : ℝ) :
    hyperbolicRotor θ (-s) * hyperbolicRotor θ t = hyperbolicRotor θ (t - s) := by
  exact hyperbolicRotor_add θ (-s) t ▸ by congr 1; ring

end InfoGeometry.Canonical.PositionalDynamicsRegimeBridge
