/-
InfoGeometry/OperatorAlgebra/SpectralGeneratorProxy.lean

Bounded proxies for spectral generators.

This module supplies three sockets:

* `PhaseResolventDatum`:
  a proof-carrying bounded Cayley transform
      U = (D - K) (D + K)^(-1)
  with phase-linearity proved from the phase-linearity of `D`, `K`, and the
  supplied inverse.

* `BoundedTransformDatum`:
  a bounded transform proxy for an unbounded or spectral generator.

* `BoundedKasparovCycle`:
  compact-defect conditions for the bounded/Kasparov layer.

The point is to avoid faking an unbounded closed-operator API. Downstream
operator-geometry modules should consume bounded endomorphisms and proof
certificates.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SpectralGeneratorProxy

/-! ## 1. Bounded real endomorphisms and phase-linearity -/

/-- Bounded real endomorphisms of a normed real carrier. -/
abbrev EndR
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  H →L[ℝ] H

/--
An endomorphism is phase-linear when it commutes with the chosen phase axis `K`.
-/
def PhaseLinear
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H)
    (T : EndR H) : Prop :=
  T.comp K = K.comp T

namespace PhaseLinear

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K S T : EndR H}

/-- Pointwise form of phase-linearity. -/
theorem apply
    (hT : PhaseLinear K T)
    (x : H) :
    T (K x) = K (T x) := by
  have h := congrArg (fun A : EndR H => A x) hT
  simpa [PhaseLinear, ContinuousLinearMap.comp_apply] using h

/-- The phase axis is phase-linear with respect to itself. -/
theorem self
    (K : EndR H) :
    PhaseLinear K K :=
  rfl

/-- The zero endomorphism is phase-linear. -/
theorem zero
    (K : EndR H) :
    PhaseLinear K (0 : EndR H) := by
  ext x
  simp

/-- Sums of phase-linear maps are phase-linear. -/
theorem add
    (hS : PhaseLinear K S)
    (hT : PhaseLinear K T) :
    PhaseLinear K (S + T) := by
  ext x
  change S (K x) + T (K x) = K (S x + T x)
  rw [apply hS x, apply hT x]
  simp

/-- Negatives of phase-linear maps are phase-linear. -/
theorem neg
    (hT : PhaseLinear K T) :
    PhaseLinear K (-T) := by
  ext x
  change -T (K x) = K (-T x)
  rw [apply hT x]
  simp

/-- Differences of phase-linear maps are phase-linear. -/
theorem sub
    (hS : PhaseLinear K S)
    (hT : PhaseLinear K T) :
    PhaseLinear K (S - T) := by
  simpa [sub_eq_add_neg] using add hS (neg hT)

/-- Scalar multiples of phase-linear maps are phase-linear. -/
theorem smul
    (a : ℝ)
    (hT : PhaseLinear K T) :
    PhaseLinear K (a • T) := by
  ext x
  change a • T (K x) = K (a • T x)
  rw [apply hT x]
  simp

/-- Compositions of phase-linear maps are phase-linear. -/
theorem comp
    (hS : PhaseLinear K S)
    (hT : PhaseLinear K T) :
    PhaseLinear K (S.comp T) := by
  ext x
  change S (T (K x)) = K (S (T x))
  rw [apply hT x, apply hS (T x)]

end PhaseLinear

/-! ## 2. Operator Cayley identities -/

/--
Right Cayley transform relation.

Let `U` be a right inverse witness for `1 - X` in the sense

`U * (1 - X) = 1`.

For the right Cayley expression

`Y = (1 + X) * U`,

we have

`(Y - 1) * (1 - X) = 2 * X`.

This is the noncommutative operator version of the scalar identity underlying
`C⁻¹(C(x)) = x`, before dividing by `2`.
-/
theorem operator_cayley_right_sub_relation
    {R : Type*} [Ring R]
    (X U : R)
    (hU : U * (1 - X) = 1) :
    (((1 + X) * U) - 1) * (1 - X) = (2 : R) * X := by
  calc
    (((1 + X) * U) - 1) * (1 - X)
        = (1 + X) * (U * (1 - X)) - (1 - X) := by
          noncomm_ring
    _ = (1 + X) * 1 - (1 - X) := by
          rw [hU]
    _ = (2 : R) * X := by
          noncomm_ring

/--
Right Cayley denominator relation.

Under the same hypothesis,

`(((1 + X) * U) + 1) * (1 - X) = 2`.

This is the operator denominator identity behind the inverse Cayley formula.
-/
theorem operator_cayley_right_add_relation
    {R : Type*} [Ring R]
    (X U : R)
    (hU : U * (1 - X) = 1) :
    (((1 + X) * U) + 1) * (1 - X) = (2 : R) := by
  calc
    (((1 + X) * U) + 1) * (1 - X)
        = (1 + X) * (U * (1 - X)) + (1 - X) := by
          noncomm_ring
    _ = (1 + X) * 1 + (1 - X) := by
          rw [hU]
    _ = (2 : R) := by
          norm_num

/-! ## Common Gibbs half-factor lemmas -/

/--
Common Gibbs half-factor for the bosonic denominator.

If `Eminus * Eplus = 1`, then

`1 - Eminus * Eminus = Eminus * (Eplus - Eminus)`.

In the thermal specialization:

`Eplus = exp(βH/2)`,
`Eminus = exp(-βH/2)`,
so this is

`1 - exp(-βH) = exp(-βH/2) * (exp(βH/2) - exp(-βH/2))`.
-/
theorem common_gibbs_half_factor_sub
    {R : Type*} [Ring R]
    {Eplus Eminus : R}
    (hInv : Eminus * Eplus = 1) :
    1 - Eminus * Eminus = Eminus * (Eplus - Eminus) := by
  calc
    1 - Eminus * Eminus
        = Eminus * Eplus - Eminus * Eminus := by
          rw [hInv]
    _ = Eminus * (Eplus - Eminus) := by
          rw [mul_sub]

/--
Common Gibbs half-factor for the fermionic factor.

If `Eminus * Eplus = 1`, then

`1 + Eminus * Eminus = Eminus * (Eplus + Eminus)`.

In the thermal specialization:

`1 + exp(-βH) = exp(-βH/2) * (exp(βH/2) + exp(-βH/2))`.
-/
theorem common_gibbs_half_factor_add
    {R : Type*} [Ring R]
    {Eplus Eminus : R}
    (hInv : Eminus * Eplus = 1) :
    1 + Eminus * Eminus = Eminus * (Eplus + Eminus) := by
  calc
    1 + Eminus * Eminus
        = Eminus * Eplus + Eminus * Eminus := by
          rw [hInv]
    _ = Eminus * (Eplus + Eminus) := by
          rw [mul_add]

/-! ## 3. Phase-compatible Cayley transform -/

/--
Phase-compatible resolvent datum for the bounded Cayley transform.

The intended Cayley transform is

`U = (D - K) (D + K)^(-1)`.

The inverse of `D + K` is supplied as bounded data. This avoids requiring a
full unbounded resolvent API.
-/
structure PhaseResolventDatum
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  /-- Hestenes/modular phase axis. -/
  K : EndR H

  /-- Bounded spectral-generator proxy. -/
  D : EndR H

  /-- Supplied inverse of `D + K`. -/
  denomInv : EndR H

  /-- `D` commutes with the phase axis. -/
  D_phase_linear :
    PhaseLinear K D

  /-- The supplied inverse commutes with the phase axis. -/
  denomInv_phase_linear :
    PhaseLinear K denomInv

  /-- Right inverse law: `(D + K) ∘ denomInv = id`. -/
  denom_right :
    (D + K).comp denomInv = ContinuousLinearMap.id ℝ H

  /-- Left inverse law: `denomInv ∘ (D + K) = id`. -/
  denom_left :
    denomInv.comp (D + K) = ContinuousLinearMap.id ℝ H

namespace PhaseResolventDatum

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

variable (R : PhaseResolventDatum H)

/-- The Cayley denominator `D + K` is phase-linear. -/
theorem denom_phase_linear :
    PhaseLinear R.K (R.D + R.K) :=
  PhaseLinear.add R.D_phase_linear (PhaseLinear.self R.K)

/-- The Cayley numerator `D - K` is phase-linear. -/
theorem numerator_phase_linear :
    PhaseLinear R.K (R.D - R.K) :=
  PhaseLinear.sub R.D_phase_linear (PhaseLinear.self R.K)

/--
Bounded Cayley transform:

`U = (D - K) ∘ (D + K)^(-1)`.
-/
def boundedCayley : EndR H :=
  (R.D - R.K).comp R.denomInv

/--
The bounded Cayley transform is phase-linear.

This is derived, not asserted.
-/
theorem boundedCayley_phase_linear :
    PhaseLinear R.K R.boundedCayley :=
  PhaseLinear.comp R.numerator_phase_linear R.denomInv_phase_linear

/-- Right inverse law for the Cayley denominator. -/
theorem denom_right_apply :
    (R.D + R.K).comp R.denomInv = ContinuousLinearMap.id ℝ H :=
  R.denom_right

/-- Left inverse law for the Cayley denominator. -/
theorem denom_left_apply :
    R.denomInv.comp (R.D + R.K) = ContinuousLinearMap.id ℝ H :=
  R.denom_left

end PhaseResolventDatum

/-! ## 3. Bounded transform proxy -/

/--
Bounded transform datum.

A concrete unbounded spectral generator `D_unbd` may later produce this bounded
operator by a Baaj-Julg style transform, for example

`F = D (1 + D^2)^(-1/2)`.

At this layer, `F` is the bounded object consumed by downstream modules.
-/
structure BoundedTransformDatum
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  /-- Phase axis. -/
  K : EndR H

  /-- Bounded transform of the spectral generator. -/
  F : EndR H

  /-- `F` is phase-linear. -/
  F_phase_linear :
    PhaseLinear K F

namespace BoundedTransformDatum

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

variable (B : BoundedTransformDatum H)

/-- Re-export phase-linearity of the bounded transform. -/
theorem phase_linear :
    PhaseLinear B.K B.F :=
  B.F_phase_linear

end BoundedTransformDatum

/-! ## 4. Representation and compact-defect sockets -/

/--
A bounded real representation of an algebra by bounded endomorphisms.

This is deliberately lightweight. A star/algebra-hom version can be added for
concrete C*-algebraic models.
-/
structure BoundedRealRepresentation
    (A H : Type*)
    [Ring A] [Module ℝ A]
    [NormedAddCommGroup H] [NormedSpace ℝ H] where
  /-- Representation map. -/
  rep : A →+* EndR H

  /-- Compatibility with the given real module structure. -/
  map_smul :
    ∀ (r : ℝ) (a : A), rep (r • a) = r • rep a

namespace BoundedRealRepresentation

variable
    {A H : Type*}
    [Ring A] [Module ℝ A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]

variable (ρ : BoundedRealRepresentation A H)

theorem rep_one :
    ρ.rep 1 = ContinuousLinearMap.id ℝ H :=
  ρ.rep.map_one

theorem map_one :
    ρ.rep 1 = ContinuousLinearMap.id ℝ H :=
  ρ.rep.map_one

theorem map_add
    (a b : A) :
    ρ.rep (a + b) = ρ.rep a + ρ.rep b :=
  ρ.rep.map_add a b

theorem rep_mul
    (a b : A) :
    ρ.rep (a * b) = (ρ.rep a).comp (ρ.rep b) :=
  ρ.rep.map_mul a b

theorem map_mul
    (a b : A) :
    ρ.rep (a * b) = (ρ.rep a).comp (ρ.rep b) :=
  ρ.rep.map_mul a b

end BoundedRealRepresentation

/--
Operator commutator using bounded composition.
-/
def endCommutator
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (S T : EndR H) : EndR H :=
  S.comp T - T.comp S

@[simp]
theorem endCommutator_self
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : EndR H) :
    endCommutator T T = 0 := by
  ext x
  simp [endCommutator]

/--
Adjoint backend for bounded endomorphisms.

Concrete Hilbert-space models may instantiate this using Mathlib's adjoint API.
Keeping it explicit makes the Kasparov socket usable in weaker or Krein-style
settings.
-/
structure AdjointBackend
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  adj : EndR H → EndR H

/--
Compact/ideal backend for Kasparov compact defects.

A concrete implementation can replace `IsCompactLike` by Mathlib compact
operators, finite-rank operators, Schatten ideals, or a model-specific ideal.
-/
structure CompactDefectBackend
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  IsCompactLike : EndR H → Prop

  /-- The zero operator is compact-like. -/
  zero_mem :
    IsCompactLike 0

  /-- Addition closure of the compact-like ideal. -/
  add_mem :
    ∀ S T : EndR H,
      IsCompactLike S →
      IsCompactLike T →
        IsCompactLike (S + T)

  /-- Negation closure of the compact-like ideal. -/
  neg_mem :
    ∀ T : EndR H,
      IsCompactLike T →
        IsCompactLike (-T)

namespace CompactDefectBackend

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

variable (Kc : CompactDefectBackend H)

/-- Subtraction closure. -/
theorem sub_mem
    (S T : EndR H)
    (hS : Kc.IsCompactLike S)
    (hT : Kc.IsCompactLike T) :
    Kc.IsCompactLike (S - T) := by
  simpa [sub_eq_add_neg] using Kc.add_mem S (-T) hS (Kc.neg_mem T hT)

end CompactDefectBackend

/-! ## 5. Bounded Kasparov cycle socket -/

/--
Bounded Kasparov/Fredholm-module socket.

This structure does not try to prove compactness from pure algebra. It records
the compact-defect obligations required once a bounded transform `F` has been
chosen.
-/
structure BoundedKasparovCycle
    (A H : Type*)
    [Ring A] [Module ℝ A]
    [NormedAddCommGroup H] [NormedSpace ℝ H] where
  /-- Representation of the algebra. -/
  representation :
    BoundedRealRepresentation A H

  /-- Phase axis. -/
  K : EndR H

  /-- Bounded transform/Fredholm operator. -/
  F : EndR H

  /-- `F` is phase-linear. -/
  F_phase_linear :
    PhaseLinear K F

  /-- Represented algebra is phase-linear. -/
  rep_phase_linear :
    ∀ a : A, PhaseLinear K (representation.rep a)

  /-- Adjoint backend. -/
  adjointBackend :
    AdjointBackend H

  /-- Compact-defect backend. -/
  compactBackend :
    CompactDefectBackend H

  /-- Compactness of `F² - 1`. -/
  square_defect_compact :
    compactBackend.IsCompactLike
      (F.comp F - ContinuousLinearMap.id ℝ H)

  /-- Compactness of `F* - F`, where `*` is supplied by the backend. -/
  selfadjoint_defect_compact :
    compactBackend.IsCompactLike
      (adjointBackend.adj F - F)

  /-- Compactness of commutators `[F,ρ(a)]`. -/
  commutator_defect_compact :
    ∀ a : A,
      compactBackend.IsCompactLike
        (endCommutator F (representation.rep a))

namespace BoundedKasparovCycle

variable
    {A H : Type*}
    [Ring A] [Module ℝ A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]

variable (Kcy : BoundedKasparovCycle A H)

/-- Re-export compactness of the square defect. -/
theorem square_defect :
    Kcy.compactBackend.IsCompactLike
      (Kcy.F.comp Kcy.F - ContinuousLinearMap.id ℝ H) :=
  Kcy.square_defect_compact

/-- Re-export compactness of the self-adjointness defect. -/
theorem selfadjoint_defect :
    Kcy.compactBackend.IsCompactLike
      (Kcy.adjointBackend.adj Kcy.F - Kcy.F) :=
  Kcy.selfadjoint_defect_compact

/-- Re-export compactness of represented commutators. -/
theorem commutator_defect
    (a : A) :
    Kcy.compactBackend.IsCompactLike
      (endCommutator Kcy.F (Kcy.representation.rep a)) :=
  Kcy.commutator_defect_compact a

/-- The bounded transform is phase-linear. -/
theorem F_phase :
    PhaseLinear Kcy.K Kcy.F :=
  Kcy.F_phase_linear

/-- The represented algebra is phase-linear. -/
theorem rep_phase
    (a : A) :
    PhaseLinear Kcy.K (Kcy.representation.rep a) :=
  Kcy.rep_phase_linear a

end BoundedKasparovCycle

/-! ## 6. Constructive readouts -/

/-- Supplied phase-resolvent data produce a phase-linear bounded Cayley transform. -/
@[owner_target_tag]
theorem phaseResolventOwnerTarget :
  ∀ (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H],
    ∀ R : PhaseResolventDatum H,
      PhaseLinear R.K R.boundedCayley := by
  intro H _ _ R
  exact R.boundedCayley_phase_linear

/-- Supplied bounded-transform data carry phase-linearity of `F`. -/
@[owner_target_tag]
theorem boundedTransformOwnerTarget :
  ∀ (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H],
    ∀ B : BoundedTransformDatum H,
      PhaseLinear B.K B.F := by
  intro H _ _ B
  exact B.phase_linear

/-- Supplied bounded Kasparov cycles expose their compact-defect and phase laws. -/
@[owner_target_tag]
theorem boundedKasparovCycleOwnerTarget :
  ∀ (A H : Type*)
    [Ring A] [Module ℝ A]
    [NormedAddCommGroup H] [NormedSpace ℝ H],
    ∀ Kcy : BoundedKasparovCycle A H,
      PhaseLinear Kcy.K Kcy.F ∧
      Kcy.compactBackend.IsCompactLike
        (Kcy.F.comp Kcy.F - ContinuousLinearMap.id ℝ H) ∧
      (∀ a : A,
        Kcy.compactBackend.IsCompactLike
          (endCommutator Kcy.F (Kcy.representation.rep a))) := by
  intro A H _ _ _ _ Kcy
  exact ⟨Kcy.F_phase, Kcy.square_defect, Kcy.commutator_defect⟩

end InfoGeometry.OperatorAlgebra.SpectralGeneratorProxy
