import Mathlib
import InfoGeometry.Krein.DoubledSpace

/-!
# Real Doubled Chiral Krein Operators

This module records the finite algebraic constraints for a purely real doubled
Krein carrier

`K_R = H_R ⊕ H_R`.

It keeps three structures separate:

* the split Krein metric, represented by the diagonal sign flip
  `spectral_epsilon`;
* the chiral/off-block metric, represented by the swap `modular_j`;
* chiral grading and block/off-block operator predicates.

No complex phase, unbounded Hamiltonian, exponential flow, zeta theorem, or
Type-III operator-algebraic claim is asserted here.
-/

noncomputable section

open scoped InnerProductSpace

namespace InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein

open InfoGeometry.Krein

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The real doubled carrier `H_R ⊕ H_R`. -/
abbrev H₂ :=
  DoubledSpace E

/-- Real continuous endomorphisms of the doubled carrier. -/
abbrev EndH₂ :=
  H₂ (E := E) →L[ℝ] H₂ (E := E)

/-! ## 1. Split and chiral Krein forms -/

/-- Split Krein form: `[(x,ξ),(y,η)] = ⟪x,y⟫ - ⟪ξ,η⟫`. -/
def splitKreinForm
    (u v : H₂ (E := E)) : ℝ :=
  inner ℝ (WithLp.fst u) (WithLp.fst v) -
    inner ℝ (WithLp.snd u) (WithLp.snd v)

/-- Off-block/chiral Krein form: `⟪x,η⟫ + ⟪ξ,y⟫`. -/
def chiralKreinForm
    (u v : H₂ (E := E)) : ℝ :=
  inner ℝ (WithLp.fst u) (WithLp.snd v) +
    inner ℝ (WithLp.snd u) (WithLp.fst v)

omit [CompleteSpace E] in
/-- Coordinate formula for the split Krein form. -/
theorem splitKreinForm_to_doubled
    (x ξ y η : E) :
    splitKreinForm
        (to_doubled x ξ : H₂ (E := E))
        (to_doubled y η : H₂ (E := E)) =
      inner ℝ x y - inner ℝ ξ η := by
  rfl

omit [CompleteSpace E] in
/-- Coordinate formula for the chiral/off-block Krein form. -/
theorem chiralKreinForm_to_doubled
    (x ξ y η : E) :
    chiralKreinForm
        (to_doubled x ξ : H₂ (E := E))
        (to_doubled y η : H₂ (E := E)) =
      inner ℝ x η + inner ℝ ξ y := by
  rfl

/-! ## 2. Chiral grading, metric, and block predicates -/

/-- Chiral grading in the chiral basis: `γ₅ = diag(1,-1)`. -/
def gamma5 : EndH₂ (E := E) :=
  spectral_epsilon (E := E)

/-- Chiral Krein metric: off-block swap `γ₀ = σₓ`. -/
def etaChiral : EndH₂ (E := E) :=
  modular_j (E := E)

/-- Split Krein metric: diagonal signature `η = diag(1,-1)`. -/
def etaSplit : EndH₂ (E := E) :=
  spectral_epsilon (E := E)

/-- Operators preserving the chiral decomposition commute with `γ₅`. -/
def IsBlockDiagonal
    (X : EndH₂ (E := E)) : Prop :=
  X.comp (gamma5 (E := E)) = (gamma5 (E := E)).comp X

/-- Operators exchanging chiral sectors anticommute with `γ₅`. -/
def IsOffBlockDiagonal
    (X : EndH₂ (E := E)) : Prop :=
  X.comp (gamma5 (E := E)) = -((gamma5 (E := E)).comp X)

/-- Self-adjointness with respect to an explicitly supplied real bilinear form. -/
def IsSelfAdjointFor
    (B : H₂ (E := E) → H₂ (E := E) → ℝ)
    (X : EndH₂ (E := E)) : Prop :=
  ∀ u v, B (X u) v = B u (X v)

/-- Skew-adjointness with respect to an explicitly supplied real bilinear form. -/
def IsSkewAdjointFor
    (B : H₂ (E := E) → H₂ (E := E) → ℝ)
    (X : EndH₂ (E := E)) : Prop :=
  ∀ u v, B (X u) v = -B u (X v)

omit [CompleteSpace E] in
/-- The chiral grading is block-diagonal with respect to itself. -/
theorem gamma5_isBlockDiagonal :
    IsBlockDiagonal (gamma5 (E := E)) := by
  rfl

/-- The chiral/off-block metric exchanges chiral sectors. -/
theorem etaChiral_isOffBlockDiagonal :
    IsOffBlockDiagonal (etaChiral (E := E)) := by
  simpa [IsOffBlockDiagonal, etaChiral, gamma5] using
    (modular_j_spectral_epsilon_anticommute E)

omit [CompleteSpace E] in
/-- The split metric is block-diagonal with respect to the chiral grading. -/
theorem etaSplit_isBlockDiagonal :
    IsBlockDiagonal (etaSplit (E := E)) := by
  rfl

/-- The chiral grading is an involution. -/
theorem gamma5_involution :
    (gamma5 (E := E)).comp (gamma5 (E := E)) =
      ContinuousLinearMap.id ℝ (H₂ (E := E)) := by
  simpa [gamma5] using spectral_epsilon_involution E

/-- The off-block chiral metric is an involution. -/
theorem etaChiral_involution :
    (etaChiral (E := E)).comp (etaChiral (E := E)) =
      ContinuousLinearMap.id ℝ (H₂ (E := E)) := by
  simpa [etaChiral] using modular_j_involution E

/-- The split grading and off-block chiral metric anticommute. -/
theorem etaChiral_gamma5_anticommute :
    (etaChiral (E := E)).comp (gamma5 (E := E)) =
      -((gamma5 (E := E)).comp (etaChiral (E := E))) := by
  simpa [etaChiral, gamma5] using modular_j_spectral_epsilon_anticommute E

/-! ## 3. Algebraic closure laws for block/off-block operators -/

omit [CompleteSpace E] in
/-- The zero operator is block-diagonal. -/
theorem isBlockDiagonal_zero :
    IsBlockDiagonal (0 : EndH₂ (E := E)) := by
  simp [IsBlockDiagonal]

omit [CompleteSpace E] in
/-- The identity operator is block-diagonal. -/
theorem isBlockDiagonal_id :
    IsBlockDiagonal (ContinuousLinearMap.id ℝ (H₂ (E := E))) := by
  simp [IsBlockDiagonal]

omit [CompleteSpace E] in
/-- Block-diagonal operators are closed under addition. -/
theorem IsBlockDiagonal.add
    {X Y : EndH₂ (E := E)}
    (hX : IsBlockDiagonal X)
    (hY : IsBlockDiagonal Y) :
    IsBlockDiagonal (X + Y) := by
  unfold IsBlockDiagonal at hX hY ⊢
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hX, hY]

omit [CompleteSpace E] in
/-- Block-diagonal operators are closed under negation. -/
theorem IsBlockDiagonal.neg
    {X : EndH₂ (E := E)}
    (hX : IsBlockDiagonal X) :
    IsBlockDiagonal (-X) := by
  unfold IsBlockDiagonal at hX ⊢
  rw [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg, hX]

omit [CompleteSpace E] in
/-- Off-block operators are closed under addition. -/
theorem IsOffBlockDiagonal.add
    {X Y : EndH₂ (E := E)}
    (hX : IsOffBlockDiagonal X)
    (hY : IsOffBlockDiagonal Y) :
    IsOffBlockDiagonal (X + Y) := by
  unfold IsOffBlockDiagonal at hX hY ⊢
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hX, hY]
  simp [add_comm]

omit [CompleteSpace E] in
/-- Off-block operators are closed under negation. -/
theorem IsOffBlockDiagonal.neg
    {X : EndH₂ (E := E)}
    (hX : IsOffBlockDiagonal X) :
    IsOffBlockDiagonal (-X) := by
  unfold IsOffBlockDiagonal at hX ⊢
  rw [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg, hX]

omit [CompleteSpace E] in
/-- The product/composition of two block-diagonal operators is block-diagonal. -/
theorem IsBlockDiagonal.comp
    {X Y : EndH₂ (E := E)}
    (hX : IsBlockDiagonal X)
    (hY : IsBlockDiagonal Y) :
    IsBlockDiagonal (X.comp Y) := by
  unfold IsBlockDiagonal at hX hY ⊢
  calc
    (X.comp Y).comp (gamma5 (E := E))
        = X.comp (Y.comp (gamma5 (E := E))) := by
            rw [ContinuousLinearMap.comp_assoc]
    _ = X.comp ((gamma5 (E := E)).comp Y) := by
            rw [hY]
    _ = (X.comp (gamma5 (E := E))).comp Y := by
            rw [← ContinuousLinearMap.comp_assoc]
    _ = ((gamma5 (E := E)).comp X).comp Y := by
            rw [hX]
    _ = (gamma5 (E := E)).comp (X.comp Y) := by
            rw [ContinuousLinearMap.comp_assoc]

omit [CompleteSpace E] in
/-- A block-diagonal operator after an off-block operator is off-block. -/
theorem IsBlockDiagonal.comp_off
    {X Y : EndH₂ (E := E)}
    (hX : IsBlockDiagonal X)
    (hY : IsOffBlockDiagonal Y) :
    IsOffBlockDiagonal (X.comp Y) := by
  unfold IsBlockDiagonal at hX
  unfold IsOffBlockDiagonal at hY ⊢
  calc
    (X.comp Y).comp (gamma5 (E := E))
        = X.comp (Y.comp (gamma5 (E := E))) := by
            rw [ContinuousLinearMap.comp_assoc]
    _ = X.comp (-(gamma5 (E := E)).comp Y) := by
            rw [hY]
    _ = -(X.comp ((gamma5 (E := E)).comp Y)) := by
            simp
    _ = -((X.comp (gamma5 (E := E))).comp Y) := by
            rw [← ContinuousLinearMap.comp_assoc]
    _ = -(((gamma5 (E := E)).comp X).comp Y) := by
            rw [hX]
    _ = -((gamma5 (E := E)).comp (X.comp Y)) := by
            rw [ContinuousLinearMap.comp_assoc]

omit [CompleteSpace E] in
/-- An off-block operator after a block-diagonal operator is off-block. -/
theorem IsOffBlockDiagonal.comp_block
    {X Y : EndH₂ (E := E)}
    (hX : IsOffBlockDiagonal X)
    (hY : IsBlockDiagonal Y) :
    IsOffBlockDiagonal (X.comp Y) := by
  unfold IsOffBlockDiagonal at hX ⊢
  unfold IsBlockDiagonal at hY
  calc
    (X.comp Y).comp (gamma5 (E := E))
        = X.comp (Y.comp (gamma5 (E := E))) := by
            rw [ContinuousLinearMap.comp_assoc]
    _ = X.comp ((gamma5 (E := E)).comp Y) := by
            rw [hY]
    _ = (X.comp (gamma5 (E := E))).comp Y := by
            rw [← ContinuousLinearMap.comp_assoc]
    _ = (-(gamma5 (E := E)).comp X).comp Y := by
            rw [hX]
    _ = -(((gamma5 (E := E)).comp X).comp Y) := by
            simp
    _ = -((gamma5 (E := E)).comp (X.comp Y)) := by
            rw [ContinuousLinearMap.comp_assoc]

omit [CompleteSpace E] in
/-- The product/composition of two off-block operators is block-diagonal. -/
theorem IsOffBlockDiagonal.comp
    {X Y : EndH₂ (E := E)}
    (hX : IsOffBlockDiagonal X)
    (hY : IsOffBlockDiagonal Y) :
    IsBlockDiagonal (X.comp Y) := by
  unfold IsOffBlockDiagonal at hX hY
  unfold IsBlockDiagonal
  calc
    (X.comp Y).comp (gamma5 (E := E))
        = X.comp (Y.comp (gamma5 (E := E))) := by
            rw [ContinuousLinearMap.comp_assoc]
    _ = X.comp (-(gamma5 (E := E)).comp Y) := by
            rw [hY]
    _ = -(X.comp ((gamma5 (E := E)).comp Y)) := by
            simp
    _ = -((X.comp (gamma5 (E := E))).comp Y) := by
            rw [← ContinuousLinearMap.comp_assoc]
    _ = -((-(gamma5 (E := E)).comp X).comp Y) := by
            rw [hX]
    _ = ((gamma5 (E := E)).comp X).comp Y := by
            simp
    _ = (gamma5 (E := E)).comp (X.comp Y) := by
            rw [ContinuousLinearMap.comp_assoc]

/-! ## 4. Even/odd additive operator sectors -/

/--
The additive real submodule of block-diagonal/even operators.

This is the Lean-safe replacement for saying "the even block operators form
the even part of a `Z₂`-graded operator algebra".
-/
def blockDiagonalSubmodule :
    Submodule ℝ (EndH₂ (E := E)) where
  carrier := {X | IsBlockDiagonal X}
  zero_mem' := isBlockDiagonal_zero
  add_mem' := by
    intro X Y hX hY
    exact hX.add hY
  smul_mem' := by
    intro a X hX
    change IsBlockDiagonal X at hX
    change IsBlockDiagonal (a • X)
    unfold IsBlockDiagonal at hX ⊢
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hX]

/--
The additive real submodule of off-block/odd operators.

It is not a ring ideal: composition of two odd operators is even.
-/
def offBlockSubmodule :
    Submodule ℝ (EndH₂ (E := E)) where
  carrier := {X | IsOffBlockDiagonal X}
  zero_mem' := by
    simp [IsOffBlockDiagonal]
  add_mem' := by
    intro X Y hX hY
    exact hX.add hY
  smul_mem' := by
    intro a X hX
    change IsOffBlockDiagonal X at hX
    change IsOffBlockDiagonal (a • X)
    unfold IsOffBlockDiagonal at hX ⊢
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hX]
    simp

omit [CompleteSpace E] in
/-- Membership in the even/block submodule is the block-diagonal predicate. -/
theorem mem_blockDiagonalSubmodule_iff
    (X : EndH₂ (E := E)) :
    X ∈ blockDiagonalSubmodule (E := E) ↔ IsBlockDiagonal X :=
  Iff.rfl

omit [CompleteSpace E] in
/-- Membership in the odd/off-block submodule is the off-block predicate. -/
theorem mem_offBlockSubmodule_iff
    (X : EndH₂ (E := E)) :
    X ∈ offBlockSubmodule (E := E) ↔ IsOffBlockDiagonal X :=
  Iff.rfl

omit [CompleteSpace E] in
/-- Even-after-even composition stays even. -/
theorem blockSubmodule_comp_block
    {X Y : EndH₂ (E := E)}
    (hX : X ∈ blockDiagonalSubmodule (E := E))
    (hY : Y ∈ blockDiagonalSubmodule (E := E)) :
    X.comp Y ∈ blockDiagonalSubmodule (E := E) :=
  IsBlockDiagonal.comp hX hY

omit [CompleteSpace E] in
/-- Even-after-odd composition is odd. -/
theorem blockSubmodule_comp_off
    {X Y : EndH₂ (E := E)}
    (hX : X ∈ blockDiagonalSubmodule (E := E))
    (hY : Y ∈ offBlockSubmodule (E := E)) :
    X.comp Y ∈ offBlockSubmodule (E := E) :=
  IsBlockDiagonal.comp_off hX hY

omit [CompleteSpace E] in
/-- Odd-after-even composition is odd. -/
theorem offSubmodule_comp_block
    {X Y : EndH₂ (E := E)}
    (hX : X ∈ offBlockSubmodule (E := E))
    (hY : Y ∈ blockDiagonalSubmodule (E := E)) :
    X.comp Y ∈ offBlockSubmodule (E := E) :=
  IsOffBlockDiagonal.comp_block hX hY

omit [CompleteSpace E] in
/-- Odd-after-odd composition is even. -/
theorem offSubmodule_comp_off
    {X Y : EndH₂ (E := E)}
    (hX : X ∈ offBlockSubmodule (E := E))
    (hY : Y ∈ offBlockSubmodule (E := E)) :
    X.comp Y ∈ blockDiagonalSubmodule (E := E) :=
  IsOffBlockDiagonal.comp hX hY

/--
Witness package for a concrete real chiral Liouvillean.

The generator is required to be off-block.  Krein self-adjointness and
flow-level invariance remain separate gates because they depend on the chosen
adjoint/domain model.
-/
structure RealChiralLiouvillean where
  /-- Chiral Liouvillean candidate. -/
  L : EndH₂ (E := E)
  /-- Algebraic oddness: `L` exchanges the chiral sectors. -/
  off_block : L ∈ offBlockSubmodule (E := E)

namespace RealChiralLiouvillean

omit [CompleteSpace E] in
/-- The chiral Liouvillean anticommutes with `γ₅`. -/
theorem isOffBlock
    (L : RealChiralLiouvillean (E := E)) :
    IsOffBlockDiagonal L.L :=
  L.off_block

omit [CompleteSpace E] in
/-- The square of an off-block chiral Liouvillean is block-diagonal. -/
theorem square_isBlock
    (L : RealChiralLiouvillean (E := E)) :
    L.L.comp L.L ∈ blockDiagonalSubmodule (E := E) :=
  offSubmodule_comp_off L.off_block L.off_block

end RealChiralLiouvillean

/-! ## 5. Chiral projectors -/

/-- Left chiral projector `(1 + γ₅) / 2`. -/
def leftChiralProjector : EndH₂ (E := E) :=
  (1 / 2 : ℝ) •
    (ContinuousLinearMap.id ℝ (H₂ (E := E)) + gamma5 (E := E))

/-- Right chiral projector `(1 - γ₅) / 2`. -/
def rightChiralProjector : EndH₂ (E := E) :=
  (1 / 2 : ℝ) •
    (ContinuousLinearMap.id ℝ (H₂ (E := E)) - gamma5 (E := E))

omit [CompleteSpace E] in
/-- The left chiral projector keeps the first component. -/
theorem leftChiralProjector_to_doubled
    (x ξ : E) :
    leftChiralProjector (E := E) (to_doubled x ξ : H₂ (E := E)) =
      to_doubled x 0 := by
  apply DoubledSpace.ext
  · simp [leftChiralProjector, gamma5, one_div]
    rw [← add_smul]
    norm_num
  · simp [leftChiralProjector, gamma5, one_div]

omit [CompleteSpace E] in
/-- The right chiral projector keeps the second component. -/
theorem rightChiralProjector_to_doubled
    (x ξ : E) :
    rightChiralProjector (E := E) (to_doubled x ξ : H₂ (E := E)) =
      to_doubled 0 ξ := by
  apply DoubledSpace.ext
  · simp [rightChiralProjector, gamma5, one_div, sub_eq_add_neg]
  · simp [rightChiralProjector, gamma5, one_div, sub_eq_add_neg]
    rw [← add_smul]
    norm_num

omit [CompleteSpace E] in
/-- The off-block chiral metric sends the left projector to the right one. -/
theorem etaChiral_comp_left_projector :
    (etaChiral (E := E)).comp (leftChiralProjector (E := E)) =
      (rightChiralProjector (E := E)).comp (etaChiral (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [etaChiral, leftChiralProjector, rightChiralProjector, gamma5,
      modular_j, spectral_epsilon, one_div, sub_eq_add_neg]

omit [CompleteSpace E] in
/-- The off-block chiral metric sends the right projector to the left one. -/
theorem etaChiral_comp_right_projector :
    (etaChiral (E := E)).comp (rightChiralProjector (E := E)) =
      (leftChiralProjector (E := E)).comp (etaChiral (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [etaChiral, leftChiralProjector, rightChiralProjector, gamma5,
      modular_j, spectral_epsilon, one_div, sub_eq_add_neg]

/-! ## 6. Hyperbolic-flow socket -/

/--
Witness socket for a real hyperbolic primon flow.

The exponential `exp(t L)` is not constructed here.  A concrete owner module may
supply such a flow together with preservation of the chosen Krein form and any
differential law.
-/
structure HyperbolicPrimonFlow where
  /-- One-parameter family of real doubled operators. -/
  U : ℝ → EndH₂ (E := E)
  /-- Preservation of the chiral/off-block Krein form. -/
  preserves_chiral_form :
    ∀ t u v,
      chiralKreinForm (U t u) (U t v) =
        chiralKreinForm u v

namespace HyperbolicPrimonFlow

omit [CompleteSpace E] in
/-- Re-export of chiral Krein-form invariance. -/
theorem chiral_form_invariant
    (F : HyperbolicPrimonFlow (E := E))
    (t : ℝ)
    (u v : H₂ (E := E)) :
    chiralKreinForm (F.U t u) (F.U t v) =
      chiralKreinForm u v :=
  F.preserves_chiral_form t u v

end HyperbolicPrimonFlow

/-! ## 7. Chiral Liouvillean versus Möbius heat-supertrace calibration -/

/--
Regularized comparison between a chiral Liouvillean readout and a Möbius heat
supertrace.

This is deliberately a witness gate.  The expression
`Tr(J_chiral exp(-β L_chiral / 2))` is not automatically the positive-decay
Möbius heat trace `Tr(Γ exp(-β H))`: the raw hyperbolic calculation contains
growing `sinh(βH/2)` terms and requires a concrete regulator/projection before
it can be compared to the inverse-zeta Dirichlet series.
-/
structure ChiralMobiusSupertraceCalibration
    (Readout : Type*) where
  /-- Inverse-temperature or Euclidean-time parameter used by the model. -/
  beta : ℝ
  /-- Chiral Liouvillean generator, algebraically odd/off-block. -/
  liouvillean : RealChiralLiouvillean (E := E)
  /-- Chiral signature/readout operator, usually an off-block Möbius parity. -/
  signature : EndH₂ (E := E)
  /-- Raw chiral Liouvillean signed readout. -/
  chiralReadout : Readout
  /-- Positive-decay Möbius heat readout, intended as `Tr(Γ exp(-βH))`. -/
  mobiusHeatReadout : Readout
  /-- Supplied comparison law after regularization. -/
  calibrated_eq : chiralReadout = mobiusHeatReadout

namespace ChiralMobiusSupertraceCalibration

omit [CompleteSpace E] in
/--
The calibrated equality is available only because it is supplied by the
regularized model.
-/
theorem calibrated_readout_eq
    {Readout : Type*}
    (C : ChiralMobiusSupertraceCalibration (E := E) Readout) :
    C.chiralReadout = C.mobiusHeatReadout :=
  C.calibrated_eq

omit [CompleteSpace E] in
/-- The Liouvillean in a calibration packet is algebraically off-block. -/
theorem liouvillean_isOffBlock
    {Readout : Type*}
    (C : ChiralMobiusSupertraceCalibration (E := E) Readout) :
    IsOffBlockDiagonal C.liouvillean.L :=
  C.liouvillean.isOffBlock

end ChiralMobiusSupertraceCalibration

/--
Analytic inverse-zeta witness for the positive-decay Möbius heat trace.

This is separate from the chiral Liouvillean calibration.  The theorem
`Σ μ(n)n^{-s} = 1 / ζ(s)` belongs to an analytic Dirichlet-series/Euler-product
owner, not to the finite real doubled operator algebra.
-/
structure MobiusHeatInverseZetaWitness
    (Readout ZetaReadout : Type*) where
  /-- Analytic spectral parameter. -/
  s : ℝ
  /-- Domain/convergence condition, e.g. `1 < s`. -/
  admissible : Prop
  /-- Positive-decay Möbius heat/supertrace readout. -/
  mobiusHeatReadout : Readout
  /-- Reciprocal-zeta readout. -/
  inverseZetaReadout : ZetaReadout
  /-- Supplied comparison between the two readout types. -/
  compare : Readout → ZetaReadout → Prop
  /-- Analytic calibration law. -/
  heat_eq_inverseZeta :
    compare mobiusHeatReadout inverseZetaReadout

namespace MobiusHeatInverseZetaWitness

/-- Re-export of the supplied analytic inverse-zeta calibration. -/
theorem valid
    {Readout ZetaReadout : Type*}
    (W : MobiusHeatInverseZetaWitness Readout ZetaReadout) :
    W.compare W.mobiusHeatReadout W.inverseZetaReadout :=
  W.heat_eq_inverseZeta

end MobiusHeatInverseZetaWitness

end InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
