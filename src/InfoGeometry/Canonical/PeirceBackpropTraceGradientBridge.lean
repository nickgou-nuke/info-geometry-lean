/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceBackpropTraceGradient
import InfoGeometry.Canonical.TensorPeirceAttentionNetworkAmariYangianPoset
import InfoGeometry.Canonical.CPTDyckParseTree

/-!
# Trace-adjoint bridge to the Tensor-Peirce BP₃ gradient declarations & Multi-Layer / Dyck-Tree Cotangent Transport

This module identifies the reusable finite-matrix trace adjoints with the
exact gradient expressions used by the BP₃ owner, including its reconstructed
midpoint state, the input-cotangent trace adjoint, multi-layer $n$-stage
zero-activation-memory reverse state reconstruction, and zero-attenuation
cotangent transport across balanced `CPTDyckParseTree.DyckTree` clauses.
-/

namespace InfoGeometry.Canonical.PeirceBackpropTraceGradientBridge

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.PeirceBackpropTraceGradient
open InfoGeometry.Canonical.TensorPeirceAttentionNetworkAmariYangianPoset
open InfoGeometry.Canonical.CPTDyckParseTree
open Matrix

variable {R n : Type*} [CommRing R] [StarRing R] [Fintype n] [DecidableEq n]

/-- The reduced BP₃ primal parameter term has the declared primal gate
gradient as its trace adjoint. The idempotent-dependent reduction from the
full layer differential is stated separately below. -/
theorem bp3_primalGate_trace_adjoint
    {P dA Xbar Xout : Matrix n n R} (hPstar : star P = P) :
    trace (star Xbar * (conePlus P dA * Xout)) =
      trace (star (primalGateGrad P Xbar Xout) * dA) := by
  change trace (star Xbar * (conePlus P dA * Xout)) =
    trace (star (primalGradient P Xbar Xout) * dA)
  exact primal_variation_trace_adjoint hPstar

/-- BP₃ dual differential paired with an output cotangent has the declared
dual gate gradient as its trace adjoint, using the midpoint reconstructed from
the output activation. -/
theorem bp3_dualGate_trace_adjoint
    {P A dC Xbar Xout : Matrix n n R} (hPstar : star P = P) :
    trace (star Xbar * ((1 + conePlus P A) *
        (coneMinus P dC * backpropMidpoint P A Xout))) =
      trace (star (dualGateGrad P A Xbar Xout) * dC) := by
  change trace (star Xbar * ((1 + conePlus P A) *
      (coneMinus P dC * backpropMidpoint P A Xout))) =
    trace (star (dualGradient P (conePlus P A) Xbar
      (backpropMidpoint P A Xout)) * dC)
  exact dual_variation_trace_adjoint hPstar

/-- Input-variation trace adjoint: pairing the forward layer action
`attentionGaussianPlus P A C * dX_in` with `Xbar` equals pairing `dX_in`
with `inputCotangentGrad P A C Xbar = star (attentionGaussianPlus P A C) * Xbar`. -/
theorem bp3_inputCotangent_trace_adjoint
    (P A C Xbar dX_in : Matrix n n R) :
    trace (star Xbar * (attentionGaussianPlus P A C * dX_in)) =
      trace (star (inputCotangentGrad P A C Xbar) * dX_in) := by
  dsimp [inputCotangentGrad]
  rw [star_mul, star_star, mul_assoc]

/-- Full BP₃ parameter differential adjoint formula. The input activation is
reconstructed from `Xout` by the owner's polynomial inverse; idempotence
reduces the differential to its primal and dual contributions, whose trace
adjoints are the two BP₃ gate gradients. -/
theorem bp3_parameter_variation_trace_adjoint
    {P A C dA dC Xbar Xout : Matrix n n R}
    (hP : P * P = P) (hPstar : star P = P) :
    trace (star Xbar *
        (attentionGaussianPlusDiff P A C dA dC * backpropInput P A C Xout)) =
      trace (star (primalGateGrad P Xbar Xout) * dA) +
        trace (star (dualGateGrad P A Xbar Xout) * dC) := by
  have hReduction :
      attentionGaussianPlusDiff P A C dA dC * backpropInput P A C Xout =
        conePlus P dA * Xout +
          (1 + conePlus P A) *
            (coneMinus P dC * backpropMidpoint P A Xout) := by
    dsimp [attentionGaussianPlusDiff, backpropInput, backpropMidpoint,
      attentionGaussianPlusInv, amariGatePlus, amariGateMinus,
      genPhi, qgtMinus]
    peirce_nf hP
  rw [hReduction, mul_add, Matrix.trace_add]
  rw [bp3_primalGate_trace_adjoint hPstar]
  rw [bp3_dualGate_trace_adjoint hPstar]

/-- Complete single-layer total differential trace-adjoint identity:
combines the primal gate gradient, dual gate gradient, and input cotangent
gradient for `dX_out = d𝒢_+ * backpropInput(X_out) + 𝒢_+ * dX_in`. -/
theorem bp3_total_layer_differential_trace_adjoint
    {P A C dA dC Xbar Xout dX_in : Matrix n n R}
    (hP : P * P = P) (hPstar : star P = P) :
    trace (star Xbar *
        (attentionGaussianPlusDiff P A C dA dC * backpropInput P A C Xout +
          attentionGaussianPlus P A C * dX_in)) =
      trace (star (primalGateGrad P Xbar Xout) * dA) +
        trace (star (dualGateGrad P A Xbar Xout) * dC) +
        trace (star (inputCotangentGrad P A C Xbar) * dX_in) := by
  rw [mul_add, Matrix.trace_add,
    bp3_parameter_variation_trace_adjoint hP hPstar,
    bp3_inputCotangent_trace_adjoint]

/-- Plus-dressed primal direction used by the trace-adjoint parameterization:
`(1 + qgtPlus P A C) * primalGateGrad P Xbar Xout`. This is distinct from
the canonical minus-dressed `amariNatPrimalGateGrad` in the Tensor-Peirce owner. -/
def plusDressedPrimalGrad {B : Type*} [Ring B] [StarRing B]
    (P A C Xbar Xout : B) : B :=
  (1 + qgtPlus P A C) * primalGateGrad P Xbar Xout

/-- Plus-dressed dual direction paired with `plusDressedPrimalGrad`:
`(1 + qgtMinus P A C) * dualGateGrad P A Xbar Xout`. -/
def plusDressedDualGrad {B : Type*} [Ring B] [StarRing B]
    (P A C Xbar Xout : B) : B :=
  (1 + qgtMinus P A C) * dualGateGrad P A Xbar Xout

/-- The plus-dressed primal and dual directions remain in their Peirce corners
and are square-zero. The displayed qgt identities are exact ring
factorizations; this theorem does not identify these directions with the
canonical minus-dressed natural-gradient directions in the Tensor-Peirce owner. -/
theorem bp3_plus_dressed_gradient_corner_and_square_zero
    {B : Type*} [Ring B] [StarRing B]
    {P : B} (hP : P * P = P) (A C Xbar Xout : B) :
    P * plusDressedPrimalGrad P A C Xbar Xout * (1 - P) =
      plusDressedPrimalGrad P A C Xbar Xout ∧
    plusDressedPrimalGrad P A C Xbar Xout * plusDressedPrimalGrad P A C Xbar Xout = 0 ∧
    (1 - plusDressedPrimalGrad P A C Xbar Xout) *
      (1 + plusDressedPrimalGrad P A C Xbar Xout) = 1 ∧
    (1 - qgtPlus P A C) * plusDressedPrimalGrad P A C Xbar Xout =
      (1 - qgtPlus P A C * qgtPlus P A C) * primalGateGrad P Xbar Xout ∧
    (1 - P) * plusDressedDualGrad P A C Xbar Xout * P =
      plusDressedDualGrad P A C Xbar Xout ∧
    plusDressedDualGrad P A C Xbar Xout * plusDressedDualGrad P A C Xbar Xout = 0 ∧
    (1 - plusDressedDualGrad P A C Xbar Xout) *
      (1 + plusDressedDualGrad P A C Xbar Xout) = 1 ∧
    (1 - qgtMinus P A C) * plusDressedDualGrad P A C Xbar Xout =
      (1 - qgtMinus P A C * qgtMinus P A C) * dualGateGrad P A Xbar Xout := by
  let gp := plusDressedPrimalGrad P A C Xbar Xout
  let gm := plusDressedDualGrad P A C Xbar Xout
  have hPrimalCorner : P * gp * (1 - P) = gp := by
    dsimp [gp, plusDressedPrimalGrad, primalGateGrad, qgtPlus]
    peirce_nf hP
  have hPrimalSq : gp * gp = 0 := by
    rw [← hPrimalCorner]
    peirce_nf hP
  have hDualCorner : (1 - P) * gm * P = gm := by
    dsimp [gm, plusDressedDualGrad, dualGateGrad, backpropMidpoint, qgtMinus]
    peirce_nf hP
  have hDualSq : gm * gm = 0 := by
    rw [← hDualCorner]
    peirce_nf hP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hPrimalCorner
  · exact hPrimalSq
  · change (1 - gp) * (1 + gp) = 1
    calc
      (1 - gp) * (1 + gp) = 1 - gp * gp := by noncomm_ring
      _ = 1 := by rw [hPrimalSq]; simp
  · change (1 - qgtPlus P A C) *
      ((1 + qgtPlus P A C) * primalGateGrad P Xbar Xout) =
        (1 - qgtPlus P A C * qgtPlus P A C) * primalGateGrad P Xbar Xout
    noncomm_ring
  · exact hDualCorner
  · exact hDualSq
  · change (1 - gm) * (1 + gm) = 1
    calc
      (1 - gm) * (1 + gm) = 1 - gm * gm := by noncomm_ring
      _ = 1 := by rw [hDualSq]; simp
  · change (1 - qgtMinus P A C) *
      ((1 + qgtMinus P A C) * dualGateGrad P A Xbar Xout) =
        (1 - qgtMinus P A C * qgtMinus P A C) * dualGateGrad P A Xbar Xout
    noncomm_ring

/-- Trace-adjoint identity for the plus-dressed primal parameter direction. -/
theorem plusDressedPrimal_variation_trace_adjoint
    {P A C dA Xbar Xout : Matrix n n R} (hPstar : star P = P) :
    trace (star Xbar * (conePlus P (star (1 + qgtPlus P A C) * dA) * Xout)) =
      trace (star (plusDressedPrimalGrad P A C Xbar Xout) * dA) := by
  rw [bp3_primalGate_trace_adjoint hPstar]
  dsimp [plusDressedPrimalGrad]
  rw [star_mul, mul_assoc]

/-- Star of the backpropagated cotangent `inputCotangentGrad P A C Xbar`:
`star (inputCotangentGrad P A C Xbar) = star Xbar * attentionGaussianPlus P A C`. -/
theorem inputCotangentGrad_star
    (P A C Xbar : Matrix n n R) :
    star (inputCotangentGrad P A C Xbar) =
      star Xbar * attentionGaussianPlus P A C := by
  dsimp [inputCotangentGrad]
  rw [star_mul, star_star]

/-- **Two-layer zero-activation-memory parameter gradient trace-adjoint split**:
for an outer Operator Gaussian layer `(P₂, A₂, C₂)` and an inner Operator Gaussian
layer `(P₁, A₁, C₁)` with reconstructed intermediate state
`X₁ = backpropInput P₂ A₂ C₂ X₂` and backpropagated cotangent
`Xbar₁ = inputCotangentGrad P₂ A₂ C₂ Xbar₂`, pairing `Xbar₂` with the two-layer
parameter variation splits into the outer layer's primal/dual gate trace adjoints
at `(X₂, Xbar₂)` plus the inner layer's primal/dual gate trace adjoints at
`(X₁, Xbar₁)`. -/
theorem bp3_two_layer_parameter_variation_trace_adjoint
    {P₂ A₂ C₂ dA₂ dC₂ P₁ A₁ C₁ dA₁ dC₁ Xbar₂ X₂ : Matrix n n R}
    (hP₂ : P₂ * P₂ = P₂) (hP₂star : star P₂ = P₂)
    (hP₁ : P₁ * P₁ = P₁) (hP₁star : star P₁ = P₁) :
    let X₁ := backpropInput P₂ A₂ C₂ X₂
    let Xbar₁ := inputCotangentGrad P₂ A₂ C₂ Xbar₂
    trace (star Xbar₂ *
        (attentionGaussianPlusDiff P₂ A₂ C₂ dA₂ dC₂ * X₁ +
          attentionGaussianPlus P₂ A₂ C₂ *
            (attentionGaussianPlusDiff P₁ A₁ C₁ dA₁ dC₁ * backpropInput P₁ A₁ C₁ X₁))) =
      (trace (star (primalGateGrad P₂ Xbar₂ X₂) * dA₂) +
        trace (star (dualGateGrad P₂ A₂ Xbar₂ X₂) * dC₂)) +
      (trace (star (primalGateGrad P₁ Xbar₁ X₁) * dA₁) +
        trace (star (dualGateGrad P₁ A₁ Xbar₁ X₁) * dC₁)) := by
  intro X₁ Xbar₁
  rw [mul_add, Matrix.trace_add]
  rw [bp3_parameter_variation_trace_adjoint hP₂ hP₂star]
  have hInner :
      trace (star Xbar₂ *
          (attentionGaussianPlus P₂ A₂ C₂ *
            (attentionGaussianPlusDiff P₁ A₁ C₁ dA₁ dC₁ * backpropInput P₁ A₁ C₁ X₁))) =
        trace (star Xbar₁ *
          (attentionGaussianPlusDiff P₁ A₁ C₁ dA₁ dC₁ * backpropInput P₁ A₁ C₁ X₁)) := by
    dsimp [Xbar₁]
    rw [inputCotangentGrad_star, mul_assoc]
  rw [hInner, bp3_parameter_variation_trace_adjoint hP₁ hP₁star]

/-! ### Multi-Layer $n$-Stage Reversible Operator Gaussian Tower & Dyck-Tree Cotangent Transport -/

/-- Forward $n$-layer Operator Gaussian tower evaluation on initial state `X₀`
for a list of `(A, C)` parameter pairs. -/
def forwardGaussianTower {B : Type*} [Ring B]
    (P : B) (layers : List (B × B)) (X₀ : B) : B :=
  (layers.map (fun p => attentionGaussianPlus P p.1 p.2)).prod * X₀

/-- Reverse-pass $n$-layer zero-activation-memory state reconstruction from
terminal output `X_out` using the reversed product of polynomial inverses
`attentionGaussianPlusInv`. -/
def backwardGaussianTowerState {B : Type*} [Ring B]
    (P : B) (layers : List (B × B)) (X_out : B) : B :=
  (layers.reverse.map (fun p => attentionGaussianPlusInv P p.1 p.2)).prod * X_out

/-- Multi-layer cotangent backpropagation from terminal cotangent `Xbar_out`. -/
def backwardGaussianTowerCotangent {B : Type*} [Ring B] [StarRing B]
    (P : B) (layers : List (B × B)) (Xbar_out : B) : B :=
  star (layers.map (fun p => attentionGaussianPlus P p.1 p.2)).prod * Xbar_out

/-- Exact $n$-layer zero-activation-memory state reconstruction:
applying `backwardGaussianTowerState` to `forwardGaussianTower P layers X₀`
recovers `X₀` identically for any list of layers and any idempotent `P * P = P`. -/
theorem backwardGaussianTowerState_forwardGaussianTower
    {B : Type*} [Ring B] {P : B} (hP : P * P = P)
    (layers : List (B × B)) (X₀ : B) :
    backwardGaussianTowerState P layers (forwardGaussianTower P layers X₀) = X₀ := by
  dsimp [backwardGaussianTowerState, forwardGaussianTower]
  let pairs : List (B × B) :=
    layers.map (fun p => (attentionGaussianPlus P p.1 p.2, attentionGaussianPlusInv P p.1 p.2))
  have hPairs : ∀ q ∈ pairs, q.1 * q.2 = 1 ∧ q.2 * q.1 = 1 := by
    intro q hq
    rcases List.mem_map.mp hq with ⟨⟨A, C⟩, _, rfl⟩
    have hLayer := stage_TN2_TN3_dually_flat_unipotent_gates_and_reversible_gaussian_layer
      hP A A C C A C
    exact ⟨hLayer.2.2.2.2.1, hLayer.2.2.2.2.2.1⟩
  have hInv := (list_prod_mul_reverse_inv_prod pairs hPairs).2
  have hMapFst :
      pairs.map Prod.fst = layers.map (fun p => attentionGaussianPlus P p.1 p.2) := by
    simp [pairs, List.map_map]
  have hMapSnd :
      pairs.reverse.map Prod.snd =
        layers.reverse.map (fun p => attentionGaussianPlusInv P p.1 p.2) := by
    simp [pairs, List.map_reverse, List.map_map]
  rw [← hMapFst, ← hMapSnd, ← mul_assoc, hInv, one_mul]

/-- Multi-layer cotangent trace-adjoint law: pairing `Xbar_out` with a forward
tower perturbation `forwardGaussianTower P layers dX₀` equals pairing `dX₀`
with `backwardGaussianTowerCotangent P layers Xbar_out`. -/
theorem trace_backwardGaussianTowerCotangent_adjoint
    (P : Matrix n n R) (layers : List (Matrix n n R × Matrix n n R))
    (Xbar_out dX₀ : Matrix n n R) :
    trace (star Xbar_out * forwardGaussianTower P layers dX₀) =
      trace (star (backwardGaussianTowerCotangent P layers Xbar_out) * dX₀) := by
  dsimp [forwardGaussianTower, backwardGaussianTowerCotangent]
  rw [star_mul, star_star, mul_assoc]

/-- A finite matrix layer together with its two parameter variations.  This
formalization uses one fixed Peirce idempotent for the whole list of layers. -/
abbrev GaussianLayerVariation (R n : Type*) :=
  Matrix n n R × Matrix n n R × Matrix n n R × Matrix n n R

private def layerVariationA {R n : Type*} (ℓ : GaussianLayerVariation R n) : Matrix n n R := ℓ.1
private def layerVariationC {R n : Type*} (ℓ : GaussianLayerVariation R n) : Matrix n n R := ℓ.2.1
private def layerVariationDA {R n : Type*} (ℓ : GaussianLayerVariation R n) : Matrix n n R := ℓ.2.2.1
private def layerVariationDC {R n : Type*} (ℓ : GaussianLayerVariation R n) : Matrix n n R := ℓ.2.2.2

/-- The parameter pairs underlying an ordered list of matrix layers. -/
def gaussianLayerParameters {R n : Type*}
    (layers : List (GaussianLayerVariation R n)) : List (Matrix n n R × Matrix n n R) :=
  layers.map fun ℓ => (layerVariationA ℓ, layerVariationC ℓ)

/-- Product-rule tangent of a finite ordered Gaussian layer list.  The head
layer multiplies the suffix product on the left, matching
`forwardGaussianTower`. -/
def gaussianTowerParameterVariation {R n : Type*} [CommRing R] [StarRing R]
    [Fintype n] [DecidableEq n] (P : Matrix n n R) :
    List (GaussianLayerVariation R n) → Matrix n n R → Matrix n n R
  | [], _ => 0
  | ℓ :: rest, X₀ =>
      attentionGaussianPlusDiff P (layerVariationA ℓ) (layerVariationC ℓ)
        (layerVariationDA ℓ) (layerVariationDC ℓ) *
          forwardGaussianTower P (gaussianLayerParameters rest) X₀ +
      attentionGaussianPlus P (layerVariationA ℓ) (layerVariationC ℓ) *
        gaussianTowerParameterVariation P rest X₀

/-- Trace pairing of the list tangent with the sum of local primal and dual
parameter gradients.  Each local gradient is evaluated at that layer's output
`G_head * suffixState`; the suffix state itself is obtained by evaluating the
remaining layers.  Cotangents are transported through each head layer. -/
def gaussianTowerParameterGradientTrace {R n : Type*} [CommRing R] [StarRing R]
    [Fintype n] [DecidableEq n] (P : Matrix n n R) :
    List (GaussianLayerVariation R n) → Matrix n n R → Matrix n n R → R
  | [], _, _ => 0
  | ℓ :: rest, Xbar, X₀ =>
      let Xsuffix := forwardGaussianTower P (gaussianLayerParameters rest) X₀
      let Xhead := attentionGaussianPlus P (layerVariationA ℓ) (layerVariationC ℓ) * Xsuffix
      (trace (star (primalGateGrad P Xbar Xhead) * layerVariationDA ℓ) +
        trace (star (dualGateGrad P (layerVariationA ℓ) Xbar Xhead) * layerVariationDC ℓ)) +
      gaussianTowerParameterGradientTrace P rest
        (inputCotangentGrad P (layerVariationA ℓ) (layerVariationC ℓ) Xbar) X₀

/-- Arbitrary finite-depth parameter-variation trace-adjoint identity for a
list of matrix Gaussian layers sharing one self-adjoint idempotent `P`.  It is
an algebraic trace identity for the explicitly defined product-rule tangent;
it does not assert differentiability or an asymptotic memory bound. -/
theorem gaussianTower_parameter_variation_trace_adjoint
    {P : Matrix n n R} (hP : P * P = P) (hPstar : star P = P)
    (layers : List (GaussianLayerVariation R n)) (Xbar X₀ : Matrix n n R) :
    trace (star Xbar * gaussianTowerParameterVariation P layers X₀) =
      gaussianTowerParameterGradientTrace P layers Xbar X₀ := by
  induction layers generalizing Xbar X₀ with
  | nil => simp [gaussianTowerParameterVariation, gaussianTowerParameterGradientTrace]
  | cons ℓ rest ih =>
      rw [gaussianTowerParameterVariation, mul_add, Matrix.trace_add]
      let Xsuffix := forwardGaussianTower P (gaussianLayerParameters rest) X₀
      let Xhead := attentionGaussianPlus P (layerVariationA ℓ) (layerVariationC ℓ) * Xsuffix
      have hHead := bp3_parameter_variation_trace_adjoint
        hP hPstar (P := P) (A := layerVariationA ℓ) (C := layerVariationC ℓ)
        (dA := layerVariationDA ℓ) (dC := layerVariationDC ℓ) (Xbar := Xbar)
        (Xout := Xhead)
      have hBack : backpropInput P (layerVariationA ℓ) (layerVariationC ℓ) Xhead = Xsuffix := by
        dsimp [Xhead, Xsuffix]
        exact (stage_BP3_zero_memory_backward_pass_and_nilpotent_gradient_contractions
          hP (layerVariationA ℓ) (layerVariationDA ℓ)
          (layerVariationC ℓ) (layerVariationDC ℓ) Xsuffix
          (attentionGaussianPlus P (layerVariationA ℓ) (layerVariationC ℓ) * Xsuffix)
          0 0).2.1
      rw [hBack] at hHead
      rw [hHead]
      have hTail :
          trace (star Xbar *
              (attentionGaussianPlus P (layerVariationA ℓ) (layerVariationC ℓ) *
                gaussianTowerParameterVariation P rest X₀)) =
            trace (star (inputCotangentGrad P (layerVariationA ℓ)
                (layerVariationC ℓ) Xbar) * gaussianTowerParameterVariation P rest X₀) := by
        dsimp [inputCotangentGrad]
        rw [star_mul, star_star, mul_assoc]
      rw [hTail, ih (inputCotangentGrad P (layerVariationA ℓ)
        (layerVariationC ℓ) Xbar) X₀]
      rfl

/-- Zero-gradient-attenuation cotangent transport across any well-bracketed
`CPTDyckParseTree.DyckTree`: the adjoint of a balanced Peirce-shear parse tree
leaves every cotangent matrix `Xbar` strictly invariant (`= Xbar`). -/
theorem dyckTree_cotangent_transport_invariant
    {Label : Type*} {B : Type*} [Ring B] [StarRing B]
    {P : B} (hP : P * P = P) (param : Label → B)
    (tree : DyckTree Label) (Xbar : B) :
    star (DyckTree.eval
      (fun label => peirceOpen P (param label))
      (fun label => peirceClose P (param label)) tree) * Xbar = Xbar := by
  rw [peirce_tree_eval_eq_one hP param tree, star_one, one_mul]

end InfoGeometry.Canonical.PeirceBackpropTraceGradientBridge
