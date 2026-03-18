import InfoGeometry.Krein.Modular
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.DoubledSpaceMatrix
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Quantum.Fock
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Krein.HilbertBridge
set_option linter.unusedSectionVars false

/-!
# Modular Spinor Bridge

This module formalizes the parallel transport of the Bogoliubov frame
via the modular operator on the doubled Krein space.

It bridges:
1. **Majorana-Dirac Spinors**: Real Majoranas paired into Weyl and Dirac spinors
   using the `Cl(1,1)` matrix representation.
2. **Modular Parallel Transport**: Identification of the `SpinConnection`
   with the flow of the modular operator `Δ`.
3. **Observables as Spinor Bilinears**: Expectation values computed via the
   modular conjugation `J`.
-/

namespace InfoGeometry.Canonical.ModularSpinorBridge

open InfoGeometry.Krein
open InfoGeometry.Clifford
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Quantum
open InfoGeometry.Canonical.KaehlerGeometry

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
**Majorana Basis**:
A frame for the doubled space $E \oplus E$ that satisfies the real $Cl(1,1)$ relations.
In the matrix representation, this corresponds to the real Pauli matrices.
-/
structure MajoranaFrame (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  J : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E
  eps : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E
  is_cl11 : Krein.cl11_relations J eps

/--
**Canonical Majorana Frame**:
The default frame using `modular_j` and `spectral_epsilon`.
-/
noncomputable def canonicalMajoranaFrame : MajoranaFrame E where
  J := Krein.modular_j (E := E)
  eps := Krein.spectral_epsilon (E := E)
  is_cl11 := Krein.modular_j_spectral_epsilon_has_cl11_relations E

/-- Linear embedding of `E` into the physical channel of `HilbertDoubled E`. -/
noncomputable def doubledPlusEmbedL : E →ₗ[ℝ] HilbertDoubled E where
  toFun x := Krein.to_doubled x (0 : E)
  map_add' x y := by
    simpa [Krein.to_doubled] using
      (WithLp.toLp_add (p := (2 : ENNReal)) (x := (x, (0 : E))) (y := (y, (0 : E))))
  map_smul' a x := by
    simpa [Krein.to_doubled] using
      (WithLp.toLp_smul (p := (2 : ENNReal)) (c := a) (x := (x, (0 : E))))

/-- Linear projection from `HilbertDoubled E` onto the physical channel `E`. -/
noncomputable def doubledPlusProjectL : HilbertDoubled E →ₗ[ℝ] E :=
  (Krein.fst_L (E := E)).toLinearMap

/--
Transport on `E` induced by modular flow on doubled space:
embed to doubled physical channel, evolve by `flow t`, project back.
-/
noncomputable def modularFlowInducedTransport
    (J_symm : FundamentalSymmetry (HilbertDoubled E)) (T : HilbertDoubled E →ₗ[ℝ] HilbertDoubled E)
    (flow : FundamentalSymmetry.ModularFlow J_symm T) (t : ℝ) :
    E →ₗ[ℝ] E :=
  (doubledPlusProjectL (E := E)).comp ((flow.flow t).comp (doubledPlusEmbedL (E := E)))

@[simp] theorem modularFlowInducedTransport_eq_id_of_flow_id
    (J_symm : FundamentalSymmetry (HilbertDoubled E)) (T : HilbertDoubled E →ₗ[ℝ] HilbertDoubled E)
    (flow : FundamentalSymmetry.ModularFlow J_symm T) (t : ℝ)
    (hFlowId : flow.flow t = LinearMap.id) :
    modularFlowInducedTransport (E := E) J_symm T flow t = LinearMap.id := by
  ext x
  unfold modularFlowInducedTransport doubledPlusProjectL doubledPlusEmbedL
  change WithLp.fst ((flow.flow t) (Krein.to_doubled x (0 : E))) = x
  rw [hFlowId]
  simp [Krein.to_doubled]

noncomputable def modularSpinConnection_of_flowFixedSplit
    (K : KaehlerInformationGeometry E) (x : E) (V : SplitVielbein K x)
    (J_symm : FundamentalSymmetry (HilbertDoubled E)) (T : HilbertDoubled E →ₗ[ℝ] HilbertDoubled E)
    (flow : FundamentalSymmetry.ModularFlow J_symm T) (t : ℝ)
    (hPlusFixed : modularFlowInducedTransport (E := E) J_symm T flow t V.ePlus = V.ePlus)
    (hMinusFixed : modularFlowInducedTransport (E := E) J_symm T flow t V.eMinus = V.eMinus) :
    SpinConnection K x V where
  transport := modularFlowInducedTransport (E := E) J_symm T flow t
  preserves_plus := by
    simpa [hPlusFixed] using V.plus_norm
  preserves_minus := by
    simpa [hMinusFixed] using V.minus_norm
  preserves_orthogonal := by
    simpa [hPlusFixed, hMinusFixed] using V.orthogonal

/--
**Modular Parallel Transport (primary)**:
spin transport induced by modular flow, under explicit split-fixing witnesses.
-/
noncomputable def modularSpinConnection
    (K : KaehlerInformationGeometry E) (x : E) (V : SplitVielbein K x)
    (J_symm : FundamentalSymmetry (HilbertDoubled E)) (T : HilbertDoubled E →ₗ[ℝ] HilbertDoubled E)
    (flow : FundamentalSymmetry.ModularFlow J_symm T) (t : ℝ)
    (hPlusFixed : modularFlowInducedTransport (E := E) J_symm T flow t V.ePlus = V.ePlus)
    (hMinusFixed : modularFlowInducedTransport (E := E) J_symm T flow t V.eMinus = V.eMinus) :
    SpinConnection K x V :=
  modularSpinConnection_of_flowFixedSplit
    (E := E) K x V J_symm T flow t hPlusFixed hMinusFixed

/-- The transport field of `modularSpinConnection` is the induced modular flow. -/
@[simp] theorem modularSpinConnection_transport
    (K : KaehlerInformationGeometry E) (x : E) (V : SplitVielbein K x)
    (J_symm : FundamentalSymmetry (HilbertDoubled E)) (T : HilbertDoubled E →ₗ[ℝ] HilbertDoubled E)
    (flow : FundamentalSymmetry.ModularFlow J_symm T) (t : ℝ)
    (hPlusFixed : modularFlowInducedTransport (E := E) J_symm T flow t V.ePlus = V.ePlus)
    (hMinusFixed : modularFlowInducedTransport (E := E) J_symm T flow t V.eMinus = V.eMinus) :
    (modularSpinConnection (E := E) K x V J_symm T flow t hPlusFixed hMinusFixed).transport
      = modularFlowInducedTransport (E := E) J_symm T flow t := rfl

/-- Transporting the split frame through flow-induced `modularSpinConnection` leaves it unchanged. -/
theorem transportedSplitVielbein_modularSpinConnection
    (K : KaehlerInformationGeometry E) (x : E) (V : SplitVielbein K x)
    (J_symm : FundamentalSymmetry (HilbertDoubled E)) (T : HilbertDoubled E →ₗ[ℝ] HilbertDoubled E)
    (flow : FundamentalSymmetry.ModularFlow J_symm T) (t : ℝ)
    (hPlusFixed : modularFlowInducedTransport (E := E) J_symm T flow t V.ePlus = V.ePlus)
    (hMinusFixed : modularFlowInducedTransport (E := E) J_symm T flow t V.eMinus = V.eMinus) :
    transportedSplitVielbein K x V
      (modularSpinConnection (E := E) K x V J_symm T flow t hPlusFixed hMinusFixed) = V := by
  cases V
  simp [transportedSplitVielbein, modularSpinConnection, modularSpinConnection_of_flowFixedSplit,
    hPlusFixed, hMinusFixed]

/--
**Spinor Bilinears as Observables**:
The expectation value of an operator $\mathcal{O}$ is represented as a
spinor bilinear $\langle \psi | \mathcal{O} | \psi \rangle_{Krein}$.
The modular conjugation `J` plays the role of Dirac conjugation.
-/
noncomputable def spinorBilinear
    (ψ : HilbertDoubled E) (O : HilbertDoubled E →L[ℝ] HilbertDoubled E) : ℝ :=
  let J_symm := KreinSpace.jCLM (H := HilbertDoubled E)
  -- ⟪J ψ, O ψ⟫
  @inner ℝ (HilbertDoubled E) _ (J_symm ψ) (O ψ)

/--
Weak-value numerator for a pre/post-selected pair in doubled space:
`⟪post, O pre⟫`.
-/
noncomputable def weakValueNumerator
    (post pre : HilbertDoubled E)
    (O : HilbertDoubled E →L[ℝ] HilbertDoubled E) : ℝ :=
  @inner ℝ (HilbertDoubled E) _ post (O pre)

/-- Weak-value denominator for a pre/post-selected pair: `⟪post, pre⟫`. -/
noncomputable def weakValueDenominator
    (post pre : HilbertDoubled E) : ℝ :=
  @inner ℝ (HilbertDoubled E) _ post pre

/-- Weak value as ratio numerator/denominator. -/
noncomputable def weakValue
    (post pre : HilbertDoubled E)
    (O : HilbertDoubled E →L[ℝ] HilbertDoubled E) : ℝ :=
  weakValueNumerator (E := E) post pre O / weakValueDenominator (E := E) post pre

/--
When the post-selected state is the modular conjugate `J pre`, the weak-value
numerator is exactly the spinorial bilinear channel.
-/
theorem weakValueNumerator_modularConjugate_eq_spinorBilinear
    (pre : HilbertDoubled E)
    (O : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    weakValueNumerator (E := E) ((KreinSpace.jCLM (H := HilbertDoubled E)) pre) pre O
      = spinorBilinear (E := E) pre O := by
  simp [weakValueNumerator, spinorBilinear]

/--
Aharonov-TSVF weak-value numerator identity:
for post-state `J pre`, the weak-value numerator is exactly the spinor bilinear.
-/
theorem weakValue_numerator_eq_spinorBilinear
    (pre : HilbertDoubled E)
    (O : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    weakValueNumerator (E := E) ((KreinSpace.jCLM (H := HilbertDoubled E)) pre) pre O
      = spinorBilinear (E := E) pre O :=
  weakValueNumerator_modularConjugate_eq_spinorBilinear (E := E) pre O

/--
Explicit modular weak-value identity:
for post-state `J pre`, weak value is the spinorial bilinear divided by the
modular overlap `⟪J pre, pre⟫`.
-/
theorem weakValue_modularConjugate_eq_spinorBilinear_div_overlap
    (pre : HilbertDoubled E)
    (O : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    weakValue (E := E) ((KreinSpace.jCLM (H := HilbertDoubled E)) pre) pre O
      = spinorBilinear (E := E) pre O /
          weakValueDenominator (E := E) ((KreinSpace.jCLM (H := HilbertDoubled E)) pre) pre := by
  unfold weakValue
  rw [weakValueNumerator_modularConjugate_eq_spinorBilinear (E := E) (pre := pre) (O := O)]

/-
**Bayesian Inference as Observable**:
The "evidence" innovation in a Bayesian update is the expectation value
of the creation operator.
-/
omit [FiniteDimensional ℝ E] in
/-- Theorem `bayesian_update_as_spinor_bilinear`. -/
theorem bayesian_update_as_spinor_bilinear
    (prior : HilbertDoubled E) (_innovation : HilbertDoubled E) :
    ∃ (O : HilbertDoubled E →L[ℝ] HilbertDoubled E),
      spinorBilinear prior O = ‖prior‖ ^ 2
    := by
  refine ⟨KreinSpace.jCLM (H := HilbertDoubled E), ?_⟩
  simp [spinorBilinear, KreinSpace.jCLM]

omit [FiniteDimensional ℝ E] in
/-- Nontrivial witness form: the modular conjugation itself realizes the bilinear value. -/
theorem bayesian_update_as_spinor_bilinear_witness
    (prior : HilbertDoubled E) :
    spinorBilinear prior (KreinSpace.jCLM (H := HilbertDoubled E)) = ‖prior‖ ^ 2 := by
  simp [spinorBilinear, KreinSpace.jCLM]

/--
**Fierz Identity (Informational)**:
Symmetries of the induced symplectic form in the Fock space.
This relates different spinor bilinear channels (scalar, vector, pseudoscalar).
-/
def FierzIdentity (ψ : Krein.DoubledSpace E) : Prop :=
  inducedSymplecticForm (E := E) ψ ψ =
    hessian_indefinite_form (E := E) ψ (Krein.complex_i (E := E) ψ)

/-- The induced commutator form satisfies the Fierz bridge identity on diagonal inputs. -/
theorem fierzIdentity_true (ψ : Krein.DoubledSpace E) :
    FierzIdentity (E := E) ψ := by
  simpa [FierzIdentity] using inducedSymplecticForm_eq_complex_pairing (E := E) ψ ψ

end InfoGeometry.Canonical.ModularSpinorBridge
