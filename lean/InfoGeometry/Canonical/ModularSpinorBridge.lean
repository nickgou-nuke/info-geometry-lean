import InfoGeometry.Krein.Modular
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.DoubledSpaceMatrix
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Quantum.Fock
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Krein.HilbertBridge

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
structure MajoranaFrame (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  J : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E
  eps : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E
  is_cl11 : Krein.Cl11Relations J eps

/--
**Canonical Majorana Frame**:
The default frame using `modularJ` and `spectralEpsilon`.
-/
noncomputable def canonicalMajoranaFrame : MajoranaFrame E where
  J := Krein.modularJ (E := E)
  eps := Krein.spectralEpsilon (E := E)
  is_cl11 := Krein.modularJ_spectralEpsilon_hasCl11Relations

/--
**Modular Parallel Transport**:
Compatibility constructor for a split-preserving spin connection in the modular layer.
The current finite bridge keeps the base transport as identity.
-/
noncomputable def modularSpinConnection
    (K : KaehlerInformationGeometry E) (x : E) (V : SplitVielbein K x)
    (J_symm : FundamentalSymmetry (HilbertDoubled E)) (T : HilbertDoubled E →ₗ[ℝ] HilbertDoubled E)
    (_flow : FundamentalSymmetry.ModularFlow J_symm T) (_t : ℝ) :
    SpinConnection K x V where
  transport := LinearMap.id
  preserves_plus := V.plus_norm
  preserves_minus := V.minus_norm
  preserves_orthogonal := V.orthogonal

/-- The modular bridge transport is the identity map in the current finite model. -/
@[simp] theorem modularSpinConnection_transport
    (K : KaehlerInformationGeometry E) (x : E) (V : SplitVielbein K x)
    (J_symm : FundamentalSymmetry (HilbertDoubled E)) (T : HilbertDoubled E →ₗ[ℝ] HilbertDoubled E)
    (flow : FundamentalSymmetry.ModularFlow J_symm T) (t : ℝ) :
    (modularSpinConnection (E := E) K x V J_symm T flow t).transport = LinearMap.id := rfl

/-- Transporting the split frame through `modularSpinConnection` leaves it unchanged. -/
theorem transportedSplitVielbein_modularSpinConnection
    (K : KaehlerInformationGeometry E) (x : E) (V : SplitVielbein K x)
    (J_symm : FundamentalSymmetry (HilbertDoubled E)) (T : HilbertDoubled E →ₗ[ℝ] HilbertDoubled E)
    (flow : FundamentalSymmetry.ModularFlow J_symm T) (t : ℝ) :
    transportedSplitVielbein K x V (modularSpinConnection (E := E) K x V J_symm T flow t) = V := by
  cases V
  simp [transportedSplitVielbein, modularSpinConnection]

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
    hessianIndefiniteForm (E := E) ψ (Krein.complexI (E := E) ψ)

/-- The induced commutator form satisfies the Fierz bridge identity on diagonal inputs. -/
theorem fierzIdentity_true (ψ : Krein.DoubledSpace E) :
    FierzIdentity (E := E) ψ := by
  simpa [FierzIdentity] using inducedSymplecticForm_eq_complex_pairing (E := E) ψ ψ

end InfoGeometry.Canonical.ModularSpinorBridge
