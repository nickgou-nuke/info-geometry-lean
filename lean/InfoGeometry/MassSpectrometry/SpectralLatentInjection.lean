import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.LLM.SpectralToken
import InfoGeometry.LLM.TransformerArchitecture
import InfoGeometry.MassSpectrometry.CausalTransferArchitecture
import InfoGeometry.MassSpectrometry.FiniteFragmentationModel
import InfoGeometry.MassSpectrometry.VerifiedInferenceArchitecture

/-!
# Spectral latent injection into the repository Transformer backbone

This module formalizes the theorem-safe content of a multimodal spectroscopy
adapter.  It does not claim that a language model "understands" chemistry, nor
that molecular reconstruction is globally invertible.

The bridge has three levels:

* the causal transfer and its certified Moore--Penrose reverse map are packaged
  in the repository-owned primal/dual `SpectralToken` carrier;
* a spectral embedding is added directly to an existing residual state and then
  passed through the repository-owned `runDecoderStack`;
* lossless spectral decoding is available only when an explicit
  `Function.LeftInverse` certificate is supplied.

The chemical output modality is intentionally abstract.  Molecular graphs,
SMILES equivalence, IUPAC naming, and conformers require separate theorem
owners before they can be stated as invariant decoding theorems.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open InfoGeometry.LLM

/-! ## Causal forward/reverse token -/

/-- Primal/dual token associated with a certified causal transfer system.
The primal lane is the forward causal transfer and the dual lane is its
certified Moore--Penrose reverse matrix. -/
def causalTransferToken {n d q : ℕ} (S : CausalTransferSystem n d q) :
    SpectralToken.SpectralToken (AssignmentMatrix n) :=
  forwardReverseToken S.transfer S.retraction.pinv

@[simp] theorem causalTransferToken_primal {n d q : ℕ}
    (S : CausalTransferSystem n d q) :
    (causalTransferToken S).primal = S.transfer :=
  rfl

@[simp] theorem causalTransferToken_dual {n d q : ℕ}
    (S : CausalTransferSystem n d q) :
    (causalTransferToken S).dual = S.retraction.pinv :=
  rfl

@[simp] theorem causalTransferToken_swap {n d q : ℕ}
    (S : CausalTransferSystem n d q) :
    SpectralToken.SpectralToken.swap (causalTransferToken S) =
      forwardReverseToken S.retraction.pinv S.transfer := by
  rfl

/-! ## Residual-stream injection -/

/-- Generic theorem-facing spectral encoder into an LLM residual carrier. -/
structure SpectralResidualEncoder (Spec V : Type*) where
  encode : Spec → V

namespace SpectralResidualEncoder

variable {Spec V : Type*} [AddCommMonoid V]

/-- Add a spectral embedding to an already-existing residual state. -/
def inject (E : SpectralResidualEncoder Spec V) (base : V) (s : Spec) : V :=
  base + E.encode s

@[simp] theorem inject_eq (E : SpectralResidualEncoder Spec V)
    (base : V) (s : Spec) :
    E.inject base s = base + E.encode s :=
  rfl

/-- Spectral injection into the zero residual state is exactly the embedding. -/
@[simp] theorem inject_zero (E : SpectralResidualEncoder Spec V) (s : Spec) :
    E.inject 0 s = E.encode s := by
  simp [inject]

/-- Two independent residual injections associate in the native additive
residual carrier. -/
theorem inject_additive_association
    (E₁ E₂ : SpectralResidualEncoder Spec V)
    (base : V) (s₁ s₂ : Spec) :
    E₂.inject (E₁.inject base s₁) s₂ =
      base + (E₁.encode s₁ + E₂.encode s₂) := by
  simp [inject, add_assoc]

/-- Run the repository-owned decoder stack after direct spectral residual
injection. -/
def runInjected
    (E : SpectralResidualEncoder Spec V)
    (layers : List (DecoderLayer V)) (base : V) (s : Spec) : V :=
  runDecoderStack layers (E.inject base s)

@[simp] theorem runInjected_nil
    (E : SpectralResidualEncoder Spec V) (base : V) (s : Spec) :
    E.runInjected [] base s = E.inject base s := by
  rfl

/-- Decoder-stack append law is inherited unchanged after spectral injection. -/
theorem runInjected_append
    (E : SpectralResidualEncoder Spec V)
    (L₁ L₂ : List (DecoderLayer V)) (base : V) (s : Spec) :
    E.runInjected (L₁ ++ L₂) base s =
      runDecoderStack L₂ (E.runInjected L₁ base s) := by
  exact runDecoderStack_append L₁ L₂ (E.inject base s)

end SpectralResidualEncoder

/-! ## Direct Transformer-backbone adapter -/

/-- A spectral embedding can be used directly as the token embedding of the
repository's `TransformerBackbone`. -/
def spectralTransformerBackbone
    {Spec V : Type*} [AddCommMonoid V]
    (E : SpectralResidualEncoder Spec V)
    (layers : List (DecoderLayer V)) (finalNorm : V → V) :
    TransformerBackbone Spec V where
  tokenEmbedding := E.encode
  layers := layers
  finalNorm := finalNorm

@[simp] theorem spectralTransformerBackbone_hiddenState
    {Spec V : Type*} [AddCommMonoid V]
    (E : SpectralResidualEncoder Spec V)
    (layers : List (DecoderLayer V)) (finalNorm : V → V) (s : Spec) :
    (spectralTransformerBackbone E layers finalNorm).hiddenState s =
      runDecoderStack layers (E.encode s) := by
  rfl

/-! ## Certified physical-model embeddings -/

/-- Any latent embedding of a `FiniteValuedFragmentationModel` receives a
structurally admissible input by construction.  The theorem is independent of
how the latent vector itself is computed. -/
theorem physicalModel_input_structurallyAdmissible
    {n : ℕ}
    (M : FiniteValuedFragmentationModel n) :
    IsStructurallyAdmissible M := by
  exact finiteValuedFragmentationModel_structurallyAdmissible M

/-! ## Optional lossless encoding -/

/-- A spectral encoder is lossless only when an explicit decoder is supplied
with a left-inverse proof.  This is intentionally stronger than the generic
spectral residual encoder. -/
structure LosslessSpectralEncoder (Spec V : Type*) extends
    SpectralResidualEncoder Spec V where
  decode : V → Spec
  decode_encode : Function.LeftInverse decode encode

namespace LosslessSpectralEncoder

variable {Spec V : Type*}

/-- A certified lossless spectral embedding is injective. -/
theorem encode_injective (E : LosslessSpectralEncoder Spec V) :
    Function.Injective E.encode :=
  E.decode_encode.injective

/-- Exact latent-to-spectrum round trip follows from the explicit certificate. -/
@[simp] theorem decode_encode_apply (E : LosslessSpectralEncoder Spec V)
    (s : Spec) :
    E.decode (E.encode s) = s :=
  E.decode_encode s

end LosslessSpectralEncoder

/-! ## Abstract multimodal decoder contracts -/

/-- A downstream readout from a latent state.  The output type is abstract on
purpose: chemical graph owners can later instantiate it without changing the
spectral injection mathematics. -/
structure LatentReadout (V Output : Type*) where
  decode : V → Output

namespace LatentReadout

variable {V Output : Type*}

@[simp] theorem decode_apply (R : LatentReadout V Output) (v : V) :
    R.decode v = R.decode v :=
  rfl

end LatentReadout

/-- Spectral encoder + Transformer backbone + arbitrary theorem-facing output
readout.  No semantic correctness of the output is asserted by this structure. -/
structure SpectralReasoningPipeline
    (Spec V Output : Type*) [AddCommMonoid V] where
  encoder : SpectralResidualEncoder Spec V
  layers : List (DecoderLayer V)
  finalNorm : V → V
  readout : LatentReadout V Output

namespace SpectralReasoningPipeline

variable {Spec V Output : Type*} [AddCommMonoid V]

/-- Latent state produced by the repository's decoder stack. -/
def hiddenState (P : SpectralReasoningPipeline Spec V Output) (s : Spec) : V :=
  runDecoderStack P.layers (P.encoder.encode s)

/-- Normalized latent state before the downstream readout. -/
def normalizedState (P : SpectralReasoningPipeline Spec V Output) (s : Spec) : V :=
  P.finalNorm (P.hiddenState s)

/-- End-to-end theorem-facing readout. -/
def output (P : SpectralReasoningPipeline Spec V Output) (s : Spec) : Output :=
  P.readout.decode (P.normalizedState s)

/-- The pipeline is definitionally the repository decoder stack followed by
normalization and the chosen output readout. -/
theorem output_def (P : SpectralReasoningPipeline Spec V Output) (s : Spec) :
    P.output s =
      P.readout.decode
        (P.finalNorm (runDecoderStack P.layers (P.encoder.encode s))) := by
  rfl

end SpectralReasoningPipeline

end InfoGeometry.MassSpectrometry
