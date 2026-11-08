import InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.B3RepresentationBridge
import InfoGeometry.Physics.YangBaxterQSwap
import InfoGeometry.Physics.BraidIdealDescent


/-!
# Bogoliubov q-clock to explicit B₃/Yang--Baxter braid graph

This module replaces the remaining informal braid connection by explicit finite
lemmas:

* color triplet + singlet spinors carry a concrete q-scaled color braid action;
* the two adjacent color transpositions satisfy the Artin `B₃` relation after
  multiplying by the Bogoliubov q-clock;
* the same scalar is the `q` in the existing Yang--Baxter q-swap spine;
* the same scalar is the coefficient of the existing tensor `qCrossMap` used in
  braid-ideal descent.
-/

noncomputable section

namespace BogoliubovBraidGraphWeld

open InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain
open InfoGeometry.Physics.BogoliubovSU3ParafermionWeld
open InfoGeometry.Physics.BogoliubovWeylChemicalPotential
open InfoGeometry.Physics.SupergradedCuntzBdG
open InfoGeometry.Physics

/-- Permute the color triplet of a four-component spinor and leave the singlet
component fixed. -/
def permuteColorSpinor4 {V : Type*} (π : Equiv.Perm (Fin 3))
    (ψ : ColorSpinor4 V) : ColorSpinor4 V :=
  (fun i => ψ.1 (π i), ψ.2)

/-- q-scaled adjacent braid action on the color triplet/singlet spinor. -/
def qColorBraid4 {V : Type*} [SMul ℂ V] (q : ℂ) (π : Equiv.Perm (Fin 3))
    (ψ : ColorSpinor4 V) : ColorSpinor4 V :=
  q • permuteColorSpinor4 π ψ

/-- The first adjacent braid generator: color slots `0 ↔ 1`. -/
def qColorSigma0 {V : Type*} [SMul ℂ V] (q : ℂ) (ψ : ColorSpinor4 V) : ColorSpinor4 V :=
  qColorBraid4 q (Equiv.swap 0 1) ψ

/-- The second adjacent braid generator: color slots `1 ↔ 2`. -/
def qColorSigma1 {V : Type*} [SMul ℂ V] (q : ℂ) (ψ : ColorSpinor4 V) : ColorSpinor4 V :=
  qColorBraid4 q (Equiv.swap 1 2) ψ

/-- Permuting twice is the action of the product permutation. -/
@[simp] theorem permuteColorSpinor4_mul {V : Type*} (π ρ : Equiv.Perm (Fin 3))
    (ψ : ColorSpinor4 V) :
    permuteColorSpinor4 π (permuteColorSpinor4 ρ ψ) =
      permuteColorSpinor4 (ρ * π) ψ := rfl

/-- Color permutation commutes with scalar multiplication. -/
@[simp] theorem permuteColorSpinor4_smul {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (q : ℂ) (π : Equiv.Perm (Fin 3)) (ψ : ColorSpinor4 V) :
    permuteColorSpinor4 π (q • ψ) = q • permuteColorSpinor4 π ψ := rfl

/-- The q-scaled color adjacent generators satisfy the Artin braid relation on
four-component spinors.  The proof is inherited from the group relation of the
underlying adjacent transpositions, rather than checked component by component. -/
theorem qColorBraid4_artin {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (q : ℂ) (ψ : ColorSpinor4 V) :
    qColorSigma0 q (qColorSigma1 q (qColorSigma0 q ψ)) =
      qColorSigma1 q (qColorSigma0 q (qColorSigma1 q ψ)) := by
  have hArtin :
      (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) * Equiv.swap 0 1 =
        (Equiv.swap 1 2 * Equiv.swap 0 1) * Equiv.swap 1 2 := by
    decide
  simp only [qColorSigma0, qColorSigma1, qColorBraid4,
    permuteColorSpinor4_smul, permuteColorSpinor4_mul, smul_smul]
  rw [hArtin]

/-- The Bogoliubov frame q-clock supplies the q-scaled color braid phase. -/
def frameColorSigma0 {V : Type*} [SMul ℂ V]
    (F : BogoliubovInertialFrame) (ψ : ColorSpinor4 V) : ColorSpinor4 V :=
  qColorSigma0 (frameBraidingPhase F) ψ

/-- The Bogoliubov frame q-clock supplies the second q-scaled color braid phase. -/
def frameColorSigma1 {V : Type*} [SMul ℂ V]
    (F : BogoliubovInertialFrame) (ψ : ColorSpinor4 V) : ColorSpinor4 V :=
  qColorSigma1 (frameBraidingPhase F) ψ

/-- Bogoliubov q-clocked color braids satisfy the Artin relation. -/
theorem frameColorBraid_artin {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (F : BogoliubovInertialFrame) (ψ : ColorSpinor4 V) :
    frameColorSigma0 F (frameColorSigma1 F (frameColorSigma0 F ψ)) =
      frameColorSigma1 F (frameColorSigma0 F (frameColorSigma1 F ψ)) := by
  exact qColorBraid4_artin (frameBraidingPhase F) ψ

/-- The existing `S₃` braid representation has the same adjacent transposition
skeleton as the q-scaled color-braid action. -/
theorem color_braid_underlying_s3_artin :
    B3RepresentationBridge.s3_rep.σ0 * B3RepresentationBridge.s3_rep.σ1 *
      B3RepresentationBridge.s3_rep.σ0 =
    B3RepresentationBridge.s3_rep.σ1 * B3RepresentationBridge.s3_rep.σ0 *
      B3RepresentationBridge.s3_rep.σ1 :=
  B3RepresentationBridge.s3_rep.artin

/-- The same Bogoliubov phase feeds the existing explicit 8×8 Yang--Baxter
q-swap relation. -/
theorem frame_yang_baxter_qswap (F : BogoliubovInertialFrame) :
    YangBaxterQSwap.C12 (frameBraidingPhase F) *
        YangBaxterQSwap.C23 (frameBraidingPhase F) *
        YangBaxterQSwap.C12 (frameBraidingPhase F) =
      YangBaxterQSwap.C23 (frameBraidingPhase F) *
        YangBaxterQSwap.C12 (frameBraidingPhase F) *
        YangBaxterQSwap.C23 (frameBraidingPhase F) :=
  YangBaxterQSwap.yang_baxter_relation (frameBraidingPhase F)

/-- The Bogoliubov q-clock is exactly the scalar used by the tensor cross map in
braid-ideal descent. -/
theorem frame_qCrossMap_tmul {H H_dual : Type*}
    [AddCommGroup H] [Module ℂ H]
    [AddCommGroup H_dual] [Module ℂ H_dual]
    (F : BogoliubovInertialFrame) (eta : H_dual) (x : H) :
    BraidIdealDescent.qCrossMap (K := ℂ) (H := H) (H_dual := H_dual)
      (frameBraidingPhase F) (eta ⊗ₜ[ℂ] x) =
        frameBraidingPhase F • (x ⊗ₜ[ℂ] eta) := by
  exact BraidIdealDescent.qCrossMap_tmul
    (K := ℂ) (H := H) (H_dual := H_dual) (frameBraidingPhase F) eta x

/-- Chemical-potential shifts multiply the q-scaled color braid phase by
`qRapidity (β δμ Q)`. -/
theorem frameColorSigma0_mu_shift {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (F : BogoliubovInertialFrame) (δμ : ℝ) (ψ : ColorSpinor4 V) :
    frameColorSigma0 { F with μ := F.μ + δμ } ψ =
      qBraid4 (qRapidity (F.β * δμ * F.Q)) (frameColorSigma0 F ψ) := by
  unfold frameColorSigma0 qColorSigma0 qColorBraid4
  rw [frameBraidingPhase_mu_shift F δμ]
  simp [permuteColorSpinor4, qBraid4, smul_smul]

/-- Consolidated graph theorem connecting the new explicit q-color braid action
to the existing `S₃`, Yang--Baxter, and braid-ideal descent modules. -/
theorem bogoliubov_braid_graph_synthesis {V : Type*}
    [AddCommMonoid V] [Module ℂ V]
    (F : BogoliubovInertialFrame) (ψ : ColorSpinor4 V) :
    frameColorSigma0 F (frameColorSigma1 F (frameColorSigma0 F ψ)) =
      frameColorSigma1 F (frameColorSigma0 F (frameColorSigma1 F ψ)) ∧
    B3RepresentationBridge.s3_rep.σ0 * B3RepresentationBridge.s3_rep.σ1 *
        B3RepresentationBridge.s3_rep.σ0 =
      B3RepresentationBridge.s3_rep.σ1 * B3RepresentationBridge.s3_rep.σ0 *
        B3RepresentationBridge.s3_rep.σ1 ∧
    YangBaxterQSwap.C12 (frameBraidingPhase F) *
        YangBaxterQSwap.C23 (frameBraidingPhase F) *
        YangBaxterQSwap.C12 (frameBraidingPhase F) =
      YangBaxterQSwap.C23 (frameBraidingPhase F) *
        YangBaxterQSwap.C12 (frameBraidingPhase F) *
        YangBaxterQSwap.C23 (frameBraidingPhase F) := by
  exact ⟨frameColorBraid_artin F ψ,
    color_braid_underlying_s3_artin,
    frame_yang_baxter_qswap F⟩

end BogoliubovBraidGraphWeld

end noncomputable section
