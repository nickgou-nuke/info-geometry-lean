import InfoGeometry.Categorical.LogNilpotentCheckedRAdapter
import InfoGeometry.Categorical.LogEndModuleNilpotentClosure
import InfoGeometry.Projective.HadjiivanovLogConnectionReadoutBridge

/-!
# InfoGeometry.Categorical.LogNilpotentCrossCheckedR

Concrete checked braid operator on the tensor powers of a square-zero
logarithmic object.

This file reuses two repository owners rather than introducing a new braid
abstraction:

* `HadjiivanovLogConnectionReadoutBridge.unipotentResidueReadout` for the exact
  finite polynomial `I + p N` attached to a square-zero residue;
* `QuantumG2RMatrixBraidingDatum` for the checked-`R` / Yang--Baxter interface.

For a square-zero logarithmic object `X`, the mixed tensor direction
`N_X ⊗ N_X` is square-zero.  We feed that existing nilpotent into the existing
Hadjiivanov unipotent readout and compose with the canonical tensor swap:

`checkR_p = τ ∘ (I + p (N_X ⊗ N_X))`.

The resulting checked operator is proved to commute with the primitive tensor
nilpotent and to satisfy the Artin/Yang--Baxter relation on `X ⊗ X ⊗ X`.
No universal quantum-group `R`-matrix or analytic holonomy claim is made.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogNilpotentCrossCheckedR

open CategoryTheory
open scoped TensorProduct

open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule
open InfoGeometry.Categorical.LogEndModuleNilpotentClosure
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentCheckedRAdapter
open InfoGeometry.Categorical.QuantumG2RMatrixBraidingDatum
open InfoGeometry.Projective.HadjiivanovLogConnectionBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionReadoutBridge

universe u v

variable {𝕜 : Type u} [Field 𝕜]

section Complex

variable (X : LogNilpotentModule ℂ)
variable (hX : X.N ^ 2 = 0)

/-- Pointwise square-zero readback for the logarithmic generator. -/
@[simp]
theorem N_apply_twice (x : X) : X.N (X.N x) = 0 := by
  have hx := congrArg (fun T : Module.End ℂ X => T x) hX
  simpa [pow_two, Module.End.mul_eq_comp, LinearMap.comp_apply] using hx

/-- The mixed tensor logarithmic direction, packaged through the repository's
existing `LogResidue` owner so that the Hadjiivanov finite unipotent readout can
be reused directly. -/
def crossResidue : LogResidue (X ⊗[ℂ] X) where
  weight := 0
  nilpotent := crossTensorEnd X.toLogEndModule X.toLogEndModule
  nilpotent_sq := by
    rw [← Module.End.mul_eq_comp]
    simpa [pow_two] using
      (crossTensorEnd_sq_eq_zero_of_sq_zero
        X.toLogEndModule X.toLogEndModule hX hX)

/-- Existing Hadjiivanov finite readout `I + p (N ⊗ N)` on the tensor square. -/
def crossUnipotentMap (p : ℂ) :
    (X ⊗[ℂ] X) →ₗ[ℂ] (X ⊗[ℂ] X) :=
  unipotentResidueReadout (crossResidue X hX) p

/-- The finite readout is an exact linear equivalence; its inverse is obtained
by reversing the scalar parameter. -/
def crossUnipotentEquiv (p : ℂ) :
    (X ⊗[ℂ] X) ≃ₗ[ℂ] (X ⊗[ℂ] X) := by
  apply LinearEquiv.ofLinear (crossUnipotentMap X hX p)
    (crossUnipotentMap X hX (-p))
  · rw [crossUnipotentMap, crossUnipotentMap,
      unipotentResidueReadout_comp]
    simp [unipotentResidueReadout]
  · rw [crossUnipotentMap, crossUnipotentMap,
      unipotentResidueReadout_comp]
    simp [unipotentResidueReadout]

/-- The checked logarithmic braid operator: first apply the finite nilpotent
readout, then exchange the two tensor factors. -/
def logCheckedR (p : ℂ) :
    (X ⊗[ℂ] X) ≃ₗ[ℂ] (X ⊗[ℂ] X) :=
  (crossUnipotentEquiv X hX p).trans (TensorProduct.comm ℂ X X)

@[simp]
theorem crossUnipotentMap_tmul (p : ℂ) (x y : X) :
    crossUnipotentMap X hX p (x ⊗ₜ[ℂ] y) =
      x ⊗ₜ[ℂ] y + p • (X.N x ⊗ₜ[ℂ] X.N y) := by
  simp [crossUnipotentMap, crossResidue, unipotentResidueReadout_apply,
    crossTensorEnd, TensorProduct.map_tmul]

/-- Pure-tensor action of the checked logarithmic braid. -/
@[simp]
theorem logCheckedR_tmul (p : ℂ) (x y : X) :
    logCheckedR X hX p (x ⊗ₜ[ℂ] y) =
      y ⊗ₜ[ℂ] x + p • (X.N y ⊗ₜ[ℂ] X.N x) := by
  simp [logCheckedR, LinearEquiv.trans_apply, crossUnipotentMap_tmul,
    TensorProduct.comm_tmul]

/-- The finite unipotent part commutes with the primitive logarithmic tensor
endomorphism.  The mixed cross term actually annihilates it in both orders. -/
theorem crossUnipotent_commutes_tensorN (p : ℂ) :
    (crossUnipotentEquiv X hX p).toLinearMap.comp
        (PairObj X).N =
      (PairObj X).N.comp (crossUnipotentEquiv X hX p).toLinearMap := by
  apply LinearMap.ext
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp
  · intro x y
    simp [LinearMap.comp_apply, crossUnipotentEquiv,
      crossUnipotentMap_tmul, LogEndModule.tensorObj_N_tmul,
      N_apply_twice X hX]
  · intro a b ha hb
    simp [map_add, ha, hb]

/-- The checked braid is a morphism of the logarithmic tensor object. -/
theorem logCheckedR_commutes_tensorN (p : ℂ) :
    (logCheckedR X hX p).toLinearMap.comp (PairObj X).N =
      (PairObj X).N.comp (logCheckedR X hX p).toLinearMap := by
  apply LinearMap.ext
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp
  · intro x y
    simp [LinearMap.comp_apply, logCheckedR_tmul,
      LogEndModule.tensorObj_N_tmul, N_apply_twice X hX]
  · intro a b ha hb
    simp [map_add, ha, hb]

/-- First local action of `checkR` on the right-associated triple tensor. -/
def logCheckedR12 (p : ℂ) :
    (X ⊗[ℂ] (X ⊗[ℂ] X)) ≃ₗ[ℂ] (X ⊗[ℂ] (X ⊗[ℂ] X)) :=
  map12 ℂ X (logCheckedR X hX p)

/-- Second local action of `checkR` on the right-associated triple tensor. -/
def logCheckedR23 (p : ℂ) :
    (X ⊗[ℂ] (X ⊗[ℂ] X)) ≃ₗ[ℂ] (X ⊗[ℂ] (X ⊗[ℂ] X)) :=
  map23 ℂ X (logCheckedR X hX p)

/-- Artin/Yang--Baxter relation for the checked logarithmic braid.  The proof is
finite: all degree-two corrections die because the original logarithmic
direction is square-zero. -/
theorem logCheckedR_yangBaxter (p : ℂ) :
    (logCheckedR12 X hX p).toLinearMap ∘ₗ
          (logCheckedR23 X hX p).toLinearMap ∘ₗ
          (logCheckedR12 X hX p).toLinearMap =
      (logCheckedR23 X hX p).toLinearMap ∘ₗ
          (logCheckedR12 X hX p).toLinearMap ∘ₗ
          (logCheckedR23 X hX p).toLinearMap := by
  apply LinearMap.ext
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp
  · intro x yz
    refine TensorProduct.induction_on yz ?_ ?_ ?_
    · simp
    · intro y z
      simp [logCheckedR12, logCheckedR23, map12, map23,
        LinearEquiv.trans_apply, LinearMap.comp_apply, logCheckedR_tmul,
        N_apply_twice X hX, TensorProduct.assoc_tmul,
        TensorProduct.assoc_symm_tmul]
      module
    · intro a b ha hb
      simp [map_add, ha, hb]
  · intro a b ha hb
    simp [map_add, ha, hb]

/-- Existing checked-`R` datum constructor for the logarithmic braid.  The only
remaining datum not forced by square-zero algebra is whether the chosen
realization has nontrivial double braiding; that witness is kept explicit. -/
def logCheckedRDatum
    (p : ℂ)
    (hmonodromy :
      ((logCheckedR X hX p).trans (logCheckedR X hX p)).toLinearMap ≠
        LinearMap.id) :
    QuantumG2RMatrixDatum ℂ X where
  q := p
  checkR := logCheckedR X hX p
  checkR12 := logCheckedR12 X hX p
  checkR23 := logCheckedR23 X hX p
  checkR12_eq := rfl
  checkR23_eq := rfl
  yangBaxter := logCheckedR_yangBaxter X hX p
  monodromy_nontrivial := hmonodromy

/-- The generic checked-`R` adapter now promotes the concrete logarithmic braid
into an automorphism of the logarithmic tensor object. -/
def logCheckedRLogIso
    (p : ℂ)
    (hmonodromy :
      ((logCheckedR X hX p).trans (logCheckedR X hX p)).toLinearMap ≠
        LinearMap.id) :
    PairObj X ≅ PairObj X :=
  checkedRIso X (logCheckedRDatum X hX p hmonodromy)
    (logCheckedR_commutes_tensorN X hX p)

end Complex

end InfoGeometry.Categorical.LogNilpotentCrossCheckedR
