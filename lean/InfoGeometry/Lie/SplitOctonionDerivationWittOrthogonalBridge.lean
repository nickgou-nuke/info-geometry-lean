import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.SplitOctonionGogberashviliDerivationBridge
import InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge
import InfoGeometry.Lie.SplitOctonionAnnihilatorDimension

/-!
# Split-octonion derivations and the Witt-orthogonal block interface

This owner deliberately separates two facts which are often conflated:

* `CanonicalZornDerivation.IsDerivation` is the Leibniz selector for the
  split-octonion derivation algebra;
* `IsWittSkew` is the matrix-level invariant-form witness consumed by the
  Witt block owner.

The transport theorem from the native Zorn polar form to the particular
`etaW` matrix is not assumed here.  Once that transport is supplied, the
three block readouts below are immediate corollaries of the canonical block
equivalence.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionGogberashviliDerivationBridge
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge
open Matrix
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Lie.CanonicalZornDerivationDimension

abbrev Derivation := canonicalZornDerivations

abbrev PaperZorn :=
  InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.PaperZorn

/-! The native Lie embedding is already available on the paper-Zorn carrier.
This is the Lie-algebra stage before supplying the separate Witt-pairing
transport predicate. -/
noncomputable abbrev nativeDerivationLieHom :
    Derivation →ₗ⁅ℝ⁆ Module.End ℝ PaperZorn :=
  paperDerivationLieHom

theorem nativeDerivationLieHom_injective :
    Function.Injective nativeDerivationLieHom :=
  paperDerivationLieHom_injective

theorem nativeDerivationLieHom_map_lie (D E : Derivation) :
    nativeDerivationLieHom ⁅D, E⁆ =
      ⁅nativeDerivationLieHom D, nativeDerivationLieHom E⁆ := by
  exact nativeDerivationLieHom.map_lie D E

/-! The native derivation API already supplies the differentiated norm/conjugation
identity.  We expose it here as the algebraic invariant-form precursor; the
transport from this native Zorn identity to the particular `etaW` matrix is a
separate theorem and is intentionally not hidden in this wrapper. -/

theorem derivation_native_conj_norm_identity_left
    (D : Derivation) (X : InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.CanonicalZorn) :
    D.1 X *
          InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj X +
        X * D.1 (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj X) =
      0 := by
  exact canonicalDerivation_conj_norm_identity_left D X

theorem derivation_native_conj_norm_identity_right
    (D : Derivation) (X : InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.CanonicalZorn) :
    D.1 (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj X) * X +
          InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj X * D.1 X =
      0 := by
  exact canonicalDerivation_conj_norm_identity_right D X

/-! This is the exact native polar-form transport contract.  The two
hypotheses record the remaining representation-specific fact that derivation
outputs lie in the imaginary (trace-zero) conjugation eigenspace. -/
theorem derivation_native_polar_skew_of_imaginary_trace
    (D : Derivation)
    (htrace : ∀ Z : InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.CanonicalZorn,
      realZornTrace (D.1 Z) = 0)
    (hconj : ∀ Z : InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.CanonicalZorn,
      InfoGeometry.Lie.SplitOctonionImaginaryAction.canonicalConj (D.1 Z) = -D.1 Z)
    (X Y : InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.CanonicalZorn) :
    canonicalPolar (D.1 X) Y + canonicalPolar X (D.1 Y) = 0 := by
  rw [canonicalPolar_eq_trace_conj_mul, canonicalPolar_eq_trace_conj_mul]
  rw [hconj Y]
  have hmap : D.1 (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj Y) = -D.1 Y := by
    apply InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv.injective
    have h := InfoGeometry.Algebra.ZornVectorMatrix.Derivation.map_conj_eq_neg
      (canonicalToVectorDerivation D)
      (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv Y)
    rw [← InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_canonicalConj] at h
    simpa [canonicalToVectorDerivation_apply,
      InfoGeometry.Algebra.ZornVectorMatrix.neg] using h
  have hprod := D.property
    (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj Y) X
  have ht := congrArg realZornTrace hprod
  rw [htrace
    (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj Y * X)] at ht
  rw [hmap] at ht
  have hconj_eq (Z : InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.CanonicalZorn) :
      InfoGeometry.Lie.SplitOctonionImaginaryAction.canonicalConj Z =
        InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj Z := by
    apply InfoGeometry.Canonical.ZornMatrix.ext <;> rfl
  rw [hconj_eq Y]
  simp [realZornTrace, InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornTrace] at ht ⊢
  ring_nf at ht ⊢
  nlinarith

/-! The canonical Zorn polar form is written through the native vector-matrix
equivalence.  This keeps the derivation theorem on the actual carrier; the
separate `PairingTransport` below is what connects it to a chosen `etaW`
coordinate presentation. -/

def vectorNativeWittPairing (X Y : ZornVectorMatrix ℝ) : ℝ :=
  trace (mul (conj Y) X)

theorem derivation_native_parameter_polar_skew
    (p : Params) (X Y : ZornVectorMatrix ℝ) :
    vectorNativeWittPairing (parameterDerivation p X) Y +
      vectorNativeWittPairing X (parameterDerivation p Y) = 0 := by
  rcases X with ⟨xa, xv, xw, xb⟩
  rcases Y with ⟨ya, yv, yw, yb⟩
  dsimp [vectorNativeWittPairing, parameterDerivation, parameterAction,
    ZornVectorMatrix.trace, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
    ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
    ZornVec3.dot, ZornVec3.cross]
  simp [Fin.sum_univ_three]
  ring

def nativeCanonicalWittPairing
    (X Y : InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.CanonicalZorn) : ℝ :=
  trace (mul (conj (canonicalVectorEquiv Y)) (canonicalVectorEquiv X))

theorem derivation_native_witt_skew
    (D : Derivation)
    (X Y : InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.CanonicalZorn) :
    nativeCanonicalWittPairing (D.1 X) Y +
      nativeCanonicalWittPairing X (D.1 Y) = 0 := by
  let Dv := canonicalToVectorDerivation D
  let p : Params := derivationParameters Dv
  have hp : parameterDerivation p = Dv := parameterLinearEquiv.right_inv Dv
  have h := derivation_native_parameter_polar_skew p
    (canonicalVectorEquiv X) (canonicalVectorEquiv Y)
  rw [hp] at h
  simpa [nativeCanonicalWittPairing, vectorNativeWittPairing, Dv, p,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_canonicalConj,
    canonicalToVectorDerivation_apply] using h

/-! The native conjugation and trace identities let us expose the canonical
polar-form skewness without introducing a second coordinate multiplication. -/

/-- A native derivation together with its transported Witt block. -/
structure WittOrthogonalDatum where
  derivation : Derivation
  block : WittBlockMatrix
  block_is_witt_skew : IsWittSkew block

/-! A representation-independent transport interface.  The native pairing and
the coordinate `etaW` pairing are related by an explicit linear equivalence;
no analytic completion is involved. -/
structure PairingTransport (E : Type*) [AddCommGroup E] [Module ℝ E] where
  toCoord : E ≃ₗ[ℝ] (Fin 8 → ℝ)
  nativePairing : E → E → ℝ
  coordinatePairing : (Fin 8 → ℝ) → (Fin 8 → ℝ) → ℝ
  pairing_transport : ∀ x y,
    nativePairing x y = coordinatePairing (toCoord x) (toCoord y)

theorem transported_skew
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : PairingTransport E)
    (D : E →ₗ[ℝ] E)
    (hD : ∀ x y, P.nativePairing (D x) y + P.nativePairing x (D y) = 0) :
    ∀ x y, P.coordinatePairing (P.toCoord (D x)) (P.toCoord y) +
      P.coordinatePairing (P.toCoord x) (P.toCoord (D y)) = 0 := by
  intro x y
  rw [← P.pairing_transport, ← P.pairing_transport]
  exact hD x y

theorem derivation_witt_skew (d : WittOrthogonalDatum) :
    IsWittSkew d.block :=
  d.block_is_witt_skew

/-- The block equations attached to a transported derivation. -/
theorem derivation_block_equations (d : WittOrthogonalDatum) :
    IsWittOrthogonalLie d.block :=
  (isWittSkew_iff_isWittOrthogonalLie d.block).mp d.block_is_witt_skew

theorem derivation_lowerRight_eq_negTranspose (d : WittOrthogonalDatum) :
    d.block.D = - (d.block.A)ᵀ :=
  (derivation_block_equations d).1

theorem derivation_upperRight_skew (d : WittOrthogonalDatum) :
    (d.block.B)ᵀ = - d.block.B :=
  (derivation_block_equations d).2.1

theorem derivation_lowerLeft_skew (d : WittOrthogonalDatum) :
    (d.block.C)ᵀ = - d.block.C :=
  (derivation_block_equations d).2.2

/-- The missing geometric input is isolated as a named transport predicate. -/
def HasWittPolarTransport (_d : Derivation) (block : WittBlockMatrix) : Prop :=
  IsWittSkew block

theorem derivation_witt_skew_of_transport
    (d : Derivation) (block : WittBlockMatrix)
    (htransport : HasWittPolarTransport d block) :
    IsWittSkew block :=
  htransport

/-- The native derivation subalgebra remembers its underlying linear action. -/
theorem native_derivation_forget_injective :
    Function.Injective (fun d : Derivation => (d : EndCZ)) := by
  intro d e h
  exact Subtype.ext h

/-- 🏆 THEOREM: The Lie bracket of two Witt-skew matrices is Witt-skew. -/
theorem wittSkew_lie_closed (X Y : Mat8)
    (hX : Xᵀ * etaW + etaW * X = 0)
    (hY : Yᵀ * etaW + etaW * Y = 0) :
    (X * Y - Y * X)ᵀ * etaW + etaW * (X * Y - Y * X) = 0 := by
  have hX' : Xᵀ * etaW = - (etaW * X) := eq_neg_of_add_eq_zero_left hX
  have hY' : Yᵀ * etaW = - (etaW * Y) := eq_neg_of_add_eq_zero_left hY
  have hX'' : etaW * X = - (Xᵀ * etaW) := eq_neg_of_add_eq_zero_right hX
  have hY'' : etaW * Y = - (Yᵀ * etaW) := eq_neg_of_add_eq_zero_right hY
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]
  rw [Matrix.sub_mul, Matrix.mul_sub]
  rw [Matrix.mul_assoc Yᵀ Xᵀ etaW, Matrix.mul_assoc Xᵀ Yᵀ etaW]
  rw [hX', hY']
  rw [Matrix.mul_neg Yᵀ (etaW * X), Matrix.mul_neg Xᵀ (etaW * Y)]
  rw [← Matrix.mul_assoc Yᵀ etaW X, ← Matrix.mul_assoc Xᵀ etaW Y]
  rw [← Matrix.mul_assoc etaW X Y, ← Matrix.mul_assoc etaW Y X]
  rw [hX'', hY'']
  rw [Matrix.neg_mul (Xᵀ * etaW) Y, Matrix.neg_mul (Yᵀ * etaW) X]
  rw [Matrix.mul_assoc Xᵀ etaW Y, Matrix.mul_assoc Yᵀ etaW X]
  abel

end InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge
