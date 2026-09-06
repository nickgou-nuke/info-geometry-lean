import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Algebra.SupermatrixKoszul
import InfoGeometry.Clifford.KoszulFoundation
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Real.Basic

noncomputable section

/-!
# OpSignatureBridge

Central bridge from the symbolic operator-square trichotomy `Op² ∈ {-1, 0, 1}`
to the existing hypercomplex, supermatrix, and Clifford owner surfaces.

This file is deliberately thin: it reuses the theorem-owned triad, the concrete
`1|1` block matrices, and the native Clifford polarization law.
-/

namespace InfoGeometry.Clifford.OpSignatureBridge

open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Clifford.KoszulFoundation

/-- Symbolic operator-square signature. -/
inductive OpSignature where
  | elliptic
  | parabolic
  | hyperbolic
deriving DecidableEq, Repr

/-- Bridge-side parity tag for the `1|1` matrix lane. -/
inductive OpParity where
  | even
  | odd
deriving DecidableEq, Repr

/-- Classify a real scalar into the `Op² ∈ {-1, 0, 1}` trichotomy. -/
def classifySquare (op_sq : ℝ) : OpSignature :=
  if op_sq < 0 then OpSignature.elliptic
  else if op_sq = 0 then OpSignature.parabolic
  else OpSignature.hyperbolic

/-- Scalar readout for the trichotomy. -/
def opSignatureScalar : OpSignature → ℝ
  | .elliptic => -1
  | .parabolic => 0
  | .hyperbolic => 1

/-- Direct bridge into the concrete hypercomplex `2 × 2` model. -/
def toHypercomplexModel : OpSignature → Mat2
  | .elliptic => I
  | .parabolic => N
  | .hyperbolic => E

/-- Bridge-side structural parity readout. -/
def toStructuralParity : OpSignature → OpParity
  | .elliptic => .even
  | .parabolic => .odd
  | .hyperbolic => .odd

/-- Concrete `1|1` block-channel selected by the signature lane. -/
def toSupermatrixBlock : OpSignature → Mat2
  | .elliptic => InfoGeometry.Algebra.SupermatrixKoszul.evenBlock 1 1
  | .parabolic => InfoGeometry.Algebra.SupermatrixKoszul.oddBlock 1 0
  | .hyperbolic => InfoGeometry.Algebra.SupermatrixKoszul.oddBlock 1 1

/--
A 1D quadratic form encoding the sign choice for the Clifford bridge.
Elliptic: `-x²`, parabolic: `0`, hyperbolic: `x²`.
-/
def signatureToQuadraticForm {R : Type*} [CommRing R] : OpSignature → QuadraticForm R R :=
  fun sig =>
    match sig with
    | .elliptic =>
        -(QuadraticMap.linMulLin (LinearMap.id : R →ₗ[R] R)
            (LinearMap.id : R →ₗ[R] R))
    | .parabolic => 0
    | .hyperbolic =>
        QuadraticMap.linMulLin (LinearMap.id : R →ₗ[R] R)
          (LinearMap.id : R →ₗ[R] R)

@[simp] theorem toHypercomplexModel_sq (sig : OpSignature) :
    toHypercomplexModel sig * toHypercomplexModel sig =
      (opSignatureScalar sig) • (1 : Mat2) := by
  cases sig <;> simp [toHypercomplexModel, opSignatureScalar, I_sq, N_sq, E_sq]

@[simp] theorem toStructuralParity_elliptic :
    toStructuralParity OpSignature.elliptic = OpParity.even := by
  rfl

@[simp] theorem toStructuralParity_parabolic :
    toStructuralParity OpSignature.parabolic = OpParity.odd := by
  rfl

@[simp] theorem toStructuralParity_hyperbolic :
    toStructuralParity OpSignature.hyperbolic = OpParity.odd := by
  rfl

/--
Bridge theorem: the signature-selected quadratic form feeds directly into the
native Clifford anticommutator / polarization law.
-/
theorem bridge_to_polarization
    {R : Type*} [CommRing R] [Invertible (2 : R)]
    (sig : OpSignature) (v w : R) :
    CliffordAlgebra.ι (signatureToQuadraticForm (R := R) sig) v *
        CliffordAlgebra.ι (signatureToQuadraticForm (R := R) sig) w +
      CliffordAlgebra.ι (signatureToQuadraticForm (R := R) sig) w *
        CliffordAlgebra.ι (signatureToQuadraticForm (R := R) sig) v =
      algebraMap R (CliffordAlgebra (signatureToQuadraticForm (R := R) sig))
        (QuadraticMap.polar (signatureToQuadraticForm (R := R) sig) v w) := by
  simpa using
    (clifford_polarization (Q := signatureToQuadraticForm (R := R) sig) v w)

end InfoGeometry.Clifford.OpSignatureBridge
