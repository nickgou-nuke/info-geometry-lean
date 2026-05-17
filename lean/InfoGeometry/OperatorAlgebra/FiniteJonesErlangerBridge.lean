/-
InfoGeometry/OperatorAlgebra/FiniteJonesErlangerBridge.lean

Finite Jones optics and Erlanger phase invariance.

This module connects the concrete finite-dimensional Jones model to the
operator-Erlangen principle.

The key theorem is modest and exact:

  diagonal phase gauges preserve the Brewster/Drazin core projector.

Under a larger Jones unitary that mixes polarization channels, the projector is
covariant rather than fixed.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.FiniteJonesOptics
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiniteJonesErlangerBridge

open Matrix
open InfoGeometry.OperatorAlgebra.JonesCalibration
open InfoGeometry.OperatorAlgebra.FiniteJonesOptics

/-! ## 1. Diagonal Jones gauge transformations -/

/--
A diagonal Jones gauge in a fixed polarization eigenbasis.

This is the finite-dimensional optical phase stabilizer of the two-channel
basis. Physically, it includes independent phase choices for the two local
polarization eigenchannels.

The inverse coefficients are stored explicitly to avoid depending on any
particular `Units` API.
-/
structure DiagonalJonesGauge where
  a : ℂ
  b : ℂ
  aInv : ℂ
  bInv : ℂ

  a_mul_inv :
    a * aInv = 1

  b_mul_inv :
    b * bInv = 1

namespace DiagonalJonesGauge

/-- The diagonal Jones matrix of the gauge. -/
def mat
    (G : DiagonalJonesGauge) : JonesMat :=
  diagJones G.a G.b

/-- The diagonal inverse Jones matrix of the gauge. -/
def invMat
    (G : DiagonalJonesGauge) : JonesMat :=
  diagJones G.aInv G.bInv

/-- Gauge conjugation of a Jones matrix. -/
def conjugate
    (G : DiagonalJonesGauge)
    (M : JonesMat) : JonesMat :=
  G.mat * M * G.invMat

end DiagonalJonesGauge

/-! ## 2. Diagonal multiplication lemmas -/

/-- Product of diagonal Jones matrices. -/
theorem diagJones_mul
    (a b c d : ℂ) :
    diagJones a b * diagJones c d =
      diagJones (a * c) (b * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagJones, Matrix.mul_apply]

/-- A diagonal gauge fixes every diagonal Jones matrix by conjugation. -/
theorem diagonalGauge_conjugate_diagJones
    (G : DiagonalJonesGauge)
    (x y : ℂ) :
    G.conjugate (diagJones x y) = diagJones x y := by
  unfold DiagonalJonesGauge.conjugate DiagonalJonesGauge.mat DiagonalJonesGauge.invMat
  rw [diagJones_mul]
  rw [diagJones_mul]
  have hx : (G.a * x) * G.aInv = x := by
    calc
      (G.a * x) * G.aInv = x * (G.a * G.aInv) := by ring
      _ = x * 1 := by rw [G.a_mul_inv]
      _ = x := by ring
  have hy : (G.b * y) * G.bInv = y := by
    calc
      (G.b * y) * G.bInv = y * (G.b * G.bInv) := by ring
      _ = y * 1 := by rw [G.b_mul_inv]
      _ = y := by ring
  rw [hx, hy]

/-- The diagonal gauge matrix composed with its stored inverse is the identity. -/
theorem DiagonalJonesGauge.mat_mul_invMat
    (G : DiagonalJonesGauge) :
    G.mat * G.invMat = 1 := by
  unfold DiagonalJonesGauge.mat DiagonalJonesGauge.invMat
  rw [diagJones_mul]
  rw [G.a_mul_inv, G.b_mul_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagJones]

/-- The stored inverse composed with the diagonal gauge matrix is the identity. -/
theorem DiagonalJonesGauge.invMat_mul_mat
    (G : DiagonalJonesGauge) :
    G.invMat * G.mat = 1 := by
  unfold DiagonalJonesGauge.mat DiagonalJonesGauge.invMat
  rw [diagJones_mul]
  have ha : G.aInv * G.a = 1 := by
    calc
      G.aInv * G.a = G.a * G.aInv := by ring
      _ = 1 := G.a_mul_inv
  have hb : G.bInv * G.b = 1 := by
    calc
      G.bInv * G.b = G.b * G.bInv := by ring
      _ = 1 := G.b_mul_inv
  rw [ha, hb]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagJones]

/-! ## 3. Core projectors as Erlanger invariants -/

/--
The finite Jones/Brewster core projector.

This is the surviving `s` channel at a Brewster rank-collapse event.
-/
def brewsterCoreProjector : JonesMat :=
  sProjector

/-- The complementary killed channel at Brewster rank collapse. -/
def brewsterNilProjector : JonesMat :=
  pProjector

/-- Diagonal phase gauges preserve the Brewster/Drazin core projector. -/
theorem diagonalGauge_preserves_brewsterCoreProjector
    (G : DiagonalJonesGauge) :
    G.conjugate brewsterCoreProjector = brewsterCoreProjector := by
  unfold brewsterCoreProjector sProjector
  exact diagonalGauge_conjugate_diagJones G 1 0

/-- Diagonal phase gauges preserve the killed/nil Brewster channel projector. -/
theorem diagonalGauge_preserves_brewsterNilProjector
    (G : DiagonalJonesGauge) :
    G.conjugate brewsterNilProjector = brewsterNilProjector := by
  unfold brewsterNilProjector pProjector
  exact diagonalGauge_conjugate_diagJones G 0 1

/-- Diagonal phase gauges preserve the concrete Brewster Jones matrix. -/
theorem diagonalGauge_preserves_brewsterEvent_jones
    (G : DiagonalJonesGauge)
    (rs : ℂ)
    (hrs : rs ≠ 0) :
    G.conjugate (brewsterEvent rs hrs).jones =
      (brewsterEvent rs hrs).jones := by
  unfold brewsterEvent diagonalSPEvent diagonalEvent JonesOpticalEvent.jones
  exact diagonalGauge_conjugate_diagJones G rs 0

/-- The determinant of the Brewster event remains zero under diagonal phase gauges. -/
theorem diagonalGauge_brewster_det_zero
    (G : DiagonalJonesGauge)
    (rs : ℂ)
    (hrs : rs ≠ 0) :
    det2 (G.conjugate (brewsterEvent rs hrs).jones) = 0 := by
  rw [diagonalGauge_preserves_brewsterEvent_jones G rs hrs]
  exact det2_brewsterEvent_jones rs hrs

/-! ## 4. Erlanger readout socket -/

/--
A finite Jones Erlanger invariant under diagonal phase gauges.

This is a concrete finite-dimensional version of the general Erlanger
principle: `read (g T g^{-1}) = read T`.
-/
structure FiniteJonesErlangerInvariant
    (α : Type*) where
  read : JonesMat → α

  invariant_under_diagonal_gauge :
    ∀ G : DiagonalJonesGauge,
    ∀ M : JonesMat,
      read (G.conjugate M) = read M

/--
The Brewster core projector itself is an invariant object under the diagonal
phase stabilizer.

This readout ignores its input and returns the core projector; the useful
content is the theorem `diagonalGauge_preserves_brewsterCoreProjector`.
-/
def brewsterCoreInvariant :
    FiniteJonesErlangerInvariant JonesMat where
  read := fun _ => brewsterCoreProjector
  invariant_under_diagonal_gauge := by
    intro G M
    rfl

/--
A more concrete statement: the actual core projector is fixed by the diagonal
gauge action.
-/
theorem brewsterCoreProjector_is_fixed_Erlanger_object
    (G : DiagonalJonesGauge) :
    G.conjugate brewsterCoreProjector =
      brewsterCoreProjector :=
  diagonalGauge_preserves_brewsterCoreProjector G

/-! ## 5. Covariance warning socket -/

/--
A general Jones conjugation action.

For non-diagonal transformations, the core projector is generally transported
to a conjugate projector rather than fixed.
-/
def generalJonesConjugate
    (U Uinv : JonesMat)
    (M : JonesMat) : JonesMat :=
  U * M * Uinv

/--
Covariant core projector under a general Jones transformation.

This is the correct object for arbitrary basis-changing transformations.
-/
def transportedBrewsterCoreProjector
    (U Uinv : JonesMat) : JonesMat :=
  generalJonesConjugate U Uinv brewsterCoreProjector

/-! ## 6. Owner target -/

/--
Owner target for the finite Jones Erlanger bridge.

The diagonal phase stabilizer fixes the Brewster core projector and preserves
Brewster rank collapse.
-/
@[owner_target_tag]
def FiniteJonesErlangerBridgeOwnerTarget : Prop :=
  (∀ G : DiagonalJonesGauge,
    G.conjugate brewsterCoreProjector = brewsterCoreProjector)
  ∧
  (∀ G : DiagonalJonesGauge,
   ∀ rs : ℂ,
   ∀ hrs : rs ≠ 0,
    det2 (G.conjugate (brewsterEvent rs hrs).jones) = 0)

/-- The owner target follows from the diagonal-gauge invariance theorems. -/
theorem finiteJonesErlangerBridgeOwnerTarget :
    FiniteJonesErlangerBridgeOwnerTarget := by
  constructor
  · intro G
    exact diagonalGauge_preserves_brewsterCoreProjector G
  · intro G rs hrs
    exact diagonalGauge_brewster_det_zero G rs hrs

end InfoGeometry.OperatorAlgebra.FiniteJonesErlangerBridge
