import Mathlib
import InfoGeometry.Canonical.PauliHestenesSpinMomentum
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.SocketTarget

/-!
# Pauli Paravector Bridge

Finite constructive bridge between real Minkowski four-vectors and `2 × 2`
Hermitian complex matrices in the Pauli basis.

This geometry-facing adapter exposes the standard coordinate names
`(t,x,y,z)` and delegates the determinant identity to the canonical
Pauli/Hestenes owner surface.

It proves only the algebraic determinant identity and its immediate null/mass
shell corollaries.  It does not assert a Dirac equation, spin-statistics
theorem, Pauli-Lubanski classification, Hestenes real-spinor theorem, or
Hilbert-Pólya spectral theorem.
-/

noncomputable section

namespace InfoGeometry.Geometry.PauliParavectorBridge

open scoped Matrix

/-! ## 1. Minkowski four-vectors and Pauli matrices -/

/-- Real Minkowski four-vector in coordinates `(t,x,y,z)`. -/
@[rep_depth operator]
structure Minkowski4 where
  /-- Time/energy component. -/
  t : ℝ
  /-- Spatial `x` component. -/
  x : ℝ
  /-- Spatial `y` component. -/
  y : ℝ
  /-- Spatial `z` component. -/
  z : ℝ

namespace Minkowski4

/-- Minkowski quadratic form with signature `(+, -, -, -)`. -/
def q
    (v : Minkowski4) : ℝ :=
  v.t ^ 2 - v.x ^ 2 - v.y ^ 2 - v.z ^ 2

/-- Lightlike/null condition. -/
def IsNull
    (v : Minkowski4) : Prop :=
  v.q = 0

/-- Mass shell condition `q p = m²`. -/
def OnMassShell
    (p : Minkowski4)
    (m : ℝ) : Prop :=
  p.q = m ^ 2

end Minkowski4

/-- Carrier for `2 × 2` complex matrices. -/
abbrev PauliMat : Type :=
  Matrix (Fin 2) (Fin 2) ℂ

/--
Convert geometry-facing coordinates into the canonical Pauli/Hestenes
paravector owner.
-/
def toPauliParavector
    (v : Minkowski4) :
    InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector where
  energy := v.t
  px := v.x
  py := v.y
  pz := v.z

/--
Pauli/Hermitian matrix associated to a real Minkowski vector:

`[[t+z, x - i y], [x + i y, t-z]]`.
-/
def pauliMatrix
    (v : Minkowski4) : PauliMat :=
  (toPauliParavector v).pauliMatrix

/--
Constructive determinant identity:

`det(t I + x σ₁ + y σ₂ + z σ₃) = t² - x² - y² - z²`.
-/
@[rep_depth operator]
theorem det_pauliMatrix
  (v : Minkowski4) :
    Matrix.det (pauliMatrix v) = ((v.q : ℝ) : ℂ) := by
  simpa [pauliMatrix, toPauliParavector, Minkowski4.q,
    InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.minkowskiNormSq] using
    InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.det_pauliMatrix_eq_minkowskiNormSq
      (toPauliParavector v)

/--
Null four-vectors map to singular Pauli matrices.

This is determinant/rank-collapse language, not nilpotence.
-/
@[rep_depth operator]
theorem det_pauliMatrix_eq_zero_of_null
    {v : Minkowski4}
    (hv : v.IsNull) :
    Matrix.det (pauliMatrix v) = 0 := by
  rw [det_pauliMatrix, hv]
  simp

/-- Energy-momentum mass shell in Pauli determinant form. -/
@[rep_depth operator]
theorem det_pauliMatrix_eq_mass_sq
    {p : Minkowski4}
    {m : ℝ}
    (hp : p.OnMassShell m) :
    Matrix.det (pauliMatrix p) = ((m ^ 2 : ℝ) : ℂ) := by
  rw [det_pauliMatrix, hp]

/-! ## 2. Spin/rotor readout sockets -/

/--
Spinor transport socket.

A model supplies a spinor action on Pauli matrices, intended as `X ↦ L X L†`.
This file does not prove the `SL(2,ℂ)` double-cover theorem.
-/
@[rep_depth operator]
structure PauliSpinorTransport where
  /-- Transport/action on Pauli matrices. -/
  transform : PauliMat → PauliMat

  /-- Determinant preservation under the supplied transport. -/
  preservesQuadratic :
    ∀ v : Minkowski4,
      Matrix.det (transform (pauliMatrix v)) = Matrix.det (pauliMatrix v)

namespace PauliSpinorTransport

variable (T : PauliSpinorTransport)

/-- Re-export of determinant/Minkowski-norm preservation. -/
@[rep_depth operator]
theorem determinant_preserved
    (v : Minkowski4) :
    Matrix.det (T.transform (pauliMatrix v)) = Matrix.det (pauliMatrix v) :=
  T.preservesQuadratic v

end PauliSpinorTransport

/--
Bivector/spin-plane readout socket.

In Hestenes language, spin is a bivector/rotor datum extracted from the spinor,
not a component of the momentum paravector itself.
-/
@[socket_debt_tag, rep_depth operator]
structure SpinBivectorReadout
    (Spinor Bivector : Type*) where
  /-- Spin plane/bivector readout. -/
  spinPlane : Spinor → Bivector

  /-- The abstract proposition representing the readout law. -/
  ReadoutHolds : Prop

  /-- The certificate/proof of the readout law. -/
  readout : ReadoutHolds

namespace SpinBivectorReadout

variable {Spinor Bivector : Type*}

/-- Debt surface for the model-specific spin-plane readout theorem. -/
@[rep_depth operator]
theorem readout_holds
    (S : SpinBivectorReadout Spinor Bivector) :
    S.ReadoutHolds :=
  S.readout

end SpinBivectorReadout

/--
Momentum-spin coupling socket.

This is the theorem-safe representation-theoretic statement: momentum and spin
are read together through a common spinor/rotor structure.
-/
@[socket_debt_tag, rep_depth operator]
structure MomentumSpinCoupling
    (Spinor Bivector : Type*) where
  /-- Momentum/paravector readout. -/
  momentum : Spinor → Minkowski4

  /-- Spin bivector/plane readout. -/
  spinReadout : SpinBivectorReadout Spinor Bivector

  /-- Helicity readout. -/
  helicity : Spinor → ℝ

  /-- Pauli-Lubanski-style readout. -/
  pauliLubanskiReadout : Spinor → Minkowski4

  /-- The abstract proposition representing the coupling law. -/
  CouplingHolds : Prop

  /-- The certificate/proof of the coupling law. -/
  coupling : CouplingHolds

namespace MomentumSpinCoupling

variable {Spinor Bivector : Type*}

/-- Debt surface for the model-specific spin-momentum coupling theorem. -/
@[rep_depth operator]
theorem coupling_holds
    (C : MomentumSpinCoupling Spinor Bivector) :
    C.CouplingHolds :=
  C.coupling

end MomentumSpinCoupling

end InfoGeometry.Geometry.PauliParavectorBridge
