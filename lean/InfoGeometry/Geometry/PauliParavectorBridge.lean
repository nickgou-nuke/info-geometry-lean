import Mathlib.Tactic
import InfoGeometry.Canonical.PauliHestenesSpinMomentum
import InfoGeometry.Physics.MDPASJMSouriau
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

@[ext] theorem ext {u v : Minkowski4}
    (ht : u.t = v.t) (hx : u.x = v.x) (hy : u.y = v.y) (hz : u.z = v.z) : u = v := by
  cases u
  cases v
  simp_all

end Minkowski4

instance minkowski4Add : Add Minkowski4 where
  add u v := ⟨u.t + v.t, u.x + v.x, u.y + v.y, u.z + v.z⟩

instance minkowski4Zero : Zero Minkowski4 where
  zero := ⟨0, 0, 0, 0⟩

instance minkowski4AddCommMonoid : AddCommMonoid Minkowski4 where
  nsmul n u := ⟨n • u.t, n • u.x, n • u.y, n • u.z⟩
  add_assoc u v w := by
    apply Minkowski4.ext <;> change (_ + _) + _ = _ + (_ + _) <;> ring
  zero_add u := by
    apply Minkowski4.ext <;> change (0 + _) = _ <;> ring
  add_zero u := by
    apply Minkowski4.ext <;> change (_ + 0) = _ <;> ring
  add_comm u v := by
    apply Minkowski4.ext <;> change (_ + _) = _ + _ <;> ring
  nsmul_zero u := by
    apply Minkowski4.ext <;> change 0 = 0 <;> rfl
  nsmul_succ n u := by
    apply Minkowski4.ext <;> change _ = _ + _ <;> ring

instance minkowski4SMul : SMul ℝ Minkowski4 where
  smul a u := ⟨a * u.t, a * u.x, a * u.y, a * u.z⟩

instance minkowski4Module : Module ℝ Minkowski4 where
  one_smul u := by
    apply Minkowski4.ext <;> change _ * _ = _ <;> ring
  mul_smul a b u := by
    apply Minkowski4.ext <;> change (_ * _) * _ = _ * (_ * _) <;> ring
  smul_add a u v := by
    apply Minkowski4.ext <;> change _ * (_ + _) = _ * _ + _ * _ <;> ring
  smul_zero a := by
    apply Minkowski4.ext <;> change _ * 0 = 0 <;> ring
  add_smul a b u := by
    apply Minkowski4.ext <;> change (_ + _) * _ = _ * _ + _ * _ <;> ring
  zero_smul u := by
    apply Minkowski4.ext <;> change 0 * _ = 0 <;> ring

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

This finite interface owns only the readout map.  A model-specific law requires
actual bivector operations and is not represented by an opaque proposition.
-/
@[rep_depth operator]
structure SpinBivectorReadout
    (Spinor Bivector : Type*) where
  /-- Spin plane/bivector readout. -/
  spinPlane : Spinor → Bivector
  /-- Model-specific relation defining a valid spin-plane readout. -/
  IsSpinPlaneReadout : Spinor → Bivector → Prop
  /-- Every selected spin plane satisfies that relation. -/
  spinPlane_spec : ∀ psi, IsSpinPlaneReadout psi (spinPlane psi)

namespace SpinBivectorReadout

variable {Spinor Bivector : Type*}

theorem readout_holds
    (S : SpinBivectorReadout Spinor Bivector) (psi : Spinor) :
    S.IsSpinPlaneReadout psi (S.spinPlane psi) :=
  S.spinPlane_spec psi

end SpinBivectorReadout

/--
Momentum-spin coupling socket.

Momentum and spin are read together through a common spinor carrier.  No
Pauli--Lubanski coupling equation is asserted until a concrete representation
supplies one.
-/
@[rep_depth operator]
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

  /-- Relation coupling the four model-specific readouts. -/
  CouplingLaw : Minkowski4 → Bivector → ℝ → Minkowski4 → Prop

  /-- The selected readouts satisfy the coupling relation. -/
  coupling :
    ∀ psi,
      CouplingLaw (momentum psi) (spinReadout.spinPlane psi)
        (helicity psi) (pauliLubanskiReadout psi)

namespace MomentumSpinCoupling

variable {Spinor Bivector : Type*}

theorem coupling_holds
    (C : MomentumSpinCoupling Spinor Bivector) (psi : Spinor) :
    C.CouplingLaw (C.momentum psi) (C.spinReadout.spinPlane psi)
      (C.helicity psi) (C.pauliLubanskiReadout psi) :=
  C.coupling psi

end MomentumSpinCoupling

/-! ## 3. Native finite Souriau spin-particle realization -/

abbrev SouriauFiniteSpinReadout :=
  InfoGeometry.Physics.MDPASJMSouriau.FiniteSpinParticleCertificate

namespace SouriauFiniteSpinReadout

open InfoGeometry.Physics.MDPASJMSouriau

variable (C : SouriauFiniteSpinReadout)

theorem spin_antisymmetric :
    IsAntisymmetric (wedge C.u C.v) :=
  C.spin_antisym

theorem spin_plucker :
    pfaffian4 (wedge C.u C.v) = 0 :=
  InfoGeometry.Physics.MDPASJMSouriau.FiniteSpinParticleCertificate.spin_plucker C

theorem spin_transverse
    (hu : dot C.u C.p = 0) (hv : dot C.v C.p = 0) :
    contractRight (wedge C.u C.v) C.p = 0 :=
  InfoGeometry.Physics.MDPASJMSouriau.FiniteSpinParticleCertificate.spin_transverse
    C hu hv

theorem lorentz_power_zero :
    dot C.p (lorentzForce C.field C.p) = 0 :=
  InfoGeometry.Physics.MDPASJMSouriau.FiniteSpinParticleCertificate.lorentz_power_zero C

theorem normal_moment_readout
    (C : SouriauFiniteSpinReadout)
    (q m sB : ℚ) (hm : m ≠ 0) :
    gyromagneticReadout q m 2 sB = q * sB / m :=
  InfoGeometry.Physics.MDPASJMSouriau.FiniteSpinParticleCertificate.normal_moment_readout
    C q m sB hm

theorem spin_half_prequantization
    (C : SouriauFiniteSpinReadout) (h : ℚ) :
    SpinPrequantized (h / 2) h :=
  InfoGeometry.Physics.MDPASJMSouriau.FiniteSpinParticleCertificate.spin_half_prequantization
    C h

end SouriauFiniteSpinReadout

end InfoGeometry.Geometry.PauliParavectorBridge
