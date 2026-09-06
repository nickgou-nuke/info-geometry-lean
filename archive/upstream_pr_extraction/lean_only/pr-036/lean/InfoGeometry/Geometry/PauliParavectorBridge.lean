import Mathlib.Tactic
import InfoGeometry.Canonical.PauliHestenesSpinMomentum
import InfoGeometry.Physics.MDPASJMSouriau
import InfoGeometry.Meta.Architecture

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
abbrev Minkowski4 := Fin 4 → ℝ

namespace Minkowski4

abbrev t (v : Minkowski4) : ℝ := v 0
abbrev x (v : Minkowski4) : ℝ := v 1
abbrev y (v : Minkowski4) : ℝ := v 2
abbrev z (v : Minkowski4) : ℝ := v 3

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
