/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
    apply Minkowski4.ext <;> exact succ_nsmul _ n

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

/-- The Pauli determinant vanishes exactly on the Minkowski null cone. -/
@[rep_depth operator]
theorem null_iff_det_pauliMatrix_eq_zero
    (v : Minkowski4) :
    v.IsNull ↔ Matrix.det (pauliMatrix v) = 0 := by
  constructor
  · exact det_pauliMatrix_eq_zero_of_null
  · intro hdet
    rw [det_pauliMatrix] at hdet
    exact_mod_cast hdet

/-- Energy-momentum mass shell in Pauli determinant form. -/
@[rep_depth operator]
theorem det_pauliMatrix_eq_mass_sq
    {p : Minkowski4}
    {m : ℝ}
    (hp : p.OnMassShell m) :
    Matrix.det (pauliMatrix p) = ((m ^ 2 : ℝ) : ℂ) := by
  rw [det_pauliMatrix, hp]

/-! ## 2. Exact scope of the finite readout

The determinant identity and its null/mass-shell consequences above are the
concrete results of this coordinate adapter. They do not define a spin-group
action, a spinor-to-bivector map, or a Pauli--Lubanski coupling. Such structures
would need specified carriers and an actual action; storing the desired law as
a field and re-exporting it proves no additional result. The canonical
Pauli/Hestenes owner contains the separate rotor-frame and spin-momentum
development, with its own explicit proof boundary.
-/

end InfoGeometry.Geometry.PauliParavectorBridge
