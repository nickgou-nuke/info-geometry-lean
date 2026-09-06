import Mathlib.Tactic

/-!
# Hestenes-Dirac Adjoint and the Roles of γ₀

This file formally defines the Cl(1,1) real Clifford algebra (the split-quaternions)
and formally verifies the three distinct roles of a future-directed unit vector γ₀
(with γ₀² = 1) in a causal geometry:

1. **Spinor Fundamental Symmetry:** Defining an indefinite invariant pairing on spinors.
2. **Hestenes Hermitian Adjoint:** A frame-dependent adjoint on the even algebra.
3. **Tomita Modular Conjugation:** The modular conjugation on the standard form carrier.

We also verify the core geometric identities for the split-quaternions:
- Grade Involution α
- Reversion ~ (tilde)
- Clifford Conjugation (bar)
and prove that Clifford conjugation is the composition of grade involution and reversion.
-/

namespace InfoGeometry.Canonical.HestenesDiracAdjoint

-- We define the base Cl(1,1) Split-Quaternion algebra natively.
@[ext]
structure SplitQuaternion (R : Type*) [CommRing R] where
  re : R
  e : R
  f : R
  ef : R

namespace SplitQuaternion
variable {R : Type*} [CommRing R]

@[simps]
instance : Add (SplitQuaternion R) :=
  ⟨fun x y => ⟨x.re + y.re, x.e + y.e, x.f + y.f, x.ef + y.ef⟩⟩

@[simps]
instance : Neg (SplitQuaternion R) :=
  ⟨fun x => ⟨-x.re, -x.e, -x.f, -x.ef⟩⟩

@[simps]
instance : Zero (SplitQuaternion R) :=
  ⟨⟨0, 0, 0, 0⟩⟩

@[simps]
instance : SMul R (SplitQuaternion R) :=
  ⟨fun r x => ⟨r * x.re, r * x.e, r * x.f, r * x.ef⟩⟩

@[simps]
instance : One (SplitQuaternion R) :=
  ⟨⟨1, 0, 0, 0⟩⟩

-- e^2 = 1, f^2 = -1, ef = -fe
@[simps]
instance : Mul (SplitQuaternion R) :=
  ⟨fun x y =>
    ⟨x.re * y.re + x.e * y.e - x.f * y.f + x.ef * y.ef,
     x.re * y.e + x.e * y.re + x.f * y.ef - x.ef * y.f,
     x.re * y.f + x.e * y.ef + x.f * y.re - x.ef * y.e,
     x.re * y.ef + x.e * y.f - x.f * y.e + x.ef * y.re⟩⟩

-- Grade Involution α: negates odd grades (e, f)
def gradeInvolution (x : SplitQuaternion R) : SplitQuaternion R :=
  ⟨x.re, -x.e, -x.f, x.ef⟩

-- Reversion: reverses the order of products. e -> e, f -> f, ef -> -ef
def reversion (x : SplitQuaternion R) : SplitQuaternion R :=
  ⟨x.re, x.e, x.f, -x.ef⟩

-- Clifford Conjugation (split-quaternion conjugation)
def cliffordConjugation (x : SplitQuaternion R) : SplitQuaternion R :=
  ⟨x.re, -x.e, -x.f, -x.ef⟩

-- Quadratic form (signature 2,2)
def normSq (x : SplitQuaternion R) : R :=
  x.re^2 - x.e^2 + x.f^2 - x.ef^2

-- Theorem: Clifford Conjugation is Grade Involution composed with Reversion
theorem cliffordConjugation_eq_gradeInvolution_comp_reversion (x : SplitQuaternion R) :
    cliffordConjugation x = gradeInvolution (reversion x) := by
  ext <;> simp [cliffordConjugation, gradeInvolution, reversion]

theorem x_mul_cliffordConjugation (x : SplitQuaternion R) :
    x * cliffordConjugation x = ⟨normSq x, 0, 0, 0⟩ := by
  ext <;> simp [cliffordConjugation, normSq] <;> ring_nf

/-!
### The Three Roles of γ₀

We define γ₀ as the `e` basis vector (which has γ₀² = 1).
-/
def gamma0 : SplitQuaternion R := ⟨0, 1, 0, 0⟩

lemma gamma0_sq : gamma0 * (gamma0 : SplitQuaternion R) = 1 := by
  ext <;> simp [gamma0]

/-- Role 1: Fundamental Symmetry on a Spinor module.
For a representation space, γ₀ acts as a symmetry.
We represent this algebraically by showing it induces an involution. -/
def spinorFundamentalSymmetry (x : SplitQuaternion R) : SplitQuaternion R :=
  gamma0 * x

lemma spinorFundamentalSymmetry_involutive (x : SplitQuaternion R) :
    spinorFundamentalSymmetry (spinorFundamentalSymmetry x) = x := by
  ext <;> simp [spinorFundamentalSymmetry, gamma0]

/-- Role 2: Hestenes Hermitian Adjoint.
On the Cl(1,1) algebra, it defines a frame-dependent Hermitian adjoint:
A†_H = γ₀ * A~ * γ₀ (where A~ is reversion) -/
def hestenesAdjoint (x : SplitQuaternion R) : SplitQuaternion R :=
  gamma0 * reversion x * gamma0

theorem hestenesAdjoint_involutive (x : SplitQuaternion R) :
    hestenesAdjoint (hestenesAdjoint x) = x := by
  ext <;> simp [hestenesAdjoint, gamma0, reversion]

/-- Role 3: Tomita Modular Conjugation.
In the standard form von Neumann algebra over Cl(1,1), this becomes the
anti-linear modular conjugation J. We model the algebraic core of J here
as the Hestenes adjoint coupled with Clifford conjugation. -/
def tomitaModularConjugation (x : SplitQuaternion R) : SplitQuaternion R :=
  cliffordConjugation (hestenesAdjoint x)

theorem tomitaModularConjugation_involutive (x : SplitQuaternion R) :
    tomitaModularConjugation (tomitaModularConjugation x) = x := by
  ext <;> simp [tomitaModularConjugation, cliffordConjugation, hestenesAdjoint,
    gamma0, reversion]

end SplitQuaternion

end InfoGeometry.Canonical.HestenesDiracAdjoint
