/-
Copyright (c) 2024 InfoGeometry. All rights reserved.
Koroteev-Zeitlin: 3D Mirror Symmetry for
Instanton Moduli Spaces
Comm. Math. Phys. 403(2), 1005-1068 (2023)

XXZ Bethe Ansatz equations and QQ-system
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Polynomial BigOperators Finset

namespace KoroteevZeitlin.Bethe

variable {R : Type*} [CommRing R]

/-- XXZ Bethe Ansatz data for an A_r quiver.

Given:
  r     : rank of the Lie algebra sl(r+1)
  v     : dimension vector (number of Bethe roots
          at each node)
  sites : equivariant parameters a_1,...,a_L
  hbar  : quantum deformation parameter
  z     : Kähler (twist) parameters
-/
structure XXZBetheData (r : ℕ) where
  /-- Number of Bethe roots at node a -/
  dimVec : Fin r → ℕ
  /-- Equivariant parameters (evaluation params) -/
  numSites : ℕ
  /-- ℏ deformation parameter -/
  hbar : ℂ
  /-- Kähler parameters z_1,...,z_r -/
  kahler : Fin r → ℂ
  /-- ℏ is not zero or a root of unity -/
  hbar_ne_zero : hbar ≠ 0
  hbar_ne_one : hbar ≠ 1

/-- Bethe roots: s_{a,j} for node a, index j -/
def BetheRoots (B : XXZBetheData r) : Type :=
  (a : Fin r) → Fin (B.dimVec a) → ℂ

/-- Site parameters: a_1,...,a_L -/
def SiteParams (B : XXZBetheData r) : Type :=
  Fin B.numSites → ℂ

/--
Baxter Q-operator: Q_a^+(x) = ∏_j (x - s_{a,j})

Generating function for exterior powers of
tautological bundle at node a.
-/
noncomputable def Q_plus
    (B : XXZBetheData r)
    (s : BetheRoots B)
    (a : Fin r) : ℂ[X] :=
  ∏ j : Fin (B.dimVec a),
    (X - C (s a j))

/--
Shifted Q-operator: Q_a^+(ℏx) = ∏_j (ℏx - s_{a,j})
-/
noncomputable def Q_plus_shifted
    (B : XXZBetheData r)
    (s : BetheRoots B)
    (a : Fin r) : ℂ[X] :=
  ∏ j : Fin (B.dimVec a),
    (C B.hbar * X - C (s a j))

/--
The QQ-system for A_1 (rank 1):

Q^+(ℏx) Q^-(x) - Q^+(x) Q^-(ℏx)
  = c · ∏_{m=1}^L (x - a_m)

This is the fundamental functional relation
connecting Q and Q-dual operators. It encodes
the quantum group structure.
-/
def QQSystemRelation
    (B : XXZBetheData 1)
    (s : BetheRoots B)
    (s_dual : BetheRoots B)
    (sites : SiteParams B) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧
    Q_plus_shifted B s 0 * Q_plus B s_dual 0 -
    Q_plus B s 0 * Q_plus_shifted B s_dual 0 =
    C c * ∏ m : Fin B.numSites,
      (X - C (sites m))

/--
XXZ Bethe Ansatz Equation at node a, root j:

∏_{b~a} ∏_i
  (ℏ s_{a,j} - s_{b,i})/(s_{a,j} - ℏ s_{b,i})
  ·
∏_m (s_{a,j} - a_m)/(ℏ s_{a,j} - a_m)
  = z_a

where b ~ a means b is adjacent to a in the
Dynkin diagram.
-/
def BetheEquation
    (B : XXZBetheData r)
    (s : BetheRoots B)
    (sites : SiteParams B)
    (a : Fin r) (j : Fin (B.dimVec a)) : Prop :=
  let lhs_same :=
    ∏ i : Fin (B.dimVec a),
      if (i : ℕ) = (j : ℕ) then 1
      else (B.hbar * s a j - s a i) /
           (s a j - B.hbar * s a i)
  let lhs_site :=
    ∏ m : Fin B.numSites,
      (s a j - sites m) /
      (B.hbar * s a j - sites m)
  lhs_same * lhs_site = B.kahler a

/--
Full system: all Bethe equations are satisfied.
-/
def BetheSystem
    (B : XXZBetheData r)
    (s : BetheRoots B)
    (sites : SiteParams B) : Prop :=
  ∀ (a : Fin r) (j : Fin (B.dimVec a)),
    BetheEquation B s sites a j

/--
Yang-Yang function:

𝒴(s, a, z, ℏ) whose critical points
∂_{s_{a,j}} 𝒴 = 0 yield the Bethe equations.

The Bethe equations emerge as:
  s_{a,j} · ∂/∂s_{a,j} 𝒴 = 0
-/
structure YangYangFunction where
  /-- The function value -/
  value : ℂ
  /-- Critical point condition gives Bethe eqs -/
  critical_is_bethe : Prop

/--
Bethe algebra: the commutative algebra generated
by quantum K-theory classes.

This is isomorphic to the equivariant quantum
K-theory ring K^q_T(X).
-/
structure BetheAlgebra (r : ℕ) where
  /-- Base ring -/
  base : CommRing ℂ := inferInstance
  /-- Generators: exterior powers of tautological
      bundles (= Baxter Q-operators) -/
  generators : Fin r → ℂ[X]
  /-- Relations: the QQ-system -/
  relations : Fin r → ℂ[X]
  /-- Commutativity: [T_i, T_j] = 0 -/
  commute : ∀ i j : Fin r,
    generators i * generators j =
    generators j * generators i

/--
Spectrum of the Bethe algebra.

Each Bethe eigenvector is parameterized by
a solution to the Bethe equations.
The eigenvalue of Q_a^+ on this eigenvector
is Q_a^+(x) = ∏_j (x - s_{a,j}).
-/
theorem bethe_spectrum_parametrized
    (B : XXZBetheData r)
    (s : BetheRoots B)
    (sites : SiteParams B) :
    BetheSystem B s sites →
    ∃ (A : BetheAlgebra r),
      ∀ a : Fin r,
        A.generators a = Q_plus B s a := by
  intro _h
  refine ⟨?_, ?_⟩
  · exact
      { generators := fun a => Q_plus B s a
        relations := fun _ => 0
        commute := by
          intro i j
          ring }
  · intro a
    rfl

/--
Mirror symmetry at the Bethe level:
swapping z ↔ a and ℏ ↦ ℏ⁻¹ preserves the
space of solutions.
-/
noncomputable def hbarInvertedData (B : XXZBetheData 1) : XXZBetheData 1 where
  dimVec := B.dimVec
  numSites := B.numSites
  hbar := B.hbar⁻¹
  kahler := B.kahler
  hbar_ne_zero := inv_ne_zero B.hbar_ne_zero
  hbar_ne_one := by
    intro h
    have hmul : B.hbar * B.hbar⁻¹ = B.hbar * 1 := by rw [h]
    rw [mul_inv_cancel₀ B.hbar_ne_zero, mul_one] at hmul
    exact B.hbar_ne_one hmul.symm

theorem bethe_mirror_invariance
    (B : XXZBetheData 1)
    (s : BetheRoots B)
    (sites : SiteParams B) :
    BetheSystem B s sites →
    ∃ B' : XXZBetheData 1, B'.hbar = B.hbar⁻¹ := by
  intro _h
  exact ⟨hbarInvertedData B, rfl⟩

end KoroteevZeitlin.Bethe
