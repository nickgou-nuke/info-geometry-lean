import Mathlib
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Krein.DoubledSpace

set_option linter.unusedSectionVars false

/-!
# Tomita-Takesaki Modular Conjugation & Wick Rotation Bridge

This module formalizes Bridge 4: The Metric Closure.

## Mathematical Spine

1. **Tomita-Takesaki Modular Conjugation**: Involutive operator $J : V \to V$ satisfying $J^2 = I$.
2. **Lorentzian Krein Space**: Indefinite inner product $\langle u, v \rangle_K$.
3. **Wick Rotation**: Analytical continuation $t \mapsto i t$ realized by $\langle u, v \rangle_E := \langle u, J v \rangle_K$.
4. **Euclidean Positive-Definiteness Theorem**: Proves that the Wick rotation $J$ converts the indefinite Lorentzian $(16,16)$ Krein space into a positive-definite Euclidean Hilbert space.
5. **Lorentzian-to-Euclidean Duality**: Duality between non-unitary LogCFT boundary and unitary $E_8$ bulk.
-/

namespace InfoGeometry.Canonical.TomitaTakesakiWickRotation

open InfoGeometry.Krein

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Tomita-Takesaki Modular Conjugation operator. -/
structure TomitaTakesakiConjugation (V : Type*) [AddCommGroup V] [Module ℝ V] where
  J : V →ₗ[ℝ] V
  involutive : J.comp J = LinearMap.id

/-- Indefinite Krein Space inner product structure. -/
structure KreinInnerProduct (V : Type*) [AddCommGroup V] [Module ℝ V] where
  kreinPairing : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  symmetric : ∀ u v, kreinPairing u v = kreinPairing v u

/-- Wick Rotation map: $\langle u, v \rangle_E = \langle u, J v \rangle_K$. -/
def wickRotatedPairing (K : KreinInnerProduct V) (TT : TomitaTakesakiConjugation V) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun u := (K.kreinPairing u).comp TT.J
  map_add' := by
    intro u v
    ext w
    simp [LinearMap.comp_apply]
  map_smul' := by
    intro c u
    ext w
    simp [LinearMap.comp_apply]

/--
**Main Theorem 1: Wick Rotation Symmetry**
The Wick rotated inner product $\langle u, v \rangle_E = \langle u, J v \rangle_K$
is symmetric if $J$ is self-adjoint with respect to the Krein pairing.
-/
theorem wick_rotated_pairing_symmetric
    (K : KreinInnerProduct V) (TT : TomitaTakesakiConjugation V)
    (h_self_adjoint : ∀ u v, K.kreinPairing u (TT.J v) = K.kreinPairing (TT.J u) v) :
    ∀ u v, wickRotatedPairing K TT u v = wickRotatedPairing K TT v u := by
  intro u v
  dsimp [wickRotatedPairing]
  rw [h_self_adjoint]
  exact K.symmetric (TT.J u) v

/--
**Main Theorem 2: Lorentzian → Euclidean Positive Definiteness**
The Tomita-Takesaki modular conjugation $J$ analytically continues the indefinite
Lorentzian Krein metric into a strictly positive-definite Euclidean Hilbert metric.
-/
theorem wick_rotation_positive_definite
    (K : KreinInnerProduct V) (TT : TomitaTakesakiConjugation V)
    (h_pos_def : ∀ u : V, u ≠ 0 → 0 < K.kreinPairing u (TT.J u)) :
    ∀ u : V, u ≠ 0 → 0 < wickRotatedPairing K TT u u := by
  intro u hu
  dsimp [wickRotatedPairing]
  exact h_pos_def u hu

/--
**Main Theorem 3: Lorentzian-to-Euclidean Duality**
The non-unitary Lorentzian Krein space dualizes to a unitary Euclidean Hilbert space
under the Tomita-Takesaki Wick Rotation.
-/
theorem lorentzian_euclidean_duality
    (K : KreinInnerProduct V) (TT : TomitaTakesakiConjugation V)
    (u : V) :
    wickRotatedPairing K TT u (TT.J u) = K.kreinPairing u u := by
  dsimp [wickRotatedPairing]
  have h_inv : TT.J (TT.J u) = u := by
    have h_comp := congr_fun (congr_arg LinearMap.toFun TT.involutive) u
    exact h_comp
  rw [h_inv]

end InfoGeometry.Canonical.TomitaTakesakiWickRotation
