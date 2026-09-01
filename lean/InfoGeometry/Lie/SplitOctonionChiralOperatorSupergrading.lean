import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis

/-!
# Native operator supergrading from split-octonion derivations

This owner records the exact operator-level statement that is valid for a
multiplication derivation of the canonical split-octonion Zorn carrier.

For any derivation `D` and any state `x`, the commutator with left regular
multiplication satisfies

`[D, Lₓ] = L_(D x)`.

Consequently, whenever `x` is a `D`-eigenstate with eigenvalue `λ`, its left
regular multiplication operator is an eigenoperator for the adjoint action of
`D` with the same eigenvalue.

The concrete application below uses the genuine traceless Cartan derivations
`axialCartanEnd k` from `SplitOctonionAxialCartanDerivation`.  The separate
uniform tripotent `axialGrading` is intentionally not used as a derivation:
that owner already proves `axialGrading_not_derivation`.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading

open scoped BigOperators
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ

/-- The native left-regular operator, reusing the genuine circular Peirce
owner rather than creating a second multiplication representation. -/
noncomputable def leftRegular (x : CZ) : EndCZ :=
  leftMultiplication x

@[simp] theorem leftRegular_apply (x y : CZ) :
    leftRegular x y = x * y :=
  rfl

/-- A genuine derivation acts on the left-regular representation by the
expected commutator identity `[D,Lₓ] = L_(D x)`.  No associativity assumption
is used; the proof is exactly the Leibniz law. -/
theorem derivation_lie_leftRegular
    (D : EndCZ) (hD : IsDerivation D) (x : CZ) :
    ⁅D, leftRegular x⁆ = leftRegular (D x) := by
  rw [LieRing.of_associative_ring_bracket]
  apply LinearMap.ext
  intro y
  change D (x * y) - x * D y = D x * y
  rw [hD x y]
  abel

/-- Eigenstate-to-eigenoperator lift for any native split-octonion derivation. -/
theorem eigenstate_leftRegular_eigenoperator
    (D : EndCZ) (hD : IsDerivation D)
    (x : CZ) (λ : ℝ) (hx : D x = λ • x) :
    ⁅D, leftRegular x⁆ = λ • leftRegular x := by
  rw [derivation_lie_leftRegular D hD x, hx]
  apply LinearMap.ext
  intro y
  change (λ • x) * y = λ • (x * y)
  rw [smul_mul]

/-- The traceless axial Cartan derivation therefore gives the exact operator
supergrading on every native upper chiral root operator. -/
theorem axialCartan_upper_eigenoperator
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (i : Fin 3) :
    ⁅axialCartanEnd k, leftRegular (chiralUpperBasis i)⁆ =
      k i • leftRegular (chiralUpperBasis i) := by
  exact eigenstate_leftRegular_eigenoperator
    (axialCartanEnd k) (axialCartanEnd_isDerivation k hk)
    (chiralUpperBasis i) (k i) (axialCartanEnd_chiralUpperBasis k i)

/-- The lower chiral root operators have the opposite Cartan weight. -/
theorem axialCartan_lower_eigenoperator
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (i : Fin 3) :
    ⁅axialCartanEnd k, leftRegular (chiralLowerBasis i)⁆ =
      (-k i) • leftRegular (chiralLowerBasis i) := by
  exact eigenstate_leftRegular_eigenoperator
    (axialCartanEnd k) (axialCartanEnd_isDerivation k hk)
    (chiralLowerBasis i) (-k i) (axialCartanEnd_chiralLowerBasis k i)

/-- The same theorem written on the circular `rootPlus` coordinate readout.
The existing circular-basis bridge identifies its canonical Zorn image with
`chiralUpperBasis`. -/
theorem axialCartan_circular_rootPlus_eigenoperator
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (i : Fin 3) :
    ⁅axialCartanEnd k,
        leftRegular (cartesianZornLinearEquiv
          (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootPlus i))⁆ =
      k i • leftRegular (cartesianZornLinearEquiv
        (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootPlus i)) := by
  simpa using axialCartan_upper_eigenoperator k hk i

/-- Circular negative roots lift to eigenoperators of the opposite weight. -/
theorem axialCartan_circular_rootMinus_eigenoperator
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (i : Fin 3) :
    ⁅axialCartanEnd k,
        leftRegular (cartesianZornLinearEquiv
          (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootMinus i))⁆ =
      (-k i) • leftRegular (cartesianZornLinearEquiv
        (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootMinus i)) := by
  simpa using axialCartan_lower_eigenoperator k hk i

/-- The two diagonal Peirce projectors are stationary under every traceless
axial Cartan derivation. -/
@[simp] theorem axialCartan_zornPlus (k : Fin 3 → ℝ) :
    axialCartanEnd k (zornPlus : CZ) = 0 := by
  ext i <;> simp [axialCartanEnd, zornPlus]

@[simp] theorem axialCartan_zornMinus (k : Fin 3 → ℝ) :
    axialCartanEnd k (zornMinus : CZ) = 0 := by
  ext i <;> simp [axialCartanEnd, zornMinus]

/-- Hence the positive Peirce projector operator has Cartan operator grade zero. -/
theorem axialCartan_zornPlus_operator_grade_zero
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) :
    ⁅axialCartanEnd k, leftRegular (zornPlus : CZ)⁆ = 0 := by
  rw [derivation_lie_leftRegular (axialCartanEnd k)
    (axialCartanEnd_isDerivation k hk), axialCartan_zornPlus]
  apply LinearMap.ext
  intro y
  rfl

/-- The negative Peirce projector operator also has Cartan operator grade zero. -/
theorem axialCartan_zornMinus_operator_grade_zero
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) :
    ⁅axialCartanEnd k, leftRegular (zornMinus : CZ)⁆ = 0 := by
  rw [derivation_lie_leftRegular (axialCartanEnd k)
    (axialCartanEnd_isDerivation k hk), axialCartan_zornMinus]
  apply LinearMap.ext
  intro y
  rfl

/-- Compact packet: the native chiral regular operators carry the Cartan
operator grading `0, +kᵢ, -kᵢ`. -/
theorem axialCartan_chiral_operator_packet
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (i : Fin 3) :
    ⁅axialCartanEnd k, leftRegular (zornPlus : CZ)⁆ = 0 ∧
    ⁅axialCartanEnd k, leftRegular (chiralUpperBasis i)⁆ =
      k i • leftRegular (chiralUpperBasis i) ∧
    ⁅axialCartanEnd k, leftRegular (chiralLowerBasis i)⁆ =
      (-k i) • leftRegular (chiralLowerBasis i) ∧
    ⁅axialCartanEnd k, leftRegular (zornMinus : CZ)⁆ = 0 := by
  exact ⟨axialCartan_zornPlus_operator_grade_zero k hk,
    axialCartan_upper_eigenoperator k hk i,
    axialCartan_lower_eigenoperator k hk i,
    axialCartan_zornMinus_operator_grade_zero k hk⟩

end InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading
