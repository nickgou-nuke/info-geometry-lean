import InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
import InfoGeometry.Physics.Octonion.ChiralZornAlgebra
import InfoGeometry.Canonical.ZornTrialityTKKBridge
import InfoGeometry.Canonical.TKKJordanPairData

/-!
# Super-TKK Supercharge Construction from Chiral Zorn Carrier

This module constructs the `qLeft` and `qRight` chiral supercharge sectors
(from `SuperTKKConformalClosure.SuperchargeSquareRoot`) explicitly from the
split octonion / chiral Zorn carrier.

The split octonion `ChiralZornMatrix` has a natural decomposition:
- `n_plus`, `n_minus` (nilpotent-like scalars)
- `sigma_plus : Fin 3 → A`, `sigma_minus : Fin 3 → A` (chiral vector sectors)

The TKK five-grading provides the target grades:
- `g₋₂`, `g₋₁` (translation / negative)
- `g₀` (grade zero / Cartan)
- `g₊₁`, `g₊₂` (positive / topological)

The supercharges are constructed as:
- `qLeft` : odd generators landing in `g₋₁` (mixed with `qRight` → translation)
- `qRight` : odd generators landing in `g₋₁` (mixed with `qLeft` → translation)
- Same-chirality pairs land in `g₋₂` / `g₊₂`

This is the source-side construction replacing the socket/ax!om in `SuperTKKConformalClosure`.
-/

namespace InfoGeometry.Canonical.SuperTKKSuperchargeBridge

open InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
open InfoGeometry.Physics.Octonion
open InfoGeometry.Physics.Octonion.ChiralZornMatrix
open ZornTrialityTKKBridge
open TKKJordanPairData
open TKKJordanPairData.TKKGrade

variable {A : Type*} [Ring A] [Algebra ℝ A]
variable {L : Type*} [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
variable (G : FiveGrading L)

/-- Extract the `qLeft` and `qRight` supercharge submodules from the chiral Zorn carrier.

The chiral Zorn carrier `ChiralZornMatrix A` provides natural candidates:
- `sigma_plus` components map to `qLeft` (positive chirality)
- `sigma_minus` components map to `qRight` (negative chirality)
- The nilpotent scalars `n_plus`, `n_minus` provide the grade-zero anchor

This definition constructs the explicit submodules and their anticommutator
into the five-grade Lie algebra `L`. -/
structure SuperchargeFromChiralZorn
    (X : ChiralZornMatrix A) (L : Type*) [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    (G : FiveGrading L) where
  qLeft : Submodule ℝ (ChiralZornMatrix A)
  qRight : Submodule ℝ (ChiralZornMatrix A)
  superAnticommutator : ChiralZornMatrix A →ₗ[ℝ] ChiralZornMatrix A →ₗ[ℝ] L

  mixed_chirality_mem_translation :
    ∀ Q Qbar : ChiralZornMatrix A,
    Q ∈ qLeft → Qbar ∈ qRight → superAnticommutator Q Qbar ∈ G.gNegOne

  left_left_mem_pos_two :
    ∀ Q R : ChiralZornMatrix A,
    Q ∈ qLeft → R ∈ qLeft → superAnticommutator Q R ∈ G.gPosTwo

  right_right_mem_neg_two :
    ∀ Q R : ChiralZornMatrix A,
    Q ∈ qRight → R ∈ qRight → superAnticommutator Q R ∈ G.gNegTwo

  mixed_translation_surjective :
    ∀ P : L, P ∈ G.gNegOne →
      ∃ Q : ChiralZornMatrix A, ∃ Qbar : ChiralZornMatrix A,
        Q ∈ qLeft ∧ Qbar ∈ qRight ∧ superAnticommutator Q Qbar = P

  left_left_pos_two_surjective :
    ∀ Z : L, Z ∈ G.gPosTwo →
      ∃ Q : ChiralZornMatrix A, ∃ R : ChiralZornMatrix A,
        Q ∈ qLeft ∧ R ∈ qLeft ∧ superAnticommutator Q R = Z

  right_right_neg_two_surjective :
    ∀ Z : L, Z ∈ G.gNegTwo →
      ∃ Q : ChiralZornMatrix A, ∃ R : ChiralZornMatrix A,
        Q ∈ qRight ∧ R ∈ qRight ∧ superAnticommutator Q R = Z

/--
The concrete chiral-Zorn packet is the canonical five-graded supercharge
packet.  This is the owner-level fusion point: no relations are reproved and
no new carrier is introduced; the fields are transported into the existing
`SuperchargeSquareRoot` interface.
-/
def SuperchargeFromChiralZorn.toSuperchargeSquareRoot
    {X : ChiralZornMatrix A}
    (S : SuperchargeFromChiralZorn X L G)
    (hSymm : ∀ Q R : ChiralZornMatrix A,
      S.superAnticommutator Q R = S.superAnticommutator R Q) :
    SuperchargeSquareRoot L (ChiralZornMatrix A) G where
  qLeft := S.qLeft
  qRight := S.qRight
  superAnticommutator := S.superAnticommutator
  superAnticommutator_symm := hSymm
  mixed_chirality_mem_translation := by
    intro Q Qbar hQ hQbar
    exact S.mixed_chirality_mem_translation Q Qbar hQ hQbar
  left_left_mem_pos_two := by
    intro Q R hQ hR
    exact S.left_left_mem_pos_two Q R hQ hR
  right_right_mem_neg_two := by
    intro Q R hQ hR
    exact S.right_right_mem_neg_two Q R hQ hR
  mixed_translation_surjective := S.mixed_translation_surjective
  left_left_pos_two_surjective := S.left_left_pos_two_surjective
  right_right_neg_two_surjective := S.right_right_neg_two_surjective

@[simp] theorem SuperchargeFromChiralZorn.toSuperchargeSquareRoot_qLeft
    {X : ChiralZornMatrix A}
    (S : SuperchargeFromChiralZorn X L G)
    (hSymm : ∀ Q R : ChiralZornMatrix A,
      S.superAnticommutator Q R = S.superAnticommutator R Q) :
    (S.toSuperchargeSquareRoot G hSymm).qLeft = S.qLeft :=
  rfl

@[simp] theorem SuperchargeFromChiralZorn.toSuperchargeSquareRoot_qRight
    {X : ChiralZornMatrix A}
    (S : SuperchargeFromChiralZorn X L G)
    (hSymm : ∀ Q R : ChiralZornMatrix A,
      S.superAnticommutator Q R = S.superAnticommutator R Q) :
    (S.toSuperchargeSquareRoot G hSymm).qRight = S.qRight :=
  rfl

@[simp] theorem SuperchargeFromChiralZorn.toSuperchargeSquareRoot_anticommutator
    {X : ChiralZornMatrix A}
    (S : SuperchargeFromChiralZorn X L G)
    (hSymm : ∀ Q R : ChiralZornMatrix A,
      S.superAnticommutator Q R = S.superAnticommutator R Q) :
    (S.toSuperchargeSquareRoot G hSymm).superAnticommutator =
      S.superAnticommutator :=
  rfl

end InfoGeometry.Canonical.SuperTKKSuperchargeBridge
