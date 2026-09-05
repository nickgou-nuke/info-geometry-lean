import InfoGeometry.Analysis.BipolarMobiusPunctureEquiv
import InfoGeometry.Canonical.BipolarLogSL2
import Mathlib.Tactic

/-!
# Square-root cover and half-Cartan spinorial descent

The bipolar coordinate does not define physical spin.  It canonically defines
a different, precise object: the square-root cover

`{(s,z) | z^2 = q(s)}`

over the twice-punctured plane.  The deck involution sends `z` to `-z`.
The diagonal half-Cartan lift changes by the central sign `-I` under this deck
transformation, while its conjugation action on matrix observables is
unchanged.

This is the exact finite mechanism called here *monodromy-induced
spinoriality* or the *half-weight descent obstruction*.  It is weaker than a
spin structure on a tangent frame bundle and weaker than a classification of
`Spin(p,q)` representations.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarSquareRootSpinorialDescent

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarMobiusPunctureEquiv
open InfoGeometry.Canonical.BipolarLogSL2

abbrev Matrix2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev Spinor2 := Fin 2 → ℂ

/-- A point of the pullback of the squaring map along `q`. -/
structure SquareRootPoint where
  base : SourcePoint
  root : ℂ
  root_sq : root ^ 2 = crossRatio01 (base : ℂ)

@[ext] theorem SquareRootPoint.ext
    {p q : SquareRootPoint}
    (hbase : p.base = q.base) (hroot : p.root = q.root) : p = q := by
  cases p
  cases q
  cases hbase
  cases hroot
  rfl

/-- Projection of the square-root cover to the base. -/
def projection (p : SquareRootPoint) : SourcePoint := p.base

/-- The square root is nonzero because `q` is nonzero on the punctured base. -/
theorem root_ne_zero (p : SquareRootPoint) : p.root ≠ 0 := by
  intro h
  have hq : crossRatio01 (p.base : ℂ) = 0 := by
    rw [← p.root_sq, h]
    norm_num
  exact (crossRatio01_ne_zero p.base.property) hq

/-- Nontrivial deck transformation of the square-root cover. -/
def deck (p : SquareRootPoint) : SquareRootPoint where
  base := p.base
  root := -p.root
  root_sq := by
    simpa using p.root_sq

@[simp] theorem projection_deck (p : SquareRootPoint) :
    projection (deck p) = projection p := rfl

/-- The deck transformation is an involution. -/
@[simp] theorem deck_involutive (p : SquareRootPoint) :
    deck (deck p) = p := by
  apply SquareRootPoint.ext
  · rfl
  · simp [deck]

/-- The cover has no deck-fixed point over the punctured base. -/
theorem deck_ne_self (p : SquareRootPoint) : deck p ≠ p := by
  intro h
  have hr : -p.root = p.root :=
    congrArg SquareRootPoint.root h
  have hsum : p.root + p.root = 0 := by
    calc
      p.root + p.root = -p.root + p.root := by rw [hr]
      _ = 0 := neg_add_cancel p.root
  have htwo : (2 : ℂ) * p.root = 0 := by
    simpa [two_mul] using hsum
  have hroot : p.root = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact root_ne_zero p hroot

/-- Any two square roots in one fibre differ by at most the deck sign. -/
theorem roots_eq_or_eq_neg
    {s : SourcePoint} {z w : ℂ}
    (hz : z ^ 2 = crossRatio01 (s : ℂ))
    (hw : w ^ 2 = crossRatio01 (s : ℂ)) :
    w = z ∨ w = -z := by
  have hfac : (w - z) * (w + z) = 0 := by
    calc
      (w - z) * (w + z) = w ^ 2 - z ^ 2 := by ring
      _ = 0 := by rw [hw, hz, sub_self]
  rcases mul_eq_zero.mp hfac with hminus | hplus
  · exact Or.inl (sub_eq_zero.mp hminus)
  · right
    calc
      w = (w + z) - z := by ring
      _ = 0 - z := by rw [hplus]
      _ = -z := by ring

/-- Determinant-one half-Cartan lift defined without choosing a logarithm. -/
def squareRootCartanLift (p : SquareRootPoint) : Matrix2C :=
  !![p.root, 0;
     0, p.root⁻¹]

/-- The square-root lift lies in the determinant-one matrix locus. -/
theorem squareRootCartanLift_det (p : SquareRootPoint) :
    Matrix.det (squareRootCartanLift p) = 1 := by
  simp [squareRootCartanLift, Matrix.det_fin_two, root_ne_zero p]

/-- Deck exchange acts on the fundamental lift by the central sign. -/
theorem squareRootCartanLift_deck (p : SquareRootPoint) :
    squareRootCartanLift (deck p) = -squareRootCartanLift p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [squareRootCartanLift, deck]

/-- Explicit action of the half-Cartan lift on its two-component fundamental
carrier. -/
def fundamentalAction (p : SquareRootPoint) (ψ : Spinor2) : Spinor2 :=
  ![p.root * ψ 0, p.root⁻¹ * ψ 1]

/-- The fundamental carrier detects the deck sign. -/
theorem fundamentalAction_deck
    (p : SquareRootPoint) (ψ : Spinor2) :
    fundamentalAction (deck p) ψ = -fundamentalAction p ψ := by
  funext i
  fin_cases i <;>
    simp [fundamentalAction, deck]

/-- Matrix/Hermitian-style conjugation action of the half-Cartan lift. -/
def observableAction
    (p : SquareRootPoint) (X : Matrix2C) : Matrix2C :=
  squareRootCartanLift p * X * (squareRootCartanLift p)ᴴ

/-- The observable action descends to the base because the central deck sign
cancels in conjugation. -/
theorem observableAction_deck
    (p : SquareRootPoint) (X : Matrix2C) :
    observableAction (deck p) X = observableAction p X := by
  rw [observableAction, observableAction, squareRootCartanLift_deck]
  simp

/-- Two applications of the deck transformation restore the fundamental
carrier. -/
theorem fundamentalAction_two_deck
    (p : SquareRootPoint) (ψ : Spinor2) :
    fundamentalAction (deck (deck p)) ψ = fundamentalAction p ψ := by
  rw [deck_involutive]

/-- The squared root recovers the base multiplicative character. -/
theorem root_sq_eq_base_character (p : SquareRootPoint) :
    p.root ^ 2 = crossRatio01 ((projection p : SourcePoint) : ℂ) :=
  p.root_sq

/-- Compact half-weight descent packet. -/
theorem bipolar_square_root_spinorial_descent_packet
    (p : SquareRootPoint) (ψ : Spinor2) (X : Matrix2C) :
    deck (deck p) = p ∧
      deck p ≠ p ∧
      Matrix.det (squareRootCartanLift p) = 1 ∧
      squareRootCartanLift (deck p) = -squareRootCartanLift p ∧
      fundamentalAction (deck p) ψ = -fundamentalAction p ψ ∧
      observableAction (deck p) X = observableAction p X := by
  exact ⟨deck_involutive p, deck_ne_self p,
    squareRootCartanLift_det p, squareRootCartanLift_deck p,
    fundamentalAction_deck p ψ, observableAction_deck p X⟩

end InfoGeometry.Canonical.BipolarSquareRootSpinorialDescent
