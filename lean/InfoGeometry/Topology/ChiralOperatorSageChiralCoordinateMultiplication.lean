import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ChiralOperatorSageTranslation
import InfoGeometry.Topology.ChiralOperatorZornTopologicalMultiplication

/-!
# Native multiplication in chiral operator coordinates

This owner exposes the existing operator-valued Zorn multiplication directly
on `(u+, s+) × (u-, s-)`.  The vector entries remain elements of the possibly
noncommutative coefficient algebra, so the cross terms retain commutators.
No associativity of this displayed multiplication is asserted.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Algebra
open InfoGeometry.Canonical

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]

def operatorSageTopologicalToChiral
    (X : OperatorSageTopologicalCarrier A) :
    ChiralConeCoordinates A :=
  ((X.1, X.2.2.1), (X.2.1, X.2.2.2))

def operatorSageChiralToTopological
    (X : ChiralConeCoordinates A) :
    OperatorSageTopologicalCarrier A :=
  (X.1.1, X.2.1, X.1.2, X.2.2)

@[simp] theorem operatorSageChiralToTopological_toChiral
    (X : ChiralConeCoordinates A) :
    operatorSageTopologicalToChiral
      (operatorSageChiralToTopological X) = X := by
  rcases X with ⟨⟨uPlus, sPlus⟩, ⟨uMinus, sMinus⟩⟩
  rfl

@[simp] theorem operatorSageTopologicalToChiral_toTopological
    (X : OperatorSageTopologicalCarrier A) :
    operatorSageChiralToTopological
      (operatorSageTopologicalToChiral X) = X := by
  rcases X with ⟨uPlus, uMinus, sPlus, sMinus⟩
  rfl

def operatorSageChiralMul
    (X Y : ChiralConeCoordinates A) :
    ChiralConeCoordinates A :=
  ((X.1.1 * Y.1.1 + operatorDot X.1.2 Y.2.2,
      fun c => X.1.1 * Y.1.2 c + X.1.2 c * Y.2.1 -
        operatorCross X.2.2 Y.2.2 c),
    (X.2.1 * Y.2.1 + operatorDot X.2.2 Y.1.2,
      fun c => X.2.1 * Y.2.2 c + X.2.2 c * Y.1.1 +
        operatorCross X.1.2 Y.1.2 c))

theorem operatorSageTopologicalToChiral_mul
    (X Y : OperatorSageTopologicalCarrier A) :
    operatorSageTopologicalToChiral
        (operatorSageTopologicalMul X Y) =
      operatorSageChiralMul
        (operatorSageTopologicalToChiral X)
        (operatorSageTopologicalToChiral Y) := by
  rfl

theorem continuous_operatorSageTopologicalToChiral :
    Continuous (operatorSageTopologicalToChiral (A := A)) := by
  change Continuous (fun X : OperatorSageTopologicalCarrier A =>
    ((X.1, X.2.2.1), (X.2.1, X.2.2.2)))
  exact
    (continuous_fst.prodMk
      (continuous_fst.comp (continuous_snd.comp continuous_snd))).prodMk
      ((continuous_fst.comp continuous_snd).prodMk
        (continuous_snd.comp (continuous_snd.comp continuous_snd)))

theorem continuous_operatorSageChiralToTopological :
    Continuous (operatorSageChiralToTopological (A := A)) := by
  change Continuous (fun X : ChiralConeCoordinates A =>
    (X.1.1, X.2.1, X.1.2, X.2.2))
  exact
    (continuous_fst.comp continuous_fst).prodMk
      ((continuous_fst.comp continuous_snd).prodMk
        ((continuous_snd.comp continuous_fst).prodMk
          (continuous_snd.comp continuous_snd)))

theorem operatorSageChiralMul_toTopological
    (X Y : ChiralConeCoordinates A) :
    operatorSageChiralToTopological
        (operatorSageChiralMul X Y) =
      operatorSageTopologicalMul
        (operatorSageChiralToTopological X)
        (operatorSageChiralToTopological Y) := by
  rfl

theorem continuous_operatorSageChiralMul :
    Continuous (fun p : ChiralConeCoordinates A ×
      ChiralConeCoordinates A =>
      operatorSageChiralMul p.1 p.2) := by
  have hfun :
      (fun p : ChiralConeCoordinates A × ChiralConeCoordinates A =>
        operatorSageChiralMul p.1 p.2) =
      (fun p : ChiralConeCoordinates A × ChiralConeCoordinates A =>
        operatorSageTopologicalToChiral
          (operatorSageTopologicalMul
            (operatorSageChiralToTopological p.1)
            (operatorSageChiralToTopological p.2))) := by
    funext p
    exact congrArg operatorSageTopologicalToChiral
      (operatorSageChiralMul_toTopological p.1 p.2).symm
  rw [hfun]
  exact continuous_operatorSageTopologicalToChiral.comp
    (continuous_operatorSageTopologicalMul.comp
      ((continuous_operatorSageChiralToTopological.comp continuous_fst).prodMk
        (continuous_operatorSageChiralToTopological.comp continuous_snd)))

end
end InfoGeometry.Topology
