import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

abbrev PhaseSpace := ℝ × ℝ

namespace PhaseSpace

abbrev q (x : PhaseSpace) : ℝ := x.1

abbrev p (x : PhaseSpace) : ℝ := x.2

end PhaseSpace

abbrev WignerDistribution := PhaseSpace → ℝ

namespace WignerDistribution

abbrev W (w : WignerDistribution) : PhaseSpace → ℝ := w

end WignerDistribution

abbrev MadelungFluid := (PhaseSpace → ℝ) × (PhaseSpace → ℝ)

namespace MadelungFluid

abbrev rho (M : MadelungFluid) : PhaseSpace → ℝ := M.1

abbrev S (M : MadelungFluid) : PhaseSpace → ℝ := M.2

end MadelungFluid

def wigner_to_madelung (w : WignerDistribution) : MadelungFluid :=
  (w.W, fun x => x.q * x.p)

def phaseFlip (x : PhaseSpace) : PhaseSpace :=
  (-x.q, -x.p)

theorem wigner_madelung_density_projection
    (w : WignerDistribution) (x : PhaseSpace) :
    (wigner_to_madelung w).rho x = w.W x := by
  show w.W x = w.W x
  exact Eq.refl (w.W x)

theorem wigner_madelung_phase_action
    (w : WignerDistribution) (x : PhaseSpace) :
    (wigner_to_madelung w).S x = x.q * x.p := by
  show x.q * x.p = x.q * x.p
  exact Eq.refl (x.q * x.p)

theorem madelung_phase_even_under_phase_flip
    (w : WignerDistribution) (x : PhaseSpace) :
    (wigner_to_madelung w).S (phaseFlip x) =
      (wigner_to_madelung w).S x := by
  change (-x.q) * (-x.p) = x.q * x.p
  ring

structure KreinSpace where
  indefinite_metric : ℝ → ℝ → ℝ
  parity : ℝ → ℝ
  parity_isometry :
    ∀ x y : ℝ, indefinite_metric (parity x) (parity y) = indefinite_metric x y

def chiral_orientability (k : KreinSpace) : Prop :=
  ∀ x y : ℝ, k.indefinite_metric (k.parity x) (k.parity y) =
    k.indefinite_metric x y

theorem krein_orientability_from_parity_isometry (k : KreinSpace) :
    chiral_orientability k := by
  intro x y
  exact k.parity_isometry x y

theorem krein_line_metric_parity (k : KreinSpace) (x : ℝ) :
    k.indefinite_metric (k.parity x) (k.parity x) =
      k.indefinite_metric x x := by
  exact k.parity_isometry x x
