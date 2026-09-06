import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

structure PhaseSpace where
  q : ℝ
  p : ℝ

structure WignerDistribution where
  W : PhaseSpace → ℝ

structure MadelungFluid where
  rho : PhaseSpace → ℝ
  S : PhaseSpace → ℝ

def wigner_to_madelung (w : WignerDistribution) : MadelungFluid :=
  { rho := w.W
    S := fun x => x.q * x.p }

def phaseFlip (x : PhaseSpace) : PhaseSpace :=
  { q := -x.q
    p := -x.p }

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
  have hmul : (-x.q) * (-x.p) = x.q * x.p := by
    ring
  simp [wigner_to_madelung, phaseFlip, hmul]

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
