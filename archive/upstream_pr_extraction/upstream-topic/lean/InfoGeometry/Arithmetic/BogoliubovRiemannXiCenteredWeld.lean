import InfoGeometry.Arithmetic.RiemannXiV4CharacterBridge
import InfoGeometry.Canonical.BogoliubovCenteredMellinMoebiusWeld

/-!
# Centered Riemann coordinate and the existing Bogoliubov/Möbius owner

This is a thin arithmetic readout.  It does not define a new matrix, Fock
space, or quantization.  It identifies the real centered abscissa of the
existing `centeredPoint` chart with the rapidity used by the existing
Möbius/Bogoliubov owner for a Mellin mode.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.BogoliubovRiemannXiCenteredWeld

open InfoGeometry.Arithmetic.RiemannXiV4CharacterBridge
open InfoGeometry.Canonical.BogoliubovMellinKrein
open InfoGeometry.Canonical.BogoliubovCenteredMellinMoebiusWeld
open InfoGeometry.Canonical.MoebiusBogoliubovVirasoro

def centeredAbscissa (s : ℂ) : ℝ := s.re - 1 / 2

def centeredModeScale (n : ℕ) (s : ℂ) : ℝ :=
  Real.exp (bogoliubovRapidity n (centeredAbscissa s))

theorem centeredPoint_abscissa (u τ : ℝ) :
    centeredAbscissa (1 / 2 + centeredPoint u τ) = u := by
  simp [centeredAbscissa, centeredPoint]

theorem centeredAbscissa_eq_zero_iff (s : ℂ) :
    centeredAbscissa s = 0 ↔ s.re = 1 / 2 := by
  constructor <;> intro h
  · dsimp [centeredAbscissa] at h
    linarith
  · dsimp [centeredAbscissa]
    linarith

theorem centeredModeScale_log (n : ℕ) (s : ℂ) :
    Real.log (centeredModeScale n s) =
      bogoliubovRapidity n (centeredAbscissa s) := by
  exact Real.log_exp _

theorem centeredMode_unmixed_iff_of_one_lt
    (n : ℕ) (hn : 1 < n) (s : ℂ) :
    (bogoliubovTiltOfBoost (centeredModeScale n s)).v = 0 ↔
      s.re = 1 / 2 := by
  have hlog : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hn
  rw [show centeredModeScale n s =
      centeredMellinScale (bogoliubovRapidity n (centeredAbscissa s)) by
        rfl]
  rw [centeredMellinTilt_unmixed_iff]
  constructor
  · intro h
    have hrap : bogoliubovRapidity n (centeredAbscissa s) = 0 := h
    dsimp [bogoliubovRapidity] at hrap
    apply (centeredAbscissa_eq_zero_iff s).1
    exact (mul_eq_zero.mp hrap).resolve_right (ne_of_gt hlog)
  · intro h
    have hcenter : centeredAbscissa s = 0 :=
      (centeredAbscissa_eq_zero_iff s).2 h
    simp [bogoliubovRapidity, hcenter]

theorem criticalPoint_unmixed_of_mode
    (n : ℕ) (τ : ℝ) :
    (bogoliubovTiltOfBoost
      (centeredModeScale n (1 / 2 + centeredPoint 0 τ))).v = 0 := by
  change (bogoliubovTiltOfBoost
      (Real.exp (bogoliubovRapidity n
        (centeredAbscissa (1 / 2 + centeredPoint 0 τ))))).v = 0
  rw [centeredPoint_abscissa]
  simp [bogoliubovTiltOfBoost,
    InfoGeometry.Canonical.BogoliubovFockSuper.HyperbolicMixingParams.ofAngle,
    bogoliubovRapidity]

end InfoGeometry.Arithmetic.BogoliubovRiemannXiCenteredWeld
