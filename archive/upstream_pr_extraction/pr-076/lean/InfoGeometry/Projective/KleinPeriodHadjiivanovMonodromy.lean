import InfoGeometry.Projective.KleinQuadricLogDeRhamClass
import InfoGeometry.Projective.HadjiivanovLogConnectionReadoutBridge

/-!
# Winding periods and square-zero logarithmic monodromy

The existing Klein logarithmic period laws and the existing square-zero
residue readout compose on the same additive winding parameter.  This file
contains only the resulting product identities; it does not introduce an
analytic holonomy or a manifold de Rham complex.
-/

namespace InfoGeometry.Projective.KleinPeriodHadjiivanovMonodromy

open InfoGeometry.Projective.KleinQuadric.LogDeRhamClass
open InfoGeometry.Projective.HadjiivanovLogConnectionBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionKleinBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionReadoutBridge
open InfoGeometry.Clifford.LogCftMonodromy

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem lcftPhase_nat_pow_eq_windingAddChar
    (h : ℝ) (n : ℕ) :
    lcftPhase (h : ℂ) ^ n =
      (windingAddChar (-h) (n : ℤ) : ℂ) := by
  rw [windingAddChar_apply_coe]
  unfold lcftPhase windingCharacter
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem unipotentResidueReadout_winding_add
    (R : LogResidue V) (radius : ℝ) (hradius : 0 < radius)
    (m n : ℤ) :
    (unipotentResidueReadout R ((m : ℂ) * logarithmicPeriod radius)).comp
        (unipotentResidueReadout R ((n : ℂ) * logarithmicPeriod radius)) =
      unipotentResidueReadout R
        (((m + n : ℤ) : ℂ) * logarithmicPeriod radius) := by
  rw [unipotentResidueReadout_comp]
  rw [← klein_logarithmic_period_class_add radius hradius m n]

noncomputable def unipotentWindingEndRepresentation
    (R : LogResidue V) (radius : ℝ) (hradius : 0 < radius) :
    Multiplicative ℤ →* Function.End V where
  toFun n :=
    fun v =>
      unipotentResidueReadout R
        (((Multiplicative.toAdd n : ℤ) : ℂ) * logarithmicPeriod radius) v
  map_one' := by
    funext v
    rw [show Multiplicative.toAdd (1 : Multiplicative ℤ) = 0 by rfl]
    simp only [Int.cast_zero, zero_mul]
    change unipotentResidueReadout R (0 : ℂ) v = v
    simp [unipotentResidueReadout]
  map_mul' := by
    intro m n
    funext v
    have h := congrArg (fun L : V →ₗ[ℂ] V => L v)
      (unipotentResidueReadout_winding_add R radius hradius
        (Multiplicative.toAdd m) (Multiplicative.toAdd n)).symm
    exact h

theorem unipotentWindingEndRepresentation_eq_one_iff
    (R : LogResidue V) (hN : R.nilpotent ≠ 0)
    (radius : ℝ) (hradius : 0 < radius) (n : Multiplicative ℤ) :
    unipotentWindingEndRepresentation R radius hradius n = 1 ↔
      Multiplicative.toAdd n = 0 := by
  constructor
  · intro h
    have hlin :
        unipotentResidueReadout R
            (((Multiplicative.toAdd n : ℤ) : ℂ) * logarithmicPeriod radius) =
          LinearMap.id := by
      ext v
      have hv := congrFun h v
      change unipotentResidueReadout R
          (((Multiplicative.toAdd n : ℤ) : ℂ) * logarithmicPeriod radius) v = v
        at hv
      exact hv
    have hp :=
      (unipotentResidueReadout_eq_id_iff R hN
        (((Multiplicative.toAdd n : ℤ) : ℂ) * logarithmicPeriod radius)).mp hlin
    have hperiod : logarithmicPeriod radius ≠ 0 :=
      logarithmicPeriod_ne_zero radius hradius
    have hcast : ((Multiplicative.toAdd n : ℤ) : ℂ) = 0 := by
      exact (mul_eq_zero.mp hp).resolve_right hperiod
    exact_mod_cast hcast
  · intro hn
    have hlin :
        unipotentResidueReadout R
            (((Multiplicative.toAdd n : ℤ) : ℂ) * logarithmicPeriod radius) =
          LinearMap.id := by
      apply (unipotentResidueReadout_eq_id_iff R hN _).mpr
      rw [hn]
      simp
    funext v
    change unipotentResidueReadout R
        (((Multiplicative.toAdd n : ℤ) : ℂ) * logarithmicPeriod radius) v = v
    exact congrArg (fun L : V →ₗ[ℂ] V => L v) hlin

theorem unipotentWindingEndRepresentation_neg_mul
    (R : LogResidue V) (radius : ℝ) (hradius : 0 < radius)
    (n : ℤ) :
    unipotentWindingEndRepresentation R radius hradius
        (Multiplicative.ofAdd (-n)) *
        unipotentWindingEndRepresentation R radius hradius
          (Multiplicative.ofAdd n) = 1 := by
  have h :=
    (unipotentWindingEndRepresentation R radius hradius).map_mul
      (Multiplicative.ofAdd (-n)) (Multiplicative.ofAdd n)
  simpa using h.symm

theorem unipotentWindingEndRepresentation_mul_neg
    (R : LogResidue V) (radius : ℝ) (hradius : 0 < radius)
    (n : ℤ) :
    unipotentWindingEndRepresentation R radius hradius
        (Multiplicative.ofAdd n) *
        unipotentWindingEndRepresentation R radius hradius
          (Multiplicative.ofAdd (-n)) = 1 := by
  have h :=
    (unipotentWindingEndRepresentation R radius hradius).map_mul
      (Multiplicative.ofAdd n) (Multiplicative.ofAdd (-n))
  simpa using h.symm

theorem unipotentResidueReadout_winding_neg
    (R : LogResidue V) (radius : ℝ) (hradius : 0 < radius)
    (n : ℤ) :
    unipotentResidueReadout (reverseResidue R)
        ((n : ℂ) * logarithmicPeriod radius) =
      unipotentResidueReadout R
        (((-n : ℤ) : ℂ) * logarithmicPeriod radius) := by
  calc
    unipotentResidueReadout (reverseResidue R)
        ((n : ℂ) * logarithmicPeriod radius) =
        unipotentResidueReadout R
          (-((n : ℂ) * logarithmicPeriod radius)) := by
            simpa using
              (unipotentResidueReadout_reverse R
                (-((n : ℂ) * logarithmicPeriod radius)))
    _ = unipotentResidueReadout R
        (((-n : ℤ) : ℂ) * logarithmicPeriod radius) := by
          rw [klein_logarithmic_period_class_neg radius hradius n]

theorem unipotentResidueReadout_winding_eq_id_iff
    (R : LogResidue V) (hN : R.nilpotent ≠ 0)
    (radius : ℝ) (hradius : 0 < radius) (n : ℤ) :
    unipotentResidueReadout R
        ((n : ℂ) * logarithmicPeriod radius) = LinearMap.id ↔
      n = 0 := by
  rw [unipotentResidueReadout_eq_id_iff R hN]
  constructor
  · intro h
    by_contra hn
    have hcast : (n : ℂ) ≠ 0 := by
      exact_mod_cast hn
    exact (mul_ne_zero hcast
      (logarithmicPeriod_ne_zero radius hradius)) h
  · intro hn
    subst n
    simp

theorem hadjiivanovMonodromy_pow_winding_period
    (h : ℂ) (radius : ℝ) (hradius : 0 < radius) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          (-(n : ℂ) * logarithmicPeriod radius) • jordanNilpotent) := by
  rw [hadjiivanovMonodromy_pow_winding, logarithmicPeriod_eq_residue radius hradius]
  simp [logShearBase]
  ring_nf

theorem hadjiivanovMonodromy_nat_pow_winding_factorized
    (h : ℝ) (radius : ℝ) (hradius : 0 < radius) (n : ℕ) :
    hadjiivanovMonodromy (h : ℂ) ^ n =
      (windingAddChar (-h) (n : ℤ) : ℂ) •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          (-(n : ℂ) * logarithmicPeriod radius) • jordanNilpotent) := by
  rw [hadjiivanovMonodromy_pow_winding_period (h := (h : ℂ))
    (radius := radius) hradius n]
  rw [lcftPhase_nat_pow_eq_windingAddChar]

end

end InfoGeometry.Projective.KleinPeriodHadjiivanovMonodromy
