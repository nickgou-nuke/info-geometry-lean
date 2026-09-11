
import InfoGeometry.PositiveMeasure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Gauge reduction and KL decomposition

KL-like decomposition, gauge reduction, and mass-matching results.
-/


namespace InfoGeometry

namespace Projective.GaugeReduction
end Projective.GaugeReduction

namespace PositiveMeasure

variable {α : Type u} [Fintype α]
open scoped BigOperators

/-- The “pure log-ratio” sum (the KL-like part). -/
noncomputable def klLike (μ ν : PositiveMeasure α ℝ) : ℝ :=
  ∑ a ∈ (Finset.univ : Finset α), (μ a) * Real.log ((μ a) / (ν a))

/-- `generalizedKL = klLike + (Z ν - Z μ)` (mass slack explicitly separated). -/
@[simp]
lemma generalizedKL_eq_klLike_add_Z (μ ν : PositiveMeasure α ℝ) :
    generalizedKL (α := α) μ ν =
      klLike (α := α) μ ν +
        (Z (α := α) (R := ℝ) ν - Z (α := α) (R := ℝ) μ) := by
  unfold generalizedKL klLike gklTerm PositiveMeasure.Z
  calc
    ∑ x ∈ (Finset.univ : Finset α), (μ x * Real.log (μ x / ν x) - μ x + ν x)
        = ∑ x ∈ (Finset.univ : Finset α), (μ x * Real.log (μ x / ν x) + (-μ x + ν x)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring
    _ = (∑ x ∈ (Finset.univ : Finset α), μ x * Real.log (μ x / ν x))
          + (∑ x ∈ (Finset.univ : Finset α), (-μ x + ν x)) := by
            simp [Finset.sum_add_distrib]
    _ = (∑ x ∈ (Finset.univ : Finset α), μ x * Real.log (μ x / ν x))
          + ((∑ x ∈ (Finset.univ : Finset α), (-μ x))
              + (∑ x ∈ (Finset.univ : Finset α), ν x)) := by
            simp [Finset.sum_add_distrib]
    _ = (∑ x ∈ (Finset.univ : Finset α), μ x * Real.log (μ x / ν x))
          + (-(∑ x ∈ (Finset.univ : Finset α), μ x)
              + (∑ x ∈ (Finset.univ : Finset α), ν x)) := by
            simp
    _ = (∑ x ∈ (Finset.univ : Finset α), μ x * Real.log (μ x / ν x))
          + ((∑ x ∈ (Finset.univ : Finset α), ν x)
              - (∑ x ∈ (Finset.univ : Finset α), μ x)) := by
            ring
    _ = klLike (α := α) μ ν + (Z (α := α) (R := ℝ) ν - Z (α := α) (R := ℝ) μ) := rfl

/-- If masses match, generalized KL collapses to the log-ratio sum. -/
@[simp]
lemma generalizedKL_eq_klLike_of_Z_eq (μ ν : PositiveMeasure α ℝ)
    (hZ : Z (α := α) (R := ℝ) μ = Z (α := α) (R := ℝ) ν) :
    generalizedKL (α := α) μ ν = klLike (α := α) μ ν := by
  rw [generalizedKL_eq_klLike_add_Z]
  have hslack : Z (α := α) (R := ℝ) ν - Z (α := α) (R := ℝ) μ = 0 := by
    exact sub_eq_zero.mpr hZ.symm
  rw [hslack]
  ring

/-- Two-scale law for the KL-like part:
`klLike(cμ,dν) = c * klLike(μ,ν) + c * Z(μ) * log(c/d)` for `c,d > 0`. -/
lemma klLike_scale_scale_two (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (μ ν : PositiveMeasure α ℝ) :
    klLike (α := α) (scale c hc μ) (scale d hd ν)
      = c * klLike (α := α) μ ν
        + c * Z (α := α) (R := ℝ) μ * Real.log (c / d) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hd0 : d ≠ 0 := hd.ne'
  unfold klLike
  have hsplit :
      ∑ a ∈ (Finset.univ : Finset α),
        scale c hc μ a * Real.log (scale c hc μ a / scale d hd ν a)
      =
      (∑ a ∈ (Finset.univ : Finset α), (c * μ a) * Real.log (μ a / ν a))
      + (∑ a ∈ (Finset.univ : Finset α), (c * μ a) * Real.log (c / d)) := by
    calc
      ∑ a ∈ (Finset.univ : Finset α),
          scale c hc μ a * Real.log (scale c hc μ a / scale d hd ν a)
          =
        ∑ a ∈ (Finset.univ : Finset α),
          ((c * μ a) * Real.log (μ a / ν a)
            + (c * μ a) * Real.log (c / d)) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              have hμ0 : μ a ≠ 0 := (μ.pos a).ne'
              have hν0 : ν a ≠ 0 := (ν.pos a).ne'
              have hratio :
                  (c * μ a) / (d * ν a) = (c / d) * (μ a / ν a) := by
                field_simp [hc0, hd0, hμ0, hν0]
              rw [scale_apply, scale_apply, hratio]
              rw [Real.log_mul (div_ne_zero hc0 hd0) (div_ne_zero hμ0 hν0)]
              ring
      _ = (∑ a ∈ (Finset.univ : Finset α), (c * μ a) * Real.log (μ a / ν a))
            + (∑ a ∈ (Finset.univ : Finset α), (c * μ a) * Real.log (c / d)) := by
              simp [Finset.sum_add_distrib]
  have hfirst :
      ∑ a ∈ (Finset.univ : Finset α), (c * μ a) * Real.log (μ a / ν a)
        = c * klLike (α := α) μ ν := by
    calc
      ∑ a ∈ (Finset.univ : Finset α), (c * μ a) * Real.log (μ a / ν a)
          = ∑ a ∈ (Finset.univ : Finset α), c * (μ a * Real.log (μ a / ν a)) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              ring
      _ = c * (∑ a ∈ (Finset.univ : Finset α), μ a * Real.log (μ a / ν a)) := by
            simp [Finset.mul_sum]
      _ = c * klLike (α := α) μ ν := by
            simp [klLike]
  have hsecond :
      ∑ a ∈ (Finset.univ : Finset α), (c * μ a) * Real.log (c / d)
        = c * Z (α := α) (R := ℝ) μ * Real.log (c / d) := by
    calc
      ∑ a ∈ (Finset.univ : Finset α), (c * μ a) * Real.log (c / d)
          = ∑ a ∈ (Finset.univ : Finset α), c * (μ a * Real.log (c / d)) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              ring
      _ = c * (∑ a ∈ (Finset.univ : Finset α), μ a * Real.log (c / d)) := by
            simp [Finset.mul_sum]
      _ = c * ((Real.log (c / d)) * ∑ a ∈ (Finset.univ : Finset α), μ a) := by
            congr 1
            calc
              ∑ a ∈ (Finset.univ : Finset α), μ a * Real.log (c / d)
                  = ∑ a ∈ (Finset.univ : Finset α), (Real.log (c / d)) * μ a := by
                      refine Finset.sum_congr rfl ?_
                      intro a ha
                      ring
              _ = (Real.log (c / d)) * ∑ a ∈ (Finset.univ : Finset α), μ a := by
                    simp [Finset.mul_sum]
      _ = c * ((Real.log (c / d)) * Z (α := α) (R := ℝ) μ) := by
            simp [PositiveMeasure.Z]
      _ = c * Z (α := α) (R := ℝ) μ * Real.log (c / d) := by
            ring
  calc
    klLike (α := α) (scale c hc μ) (scale d hd ν)
        =
      (∑ a ∈ (Finset.univ : Finset α), (c * μ a) * Real.log (μ a / ν a))
      + (∑ a ∈ (Finset.univ : Finset α), (c * μ a) * Real.log (c / d)) := hsplit
    _ = c * klLike (α := α) μ ν + c * Z (α := α) (R := ℝ) μ * Real.log (c / d) := by
          rw [hfirst, hsecond]

/-- Projective + radial decomposition:
`generalizedKL(μ||ν) = Z(μ) * generalizedKL(normalize μ || normalize ν) + gklTerm(Z μ)(Z ν)`. -/
lemma generalizedKL_projective_radial_decomposition [Nonempty α]
    (μ ν : PositiveMeasure α ℝ) :
    generalizedKL (α := α) μ ν
      =
    Z (α := α) (R := ℝ) μ
      * generalizedKL (α := α)
          (normalize (α := α) (R := ℝ) μ)
          (normalize (α := α) (R := ℝ) ν)
      + gklTerm (Z (α := α) (R := ℝ) μ) (Z (α := α) (R := ℝ) ν) := by
  have hμpt :
      ∀ a : α,
        scale (Z (α := α) (R := ℝ) μ)
          (Z_pos (α := α) (R := ℝ) μ)
          (normalize (α := α) (R := ℝ) μ) a = μ a := by
    intro a
    rw [scale_apply, normalize_apply]
    have hZμ0 : Z (α := α) (R := ℝ) μ ≠ 0 := Z_ne_zero (α := α) (R := ℝ) μ
    field_simp [hZμ0]
  have hνpt :
      ∀ a : α,
        scale (Z (α := α) (R := ℝ) ν)
          (Z_pos (α := α) (R := ℝ) ν)
          (normalize (α := α) (R := ℝ) ν) a = ν a := by
    intro a
    rw [scale_apply, normalize_apply]
    have hZν0 : Z (α := α) (R := ℝ) ν ≠ 0 := Z_ne_zero (α := α) (R := ℝ) ν
    field_simp [hZν0]
  have hkl_scale_to_original :
      klLike (α := α)
        (scale (Z (α := α) (R := ℝ) μ)
          (Z_pos (α := α) (R := ℝ) μ)
          (normalize (α := α) (R := ℝ) μ))
        (scale (Z (α := α) (R := ℝ) ν)
          (Z_pos (α := α) (R := ℝ) ν)
          (normalize (α := α) (R := ℝ) ν))
        = klLike (α := α) μ ν := by
    unfold klLike
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [hμpt a, hνpt a]
  have hkl :
    klLike (α := α) μ ν
      =
    Z (α := α) (R := ℝ) μ
      * klLike (α := α)
          (normalize (α := α) (R := ℝ) μ)
          (normalize (α := α) (R := ℝ) ν)
      + Z (α := α) (R := ℝ) μ * Real.log
          (Z (α := α) (R := ℝ) μ / Z (α := α) (R := ℝ) ν) := by
    calc
      klLike (α := α) μ ν
        =
      klLike (α := α)
        (scale (Z (α := α) (R := ℝ) μ)
          (Z_pos (α := α) (R := ℝ) μ)
          (normalize (α := α) (R := ℝ) μ))
        (scale (Z (α := α) (R := ℝ) ν)
          (Z_pos (α := α) (R := ℝ) ν)
          (normalize (α := α) (R := ℝ) ν)) := by
          exact hkl_scale_to_original.symm
    _ =
      Z (α := α) (R := ℝ) μ
        * klLike (α := α)
            (normalize (α := α) (R := ℝ) μ)
            (normalize (α := α) (R := ℝ) ν)
        +
      Z (α := α) (R := ℝ) μ
        * Z (α := α) (R := ℝ) (normalize (α := α) (R := ℝ) μ)
        * Real.log (Z (α := α) (R := ℝ) μ / Z (α := α) (R := ℝ) ν) := by
          simpa using
            klLike_scale_scale_two (α := α)
              (c := Z (α := α) (R := ℝ) μ)
              (d := Z (α := α) (R := ℝ) ν)
              (hc := Z_pos (α := α) (R := ℝ) μ)
              (hd := Z_pos (α := α) (R := ℝ) ν)
              (μ := normalize (α := α) (R := ℝ) μ)
              (ν := normalize (α := α) (R := ℝ) ν)
    _ =
      Z (α := α) (R := ℝ) μ
        * klLike (α := α)
            (normalize (α := α) (R := ℝ) μ)
            (normalize (α := α) (R := ℝ) ν)
        +
      Z (α := α) (R := ℝ) μ
        * Real.log (Z (α := α) (R := ℝ) μ / Z (α := α) (R := ℝ) ν) := by
          rw [Z_normalize (α := α) (R := ℝ) μ]
          ring
  have hnorm :
      generalizedKL (α := α)
          (normalize (α := α) (R := ℝ) μ)
          (normalize (α := α) (R := ℝ) ν)
        =
      klLike (α := α)
          (normalize (α := α) (R := ℝ) μ)
          (normalize (α := α) (R := ℝ) ν) := by
    refine generalizedKL_eq_klLike_of_Z_eq (α := α)
      (μ := normalize (α := α) (R := ℝ) μ)
      (ν := normalize (α := α) (R := ℝ) ν) ?_
    calc
      Z (α := α) (R := ℝ) (normalize (α := α) (R := ℝ) μ) = 1 := by
        simpa using Z_normalize (α := α) (R := ℝ) μ
      _ = Z (α := α) (R := ℝ) (normalize (α := α) (R := ℝ) ν) := by
        symm
        simpa using Z_normalize (α := α) (R := ℝ) ν
  calc
    generalizedKL (α := α) μ ν
        = klLike (α := α) μ ν + (Z (α := α) (R := ℝ) ν - Z (α := α) (R := ℝ) μ) := by
            exact generalizedKL_eq_klLike_add_Z (α := α) μ ν
    _ =
      (Z (α := α) (R := ℝ) μ
          * klLike (α := α)
              (normalize (α := α) (R := ℝ) μ)
              (normalize (α := α) (R := ℝ) ν)
          + Z (α := α) (R := ℝ) μ * Real.log
              (Z (α := α) (R := ℝ) μ / Z (α := α) (R := ℝ) ν))
        + (Z (α := α) (R := ℝ) ν - Z (α := α) (R := ℝ) μ) := by
          rw [hkl]
    _ =
      (Z (α := α) (R := ℝ) μ
          * generalizedKL (α := α)
              (normalize (α := α) (R := ℝ) μ)
              (normalize (α := α) (R := ℝ) ν))
        + (Z (α := α) (R := ℝ) μ * Real.log
              (Z (α := α) (R := ℝ) μ / Z (α := α) (R := ℝ) ν)
            - Z (α := α) (R := ℝ) μ
            + Z (α := α) (R := ℝ) ν) := by
          rw [hnorm]
          ring
    _ =
      Z (α := α) (R := ℝ) μ
        * generalizedKL (α := α)
            (normalize (α := α) (R := ℝ) μ)
            (normalize (α := α) (R := ℝ) ν)
        + gklTerm (Z (α := α) (R := ℝ) μ) (Z (α := α) (R := ℝ) ν) := by
          unfold gklTerm
          ring

/-- Gauge reduction for normalized representatives (simplex gauge). -/
@[simp]
lemma generalizedKL_normalize_eq_klLike_normalize [Nonempty α] (μ ν : PositiveMeasure α ℝ) :
    generalizedKL (α := α)
        (normalize (α := α) (R := ℝ) μ)
        (normalize (α := α) (R := ℝ) ν)
      =
    klLike (α := α)
        (normalize (α := α) (R := ℝ) μ)
        (normalize (α := α) (R := ℝ) ν) := by
  refine generalizedKL_eq_klLike_of_Z_eq (α := α)
    (μ := normalize (α := α) (R := ℝ) μ)
    (ν := normalize (α := α) (R := ℝ) ν) ?_
  calc
    Z (α := α) (R := ℝ) (normalize (α := α) (R := ℝ) μ) = 1 := by
      simpa using Z_normalize (α := α) (R := ℝ) μ
    _ = Z (α := α) (R := ℝ) (normalize (α := α) (R := ℝ) ν) := by
      symm
      simpa using Z_normalize (α := α) (R := ℝ) ν

/-- Homogeneity of generalized KL: D_GKL(cμ|cν) = c D_GKL(μ|ν) for c > 0. -/
@[simp]
lemma generalizedKL_scale_scale (c : ℝ) (hc : 0 < c)
    (μ ν : PositiveMeasure α ℝ) :
    generalizedKL (α := α) (scale c hc μ) (scale c hc ν)
      = c * generalizedKL (α := α) μ ν := by
  have hterm :
      ∀ a : α, gklTerm (scale c hc μ a) (scale c hc ν a) = c * gklTerm (μ a) (ν a) := by
    intro a
    have hc0 : c ≠ 0 := hc.ne'
    have hν0 : ν a ≠ 0 := (ν.pos a).ne'
    unfold gklTerm
    have hratio : (c * μ a) / (c * ν a) = μ a / ν a := by
      field_simp [hc0, hν0]
    rw [scale_apply, scale_apply, hratio]
    ring
  unfold generalizedKL
  calc
    ∑ a ∈ (Finset.univ : Finset α), gklTerm (scale c hc μ a) (scale c hc ν a)
        = ∑ a ∈ (Finset.univ : Finset α), c * gklTerm (μ a) (ν a) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            exact hterm a
    _ = c * ∑ a ∈ (Finset.univ : Finset α), gklTerm (μ a) (ν a) := by
          simp [Finset.mul_sum]

end PositiveMeasure

end InfoGeometry
