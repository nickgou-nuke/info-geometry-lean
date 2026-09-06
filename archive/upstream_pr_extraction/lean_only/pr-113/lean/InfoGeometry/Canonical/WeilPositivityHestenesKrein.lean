import Mathlib.Tactic
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport

/-!
# Finite Weil positivity on the Hestenes--Krein colimit lane

This owner keeps the arithmetic and spectral positivity mechanisms honest.
It proves positivity for finite weighted square forms and transports those
forms through the native Hestenes--Krein cone maps.  It does not assert the
Riemann Hypothesis, an infinite Weil criterion, or an analytic Euler-product
identity.
-/

noncomputable section

namespace InfoGeometry.Canonical.WeilPositivityHestenesKrein

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Krein
open scoped BigOperators

/-! ## Finite weighted Weil form -/

def weilQuadraticEnergy {ι : Type*} (marks : Finset ι)
    (weight value : ι → ℝ) : ℝ :=
  marks.sum (fun i => weight i * value i ^ 2)

theorem weilQuadraticEnergy_nonneg
    {ι : Type*} (marks : Finset ι)
    (weight value : ι → ℝ)
    (hweight : ∀ i ∈ marks, 0 ≤ weight i) :
    0 ≤ weilQuadraticEnergy marks weight value := by
  unfold weilQuadraticEnergy
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hweight i hi) (sq_nonneg (value i))

theorem weilQuadraticEnergy_insert
    {ι : Type*} [DecidableEq ι]
    (marks : Finset ι) (weight value : ι → ℝ)
    (i : ι) (hi : i ∉ marks) :
    weilQuadraticEnergy (insert i marks) weight value =
      weight i * value i ^ 2 + weilQuadraticEnergy marks weight value := by
  rw [weilQuadraticEnergy, Finset.sum_insert hi]
  rfl

/-! ## Finite prime-power comb -/

structure PrimePowerEntry where
  prime : ℕ
  power : ℕ
  logPrime : ℝ
  weight : ℝ

def primePowerArgument (p : PrimePowerEntry) : ℝ :=
  (p.power : ℝ) * p.logPrime

/-- The finite square-comb analogue of a Weil convolution with its reverse. -/
def weilPrimePowerComb (entries : List PrimePowerEntry) (f : ℝ → ℝ) : ℝ :=
  (entries.map (fun p =>
    p.weight *
      (f (primePowerArgument p) ^ 2 +
        f (-primePowerArgument p) ^ 2))).sum

theorem weilPrimePowerComb_nonneg
    (entries : List PrimePowerEntry) (f : ℝ → ℝ)
    (hweight : ∀ p ∈ entries, 0 ≤ p.weight) :
    0 ≤ weilPrimePowerComb entries f := by
  induction entries with
  | nil => simp [weilPrimePowerComb]
  | cons p ps ih =>
      simp only [weilPrimePowerComb, List.map_cons, List.sum_cons]
      have hp : 0 ≤ p.weight := hweight p (by simp)
      have hps : ∀ q ∈ ps, 0 ≤ q.weight := by
        intro q hq
        exact hweight q (by simp [hq])
      apply add_nonneg
      · exact mul_nonneg hp (add_nonneg
          (sq_nonneg (f (primePowerArgument p)))
          (sq_nonneg (f (-primePowerArgument p))))
      · exact ih hps

theorem weilPrimePowerComb_reverse_invariant
    (entries : List PrimePowerEntry) (f : ℝ → ℝ) :
    weilPrimePowerComb entries (fun x => f (-x)) =
      weilPrimePowerComb entries f := by
  induction entries with
  | nil => simp [weilPrimePowerComb]
  | cons p ps ih =>
      change
        p.weight *
            (f (-primePowerArgument p) ^ 2 +
              f (- -primePowerArgument p) ^ 2) +
            weilPrimePowerComb ps (fun x => f (-x)) =
          p.weight *
            (f (primePowerArgument p) ^ 2 +
              f (-primePowerArgument p) ^ 2) +
            weilPrimePowerComb ps f
      rw [ih]
      congr 1
      ring_nf

/-! ## Native filtered-colimit transport -/

theorem colimit_square_stage_readout
    {C : HestenesKreinCone}
    (stage : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limit : DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n x, stage n x = limit (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stage n x ^ 2 = limit (C.ι n x) ^ 2 := by
  rw [hreadout n x]

theorem colimit_square_bondIterate
    {C : HestenesKreinCone}
    (stage : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limit : DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n x, stage n x = limit (C.ι n x))
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    stage (n + m)
        (C.toFilteredPhaseCone.bondIterate n m x) ^ 2 =
      stage n x ^ 2 := by
  rw [hreadout (n + m), hreadout n]
  exact congrArg (fun y => limit y ^ 2)
    (C.toFilteredPhaseCone.ι_bondIterate_apply n m x)

/-! ## Weighted finite energies on the colimit carrier -/

theorem colimit_weilQuadraticEnergy_readout
    {C : HestenesKreinCone} {ι : Type*}
    (marks : Finset ι) (weight : ι → ℝ)
    (stage : ∀ n, ι → DoubledSpace (C.Base n) → ℝ)
    (limit : ι → DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n i x, stage n i x = limit i (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    weilQuadraticEnergy marks weight (fun i => stage n i x) =
      weilQuadraticEnergy marks weight (fun i => limit i (C.ι n x)) := by
  unfold weilQuadraticEnergy
  apply Finset.sum_congr rfl
  intro i hi
  change weight i * (stage n i x) ^ 2 =
    weight i * (limit i (C.ι n x)) ^ 2
  rw [hreadout n i x]

theorem colimit_weilQuadraticEnergy_bondIterate
    {C : HestenesKreinCone} {ι : Type*}
    (marks : Finset ι) (weight : ι → ℝ)
    (stage : ∀ n, ι → DoubledSpace (C.Base n) → ℝ)
    (limit : ι → DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n i x, stage n i x = limit i (C.ι n x))
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    weilQuadraticEnergy marks weight
        (fun i => stage (n + m) i
          (C.toFilteredPhaseCone.bondIterate n m x)) =
      weilQuadraticEnergy marks weight (fun i => stage n i x) := by
  calc
    weilQuadraticEnergy marks weight
        (fun i => stage (n + m) i
          (C.toFilteredPhaseCone.bondIterate n m x)) =
        weilQuadraticEnergy marks weight
          (fun i => limit i
            (C.ι (n + m)
              (C.toFilteredPhaseCone.bondIterate n m x))) :=
      colimit_weilQuadraticEnergy_readout marks weight stage limit hreadout
        (n + m) (C.toFilteredPhaseCone.bondIterate n m x)
    _ = weilQuadraticEnergy marks weight (fun i => limit i (C.ι n x)) := by
      apply Finset.sum_congr rfl
      intro i hi
      change weight i *
          (limit i (C.toFilteredPhaseCone.ι (n + m)
            (C.toFilteredPhaseCone.bondIterate n m x))) ^ 2 =
        weight i * (limit i (C.toFilteredPhaseCone.ι n x)) ^ 2
      rw [C.toFilteredPhaseCone.ι_bondIterate_apply n m x]
    _ = weilQuadraticEnergy marks weight (fun i => stage n i x) :=
      (colimit_weilQuadraticEnergy_readout marks weight stage limit hreadout
        n x).symm

theorem colimit_weilQuadraticEnergy_nonneg
    {C : HestenesKreinCone} {ι : Type*}
    (marks : Finset ι) (weight : ι → ℝ)
    (limit : ι → DoubledSpace C.LimitBase → ℝ)
    (hweight : ∀ i ∈ marks, 0 ≤ weight i)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    0 ≤ weilQuadraticEnergy marks weight (fun i => limit i (C.ι n x)) := by
  exact weilQuadraticEnergy_nonneg marks weight (fun i => limit i (C.ι n x)) hweight

end InfoGeometry.Canonical.WeilPositivityHestenesKrein

end noncomputable section
