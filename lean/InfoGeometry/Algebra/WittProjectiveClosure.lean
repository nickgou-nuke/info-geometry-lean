import InfoGeometry.Algebra.WittProjectiveClosureHonest

/-!
# Honest Witt / projective closure surface

This module replaces the earlier over-claimed `WittProjectiveClosure` surface
with theorem-backed finite facts re-exported from
`InfoGeometry.Algebra.WittProjectiveClosureHonest`.

It does NOT prove any global `O(5,5)` Virasoro anomaly cancellation, any Krein
realization theorem for the full Witt/Virasoro system, or any physical `c = 0`
statement.

It DOES provide the finite honest surface already verified in-repo:
- the anomaly polynomial `m^3 - m` vanishes on `{-1, 0, 1}`;
- the Virasoro cocycle vanishes on projective generators;
- the Witt bracket on `ℓ_{-1}, ℓ_0, ℓ_1` is the usual centerless bracket;
- nonzero projective brackets stay inside the projective index set.
-/

namespace InfoGeometry.Algebra.WittProjectiveClosure

open VirasoroProject
open VirasoroProject.WittAlgebra

abbrev ProjectiveClosure :=
  WittProjectiveClosureHonest.ProjectiveClosure

@[simp] theorem mem_projectiveClosure (n : ℤ) :
    n ∈ ProjectiveClosure ↔ n = -1 ∨ n = 0 ∨ n = 1 :=
  WittProjectiveClosureHonest.mem_projectiveClosure n

abbrev anomalyFactor :=
  WittProjectiveClosureHonest.anomalyFactor

@[simp] theorem anomalyFactor_neg_one : anomalyFactor (-1) = 0 :=
  WittProjectiveClosureHonest.anomalyFactor_neg_one

@[simp] theorem anomalyFactor_zero : anomalyFactor 0 = 0 :=
  WittProjectiveClosureHonest.anomalyFactor_zero

@[simp] theorem anomalyFactor_one : anomalyFactor 1 = 0 :=
  WittProjectiveClosureHonest.anomalyFactor_one

theorem anomalyFactor_eq_zero_of_mem_projective {m : ℤ} (hm : m ∈ ProjectiveClosure) :
    anomalyFactor m = 0 :=
  WittProjectiveClosureHonest.anomalyFactor_eq_zero_of_mem_projective hm

section Field

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]

theorem virasoroCocycle_lgen_left_projective_zero (m n : ℤ) (hm : m ∈ ProjectiveClosure) :
    virasoroCocycle 𝕜 (lgen 𝕜 m) (lgen 𝕜 n) = 0 :=
  WittProjectiveClosureHonest.virasoroCocycle_lgen_left_projective_zero
    (𝕜 := 𝕜) m n hm

theorem virasoroCocycle_lgen_right_projective_zero (m n : ℤ) (hn : n ∈ ProjectiveClosure) :
    virasoroCocycle 𝕜 (lgen 𝕜 m) (lgen 𝕜 n) = 0 :=
  WittProjectiveClosureHonest.virasoroCocycle_lgen_right_projective_zero
    (𝕜 := 𝕜) m n hn

end Field

section CommRing

variable (𝕜 : Type*) [CommRing 𝕜] [CharZero 𝕜] [IsDomain 𝕜]
  [Module.IsTorsionFree 𝕜 (WittAlgebra 𝕜)]

theorem projective_bracket_eq_witt (m n : ℤ)
    (_hm : m ∈ ProjectiveClosure) (_hn : n ∈ ProjectiveClosure) :
    ⁅lgen 𝕜 m, lgen 𝕜 n⁆ = (m - n : 𝕜) • lgen 𝕜 (m + n) :=
  WittProjectiveClosureHonest.projective_bracket_eq_witt
    (𝕜 := 𝕜) m n _hm _hn

end CommRing

section ClosureOnly

variable (𝕜 : Type*) [CommRing 𝕜]

theorem projective_sum_mem_of_bracket_coeff_ne_zero
    {m n : ℤ} (hm : m ∈ ProjectiveClosure) (hn : n ∈ ProjectiveClosure)
    (hcoeff : (m - n : 𝕜) ≠ 0) :
    m + n ∈ ProjectiveClosure :=
  WittProjectiveClosureHonest.projective_sum_mem_of_bracket_coeff_ne_zero
    (𝕜 := 𝕜) hm hn hcoeff

end ClosureOnly

end InfoGeometry.Algebra.WittProjectiveClosure
