import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Arithmetic.SplitMajoranaLocal

variable {A : Type*} [Ring A]

/-- Anticommutator in a possibly noncommutative ring. -/
def anticomm (x y : A) : A :=
  x * y + y * x

/-- Split-Majorana `c = ε + ι`. -/
def cMajorana (ε ι : A) : A :=
  ε + ι

/-- Split-Majorana `d = ε - ι`. -/
def dMajorana (ε ι : A) : A :=
  ε - ι

/-- Local particle-number operator candidate: `N = ε ι`. -/
def numberOp (ε ι : A) : A :=
  ε * ι

/-- Local hole-number operator candidate: `1 - N = ι ε`. -/
def holeNumberOp (ε ι : A) : A :=
  ι * ε

/-- Local parity product in split-Majorana form: `Π = c d`. -/
def parityOp (ε ι : A) : A :=
  cMajorana ε ι * dMajorana ε ι

/--
If `ε² = 0`, `ι² = 0`, and `{ι, ε} = 1`, then
`{c, c} = 2` for `c = ε + ι`.
-/
theorem anticomm_cMajorana_cMajorana
    (ε ι : A)
    (hε : ε * ε = 0)
    (hι : ι * ι = 0)
    (hcar : ι * ε + ε * ι = 1) :
    anticomm (cMajorana ε ι) (cMajorana ε ι) = (2 : A) := by
  have hcar' : ε * ι + ι * ε = 1 := by
    simpa [add_comm] using hcar
  unfold anticomm cMajorana
  calc
    (ε + ι) * (ε + ι) + (ε + ι) * (ε + ι)
        = 2 * (ε * ε) + 2 * (ε * ι + ι * ε) + 2 * (ι * ι) := by
            noncomm_ring
    _ = 2 * (0 : A) + 2 * (1 : A) + 2 * (0 : A) := by
            rw [hε, hι, hcar']
    _ = (2 : A) := by
            simp

/--
If `ε² = 0`, `ι² = 0`, and `{ι, ε} = 1`, then
`{d, d} = -2` for `d = ε - ι`.
-/
theorem anticomm_dMajorana_dMajorana
    (ε ι : A)
    (hε : ε * ε = 0)
    (hι : ι * ι = 0)
    (hcar : ι * ε + ε * ι = 1) :
    anticomm (dMajorana ε ι) (dMajorana ε ι) = -(2 : A) := by
  have hcar' : ε * ι + ι * ε = 1 := by
    simpa [add_comm] using hcar
  unfold anticomm dMajorana
  calc
    (ε - ι) * (ε - ι) + (ε - ι) * (ε - ι)
        = 2 * (ε * ε) - 2 * (ε * ι + ι * ε) + 2 * (ι * ι) := by
            noncomm_ring
    _ = 2 * (0 : A) - 2 * (1 : A) + 2 * (0 : A) := by
            rw [hε, hι, hcar']
    _ = -(2 : A) := by
            simp

/--
If `ε² = 0` and `ι² = 0`, then the two split-Majoranas anticommute:
`{c, d} = 0`.
-/
theorem anticomm_cMajorana_dMajorana
    (ε ι : A)
    (hε : ε * ε = 0)
    (hι : ι * ι = 0) :
    anticomm (cMajorana ε ι) (dMajorana ε ι) = 0 := by
  unfold anticomm cMajorana dMajorana
  calc
    (ε + ι) * (ε - ι) + (ε - ι) * (ε + ι)
        = 2 * (ε * ε) - 2 * (ι * ι) := by
            noncomm_ring
    _ = 2 * (0 : A) - 2 * (0 : A) := by
            rw [hε, hι]
    _ = 0 := by
            noncomm_ring

/--
Local parity identity:
`c d = 1 - 2 ε ι`.

Here `N = ε ι` is the local occupation projector candidate.
-/
theorem cMajorana_mul_dMajorana_eq_one_sub_two_N
    (ε ι : A)
    (hε : ε * ε = 0)
    (hι : ι * ι = 0)
    (hcar : ι * ε + ε * ι = 1) :
    cMajorana ε ι * dMajorana ε ι = 1 - (2 : A) * (ε * ι) := by
  have hιε : ι * ε = 1 - ε * ι := by
    calc
      ι * ε = (ι * ε + ε * ι) - ε * ι := by
        noncomm_ring
      _ = 1 - ε * ι := by
        rw [hcar]
  unfold cMajorana dMajorana
  calc
    (ε + ι) * (ε - ι)
        = ε * ε - ε * ι + ι * ε - ι * ι := by
            noncomm_ring
    _ = 0 - ε * ι + (1 - ε * ι) - 0 := by
            rw [hε, hι, hιε]
    _ = 1 - (2 : A) * (ε * ι) := by
            noncomm_ring

/--
Local parity identity in reversed order:
`d c = 1 - 2 ι ε`.
-/
theorem dMajorana_mul_cMajorana_eq_one_sub_two_iotaEpsilon
    (ε ι : A)
    (hε : ε * ε = 0)
    (hι : ι * ι = 0)
    (hcar : ι * ε + ε * ι = 1) :
    dMajorana ε ι * cMajorana ε ι = 1 - (2 : A) * (ι * ε) := by
  unfold dMajorana cMajorana
  calc
    (ε - ι) * (ε + ι)
        = ε * ε + ε * ι - ι * ε - ι * ι := by
            noncomm_ring
    _ = 0 + ε * ι - ι * ε - 0 := by
            rw [hε, hι]
    _ = 1 - (2 : A) * (ι * ε) := by
            have hει : ε * ι = 1 - ι * ε := by
              calc
                ε * ι = (ι * ε + ε * ι) - ι * ε := by
                  noncomm_ring
                _ = 1 - ι * ε := by
                  rw [hcar]
            rw [hει]
            noncomm_ring

/--
From CAR, the split-Majorana parity products are opposite:
`c d + d c = 0`.
-/
theorem cMajorana_mul_dMajorana_add_dMajorana_mul_cMajorana_eq_zero
    (ε ι : A)
    (hε : ε * ε = 0)
    (hι : ι * ι = 0)
    (hcar : ι * ε + ε * ι = 1) :
    cMajorana ε ι * dMajorana ε ι + dMajorana ε ι * cMajorana ε ι = 0 := by
  rw [cMajorana_mul_dMajorana_eq_one_sub_two_N (ε := ε) (ι := ι) hε hι hcar]
  rw [dMajorana_mul_cMajorana_eq_one_sub_two_iotaEpsilon (ε := ε) (ι := ι) hε hι hcar]
  have hsum : ε * ι + ι * ε = 1 := by simpa [add_comm] using hcar
  have hιε : ι * ε = 1 - ε * ι := by
    calc
      ι * ε = (ι * ε + ε * ι) - ε * ι := by noncomm_ring
      _ = 1 - ε * ι := by rw [hcar]
  rw [hιε]
  noncomm_ring

/--
Commutator form of the local split-Majorana parity products:
`c d - d c = 2 (ι ε - ε ι)`.
-/
theorem cMajorana_mul_dMajorana_sub_dMajorana_mul_cMajorana
    (ε ι : A)
    :
    cMajorana ε ι * dMajorana ε ι - dMajorana ε ι * cMajorana ε ι
      = (2 : A) * (ι * ε - ε * ι) := by
  unfold cMajorana dMajorana
  noncomm_ring

/--
Under square-zero assumptions, the parity product is exactly the local commutator density:
`c d = ι ε - ε ι`.
-/
theorem cMajorana_mul_dMajorana_eq_iotaEpsilon_sub_epsilonIota
    (ε ι : A)
    (hε : ε * ε = 0)
    (hι : ι * ι = 0) :
    cMajorana ε ι * dMajorana ε ι = ι * ε - ε * ι := by
  unfold cMajorana dMajorana
  calc
    (ε + ι) * (ε - ι) = ε * ε - ε * ι + ι * ε - ι * ι := by
      noncomm_ring
    _ = 0 - ε * ι + ι * ε - 0 := by rw [hε, hι]
    _ = ι * ε - ε * ι := by noncomm_ring

/--
Symmetric square-zero identity:
`d c = ε ι - ι ε`.
-/
theorem dMajorana_mul_cMajorana_eq_epsilonIota_sub_iotaEpsilon
    (ε ι : A)
    (hε : ε * ε = 0)
    (hι : ι * ι = 0) :
    dMajorana ε ι * cMajorana ε ι = ε * ι - ι * ε := by
  unfold dMajorana cMajorana
  calc
    (ε - ι) * (ε + ι) = ε * ε + ε * ι - ι * ε - ι * ι := by
      noncomm_ring
    _ = 0 + ε * ι - ι * ε - 0 := by rw [hε, hι]
    _ = ε * ι - ι * ε := by noncomm_ring

/--
Square-zero consequence: the split-Majorana parity products are negatives:
`c d = -(d c)`.
-/
theorem cMajorana_mul_dMajorana_eq_neg_dMajorana_mul_cMajorana
    (ε ι : A)
    (hε : ε * ε = 0)
    (hι : ι * ι = 0) :
    cMajorana ε ι * dMajorana ε ι = -(dMajorana ε ι * cMajorana ε ι) := by
  rw [cMajorana_mul_dMajorana_eq_iotaEpsilon_sub_epsilonIota (ε := ε) (ι := ι) hε hι]
  rw [dMajorana_mul_cMajorana_eq_epsilonIota_sub_iotaEpsilon (ε := ε) (ι := ι) hε hι]
  noncomm_ring

/--
Square-zero corollary in anticommutator form:
`{c, d} = 0`.
-/
theorem anticomm_cMajorana_dMajorana_eq_zero_of_sq_zero
    (ε ι : A)
    (hε : ε * ε = 0)
    (hι : ι * ι = 0) :
    anticomm (cMajorana ε ι) (dMajorana ε ι) = 0 := by
  unfold anticomm
  rw [cMajorana_mul_dMajorana_eq_neg_dMajorana_mul_cMajorana (ε := ε) (ι := ι) hε hι]
  simp

/--
Square-zero corollary in product-sum form:
`c d + d c = 0`.
-/
theorem cMajorana_mul_dMajorana_add_dMajorana_mul_cMajorana_eq_zero_of_sq_zero
    (ε ι : A)
    (hε : ε * ε = 0)
    (hι : ι * ι = 0) :
    cMajorana ε ι * dMajorana ε ι + dMajorana ε ι * cMajorana ε ι = 0 := by
  simpa [anticomm] using
    anticomm_cMajorana_dMajorana_eq_zero_of_sq_zero (ε := ε) (ι := ι) hε hι

/--
CAR readout of hole-plus-number:
`holeNumberOp + numberOp = 1`.
-/
theorem holeNumberOp_add_numberOp_eq_one
    (ε ι : A)
    (hcar : ι * ε + ε * ι = 1) :
    holeNumberOp ε ι + numberOp ε ι = 1 := by
  simpa [holeNumberOp, numberOp] using hcar

/--
Parity-number relation:
`parityOp = 1 - 2 * numberOp`.
-/
theorem parityOp_eq_one_sub_two_numberOp
    (ε ι : A)
    (hε : ε * ε = 0)
    (hι : ι * ι = 0)
    (hcar : ι * ε + ε * ι = 1) :
    parityOp ε ι = 1 - (2 : A) * numberOp ε ι := by
  simpa [parityOp, numberOp] using
    cMajorana_mul_dMajorana_eq_one_sub_two_N (ε := ε) (ι := ι) hε hι hcar

end InfoGeometry.Arithmetic.SplitMajoranaLocal
