import Mathlib

noncomputable section

namespace SplitMajoranaNumber

variable {A : Type*} [Ring A]

/-- Anticommutator in a possibly noncommutative ring. -/
def anticomm (x y : A) : A :=
  x * y + y * x

/-- Creation / exterior multiplication operator. -/
def creation (ε : A) : A := ε

/-- Annihilation / contraction operator. -/
def annihilation (ι : A) : A := ι

/--
Particle number operator.

Convention:
`ε = a†` is creation,
`ι = a` is annihilation.

Therefore `N = a† a = ε ι`.
-/
def particleNumber (ε ι : A) : A :=
  ε * ι

/--
Hole number operator.

Using CAR, `ι ε = 1 - ε ι`, so this is `1 - N`.
-/
def holeNumber (ε ι : A) : A :=
  ι * ε

/-- Split-Majorana `c = ε + ι`. -/
def cMajorana (ε ι : A) : A :=
  ε + ι

/-- Split-Majorana `d = ε - ι`. -/
def dMajorana (ε ι : A) : A :=
  ε - ι

/--
CAR local relation:
`{ι, ε} = 1`.

This is the local fermionic relation
`a a† + a† a = 1`.
-/
def LocalCAR (ε ι : A) : Prop :=
  ι * ε + ε * ι = 1

/-- `N + N_hole = 1`. -/
theorem particleNumber_add_holeNumber_eq_one
    (ε ι : A)
    (hcar : LocalCAR ε ι) :
    particleNumber ε ι + holeNumber ε ι = 1 := by
  unfold particleNumber holeNumber LocalCAR at *
  simpa [add_comm] using hcar

/-- `N_hole + N = 1`. -/
theorem holeNumber_add_particleNumber_eq_one
    (ε ι : A)
    (hcar : LocalCAR ε ι) :
    holeNumber ε ι + particleNumber ε ι = 1 := by
  unfold particleNumber holeNumber LocalCAR at *
  exact hcar

/-- Particle number is the complement of hole number: `N = 1 - N_hole`. -/
theorem particleNumber_eq_one_sub_holeNumber
    (ε ι : A)
    (hcar : LocalCAR ε ι) :
    particleNumber ε ι = 1 - holeNumber ε ι := by
  have hsum := particleNumber_add_holeNumber_eq_one (ε := ε) (ι := ι) hcar
  exact (eq_sub_iff_add_eq).2 hsum

/-- Hole number is the complement of particle number: `N_hole = 1 - N`. -/
theorem holeNumber_eq_one_sub_particleNumber
    (ε ι : A)
    (hcar : LocalCAR ε ι) :
    holeNumber ε ι = 1 - particleNumber ε ι := by
  have hsum := holeNumber_add_particleNumber_eq_one (ε := ε) (ι := ι) hcar
  exact (eq_sub_iff_add_eq).2 hsum

/--
The particle number operator is idempotent:

`N² = N`.
-/
theorem particleNumber_idempotent
    (ε ι : A)
    (hε : ε * ε = 0)
    (hcar : LocalCAR ε ι) :
    particleNumber ε ι * particleNumber ε ι = particleNumber ε ι := by
  unfold particleNumber LocalCAR at *
  have hιε : ι * ε = 1 - ε * ι := by
    calc
      ι * ε = (ι * ε + ε * ι) - ε * ι := by
        noncomm_ring
      _ = 1 - ε * ι := by
        rw [hcar]
  calc
    (ε * ι) * (ε * ι)
        = ε * (ι * ε) * ι := by
          noncomm_ring
    _ = ε * (1 - ε * ι) * ι := by
          rw [hιε]
    _ = ε * ι := by
          have hsq : ε * ε * ι * ι = 0 := by
            rw [hε]
            simp
          have hstep : ε * (1 - ε * ι) * ι = ε * ι - (ε * ε * ι * ι) := by
            noncomm_ring
          rw [hstep, hsq]
          simp

/--
The hole number operator is idempotent:

`N_hole² = N_hole`.
-/
theorem holeNumber_idempotent
    (ε ι : A)
    (hι : ι * ι = 0)
    (hcar : LocalCAR ε ι) :
    holeNumber ε ι * holeNumber ε ι = holeNumber ε ι := by
  unfold holeNumber LocalCAR at *
  have hει : ε * ι = 1 - ι * ε := by
    calc
      ε * ι = (ι * ε + ε * ι) - ι * ε := by
        noncomm_ring
      _ = 1 - ι * ε := by
        rw [hcar]
  calc
    (ι * ε) * (ι * ε)
        = ι * (ε * ι) * ε := by
          noncomm_ring
    _ = ι * (1 - ι * ε) * ε := by
          rw [hει]
    _ = ι * ε := by
          have hsq : ι * ι * ε * ε = 0 := by
            rw [hι]
            simp
          have hstep : ι * (1 - ι * ε) * ε = ι * ε - (ι * ι * ε * ε) := by
            noncomm_ring
          rw [hstep, hsq]
          simp

/-- Particle and hole projectors are orthogonal: `N * N_hole = 0`. -/
theorem particleNumber_mul_holeNumber_eq_zero
    (ε ι : A)
    (hι : ι * ι = 0) :
    particleNumber ε ι * holeNumber ε ι = 0 := by
  unfold particleNumber holeNumber
  rw [show (ε * ι) * (ι * ε) = ε * (ι * ι) * ε by noncomm_ring]
  rw [hι]
  noncomm_ring

/-- Hole and particle projectors are orthogonal: `N_hole * N = 0`. -/
theorem holeNumber_mul_particleNumber_eq_zero
    (ε ι : A)
    (hε : ε * ε = 0)
    :
    holeNumber ε ι * particleNumber ε ι = 0 := by
  unfold particleNumber holeNumber
  rw [show (ι * ε) * (ε * ι) = ι * (ε * ε) * ι by noncomm_ring]
  rw [hε]
  noncomm_ring

/--
The split-Majorana parity operator is

`Π = c d = 1 - 2N`.

Thus the particle number is equivalently determined by parity:
formally, `1 - Π = 2N`.

Over a ring where `2` is invertible, this is the usual formula
`N = (1 - Π) / 2`.
-/
theorem cMajorana_mul_dMajorana_eq_one_sub_two_particleNumber
    (ε ι : A)
    (hε : ε * ε = 0)
    (hι : ι * ι = 0)
    (hcar : LocalCAR ε ι) :
    cMajorana ε ι * dMajorana ε ι =
      1 - (2 : A) * particleNumber ε ι := by
  unfold cMajorana dMajorana particleNumber LocalCAR at *
  have hιε : ι * ε = 1 - ε * ι := by
    calc
      ι * ε = (ι * ε + ε * ι) - ε * ι := by
        noncomm_ring
      _ = 1 - ε * ι := by
        rw [hcar]
  calc
    (ε + ι) * (ε - ι)
        = ε * ε - ε * ι + ι * ε - ι * ι := by
          noncomm_ring
    _ = 0 - ε * ι + (1 - ε * ι) - 0 := by
          rw [hε, hι, hιε]
    _ = 1 - (2 : A) * (ε * ι) := by
          noncomm_ring

/--
Equivalent parity-to-number identity:

`1 - c d = 2N`.

This avoids division by `2`.
-/
theorem one_sub_cMajorana_mul_dMajorana_eq_two_particleNumber
    (ε ι : A)
    (hε : ε * ε = 0)
    (hι : ι * ι = 0)
    (hcar : LocalCAR ε ι) :
    1 - cMajorana ε ι * dMajorana ε ι =
      (2 : A) * particleNumber ε ι := by
  rw [cMajorana_mul_dMajorana_eq_one_sub_two_particleNumber ε ι hε hι hcar]
  noncomm_ring

end SplitMajoranaNumber
