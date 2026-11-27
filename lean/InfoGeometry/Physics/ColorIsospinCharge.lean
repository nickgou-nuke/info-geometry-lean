/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.ColorOccupationPolynomials
import Mathlib.Tactic.NoncommRing

/-!
# Ordered color-isospin charge table

The right-hand side is a polynomial expansion of a scaled charge expression.
It becomes an eigenvalue/spectral decomposition only after the sector terms
are proved to be mutually orthogonal idempotents on a specified module.
-/
namespace InfoGeometry.Physics.ColorIsospinCharge

open ColorOccupationPolynomials

variable {A : Type*} [Ring A]

def isoPlus (u v : A) : A := u * (1 - v)
def isoMinus (u v : A) : A := (1 - u) * v
def isoPair (u v : A) : A := u * v + (1 - u) * (1 - v)

theorem iso_partition (u v : A) :
    isoPlus u v + isoMinus u v + isoPair u v = 1 := by
  simp only [isoPlus, isoMinus, isoPair]
  noncomm_ring

/-- The scalar-free polynomial six-times-charge convention of the source note. -/
def charge6 (a b c u v : A) : A :=
  number a b c + (3 : ℕ) • (isoPlus u v - isoMinus u v)

/-- Exact ordered multiplet expansion, with no claim that the summands are
    spectral projections in an arbitrary ring. -/
theorem charge6_expansion (a b c u v : A) :
    charge6 a b c u v =
      (4 : ℕ) • (quark a b c * isoPlus u v) -
      (2 : ℕ) • (quark a b c * isoMinus u v) +
      quark a b c * isoPair u v +
      (5 : ℕ) • (diquark a b c * isoPlus u v) -
      diquark a b c * isoMinus u v +
      (2 : ℕ) • (diquark a b c * isoPair u v) +
      (6 : ℕ) • (baryon a b c * isoPlus u v) +
      (3 : ℕ) • (baryon a b c * isoPair u v) +
      (3 : ℕ) • (vacuum a b c * isoPlus u v) -
      (3 : ℕ) • (vacuum a b c * isoMinus u v) := by
  have h4 : ∀ x : A, (4 : ℕ) • x = x + x + x + x := fun x => by
    rw [show (4 : ℕ) = 2 + 2 from rfl, add_nsmul, two_nsmul]; abel
  have h5 : ∀ x : A, (5 : ℕ) • x = x + x + x + x + x := fun x => by
    rw [show (5 : ℕ) = 3 + 2 from rfl, add_nsmul, three_nsmul, two_nsmul]; abel
  have h6 : ∀ x : A, (6 : ℕ) • x = x + x + x + x + x + x := fun x => by
    rw [show (6 : ℕ) = 3 + 3 from rfl, add_nsmul, three_nsmul]; abel
  simp only [charge6, number, quark, diquark, baryon, vacuum,
    isoPlus, isoMinus, isoPair, two_nsmul, three_nsmul, h4, h5, h6]
  noncomm_ring

/-! ## Orthogonal Idempotent Projector Partitions & Spectral Eigenspaces -/

section IdempotentPartitions

private def bitProj (f : Bool) (x : A) : A :=
  if f then x else 1 - x

private theorem bitProj_mul_same {x : A} (hx : x * x = x) (i j : Bool) :
    bitProj i x * bitProj j x = if i = j then bitProj i x else 0 := by
  cases i <;> cases j <;> simp only [bitProj, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false]
  · calc
      (1 - x) * (1 - x) = 1 - x - x + x * x := by noncomm_ring
      _ = 1 - x := by rw [hx]; abel
  · calc
      (1 - x) * x = x - x * x := by noncomm_ring
      _ = 0 := by rw [hx, sub_self]
  · calc
      x * (1 - x) = x - x * x := by noncomm_ring
      _ = 0 := by rw [hx, sub_self]
  · exact hx

private theorem bitProj_comm {x y : A} (hxy : x * y = y * x) (i j : Bool) :
    bitProj i x * bitProj j y = bitProj j y * bitProj i x := by
  cases i <;> cases j <;> simp only [bitProj, ↓reduceIte, Bool.false_eq_true]
  · calc
      (1 - x) * (1 - y) = 1 - x - y + x * y := by noncomm_ring
      _ = 1 - y - x + y * x := by rw [hxy]; abel
      _ = (1 - y) * (1 - x) := by noncomm_ring
  · calc
      (1 - x) * y = y - x * y := by noncomm_ring
      _ = y - y * x := by rw [hxy]
      _ = y * (1 - x) := by noncomm_ring
  · calc
      x * (1 - y) = x - x * y := by noncomm_ring
      _ = x - y * x := by rw [hxy]
      _ = (1 - y) * x := by noncomm_ring
  · exact hxy

private def colorAtom (i₁ i₂ i₃ : Bool) (a b c : A) : A :=
  bitProj i₁ a * bitProj i₂ b * bitProj i₃ c

private theorem colorAtom_mul {a b c : A}
    (ha : a * a = a) (hb : b * b = b) (hc : c * c = c)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (i₁ i₂ i₃ j₁ j₂ j₃ : Bool) :
    colorAtom i₁ i₂ i₃ a b c * colorAtom j₁ j₂ j₃ a b c =
      if i₁ = j₁ ∧ i₂ = j₂ ∧ i₃ = j₃ then colorAtom i₁ i₂ i₃ a b c else 0 := by
  dsimp [colorAtom]
  have h1 := bitProj_comm hac.symm i₃ j₁
  have h2 := bitProj_comm hab.symm i₂ j₁
  have h3 := bitProj_comm hbc.symm i₃ j₂
  calc
    (bitProj i₁ a * bitProj i₂ b * bitProj i₃ c) *
        (bitProj j₁ a * bitProj j₂ b * bitProj j₃ c) =
      bitProj i₁ a * (bitProj i₂ b * (bitProj i₃ c * bitProj j₁ a)) *
        bitProj j₂ b * bitProj j₃ c := by noncomm_ring
    _ = bitProj i₁ a * ((bitProj i₂ b * bitProj j₁ a) * bitProj i₃ c) *
        bitProj j₂ b * bitProj j₃ c := by rw [h1]; noncomm_ring
    _ = (bitProj i₁ a * bitProj j₁ a) * (bitProj i₂ b * (bitProj i₃ c * bitProj j₂ b)) *
        bitProj j₃ c := by rw [h2]; noncomm_ring
    _ = (bitProj i₁ a * bitProj j₁ a) * (bitProj i₂ b * bitProj j₂ b) *
        (bitProj i₃ c * bitProj j₃ c) := by rw [h3]; noncomm_ring
    _ = (if i₁ = j₁ then bitProj i₁ a else 0) *
        (if i₂ = j₂ then bitProj i₂ b else 0) *
        (if i₃ = j₃ then bitProj i₃ c else 0) := by
      rw [bitProj_mul_same ha, bitProj_mul_same hb, bitProj_mul_same hc]
    _ = if i₁ = j₁ ∧ i₂ = j₂ ∧ i₃ = j₃
        then bitProj i₁ a * bitProj i₂ b * bitProj i₃ c else 0 := by
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;> by_cases h₃ : i₃ = j₃ <;>
        simp [h₁, h₂, h₃]

private def isoAtom (i₁ i₂ : Bool) (u v : A) : A :=
  bitProj i₁ u * bitProj i₂ v

private theorem pair_idem {x y : A} (hx : x * x = x) (hy : y * y = y) (hxy : x * y = y * x) :
    (x * y) * (x * y) = x * y := by
  calc
    (x * y) * (x * y) = x * (y * x) * y := by noncomm_ring
    _ = x * (x * y) * y := by rw [hxy]
    _ = (x * x) * (y * y) := by noncomm_ring
    _ = x * y := by rw [hx, hy]

private theorem isoAtom_mul {u v : A}
    (hu : u * u = u) (hv : v * v = v) (huv : u * v = v * u)
    (i₁ i₂ j₁ j₂ : Bool) :
    isoAtom i₁ i₂ u v * isoAtom j₁ j₂ u v =
      if i₁ = j₁ ∧ i₂ = j₂ then isoAtom i₁ i₂ u v else 0 := by
  dsimp [isoAtom]
  have h1 := bitProj_comm huv.symm i₂ j₁
  calc
    (bitProj i₁ u * bitProj i₂ v) * (bitProj j₁ u * bitProj j₂ v) =
      bitProj i₁ u * (bitProj i₂ v * bitProj j₁ u) * bitProj j₂ v := by noncomm_ring
    _ = (bitProj i₁ u * bitProj j₁ u) * (bitProj i₂ v * bitProj j₂ v) := by
      rw [h1]; noncomm_ring
    _ = (if i₁ = j₁ then bitProj i₁ u else 0) *
        (if i₂ = j₂ then bitProj i₂ v else 0) := by
      rw [bitProj_mul_same hu, bitProj_mul_same hv]
    _ = if i₁ = j₁ ∧ i₂ = j₂ then bitProj i₁ u * bitProj i₂ v else 0 := by
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;> simp [h₁, h₂]

private theorem color_eq_atoms (a b c : A) :
    vacuum a b c = colorAtom false false false a b c ∧
    quark a b c = colorAtom true false false a b c +
      colorAtom false true false a b c + colorAtom false false true a b c ∧
    diquark a b c = colorAtom false true true a b c +
      colorAtom true false true a b c + colorAtom true true false a b c ∧
    baryon a b c = colorAtom true true true a b c := by
  refine ⟨rfl, rfl, rfl, rfl⟩

private theorem iso_eq_atoms (u v : A) :
    isoPlus u v = isoAtom true false u v ∧
    isoMinus u v = isoAtom false true u v ∧
    isoPair u v = isoAtom true true u v + isoAtom false false u v := by
  refine ⟨rfl, rfl, rfl⟩

/-- Under commuting idempotents `(a, b, c)`, the four color sectors
    `vacuum, quark, diquark, baryon` are pairwise orthogonal idempotent projectors
    summing to `1`. -/
theorem color_orthogonal_idempotent_partition {a b c : A}
    (ha : a * a = a) (hb : b * b = b) (hc : c * c = c)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    let P0 := vacuum a b c
    let P1 := quark a b c
    let P2 := diquark a b c
    let P3 := baryon a b c
    (P0 * P0 = P0 ∧ P1 * P1 = P1 ∧ P2 * P2 = P2 ∧ P3 * P3 = P3) ∧
    (P0 * P1 = 0 ∧ P0 * P2 = 0 ∧ P0 * P3 = 0 ∧
     P1 * P0 = 0 ∧ P1 * P2 = 0 ∧ P1 * P3 = 0 ∧
     P2 * P0 = 0 ∧ P2 * P1 = 0 ∧ P2 * P3 = 0 ∧
     P3 * P0 = 0 ∧ P3 * P1 = 0 ∧ P3 * P2 = 0) ∧
    P0 + P1 + P2 + P3 = 1 := by
  intro P0 P1 P2 P3
  rcases color_eq_atoms a b c with ⟨h0, h1, h2, h3⟩
  have hm := colorAtom_mul ha hb hc hab hac hbc
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    sector_sum a b c⟩ <;>
  · dsimp [P0, P1, P2, P3]
    simp only [h0, h1, h2, h3, add_mul, mul_add, hm,
      Bool.false_eq_true, Bool.true_eq_false, and_self, and_true, and_false,
      ↓reduceIte, add_zero, zero_add]

/-- Under commuting idempotents `(u, v)`, `isoPlus, isoMinus, isoPair` are
    pairwise orthogonal idempotent projectors summing to `1`. -/
theorem iso_orthogonal_idempotent_partition {u v : A}
    (hu : u * u = u) (hv : v * v = v) (huv : u * v = v * u) :
    let Qp := isoPlus u v
    let Qm := isoMinus u v
    let Q0 := isoPair u v
    (Qp * Qp = Qp ∧ Qm * Qm = Qm ∧ Q0 * Q0 = Q0) ∧
    (Qp * Qm = 0 ∧ Qp * Q0 = 0 ∧
     Qm * Qp = 0 ∧ Qm * Q0 = 0 ∧
     Q0 * Qp = 0 ∧ Q0 * Qm = 0) ∧
    Qp + Qm + Q0 = 1 := by
  intro Qp Qm Q0
  rcases iso_eq_atoms u v with ⟨hp, hm_, h0⟩
  have hm := isoAtom_mul hu hv huv
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, iso_partition u v⟩ <;>
  · dsimp [Qp, Qm, Q0]
    simp only [hp, hm_, h0, add_mul, mul_add, hm,
      Bool.false_eq_true, Bool.true_eq_false, and_self, and_true, and_false,
      ↓reduceIte, add_zero, zero_add]

private theorem colorAtom_comm_isoAtom {a b c u v : A}
    (hau : a * u = u * a) (hav : a * v = v * a)
    (hbu : b * u = u * b) (hbv : b * v = v * b)
    (hcu : c * u = u * c) (hcv : c * v = v * c)
    (i₁ i₂ i₃ j₁ j₂ : Bool) :
    colorAtom i₁ i₂ i₃ a b c * isoAtom j₁ j₂ u v =
      isoAtom j₁ j₂ u v * colorAtom i₁ i₂ i₃ a b c := by
  dsimp [colorAtom, isoAtom]
  have ha_u := bitProj_comm hau i₁ j₁
  have ha_v := bitProj_comm hav i₁ j₂
  have hb_u := bitProj_comm hbu i₂ j₁
  have hb_v := bitProj_comm hbv i₂ j₂
  have hc_u := bitProj_comm hcu i₃ j₁
  have hc_v := bitProj_comm hcv i₃ j₂
  calc
    (bitProj i₁ a * bitProj i₂ b * bitProj i₃ c) * (bitProj j₁ u * bitProj j₂ v) =
      bitProj i₁ a * bitProj i₂ b * ((bitProj i₃ c * bitProj j₁ u) * bitProj j₂ v) := by
        noncomm_ring
    _ = bitProj i₁ a * ((bitProj i₂ b * bitProj j₁ u) * (bitProj i₃ c * bitProj j₂ v)) := by
        rw [hc_u]; noncomm_ring
    _ = bitProj i₁ a * (bitProj j₁ u * ((bitProj i₂ b * bitProj j₂ v) * bitProj i₃ c)) := by
        rw [hb_u, hc_v]; noncomm_ring
    _ = (bitProj i₁ a * bitProj j₁ u) * (bitProj j₂ v * (bitProj i₂ b * bitProj i₃ c)) := by
        rw [hb_v]; noncomm_ring
    _ = bitProj j₁ u * ((bitProj i₁ a * bitProj j₂ v) * (bitProj i₂ b * bitProj i₃ c)) := by
        rw [ha_u]; noncomm_ring
    _ = (bitProj j₁ u * bitProj j₂ v) * (bitProj i₁ a * bitProj i₂ b * bitProj i₃ c) := by
        rw [ha_v]; noncomm_ring

/-- Under mutually commuting idempotents `(a, b, c, u, v)`, every product of a color
    projector `P ∈ {vacuum, quark, diquark, baryon}` and an isospin projector
    `Q ∈ {isoPlus, isoMinus, isoPair}` is an idempotent projector, distinct pairs are
    orthogonal, and `charge6` satisfies its exact integer eigenvalue equations on every
    multiplet sector! -/
theorem charge6_spectral_projector_decomposition {a b c u v : A}
    (ha : a * a = a) (hb : b * b = b) (hc : c * c = c)
    (hu : u * u = u) (hv : v * v = v)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (huv : u * v = v * u)
    (hau : a * u = u * a) (hav : a * v = v * a)
    (hbu : b * u = u * b) (hbv : b * v = v * b)
    (hcu : c * u = u * c) (hcv : c * v = v * c) :
    let P0 := vacuum a b c
    let P1 := quark a b c
    let P2 := diquark a b c
    let P3 := baryon a b c
    let Qp := isoPlus u v
    let Qm := isoMinus u v
    let Q0 := isoPair u v
    let C6 := charge6 a b c u v
    (P0 * Qp = Qp * P0 ∧ P0 * Qm = Qm * P0 ∧ P0 * Q0 = Q0 * P0 ∧
     P1 * Qp = Qp * P1 ∧ P1 * Qm = Qm * P1 ∧ P1 * Q0 = Q0 * P1 ∧
     P2 * Qp = Qp * P2 ∧ P2 * Qm = Qm * P2 ∧ P2 * Q0 = Q0 * P2 ∧
     P3 * Qp = Qp * P3 ∧ P3 * Qm = Qm * P3 ∧ P3 * Q0 = Q0 * P3) ∧
    ((P1 * Qp) * (P1 * Qp) = P1 * Qp ∧ (P1 * Qm) * (P1 * Qm) = P1 * Qm ∧
     (P1 * Q0) * (P1 * Q0) = P1 * Q0 ∧
     (P2 * Qp) * (P2 * Qp) = P2 * Qp ∧ (P2 * Qm) * (P2 * Qm) = P2 * Qm ∧
     (P2 * Q0) * (P2 * Q0) = P2 * Q0 ∧
     (P3 * Qp) * (P3 * Qp) = P3 * Qp ∧ (P3 * Qm) * (P3 * Qm) = P3 * Qm ∧
     (P3 * Q0) * (P3 * Q0) = P3 * Q0 ∧
     (P0 * Qp) * (P0 * Qp) = P0 * Qp ∧ (P0 * Qm) * (P0 * Qm) = P0 * Qm ∧
     (P0 * Q0) * (P0 * Q0) = P0 * Q0) ∧
    (C6 * (P1 * Qp) = (4 : ℕ) • (P1 * Qp) ∧
     C6 * (P1 * Qm) + (2 : ℕ) • (P1 * Qm) = 0 ∧
     C6 * (P1 * Q0) = P1 * Q0 ∧
     C6 * (P2 * Qp) = (5 : ℕ) • (P2 * Qp) ∧
     C6 * (P2 * Qm) + (P2 * Qm) = 0 ∧
     C6 * (P2 * Q0) = (2 : ℕ) • (P2 * Q0) ∧
     C6 * (P3 * Qp) = (6 : ℕ) • (P3 * Qp) ∧
     C6 * (P3 * Qm) = 0 ∧
     C6 * (P3 * Q0) = (3 : ℕ) • (P3 * Q0) ∧
     C6 * (P0 * Qp) = (3 : ℕ) • (P0 * Qp) ∧
     C6 * (P0 * Qm) + (3 : ℕ) • (P0 * Qm) = 0 ∧
     C6 * (P0 * Q0) = 0) := by
  intro P0 P1 P2 P3 Qp Qm Q0 C6
  rcases color_orthogonal_idempotent_partition ha hb hc hab hac hbc with
    ⟨⟨hP0, hP1, hP2, hP3⟩,
     ⟨h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32⟩, _⟩
  rcases iso_orthogonal_idempotent_partition hu hv huv with
    ⟨⟨hQp, hQm, hQ0⟩, ⟨hpm, hp0, hmp, hm0, h0p, h0m⟩, _⟩
  rcases color_eq_atoms a b c with ⟨hc0, hc1, hc2, hc3⟩
  rcases iso_eq_atoms u v with ⟨hip, him, hi0⟩
  have hca := colorAtom_comm_isoAtom hau hav hbu hbv hcu hcv
  have hc0p : P0 * Qp = Qp * P0 := by
    dsimp [P0, Qp]; rw [hc0, hip, hca]
  have hc0m : P0 * Qm = Qm * P0 := by
    dsimp [P0, Qm]; rw [hc0, him, hca]
  have hc00 : P0 * Q0 = Q0 * P0 := by
    dsimp [P0, Q0]; rw [hc0, hi0, mul_add, add_mul, hca, hca]
  have hc1p : P1 * Qp = Qp * P1 := by
    dsimp [P1, Qp]; rw [hc1, hip, add_mul, add_mul, mul_add, mul_add, hca, hca, hca]
  have hc1m : P1 * Qm = Qm * P1 := by
    dsimp [P1, Qm]; rw [hc1, him, add_mul, add_mul, mul_add, mul_add, hca, hca, hca]
  have hc10 : P1 * Q0 = Q0 * P1 := by
    dsimp [P1, Q0]; rw [hc1, hi0]; simp only [add_mul, mul_add, hca]; abel
  have hc2p : P2 * Qp = Qp * P2 := by
    dsimp [P2, Qp]; rw [hc2, hip, add_mul, add_mul, mul_add, mul_add, hca, hca, hca]
  have hc2m : P2 * Qm = Qm * P2 := by
    dsimp [P2, Qm]; rw [hc2, him, add_mul, add_mul, mul_add, mul_add, hca, hca, hca]
  have hc20 : P2 * Q0 = Q0 * P2 := by
    dsimp [P2, Q0]; rw [hc2, hi0]; simp only [add_mul, mul_add, hca]; abel
  have hc3p : P3 * Qp = Qp * P3 := by
    dsimp [P3, Qp]; rw [hc3, hip, hca]
  have hc3m : P3 * Qm = Qm * P3 := by
    dsimp [P3, Qm]; rw [hc3, him, hca]
  have hc30 : P3 * Q0 = Q0 * P3 := by
    dsimp [P3, Q0]; rw [hc3, hi0, mul_add, add_mul, hca, hca]
  have hid1p : (P1 * Qp) * (P1 * Qp) = P1 * Qp := pair_idem hP1 hQp hc1p
  have hid1m : (P1 * Qm) * (P1 * Qm) = P1 * Qm := pair_idem hP1 hQm hc1m
  have hid10 : (P1 * Q0) * (P1 * Q0) = P1 * Q0 := pair_idem hP1 hQ0 hc10
  have hid2p : (P2 * Qp) * (P2 * Qp) = P2 * Qp := pair_idem hP2 hQp hc2p
  have hid2m : (P2 * Qm) * (P2 * Qm) = P2 * Qm := pair_idem hP2 hQm hc2m
  have hid20 : (P2 * Q0) * (P2 * Q0) = P2 * Q0 := pair_idem hP2 hQ0 hc20
  have hid3p : (P3 * Qp) * (P3 * Qp) = P3 * Qp := pair_idem hP3 hQp hc3p
  have hid3m : (P3 * Qm) * (P3 * Qm) = P3 * Qm := pair_idem hP3 hQm hc3m
  have hid30 : (P3 * Q0) * (P3 * Q0) = P3 * Q0 := pair_idem hP3 hQ0 hc30
  have hid0p : (P0 * Qp) * (P0 * Qp) = P0 * Qp := pair_idem hP0 hQp hc0p
  have hid0m : (P0 * Qm) * (P0 * Qm) = P0 * Qm := pair_idem hP0 hQm hc0m
  have hid00 : (P0 * Q0) * (P0 * Q0) = P0 * Q0 := pair_idem hP0 hQ0 hc00
  have hC6_short :
      C6 = (P1 + (2 : ℕ) • P2 + (3 : ℕ) • P3) + (3 : ℕ) • (Qp - Qm) := by
    dsimp [C6, P1, P2, P3, Qp, Qm, charge6]
    rw [number_expansion]
  have hcol_mul_P1 : (P1 + (2 : ℕ) • P2 + (3 : ℕ) • P3) * P1 = P1 := by
    dsimp [P1, P2, P3]
    rw [two_nsmul, three_nsmul]
    simp only [add_mul, hP1, h21, h31, add_zero]
  have hcol_mul_P2 : (P1 + (2 : ℕ) • P2 + (3 : ℕ) • P3) * P2 = (2 : ℕ) • P2 := by
    dsimp [P1, P2, P3]
    rw [two_nsmul, three_nsmul]
    simp only [add_mul, h12, hP2, h32, zero_add, add_zero]
  have hcol_mul_P3 : (P1 + (2 : ℕ) • P2 + (3 : ℕ) • P3) * P3 = (3 : ℕ) • P3 := by
    dsimp [P1, P2, P3]
    rw [two_nsmul, three_nsmul]
    simp only [add_mul, h13, h23, hP3, zero_add]
  have hcol_mul_P0 : (P1 + (2 : ℕ) • P2 + (3 : ℕ) • P3) * P0 = 0 := by
    dsimp [P0, P1, P2, P3]
    rw [two_nsmul, three_nsmul]
    simp only [add_mul, h10, h20, h30, add_zero]
  have hiso_mul_Qp : (3 : ℕ) • (Qp - Qm) * Qp = (3 : ℕ) • Qp := by
    dsimp [Qp, Qm]
    rw [three_nsmul, three_nsmul]
    simp only [add_mul, sub_mul, hQp, hmp, sub_zero]
  have hiso_mul_Qm' : (3 : ℕ) • (Qp - Qm) * Qm = -((3 : ℕ) • Qm) := by
    dsimp [Qp, Qm]
    rw [three_nsmul]
    simp only [add_mul, sub_mul, hpm, hQm, zero_sub]
    abel
  have hiso_mul_Q0 : (3 : ℕ) • (Qp - Qm) * Q0 = 0 := by
    dsimp [Qp, Qm, Q0]
    rw [three_nsmul]
    simp only [add_mul, sub_mul, hp0, hm0, sub_zero, add_zero]
  have hC6_eval :
      ∀ {P Q : A}, P * Q = Q * P →
        C6 * (P * Q) =
          ((P1 + (2 : ℕ) • P2 + (3 : ℕ) • P3) * P) * Q +
          ((3 : ℕ) • (Qp - Qm) * Q) * P := by
    intro P Q hPQ
    rw [hC6_short, add_mul, ← mul_assoc]
    congr 1
    rw [hPQ, ← mul_assoc]
  have h4 : ∀ x : A, (4 : ℕ) • x = x + (x + x + x) := fun x => by
    rw [show (4 : ℕ) = 1 + 3 from rfl, add_nsmul, one_nsmul, three_nsmul]
    abel
  have h5 : ∀ x : A, (5 : ℕ) • x = (x + x) + (x + x + x) := fun x => by
    rw [show (5 : ℕ) = 2 + 3 from rfl, add_nsmul, two_nsmul, three_nsmul]
    abel
  have h6 : ∀ x : A, (6 : ℕ) • x = (x + x + x) + (x + x + x) := fun x => by
    rw [show (6 : ℕ) = 3 + 3 from rfl, add_nsmul, three_nsmul]
    abel
  refine ⟨⟨hc0p, hc0m, hc00, hc1p, hc1m, hc10, hc2p, hc2m, hc20, hc3p, hc3m, hc30⟩,
    ⟨hid1p, hid1m, hid10, hid2p, hid2m, hid20, hid3p, hid3m, hid30, hid0p, hid0m, hid00⟩,
    ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hC6_eval hc1p, hcol_mul_P1, hiso_mul_Qp, h4]
    simp only [three_nsmul, add_mul, hc1p.symm]; abel
  · rw [hC6_eval hc1m, hcol_mul_P1, hiso_mul_Qm']
    simp only [two_nsmul, three_nsmul, neg_mul, add_mul, hc1m.symm]; abel
  · rw [hC6_eval hc10, hcol_mul_P1, hiso_mul_Q0, zero_mul, add_zero]
  · rw [hC6_eval hc2p, hcol_mul_P2, hiso_mul_Qp, h5]
    simp only [two_nsmul, three_nsmul, add_mul, hc2p.symm]; abel
  · rw [hC6_eval hc2m, hcol_mul_P2, hiso_mul_Qm']
    simp only [two_nsmul, three_nsmul, neg_mul, add_mul, hc2m.symm]; abel
  · rw [hC6_eval hc20, hcol_mul_P2, hiso_mul_Q0, zero_mul, add_zero]
    simp only [two_nsmul, add_mul]
  · rw [hC6_eval hc3p, hcol_mul_P3, hiso_mul_Qp, h6]
    simp only [three_nsmul, add_mul, hc3p.symm]; abel
  · rw [hC6_eval hc3m, hcol_mul_P3, hiso_mul_Qm']
    simp only [three_nsmul, neg_mul, add_mul, hc3m.symm]; abel
  · rw [hC6_eval hc30, hcol_mul_P3, hiso_mul_Q0, zero_mul, add_zero]
    simp only [three_nsmul, add_mul]
  · rw [hC6_eval hc0p, hcol_mul_P0, zero_mul, zero_add, hiso_mul_Qp]
    simp only [three_nsmul, add_mul, hc0p.symm]
  · rw [hC6_eval hc0m, hcol_mul_P0, zero_mul, zero_add, hiso_mul_Qm']
    simp only [three_nsmul, neg_mul, add_mul, hc0m.symm]; abel
  · rw [hC6_eval hc00, hcol_mul_P0, zero_mul, hiso_mul_Q0, zero_mul, add_zero]

end IdempotentPartitions

end InfoGeometry.Physics.ColorIsospinCharge
