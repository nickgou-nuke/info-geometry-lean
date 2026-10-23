/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Core.DiracSuperalgebra

/-!
# Theorem-safe finite color extension of the square-zero superalgebra

This file deliberately formalizes the algebraic kernel of the proposed
"extended SUSY" intake.  It does not assert a `sl(k|1)` representation or a
physical supersymmetry interpretation.  Centrality is conditional on both
cross-annihilation laws.
-/

namespace InfoGeometry.Core.SuperGrassmannianSusy

open InfoGeometry.Singular.MoorePenrose

variable {R : Type*} [Ring R] [StarRing R]

def jordanProd (x y : R) : R := x * y + y * x

def lieBracket (x y : R) : R := x * y - y * x

def IsGrassmannianTangent (p x : R) : Prop := jordanProd p x = x

def majoranaPlus (d b : R) : R := d + b

def majoranaMinus (d b : R) : R := d - b

def sectorCentralCharge (d b : R) : R := jordanProd d b

def totalCentralCharge {ι : Type*} [Fintype ι] (d b : ι → R) : R :=
  ∑ i, sectorCentralCharge (d i) (b i)

def totalMajoranaPlus {ι : Type*} [Fintype ι] (d b : ι → R) : R :=
  ∑ i, majoranaPlus (d i) (b i)

def totalMajoranaMinus {ι : Type*} [Fintype ι] (d b : ι → R) : R :=
  ∑ i, majoranaMinus (d i) (b i)

structure IsSupercolorSystem {ι : Type*} (d b : ι → R) : Prop where
  mp : ∀ i, IsMoorePenroseInverse (d i) (b i)
  d_mul_d : ∀ i j, d i * d j = 0
  b_mul_b : ∀ i j, b i * b j = 0
  b_mul_d_ne : ∀ {i j}, i ≠ j → b i * d j = 0

structure IsOrthogonalExtendedSusy {ι : Type*} (d b : ι → R) : Prop
    extends IsSupercolorSystem d b where
  d_mul_b_ne : ∀ {i j}, i ≠ j → d i * b j = 0

def colorBoson {ι : Type*} (d b : ι → R) (i j : ι) : R := d i * b j

/-! Distinct middle colors vanish under cross-annihilation. The MP identities
also give the two diagonal absorption laws below. General matching-middle
products require additional hypotheses; the common-source version is proved
in `Core.SupercolorMultiplication`. -/

theorem colorBoson_mul_eq_zero_of_middle_ne
    {ι : Type*} {d b : ι → R} (hS : IsSupercolorSystem d b)
    {i j k l : ι} (hjk : j ≠ k) :
    colorBoson d b i j * colorBoson d b k l = 0 := by
  unfold colorBoson
  calc
    d i * b j * (d k * b l) = d i * (b j * d k) * b l := by
      noncomm_ring
    _ = 0 := by rw [hS.b_mul_d_ne hjk, mul_zero, zero_mul]

theorem colorBoson_mul_left_absorb
    {ι : Type*} {d b : ι → R} (hS : IsSupercolorSystem d b)
    (i j : ι) :
    colorBoson d b i i * colorBoson d b i j = colorBoson d b i j := by
  unfold colorBoson
  calc
    (d i * b i) * (d i * b j) = (d i * b i * d i) * b j := by
      simp only [mul_assoc]
    _ = d i * b j := by rw [hS.mp i |>.aba_eq_a]

theorem colorBoson_mul_right_absorb
    {ι : Type*} {d b : ι → R} (hS : IsSupercolorSystem d b)
    (i j : ι) :
    colorBoson d b i j * colorBoson d b j j = colorBoson d b i j := by
  unfold colorBoson
  calc
    (d i * b j) * (d j * b j) = d i * (b j * d j * b j) := by
      simp only [mul_assoc]
    _ = d i * b j := by rw [hS.mp j |>.bab_eq_b]

theorem star_colorBoson_of_dual
    {ι : Type*} {d b : ι → R} (hdual : ∀ i, b i = star (d i))
    (i j : ι) :
    star (colorBoson d b i j) = colorBoson d b j i := by
  unfold colorBoson
  rw [star_mul, hdual j, hdual i, star_star]

theorem star_sectorCentralCharge_of_dual
    {ι : Type*} {d b : ι → R} (hdual : ∀ i, b i = star (d i))
    (i : ι) :
    star (sectorCentralCharge (d i) (b i)) = sectorCentralCharge (d i) (b i) := by
  unfold sectorCentralCharge jordanProd
  simp only [star_add, star_mul, hdual i, star_star]

theorem star_totalMajoranaPlus_of_dual
    {ι : Type*} [Fintype ι] {d b : ι → R}
    (hdual : ∀ i, b i = star (d i)) :
    star (totalMajoranaPlus d b) = totalMajoranaPlus d b := by
  unfold totalMajoranaPlus majoranaPlus
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [star_add, hdual i, star_star]
  abel

theorem star_totalMajoranaMinus_of_dual
    {ι : Type*} [Fintype ι] {d b : ι → R}
    (hdual : ∀ i, b i = star (d i)) :
    star (totalMajoranaMinus d b) = -totalMajoranaMinus d b := by
  unfold totalMajoranaMinus majoranaMinus
  rw [star_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [star_sub, hdual i, star_star]
  abel

theorem star_totalCentralCharge_of_dual
    {ι : Type*} [Fintype ι] {d b : ι → R}
    (hdual : ∀ i, b i = star (d i)) :
    star (totalCentralCharge d b) = totalCentralCharge d b := by
  unfold totalCentralCharge sectorCentralCharge jordanProd
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [star_add, star_mul, hdual i, star_star]

/-!
The finite-color API intentionally stops at conditional Peirce relations.  In
particular, `IsSupercolorSystem` is not presented as an `sl(k|1)`
representation: closure under a chosen Lie-superbracket, the Jacobi law, and
the representation map are separate hypotheses to be formalized when needed.
-/

lemma tangent_of_square_zero_pair {d b : R}
    (hd : d * d = 0) (h : IsMoorePenroseInverse d b) :
    IsGrassmannianTangent (d * b) d ∧
    IsGrassmannianTangent (d * b) b ∧
    IsGrassmannianTangent (b * d) d ∧
    IsGrassmannianTangent (b * d) b := by
  rcases h.dual_square_zero_orthogonality hd with ⟨hbd, hdb, hbb⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    unfold IsGrassmannianTangent jordanProd
  · calc
      d * b * d + d * (d * b) = d * b * d + (d * d) * b := by noncomm_ring
      _ = d + 0 := by rw [h.aba_eq_a, hd, zero_mul]
      _ = d := add_zero d
  · calc
      d * b * b + b * (d * b) = d * (b * b) + b * d * b := by noncomm_ring
      _ = 0 + b := by rw [hbb, h.bab_eq_b, mul_zero]
      _ = b := zero_add b
  · calc
      b * d * d + d * (b * d) = b * (d * d) + d * b * d := by noncomm_ring
      _ = 0 + d := by rw [hd, h.aba_eq_a, mul_zero]
      _ = d := zero_add d
  · calc
      b * d * b + b * (b * d) = b * d * b + (b * b) * d := by noncomm_ring
      _ = b + 0 := by rw [h.bab_eq_b, hbb, zero_mul]
      _ = b := add_zero b

theorem superGrassmannian_tangent_characterization {d b : R}
    (hd : d * d = 0) (h : IsMoorePenroseInverse d b) :
    IsGrassmannianTangent (d * b) d ∧
    IsGrassmannianTangent (d * b) b ∧
    IsGrassmannianTangent (d * b) (majoranaPlus d b) ∧
    IsGrassmannianTangent (d * b) (majoranaMinus d b) ∧
    (∀ x, IsGrassmannianTangent (d * b) x →
      IsGrassmannianTangent (b * d) x →
      jordanProd (d * b - b * d) x = 0) := by
  rcases tangent_of_square_zero_pair hd h with ⟨hpd, hpb, hqd, hqb⟩
  refine ⟨hpd, hpb, ?_, ?_, ?_⟩
  · unfold IsGrassmannianTangent majoranaPlus jordanProd at *
    calc
      (d * b) * (d + b) + (d + b) * (d * b) =
          ((d * b) * d + d * (d * b)) +
            ((d * b) * b + b * (d * b)) := by noncomm_ring
      _ = d + b := by rw [hpd, hpb]
  · unfold IsGrassmannianTangent majoranaMinus jordanProd at *
    calc
      (d * b) * (d - b) + (d - b) * (d * b) =
          ((d * b) * d + d * (d * b)) -
            ((d * b) * b + b * (d * b)) := by noncomm_ring
      _ = d - b := by rw [hpd, hpb]
  · intro x hx hy
    unfold IsGrassmannianTangent jordanProd at hx hy
    change (d * b - b * d) * x + x * (d * b - b * d) = 0
    calc
      (d * b - b * d) * x + x * (d * b - b * d) =
          ((d * b) * x + x * (d * b)) - ((b * d) * x + x * (b * d)) := by
            noncomm_ring
      _ = x - x := by rw [hx, hy]
      _ = 0 := sub_self x

theorem color_pair_relations {ι : Type*} {d b : ι → R}
    (hS : IsSupercolorSystem d b) (i j : ι) :
    majoranaPlus (d i) (b i) * majoranaPlus (d i) (b i) =
        sectorCentralCharge (d i) (b i) ∧
    majoranaMinus (d i) (b i) * majoranaMinus (d i) (b i) =
        -sectorCentralCharge (d i) (b i) ∧
    (i ≠ j →
      jordanProd (d i) (b j) = colorBoson d b i j ∧
      jordanProd (majoranaPlus (d i) (b i)) (majoranaPlus (d j) (b j)) =
        colorBoson d b i j + colorBoson d b j i ∧
      jordanProd (majoranaMinus (d i) (b i)) (majoranaMinus (d j) (b j)) =
        -(colorBoson d b i j + colorBoson d b j i)) := by
  have hi := hS.mp i
  have hbi : b i * b i = 0 := hS.b_mul_b i i
  constructor
  · unfold majoranaPlus sectorCentralCharge jordanProd
    calc
      (d i + b i) * (d i + b i) =
          d i * d i + (d i * b i + b i * d i) + b i * b i := by noncomm_ring
      _ = d i * b i + b i * d i := by
        rw [hS.d_mul_d i i, hbi, zero_add, add_zero]
  constructor
  · unfold majoranaMinus sectorCentralCharge jordanProd
    calc
      (d i - b i) * (d i - b i) =
          d i * d i - (d i * b i + b i * d i) + b i * b i := by noncomm_ring
      _ = -(d i * b i + b i * d i) := by
        rw [hS.d_mul_d i i, hbi]
        abel
  · intro hij
    have hji := hS.b_mul_d_ne hij.symm
    have hij' := hS.b_mul_d_ne hij
    have hdij := hS.d_mul_d i j
    have hbij := hS.b_mul_b i j
    have hji_d := hS.d_mul_d j i
    have hji_b := hS.b_mul_b j i
    have hdbij := hS.b_mul_d_ne hij
    have hdbji := hS.b_mul_d_ne hij.symm
    refine ⟨?_, ?_, ?_⟩
    · unfold jordanProd colorBoson
      rw [hji, add_zero]
    · unfold jordanProd majoranaPlus colorBoson
      calc
        (d i + b i) * (d j + b j) + (d j + b j) * (d i + b i) =
            (d i * d j + d j * d i) + (b i * b j + b j * b i) +
              (b i * d j + b j * d i) + (d i * b j + d j * b i) := by noncomm_ring
        _ = d i * b j + d j * b i := by
          rw [hdij, hji_d, hbij, hji_b, hdbij, hdbji]
          abel

    · unfold jordanProd majoranaMinus colorBoson
      calc
        (d i - b i) * (d j - b j) + (d j - b j) * (d i - b i) =
            (d i * d j + d j * d i) + (b i * b j + b j * b i) -
              (b i * d j + b j * d i) - (d i * b j + d j * b i) := by noncomm_ring
        _ = -(d i * b j + d j * b i) := by
          rw [hdij, hji_d, hbij, hji_b, hdbij, hdbji]
          abel

theorem extended_susy_centrality {ι : Type*} [Fintype ι]
    {d b : ι → R} (hE : IsOrthogonalExtendedSusy d b) :
    (∀ i j, lieBracket (sectorCentralCharge (d i) (b i)) (d j) = 0 ∧
      lieBracket (sectorCentralCharge (d i) (b i)) (b j) = 0) ∧
    (∀ j, lieBracket (totalCentralCharge d b) (d j) = 0 ∧
      lieBracket (totalCentralCharge d b) (b j) = 0) := by
  have hsector : ∀ i j,
      lieBracket (sectorCentralCharge (d i) (b i)) (d j) = 0 ∧
        lieBracket (sectorCentralCharge (d i) (b i)) (b j) = 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      have hi := hE.mp i
      have hdd := hE.toIsSupercolorSystem.d_mul_d i i
      have hbb := hE.toIsSupercolorSystem.b_mul_b i i
      constructor
      · unfold lieBracket sectorCentralCharge jordanProd
        calc
          (d i * b i + b i * d i) * d i - d i * (d i * b i + b i * d i) =
              d i * b i * d i + b i * d i * d i - d i * d i * b i - d i * b i * d i := by noncomm_ring
          _ = 0 := by
            rw [hi.aba_eq_a, mul_assoc (b i) (d i) (d i), hdd]
            simp only [mul_zero, zero_mul, sub_zero]
            abel
      · unfold lieBracket sectorCentralCharge jordanProd
        calc
          (d i * b i + b i * d i) * b i - b i * (d i * b i + b i * d i) =
              d i * b i * b i + b i * d i * b i - b i * d i * b i - b i * b i * d i := by noncomm_ring
          _ = 0 := by
            rw [hi.bab_eq_b, mul_assoc (d i) (b i) (b i), hbb]
            simp only [mul_zero, zero_mul, sub_zero]
            abel
    · have h := hE.toIsSupercolorSystem
      constructor <;> unfold lieBracket sectorCentralCharge jordanProd
      · calc
          (d i * b i + b i * d i) * d j - d j * (d i * b i + b i * d i) =
              d i * (b i * d j) + b i * (d i * d j) -
                (d j * d i) * b i - (d j * b i) * d i := by noncomm_ring
          _ = 0 := by rw [h.b_mul_d_ne hij, h.d_mul_d i j, h.d_mul_d j i,
            hE.d_mul_b_ne (Ne.symm hij)]; simp
      · calc
          (d i * b i + b i * d i) * b j - b j * (d i * b i + b i * d i) =
              d i * (b i * b j) + b i * (d i * b j) -
                (b j * d i) * b i - (b j * b i) * d i := by noncomm_ring
          _ = 0 := by rw [h.b_mul_b i j, hE.d_mul_b_ne hij,
            h.b_mul_d_ne (Ne.symm hij), h.b_mul_b j i]; simp
  constructor
  · exact hsector
  · intro j
    have hsum : ∀ x, (∀ i, lieBracket (sectorCentralCharge (d i) (b i)) x = 0) →
        lieBracket (totalCentralCharge d b) x = 0 := by
      intro x hx
      unfold lieBracket totalCentralCharge
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_eq_zero (fun i _ => hx i)
    exact ⟨hsum (d j) (fun i => (hsector i j).1),
      hsum (b j) (fun i => (hsector i j).2)⟩

theorem extended_susy_total_charges {ι : Type*} [Fintype ι]
    {d b : ι → R} (hE : IsOrthogonalExtendedSusy d b) :
    totalMajoranaPlus d b * totalMajoranaPlus d b = totalCentralCharge d b ∧
    totalMajoranaMinus d b * totalMajoranaMinus d b = -totalCentralCharge d b ∧
    jordanProd (totalMajoranaPlus d b) (totalMajoranaMinus d b) = 0 := by
  have hcross : ∀ {i j}, i ≠ j →
      (majoranaPlus (d i) (b i)) * majoranaPlus (d j) (b j) = 0 ∧
      (majoranaMinus (d i) (b i)) * majoranaMinus (d j) (b j) = 0 ∧
      (majoranaPlus (d i) (b i)) * majoranaMinus (d j) (b j) = 0 ∧
      (majoranaMinus (d i) (b i)) * majoranaPlus (d j) (b j) = 0 := by
    intro i j hij
    have h := hE.toIsSupercolorSystem
    have h1 : majoranaPlus (d i) (b i) * majoranaPlus (d j) (b j) = 0 := by
      unfold majoranaPlus
      calc
        (d i + b i) * (d j + b j) =
            d i * d j + d i * b j + b i * d j + b i * b j := by noncomm_ring
        _ = 0 := by rw [h.d_mul_d i j, hE.d_mul_b_ne hij,
          h.b_mul_d_ne hij, h.b_mul_b i j]; simp
    have h2 : majoranaMinus (d i) (b i) * majoranaMinus (d j) (b j) = 0 := by
      unfold majoranaMinus
      calc
        (d i - b i) * (d j - b j) =
            d i * d j - d i * b j - b i * d j + b i * b j := by noncomm_ring
        _ = 0 := by rw [h.d_mul_d i j, hE.d_mul_b_ne hij,
          h.b_mul_d_ne hij, h.b_mul_b i j]; simp
    have h3 : majoranaPlus (d i) (b i) * majoranaMinus (d j) (b j) = 0 := by
      calc
        (d i + b i) * (d j - b j) =
            d i * d j - d i * b j + b i * d j - b i * b j := by noncomm_ring
        _ = 0 := by rw [h.d_mul_d i j, hE.d_mul_b_ne hij,
          h.b_mul_d_ne hij, h.b_mul_b i j]; simp
    have h4 : majoranaMinus (d i) (b i) * majoranaPlus (d j) (b j) = 0 := by
      unfold majoranaMinus majoranaPlus
      calc
        (d i - b i) * (d j + b j) =
            d i * d j + d i * b j - b i * d j - b i * b j := by noncomm_ring
        _ = 0 := by rw [h.d_mul_d i j, hE.d_mul_b_ne hij,
          h.b_mul_d_ne hij, h.b_mul_b i j]; simp
    exact ⟨h1, h2, h3, h4⟩
  have hdiagP : ∀ i, majoranaPlus (d i) (b i) * majoranaPlus (d i) (b i) =
      sectorCentralCharge (d i) (b i) := fun i =>
    (color_pair_relations hE.toIsSupercolorSystem i i).1
  have hdiagM : ∀ i, majoranaMinus (d i) (b i) * majoranaMinus (d i) (b i) =
      -sectorCentralCharge (d i) (b i) := fun i =>
    (color_pair_relations hE.toIsSupercolorSystem i i).2.1
  constructor
  · unfold totalMajoranaPlus totalCentralCharge
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · exact hdiagP i
    · intro j _ hji; exact (hcross (Ne.symm hji)).1
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  constructor
  · unfold totalMajoranaMinus totalCentralCharge
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · exact hdiagM i
    · intro j _ hji; exact (hcross (Ne.symm hji)).2.1
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  · unfold jordanProd totalMajoranaPlus totalMajoranaMinus
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hij : i = j
    · subst j
      unfold majoranaPlus majoranaMinus
      calc
        (d i + b i) * (d i - b i) + (d i - b i) * (d i + b i) =
            (d i * d i - b i * b i) + (d i * d i - b i * b i) := by noncomm_ring
        _ = 0 := by rw [hE.toIsSupercolorSystem.d_mul_d i i,
          hE.toIsSupercolorSystem.b_mul_b i i]; simp
    · rw [(hcross hij).2.2.1, (hcross (Ne.symm hij)).2.2.2, add_zero]

theorem n4_extended_susy {d b : Fin 2 → R}
    (hE : IsOrthogonalExtendedSusy d b) :
    totalMajoranaPlus d b * totalMajoranaPlus d b = totalCentralCharge d b :=
  (extended_susy_total_charges hE).1

theorem n8_extended_susy {d b : Fin 4 → R}
    (hE : IsOrthogonalExtendedSusy d b) :
    totalMajoranaPlus d b * totalMajoranaPlus d b = totalCentralCharge d b :=
  (extended_susy_total_charges hE).1

end InfoGeometry.Core.SuperGrassmannianSusy
