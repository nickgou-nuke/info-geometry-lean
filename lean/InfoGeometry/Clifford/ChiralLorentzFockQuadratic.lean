import InfoGeometry.Clifford.ChiralLorentzCARLift
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl44Witt
import InfoGeometry.Clifford.JordanWignerCAR

/-!
# Quadratic CAR operators in the split Witt carrier

This owner specializes the generic noncommutative quadratic-CAR theorems to the
native split `Cl(4,4)` Witt generators.  The coefficients are Clifford
operators, not scalars: `adag i * a j` is an actual quadratic operator in the
associative Clifford algebra.
-/

noncomputable section

namespace InfoGeometry.Clifford.ChiralLorentzFockQuadratic

open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Clifford.ChiralLorentzCARLift
open InfoGeometry.Clifford.JordanWignerBridge
open InfoGeometry.Clifford.JordanWignerCAR

abbrev FockOperator := InfoGeometry.Clifford.Cl44

def quadraticWittGenerator (i j : Fin 4) : FockOperator :=
  adag i * a j

def wittNumberOperator (i : Fin 4) : FockOperator :=
  quadraticWittGenerator i i

theorem quadraticWittGenerator_eq (i j : Fin 4) :
    quadraticWittGenerator i j = adag i * a j := rfl

theorem wittNumberOperator_eq (i : Fin 4) :
    wittNumberOperator i = adag i * a i := rfl

theorem wittNumber_commutator_annihilation (i : Fin 4) :
    algebraCommutator (wittNumberOperator i) (a i) = -(a i) := by
  simpa [wittNumberOperator, quadraticWittGenerator] using
    (numberOperator_commutator_annihilation
      (creation := adag i) (annihilation := a i)
      (hannihilation := a_sq_zero i)
      (hcar := by simpa [add_comm] using (witt_CAR_eq i)))

theorem wittNumber_commutator_creation (i : Fin 4) :
    algebraCommutator (wittNumberOperator i) (adag i) = adag i := by
  simpa [wittNumberOperator, quadraticWittGenerator] using
    (numberOperator_commutator_creation
      (creation := adag i) (annihilation := a i)
      (hcreation := adag_sq_zero i)
      (hcar := by simpa [add_comm] using (witt_CAR_eq i)))

theorem quadraticWittGenerator_commutator_annihilation
    (i j k : Fin 4) :
    algebraCommutator (quadraticWittGenerator i j) (a k) =
      if i = k then -(a j) else 0 := by
  unfold algebraCommutator quadraticWittGenerator
  by_cases hik : i = k
  · subst k
    have hcar : a i * adag i + adag i * a i = 1 := witt_CAR_eq i
    have haa : a j * a i = -(a i * a j) :=
      eq_neg_of_add_eq_zero_left (witt_annihilation_anticomm j i)
    have hac : a i * adag i = 1 - adag i * a i :=
      eq_sub_of_add_eq hcar
    rw [if_pos (rfl : i = i)]
    calc
      adag i * a j * a i - a i * (adag i * a j) =
          adag i * (a j * a i) - (a i * adag i) * a j := by
            noncomm_ring
      _ = adag i * (a j * a i) -
          (1 - adag i * a i) * a j := by rw [hac]
      _ = -(a j) := by
        rw [haa]
        noncomm_ring
  · have hcar : a k * adag i + adag i * a k = 0 := by
      simpa [if_neg (Ne.symm hik)] using witt_CAR_ne k i (Ne.symm hik)
    have haa : a j * a k = -(a k * a j) :=
      eq_neg_of_add_eq_zero_left (witt_annihilation_anticomm j k)
    have hac : a k * adag i = -(adag i * a k) :=
      eq_neg_of_add_eq_zero_left hcar
    simp only [if_neg hik]
    calc
      adag i * a j * a k - a k * (adag i * a j) =
          adag i * (a j * a k) - (a k * adag i) * a j := by
            noncomm_ring
      _ = adag i * (a j * a k) -
          (-(adag i * a k)) * a j := by rw [hac]
      _ = 0 := by
        rw [haa]
        noncomm_ring

theorem quadraticWittGenerator_commutator_creation
    (i j k : Fin 4) :
    algebraCommutator (quadraticWittGenerator i j) (adag k) =
      if j = k then adag i else 0 := by
  unfold algebraCommutator quadraticWittGenerator
  by_cases hjk : j = k
  · subst k
    have hcar : a j * adag j + adag j * a j = 1 := witt_CAR_eq j
    have hcc : adag j * adag i = -(adag i * adag j) :=
      eq_neg_of_add_eq_zero_left (witt_creation_anticomm j i)
    have hac : a j * adag j = 1 - adag j * a j :=
      eq_sub_of_add_eq hcar
    rw [if_pos (rfl : j = j)]
    calc
      adag i * a j * adag j - adag j * (adag i * a j) =
          adag i * (a j * adag j) - (adag j * adag i) * a j := by
            noncomm_ring
      _ = adag i * (1 - adag j * a j) -
          (adag j * adag i) * a j := by rw [hac]
      _ = adag i := by
        rw [hcc]
        noncomm_ring
  · have hcar : a j * adag k + adag k * a j = 0 := by
      simpa [if_neg hjk] using witt_CAR_ne j k hjk
    have hcc : adag k * adag i = -(adag i * adag k) :=
      eq_neg_of_add_eq_zero_left (witt_creation_anticomm k i)
    have hac : a j * adag k = -(adag k * a j) :=
      eq_neg_of_add_eq_zero_left hcar
    simp only [if_neg hjk]
    calc
      adag i * a j * adag k - adag k * (adag i * a j) =
          adag i * (a j * adag k) - (adag k * adag i) * a j := by
            noncomm_ring
      _ = adag i * (a j * adag k) -
          (-(adag i * adag k)) * a j := by rw [hcc]
      _ = 0 := by
        rw [hac]
        noncomm_ring

theorem witt_CAR_delta (i j : Fin 4) :
    a i * adag j + adag j * a i = if i = j then 1 else 0 :=
  witt_CAR i j

theorem witt_CAR_off_diagonal (i j : Fin 4) (hij : i ≠ j) :
    a i * adag j + adag j * a i = 0 :=
  witt_CAR_ne i j hij

theorem quadraticWittGenerator_commutator_genuine (i j k l : Fin 4) :
    algebraCommutator (quadraticWittGenerator i j)
        (quadraticWittGenerator k l) =
      (if j = k then quadraticWittGenerator i l else 0) -
        (if l = i then quadraticWittGenerator k j else 0) := by
  unfold algebraCommutator quadraticWittGenerator
  have hcreation :
      adag i * a j * adag k - adag k * (adag i * a j) =
        if j = k then adag i else 0 := by
    by_cases hjk : j = k
    · subst k
      have hcar := witt_CAR_eq j
      have hcar' : a j * adag j = 1 - adag j * a j :=
        (eq_sub_iff_add_eq).2 hcar
      have hcc : adag j * adag i = -(adag i * adag j) :=
        eq_neg_of_add_eq_zero_right (witt_creation_anticomm i j)
      rw [show adag i * a j * adag j - adag j * (adag i * a j) =
          adag i * (a j * adag j) - (adag j * adag i) * a j by
            noncomm_ring]
      rw [hcar', hcc]
      noncomm_ring
    · have hcar : a j * adag k = -(adag k * a j) :=
        eq_neg_of_add_eq_zero_left (by
          simpa [hjk] using witt_CAR j k)
      have hcc : adag k * adag i = -(adag i * adag k) :=
        eq_neg_of_add_eq_zero_right (witt_creation_anticomm i k)
      simp only [if_neg hjk]
      rw [show adag i * a j * adag k - adag k * (adag i * a j) =
          adag i * (a j * adag k) - (adag k * adag i) * a j by
            noncomm_ring]
      rw [hcar, hcc]
      noncomm_ring
  have hannihilation :
      adag i * a j * a l - a l * (adag i * a j) =
        if l = i then -(a j) else 0 := by
    by_cases hli : l = i
    · subst l
      have hcar := witt_CAR_eq i
      have hcar' : a i * adag i = 1 - adag i * a i :=
        (eq_sub_iff_add_eq).2 hcar
      have haa : a j * a i = -(a i * a j) :=
        eq_neg_of_add_eq_zero_right (witt_annihilation_anticomm i j)
      rw [show adag i * a j * a i - a i * (adag i * a j) =
          adag i * (a j * a i) - (a i * adag i) * a j by
            noncomm_ring]
      rw [hcar']
      noncomm_ring [haa]
      simp
    · have hcar : a l * adag i = -(adag i * a l) :=
        eq_neg_of_add_eq_zero_left (by
          simpa [hli] using witt_CAR l i)
      have haa : a l * a j = -(a j * a l) :=
        eq_neg_of_add_eq_zero_right (witt_annihilation_anticomm j l)
      rw [show adag i * a j * a l - a l * (adag i * a j) =
          adag i * (a j * a l) - (a l * adag i) * a j by
            noncomm_ring]
      rw [hcar]
      simp only [if_neg hli]
      noncomm_ring [haa]
  calc
    adag i * a j * (adag k * a l) -
          (adag k * a l) * (adag i * a j) =
        (adag i * a j * adag k - adag k * (adag i * a j)) * a l +
          adag k * (adag i * a j * a l - a l * (adag i * a j)) := by
            noncomm_ring
    _ = (if j = k then adag i else 0) * a l +
          adag k * (if l = i then -(a j) else 0) := by
            rw [hcreation, hannihilation]
    _ = (if j = k then adag i * a l else 0) -
          (if l = i then adag k * a j else 0) := by
            by_cases hjk : j = k
            · by_cases hli : l = i
              · simp [hjk, hli, sub_eq_add_neg]
              · simp [hjk, hli]
            · by_cases hli : l = i
              · simp [hjk, hli, sub_eq_add_neg]
              · simp [hjk, hli]

theorem quadraticWittGenerator_commutator (i j k l : Fin 4) :
    algebraCommutator (quadraticWittGenerator i j)
        (quadraticWittGenerator k l) =
      (if j = k then quadraticWittGenerator i l else 0) -
        (if l = i then quadraticWittGenerator k j else 0) := by
  exact quadraticWittGenerator_commutator_genuine i j k l
/-
  have h₁ : a j * adag k =
      (if j = k then 1 else 0) - adag k * a j :=
    (eq_sub_iff_add_eq).2 (witt_CAR j k)
  have h₂ : a l * adag i =
      (if l = i then 1 else 0) - adag i * a l :=
    (eq_sub_iff_add_eq).2 (witt_CAR l i)
  have hcc : adag k * adag i = -(adag i * adag k) :=
    eq_neg_of_add_eq_zero_right (witt_creation_anticomm i k)
  have haa : a l * a j = -(a j * a l) :=
    eq_neg_of_add_eq_zero_right (witt_annihilation_anticomm j l)
  have hcc' : adag k * (adag i * (a j * a l)) =
      -(adag i * (adag k * (a j * a l))) := by
    rw [← mul_assoc, hcc]
    noncomm_ring
  rw [show adag i * a j * (adag k * a l) =
      adag i * (a j * adag k) * a l by noncomm_ring]
  rw [show adag k * a l * (adag i * a j) =
      adag k * (a l * adag i) * a j by noncomm_ring]
  by_cases hjk : j = k <;> by_cases hli : l = i
  all_goals simp [hjk, hli] at h₁ h₂ ⊢
  all_goals rw [h₁, h₂]
  all_goals simp [hjk, hli] at hcc haa
  all_goals try rw [hcc]
  all_goals try rw [hcc']
  all_goals try rw [haa]
  all_goals try simp
  all_goals noncomm_ring [hcc, haa]
-/

theorem jordanWigner_single_site_creation_square (k : ℕ) :
    jw_u_new k * jw_u_new k = 0 :=
  jw_u_new_sq k

theorem jordanWigner_single_site_annihilation_square (k : ℕ) :
    jw_v_new k * jw_v_new k = 0 :=
  jw_v_new_sq k

theorem jordanWigner_single_site_CAR (k : ℕ) :
    jw_u_new k * jw_v_new k + jw_v_new k * jw_u_new k = 1 :=
  jw_uv_anticomm_new k

end InfoGeometry.Clifford.ChiralLorentzFockQuadratic
