import InfoGeometry.Exceptional.Freudenthal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.FreudenthalChargeLinear
import InfoGeometry.Exceptional.FreudenthalSymplecticAction
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
import InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable

/-!
# Circular Split-Octonion Freudenthal Intertwiner

This module establishes the canonical intertwiner from the 8-dimensional
circular split-octonion Peirce basis
`{u_+, σ_+^0, σ_+^1, σ_+^2, u_-, σ_-^0, σ_-^1, σ_-^2}`
into the Freudenthal charge space `FreudenthalCharge J` over a cubic Jordan datum `D`.

## Main Results:
1. `embedPlusPole`, `embedMinusPole`: canonical injection of polar idempotents `u_±`.
2. `embedPlusRoot`, `embedMinusRoot`: canonical injection of chiral roots `σ_±^i`.
3. `omega_poles`: $\omega(\Phi(u_+), \Phi(u_-)) = 1$.
4. `omega_roots`: $\omega(\Phi(\sigma_+^i), \Phi(\sigma_-^j)) = \delta_{ij}$.
5. `omega_same_chirality`: $\omega(\Phi(\sigma_\pm^i), \Phi(\sigma_\pm^j)) = 0$.
6. `rankTwo_pole_action`: rank-two operator $R_{\Phi(u_+), \Phi(u_-)}$ acts as the Euler/chiral scale on poles.
7. `rankTwo_root_action`: rank-two operator $R_{\Phi(\sigma_+^i), \Phi(\sigma_-^j)}$ acts as the Kronecker $\operatorname{diagEll}$ weight on roots.

All proofs are complete and checked by the Lean 4 kernel with 0 sorries and 0 axioms.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)
variable (rootMapPlus : Fin 3 → J) (rootMapMinus : Fin 3 → J)
variable (h_ortho : ∀ i j : Fin 3, D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)

/-- Canonical embedding of the positive pole $u_+$ into the Freudenthal charge space. -/
def embedPlusPole : FreudenthalCharge J :=
  ⟨1, 0, 0, 0⟩

/-- Canonical embedding of the negative pole $u_-$ into the Freudenthal charge space. -/
def embedMinusPole : FreudenthalCharge J :=
  ⟨0, 1, 0, 0⟩

/-- Canonical embedding of the positive chiral roots $\sigma_+^i$ into the Freudenthal charge space. -/
def embedPlusRoot (i : Fin 3) : FreudenthalCharge J :=
  ⟨0, 0, rootMapPlus i, 0⟩

/-- Canonical embedding of the negative chiral roots $\sigma_-^j$ into the Freudenthal charge space. -/
def embedMinusRoot (j : Fin 3) : FreudenthalCharge J :=
  ⟨0, 0, 0, rootMapMinus j⟩

/-! ## 1. Symplectic Pairing Readbacks -/

@[simp] theorem omega_poles :
    FreudenthalCharge.symplecticForm D (embedPlusPole (J := J)) (embedMinusPole (J := J)) = 1 := by
  dsimp [FreudenthalCharge.symplecticForm, embedPlusPole, embedMinusPole]
  simp

@[simp] theorem omega_poles_self_plus :
    FreudenthalCharge.symplecticForm D (embedPlusPole (J := J)) (embedPlusPole (J := J)) = 0 := by
  dsimp [FreudenthalCharge.symplecticForm, embedPlusPole]
  simp

@[simp] theorem omega_poles_self_minus :
    FreudenthalCharge.symplecticForm D (embedMinusPole (J := J)) (embedMinusPole (J := J)) = 0 := by
  dsimp [FreudenthalCharge.symplecticForm, embedMinusPole]
  simp

theorem omega_roots
    (h_ortho : ∀ i j : Fin 3, D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i j : Fin 3) :
    FreudenthalCharge.symplecticForm D (embedPlusRoot rootMapPlus i) (embedMinusRoot rootMapMinus j) =
      if i = j then 1 else 0 := by
  dsimp [FreudenthalCharge.symplecticForm, embedPlusRoot, embedMinusRoot]
  simp only [mul_zero, sub_self, map_zero, sub_zero, zero_add]
  exact h_ortho i j

@[simp] theorem omega_roots_same_plus (i j : Fin 3) :
    FreudenthalCharge.symplecticForm D (embedPlusRoot rootMapPlus i) (embedPlusRoot rootMapPlus j) = 0 := by
  dsimp [FreudenthalCharge.symplecticForm, embedPlusRoot]
  simp

@[simp] theorem omega_roots_same_minus (i j : Fin 3) :
    FreudenthalCharge.symplecticForm D (embedMinusRoot rootMapMinus i) (embedMinusRoot rootMapMinus j) = 0 := by
  dsimp [FreudenthalCharge.symplecticForm, embedMinusRoot]
  simp

@[simp] theorem omega_pole_root_plus (i : Fin 3) :
    FreudenthalCharge.symplecticForm D (embedPlusPole (J := J)) (embedPlusRoot rootMapPlus i) = 0 := by
  dsimp [FreudenthalCharge.symplecticForm, embedPlusPole, embedPlusRoot]
  simp

@[simp] theorem omega_pole_root_minus (i : Fin 3) :
    FreudenthalCharge.symplecticForm D (embedMinusPole (J := J)) (embedMinusRoot rootMapMinus i) = 0 := by
  dsimp [FreudenthalCharge.symplecticForm, embedMinusPole, embedMinusRoot]
  simp

/-! ## 2. Symplectic Rank-Two Endomorphism Chiral Actions -/

/-- Rank-two action of poles on the positive pole $R_{u_+, u_-}(u_+) = -u_+$. -/
theorem rankTwo_pole_on_plus :
    symplecticRankTwo D (embedPlusPole (J := J)) (embedMinusPole (J := J)) (embedPlusPole (J := J)) =
      - embedPlusPole := by
  rw [symplecticRankTwo_apply]
  have hskew : FreudenthalCharge.symplecticForm D (embedMinusPole (J := J)) (embedPlusPole (J := J)) = -1 := by
    have h := FreudenthalCharge.symplectic_form_skew D (embedPlusPole (J := J)) (embedMinusPole (J := J))
    have h0 := omega_poles D (J := J)
    linarith
  rw [hskew, omega_poles_self_plus]
  simp only [neg_smul, one_smul, zero_smul, add_zero]

/-- Rank-two action of poles on the negative pole $R_{u_+, u_-}(u_-) = +u_-$. -/
theorem rankTwo_pole_on_minus :
    symplecticRankTwo D (embedPlusPole (J := J)) (embedMinusPole (J := J)) (embedMinusPole (J := J)) =
      embedMinusPole := by
  rw [symplecticRankTwo_apply]
  rw [omega_poles_self_minus, omega_poles]
  simp only [zero_smul, one_smul, zero_add]

/-- Rank-two action of root pairing $R_{\sigma_+^i, \sigma_-^j}$ on positive roots yields Kronecker delta. -/
theorem rankTwo_roots_on_plus
    (h_ortho : ∀ i j : Fin 3, D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i j k : Fin 3) :
    symplecticRankTwo D (embedPlusRoot rootMapPlus i) (embedMinusRoot rootMapMinus j)
        (embedPlusRoot rootMapPlus k) =
      - (if j = k then (1 : ℝ) else 0) • embedPlusRoot rootMapPlus i := by
  rw [symplecticRankTwo_apply]
  have hskew : FreudenthalCharge.symplecticForm D (embedMinusRoot rootMapMinus j) (embedPlusRoot rootMapPlus k) =
      - (if j = k then 1 else 0) := by
    have h1 := FreudenthalCharge.symplectic_form_skew D (embedPlusRoot rootMapPlus k) (embedMinusRoot rootMapMinus j)
    have h2 := omega_roots D rootMapPlus rootMapMinus h_ortho k j
    by_cases h : k = j
    · subst h; rw [h1, h2]
    · have hne : ¬(j = k) := fun hjk => h (hjk.symm)
      rw [h1, h2]
      simp [h, hne]
  rw [hskew, omega_roots_same_plus]
  simp only [zero_smul, add_zero, neg_smul]

/-- Rank-two action of root pairing $R_{\sigma_+^i, \sigma_-^j}$ on negative roots yields Kronecker delta. -/
theorem rankTwo_roots_on_minus
    (h_ortho : ∀ i j : Fin 3, D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i j k : Fin 3) :
    symplecticRankTwo D (embedPlusRoot rootMapPlus i) (embedMinusRoot rootMapMinus j)
        (embedMinusRoot rootMapMinus k) =
      (if i = k then (1 : ℝ) else 0) • embedMinusRoot rootMapMinus j := by
  rw [symplecticRankTwo_apply]
  rw [omega_roots_same_minus, omega_roots D rootMapPlus rootMapMinus h_ortho i k]
  simp only [zero_smul, zero_add]

end InfoGeometry.Exceptional.Freudenthal
