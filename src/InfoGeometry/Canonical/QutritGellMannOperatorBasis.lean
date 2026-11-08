import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.GellMannSU3
import InfoGeometry.Canonical.TwoSheetThreeColorWeyl
import InfoGeometry.Canonical.QutritWeylOperatorBasis

/-!
# The nine continuous Gell–Mann colour channels

`QutritWeylOperatorBasis` owns the *discrete* nine-word qutrit operator basis
`X^a Z^b`.  This owner supplies its *continuous* partner: the identity together
with the eight Gell–Mann matrices already owned by `Physics.GellMannSU3`.

Nothing here is postulated.  Linear independence is proved from matrix entries,
spanning follows from the dimension count, and the Hilbert–Schmidt Gram data is
computed rather than assumed.  The Gram weights are deliberately *not* uniform:
this file uses the unnormalized `gl8 = diag(1,1,-2)` of `Physics.GellMannSU3`,
whose Hilbert–Schmidt square is `6` and not `2`.

The two bases are welded to each other by the explicit expansions of the colour
shift and the colour clock in Gell–Mann coordinates.
-/

noncomputable section

namespace InfoGeometry.Canonical.QutritGellMannOperatorBasis

open Matrix
open InfoGeometry.Physics.GellMannSU3

abbrev QutritMatrix := InfoGeometry.Algebra.FiniteSpin.QutritMatrix

/-- The nine continuous colour channels: the identity together with the eight
Gell–Mann matrices. -/
def gellMannFamily : Fin 9 → QutritMatrix :=
  ![1, gl1, gl2, gl3, gl4, gl5, gl6, gl7, gl8]

/-- The Hilbert–Schmidt self-pairing of each channel.  The identity channel
weighs `3` and the unnormalized `gl8` weighs `6`; the remaining seven weigh `2`. -/
def gramWeight : Fin 9 → ℂ := ![3, 2, 2, 2, 2, 2, 2, 2, 6]

theorem gramWeight_ne_zero (r : Fin 9) : gramWeight r ≠ 0 := by
  fin_cases r <;> simp [gramWeight]

/-- Every continuous colour channel is Hermitian. -/
theorem gellMannFamily_conjTranspose (r : Fin 9) :
    (gellMannFamily r)ᴴ = gellMannFamily r := by
  fin_cases r <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [gellMannFamily, gl1, gl2, gl3, gl4, gl5, gl6, gl7, gl8,
          Matrix.conjTranspose, Complex.conj_ofNat]

/-- The eight non-identity channels are traceless; the identity channel is not. -/
theorem gellMannFamily_trace (r : Fin 9) :
    Matrix.trace (gellMannFamily r) = if r = 0 then 3 else 0 := by
  fin_cases r <;>
    simp [gellMannFamily, gl1, gl2, gl3, gl4, gl5, gl6, gl7, gl8,
      Matrix.trace, Fin.sum_univ_three, show (1 : ℂ) + 1 + -2 = 0 by norm_num]

/-- The nine continuous channels are linearly independent over `ℂ`. -/
theorem gellMannFamily_linearIndependent :
    LinearIndependent ℂ gellMannFamily := by
  rw [Fintype.linearIndependent_iff]
  intro c h
  have h00 := congrArg (fun M : QutritMatrix => M 0 0) h
  have h01 := congrArg (fun M : QutritMatrix => M 0 1) h
  have h02 := congrArg (fun M : QutritMatrix => M 0 2) h
  have h10 := congrArg (fun M : QutritMatrix => M 1 0) h
  have h11 := congrArg (fun M : QutritMatrix => M 1 1) h
  have h12 := congrArg (fun M : QutritMatrix => M 1 2) h
  have h20 := congrArg (fun M : QutritMatrix => M 2 0) h
  have h21 := congrArg (fun M : QutritMatrix => M 2 1) h
  have h22 := congrArg (fun M : QutritMatrix => M 2 2) h
  simp [gellMannFamily, gl1, gl2, gl3, gl4, gl5, gl6, gl7, gl8,
    Matrix.sum_apply, Fin.sum_univ_succ] at h00 h01 h02 h10 h11 h12 h20 h21 h22
  -- The three off-diagonal Hermitian pairs decouple completely.
  have hc1 : c 1 = 0 := by linear_combination h01 / 2 + h10 / 2
  have hc2 : c 2 = 0 := by
    have hI : c 2 * Complex.I = 0 := by linear_combination h10 / 2 - h01 / 2
    exact (mul_eq_zero.mp hI).resolve_right Complex.I_ne_zero
  have hc4 : c 4 = 0 := by linear_combination h02 / 2 + h20 / 2
  have hc5 : c 5 = 0 := by
    have hI : c 5 * Complex.I = 0 := by linear_combination h20 / 2 - h02 / 2
    exact (mul_eq_zero.mp hI).resolve_right Complex.I_ne_zero
  have hc6 : c 6 = 0 := by linear_combination h12 / 2 + h21 / 2
  have hc7 : c 7 = 0 := by
    have hI : c 7 * Complex.I = 0 := by linear_combination h21 / 2 - h12 / 2
    exact (mul_eq_zero.mp hI).resolve_right Complex.I_ne_zero
  -- The Cartan triple `c 0, c 3, c 8` is pinned by the three diagonal entries.
  have hc3 : c 3 = 0 := by linear_combination h00 / 2 - h11 / 2
  have hc8 : c 8 = 0 := by linear_combination h00 / 6 + h11 / 6 - h22 / 3
  have hc0 : c 0 = 0 := by linear_combination h00 / 3 + h11 / 3 + h22 / 3
  intro r
  fin_cases r
  · exact hc0
  · exact hc1
  · exact hc2
  · exact hc3
  · exact hc4
  · exact hc5
  · exact hc6
  · exact hc7
  · exact hc8

theorem gellMannFamily_span_eq_top :
    Submodule.span ℂ (Set.range gellMannFamily) = ⊤ := by
  apply gellMannFamily_linearIndependent.span_eq_top_of_card_eq_finrank
  simp [Module.finrank_matrix]

/-- The identity together with the eight Gell–Mann matrices is a `ℂ`-basis of
the qutrit matrix algebra. -/
def gellMannBasis : Module.Basis (Fin 9) ℂ QutritMatrix :=
  basisOfLinearIndependentOfCardEqFinrank gellMannFamily_linearIndependent (by
    simp [Module.finrank_matrix])

@[simp] theorem gellMannBasis_apply (r : Fin 9) :
    gellMannBasis r = gellMannFamily r := by
  simp [gellMannBasis]

def gellMannCoefficient (A : QutritMatrix) (r : Fin 9) : ℂ :=
  (gellMannBasis.repr A) r

theorem gellMann_expansion (A : QutritMatrix) :
    ∑ r : Fin 9, gellMannCoefficient A r • gellMannFamily r = A := by
  simpa [gellMannCoefficient] using Module.Basis.sum_repr gellMannBasis A

theorem gellMann_expansion_unique (A : QutritMatrix) (c : Fin 9 → ℂ)
    (h : ∑ r : Fin 9, c r • gellMannFamily r = A) :
    ∀ r, c r = gellMannCoefficient A r := by
  have hzero :
      ∑ r : Fin 9, (c r - gellMannCoefficient A r) • gellMannFamily r = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, h, gellMann_expansion]
    simp
  have hcoeff :=
    (Fintype.linearIndependent_iff.mp gellMannFamily_linearIndependent)
      (fun r => c r - gellMannCoefficient A r) hzero
  intro r
  exact sub_eq_zero.mp (hcoeff r)

set_option maxHeartbeats 1000000 in
/-- The nine continuous channels are Hilbert–Schmidt orthogonal, with the
non-uniform Gram weights recorded by `gramWeight`. -/
theorem gellMannFamily_hs_orthogonal (r s : Fin 9) :
    Matrix.trace ((gellMannFamily r)ᴴ * gellMannFamily s) =
      if r = s then gramWeight r else 0 := by
  rw [gellMannFamily_conjTranspose]
  fin_cases r <;> fin_cases s <;>
    simp [gellMannFamily, gramWeight, gl1, gl2, gl3, gl4, gl5, gl6, gl7, gl8,
      Matrix.trace, Fin.sum_univ_three] <;>
    ring_nf

theorem gellMann_trace_readout (A : QutritMatrix) (r : Fin 9) :
    Matrix.trace ((gellMannFamily r)ᴴ * A) =
      gramWeight r * gellMannCoefficient A r := by
  have h := congrArg
    (fun M : QutritMatrix => Matrix.trace ((gellMannFamily r)ᴴ * M))
    (gellMann_expansion A)
  change Matrix.trace
      ((gellMannFamily r)ᴴ *
        (∑ s : Fin 9, gellMannCoefficient A s • gellMannFamily s)) =
      Matrix.trace ((gellMannFamily r)ᴴ * A) at h
  rw [Matrix.mul_sum, Matrix.trace_sum] at h
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at h
  simp_rw [gellMannFamily_hs_orthogonal] at h
  have hcollapse :
      (∑ s : Fin 9,
        gellMannCoefficient A s * if r = s then gramWeight r else 0) =
        gramWeight r * gellMannCoefficient A r := by
    classical
    rw [Finset.sum_eq_single r]
    · simp [mul_comm]
    · intro s _ hne
      simp [Ne.symm hne]
    · simp
  rw [hcollapse] at h
  exact h.symm

theorem gellMannCoefficient_eq_trace (A : QutritMatrix) (r : Fin 9) :
    gellMannCoefficient A r =
      (gramWeight r)⁻¹ * Matrix.trace ((gellMannFamily r)ᴴ * A) := by
  rw [gellMann_trace_readout, ← mul_assoc, inv_mul_cancel₀ (gramWeight_ne_zero r),
    one_mul]

theorem gellMann_trace_reconstruction (A : QutritMatrix) :
    ∑ r : Fin 9,
        ((gramWeight r)⁻¹ *
          Matrix.trace ((gellMannFamily r)ᴴ * A)) • gellMannFamily r = A := by
  calc
    ∑ r : Fin 9,
        ((gramWeight r)⁻¹ *
          Matrix.trace ((gellMannFamily r)ᴴ * A)) • gellMannFamily r =
      ∑ r : Fin 9, gellMannCoefficient A r • gellMannFamily r := by
        apply Finset.sum_congr rfl
        intro r _
        rw [gellMannCoefficient_eq_trace]
    _ = A := gellMann_expansion A

/-! ## Welding the discrete and the continuous colour bases -/

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl

/-- The colour shift `X` in continuous Gell–Mann coordinates.  It has no Cartan
component: all six of its channels are root channels. -/
theorem colorShift_gellMann_expansion :
    colorShift =
      (2⁻¹ : ℂ) • gl1 + (-(Complex.I / 2)) • gl2 +
        (2⁻¹ : ℂ) • gl4 + (Complex.I / 2) • gl5 +
        (2⁻¹ : ℂ) • gl6 + (-(Complex.I / 2)) • gl7 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorShift, gl1, gl2, gl4, gl5, gl6, gl7] <;>
    ring_nf <;> simp <;> ring

/-- The colour clock `Z` in continuous Gell–Mann coordinates.  For a primitive
cube root it is purely Cartan: only `gl3` and `gl8` appear, and the identity
channel vanishes because `Z` is then traceless. -/
theorem colorClock_gellMann_expansion (ω : ℂ) (hω : 1 + ω + ω ^ 2 = 0) :
    colorClock ω = ((1 - ω) / 2) • gl3 + ((1 + ω) / 2) • gl8 := by
  have hsq : ω ^ 2 = -1 - ω := by linear_combination hω
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorClock, gl3, gl8, hsq] <;> ring

/-- Both nine-channel colour bases have the same cardinality as the qutrit
matrix algebra has dimension: the discrete Weyl count and the continuous
Gell–Mann count agree at nine. -/
theorem colour_channel_count :
    Fintype.card (Fin 3 × Fin 3) = Module.finrank ℂ QutritMatrix ∧
      Fintype.card (Fin 9) = Module.finrank ℂ QutritMatrix := by
  constructor <;> simp [Module.finrank_matrix]

/-- The change of coordinates from the discrete Weyl channels to the continuous
Gell–Mann channels. -/
def weylToGellMann :
    (Fin 3 × Fin 3 →₀ ℂ) ≃ₗ[ℂ] (Fin 9 →₀ ℂ) :=
  (InfoGeometry.Canonical.QutritWeylOperatorBasis.weylBasis.repr.symm).trans
    gellMannBasis.repr

@[simp] theorem weylToGellMann_apply (A : QutritMatrix) :
    weylToGellMann
        (InfoGeometry.Canonical.QutritWeylOperatorBasis.weylBasis.repr A) =
      gellMannBasis.repr A := by
  simp [weylToGellMann]

@[simp] theorem weylToGellMann_symm_apply (A : QutritMatrix) :
    weylToGellMann.symm (gellMannBasis.repr A) =
      InfoGeometry.Canonical.QutritWeylOperatorBasis.weylBasis.repr A := by
  simp [weylToGellMann]

end InfoGeometry.Canonical.QutritGellMannOperatorBasis

end noncomputable section
