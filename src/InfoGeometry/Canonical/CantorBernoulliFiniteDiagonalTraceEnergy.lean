/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalHilbertSchmidt

/-!
# Finite trace-energy contraction of the Cantor diagonal

The diagonal boundary `L²` map is contractive against the normalized trace
quadratic form on the full finite BitWord matrix stage. This is still a
finite-stage statement; extension from the trace GNS stages to their filtered
Hilbert colimit is separate.
-/

noncomputable section

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalTraceEnergy

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorKMSState
open InfoGeometry.Canonical.CantorBernoulliFiniteDiagL2Embedding
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalHilbertSchmidt
open Matrix

/-- The normalized BitWord matrix trace of a diagonal matrix is the existing
finite diagonal trace. -/
theorem bitWordMatrixTraceFunctional_diagonal
    (n : ℕ) (f : DiagAlg n) :
    bitWordMatrixTraceFunctional n (Matrix.diagonal f) = DiagTrace n f := by
  rw [bitWordMatrixTraceFunctional_apply, Matrix.trace]
  simp only [Matrix.diag, Matrix.diagonal_apply_eq]
  rw [card_BitWord]
  unfold DiagTrace
  congr 1
  norm_num [div_pow]

/-- The normalized trace energy of a finite BitWord matrix is its full
Hilbert--Schmidt square sum. -/
theorem bitWordMatrixTraceFunctional_star_mul_self_re_eq
    (n : ℕ) (A : BitWordMatrixStage n) :
    (bitWordMatrixTraceFunctional n (star A * A)).re =
      (1 / (Fintype.card (BitWord n) : ℝ)) *
        (∑ u : BitWord n, ∑ v : BitWord n,
          Complex.normSq (A v u)) := by
  have htrace :
      (Matrix.trace (star A * A)).re =
        ∑ u : BitWord n, ∑ v : BitWord n, Complex.normSq (A v u) := by
    dsimp [Matrix.trace, Matrix.mul_apply, star, conjTranspose_apply]
    have h_elem (v u : BitWord n) :
        (starRingEnd ℂ (A v u) * A v u).re = Complex.normSq (A v u) := by
      rw [mul_comm, Complex.mul_conj]
      rfl
    have h_sum2 (u : BitWord n) :
        (∑ v : BitWord n, starRingEnd ℂ (A v u) * A v u).re =
          ∑ v : BitWord n, Complex.normSq (A v u) := by
      have h_map := map_sum Complex.reAddGroupHom
        (fun v => starRingEnd ℂ (A v u) * A v u) Finset.univ
      change Complex.reAddGroupHom
          (∑ v : BitWord n, starRingEnd ℂ (A v u) * A v u) = _
      rw [h_map]
      congr 1
      ext v
      exact h_elem v u
    have h_map := map_sum Complex.reAddGroupHom
      (fun u => ∑ v : BitWord n,
        starRingEnd ℂ (A v u) * A v u) Finset.univ
    change Complex.reAddGroupHom
        (∑ u : BitWord n, ∑ v : BitWord n,
          starRingEnd ℂ (A v u) * A v u) = _
    rw [h_map]
    congr 1
    ext u
    exact h_sum2 u
  rw [bitWordMatrixTraceFunctional_apply]
  have hcast :
      (1 / (Fintype.card (BitWord n) : ℂ)) =
        ((1 / (Fintype.card (BitWord n) : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [htrace]

/-- Finite-stage trace-energy contraction for the canonical boundary
diagonal map. -/
theorem diagonalCylinderL2_norm_sq_le_traceEnergy
    (n : ℕ) (A : BitWordMatrixStage n) :
    ‖diagonalCylinderL2 n (diagonalPart n A)‖ ^ 2 ≤
      (bitWordMatrixTraceFunctional n (star A * A)).re := by
  let D : BitWordMatrixStage n := Matrix.diagonal (fun u => A u u)
  have hdiagProduct :
      star D * D =
        Matrix.diagonal (fun u => star (A u u) * A u u) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Matrix.diagonal, Matrix.mul_apply]
    · have hji : j ≠ i := fun h => hij h.symm
      simp [D, Matrix.diagonal, Matrix.mul_apply, hij, hji]
  have hdiagTrace :
      DiagTrace n (fun u => star (A u u) * A u u) =
        bitWordMatrixTraceFunctional n (star D * D) := by
    rw [hdiagProduct]
    exact (bitWordMatrixTraceFunctional_diagonal n _).symm
  have hnorm :
      (inner ℂ (diagonalCylinderL2 n (diagonalPart n A))
        (diagonalCylinderL2 n (diagonalPart n A))).re =
        ‖diagonalCylinderL2 n (diagonalPart n A)‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ)
      (diagonalCylinderL2 n (diagonalPart n A))
  have hL2 :
      ‖diagonalCylinderL2 n (diagonalPart n A)‖ ^ 2 =
        (DiagTrace n (fun u => star (A u u) * A u u)).re := by
    calc
      ‖diagonalCylinderL2 n (diagonalPart n A)‖ ^ 2 =
          (inner ℂ (diagonalCylinderL2 n (diagonalPart n A))
            (diagonalCylinderL2 n (diagonalPart n A))).re := hnorm.symm
      _ = (DiagTrace n (fun u => star (A u u) * A u u)).re :=
        congrArg Complex.re (diagonalCylinderL2_inner_diagonalPart n A)
  have hdiagEnergy :
      (bitWordMatrixTraceFunctional n (star D * D)).re =
        (1 / (Fintype.card (BitWord n) : ℝ)) *
          (∑ u : BitWord n, Complex.normSq (A u u)) := by
    rw [bitWordMatrixTraceFunctional_star_mul_self_re_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    have hterm (v : BitWord n) :
        Complex.normSq (D v u) =
          if v = u then Complex.normSq (A u u) else 0 := by
      by_cases hvu : v = u
      · subst v
        simp [D, Matrix.diagonal]
      · simp [D, Matrix.diagonal, hvu]
    rw [Finset.sum_congr rfl (fun v _ => hterm v)]
    rw [Finset.sum_ite_eq']
    simp
  have hfullEnergy := bitWordMatrixTraceFunctional_star_mul_self_re_eq n A
  rw [hL2, hdiagTrace, hdiagEnergy, hfullEnergy]
  exact normalized_diagonal_normSq_sum_le_hs_normSq_sum n A

end InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalTraceEnergy

end
