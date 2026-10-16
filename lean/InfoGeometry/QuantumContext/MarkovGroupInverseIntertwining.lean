/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic
import InfoGeometry.Canonical.HartwigSouriauFrameDrazin
import InfoGeometry.QuantumContext.MarkovAttentionWeightedRange
import InfoGeometry.QuantumContext.MarkovAttentionKemenySnell

/-!
# Rectangular transport of finite Markov group inverses

For strictly positive finite transition matrices, a row-sum-preserving
rectangular intertwiner transports the group inverse when it also transports
the normalized stationary row. The theorem is stated on matrix carriers and
uses column-observable multiplication (`mulVec`).
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- A rectangular Markov intertwiner carries the group inverse between the
two transition operators, provided it preserves row sums and transports the
normalized stationary row. Matrices act on column observables by `mulVec`;
`C` has shape `ι × κ`, so it maps `κ`-observables to `ι`-observables. -/
theorem groupInverse_intertwines_of_stationary_compatible
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ) (C : Matrix ι κ ℝ)
    (π : ι → ℝ) (μ : κ → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hQ : Q ∈ Matrix.rowStochastic ℝ κ)
    (hPpos : ∀ i j, 0 < P i j) (hQpos : ∀ i j, 0 < Q i j)
    (hπsum : ∑ i, π i = 1) (hμsum : ∑ j, μ j = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hμstat : ∀ j, ∑ i, μ i * Q i j = μ j)
    (hCrows : ∀ i, ∑ j, C i j = 1)
    (hCmean : ∀ j, ∑ i, π i * C i j = μ j)
    (hintertwines : P * C = C * Q)
    (G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G)
    (H : Matrix κ κ ℝ) (hH : IsGroupInverse (1 - Q) H) :
    G * C = C * H := by
  let Eπ : Matrix ι ι ℝ := stationaryMeanMatrix π
  let Eμ : Matrix κ κ ℝ := stationaryMeanMatrix μ
  let A : Matrix ι ι ℝ := 1 - P
  let B : Matrix κ κ ℝ := 1 - Q

  have hGend : IsGroupInverse (Matrix.toLin' A) (Matrix.toLin' G) := by
    constructor
    · have h := congrArg Matrix.toLin' hG.1
      simpa [A, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    constructor
    · have h := congrArg Matrix.toLin' hG.2.1
      simpa [A, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    · have h := congrArg Matrix.toLin' hG.2.2
      simpa [A, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h

  have hHend : IsGroupInverse (Matrix.toLin' B) (Matrix.toLin' H) := by
    constructor
    · have h := congrArg Matrix.toLin' hH.1
      simpa [B, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    constructor
    · have h := congrArg Matrix.toLin' hH.2.1
      simpa [B, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    · have h := congrArg Matrix.toLin' hH.2.2
      simpa [B, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h

  have hProjG := principalIdempotent_toLin_eq_stationaryMeanMatrix
    P π hP hPpos hπsum hπstat G hG
  have hProjH := principalIdempotent_toLin_eq_stationaryMeanMatrix
    Q μ hQ hQpos hμsum hμstat H hH

  have hAG : A * G = 1 - Eπ := by
    apply Matrix.toLin'.injective
    have hproj : 1 - Matrix.toLin' A * Matrix.toLin' G = Matrix.toLin' Eπ := by
      simpa [A, Eπ, principalIdempotent, regularIdempotent,
        Matrix.toLin'_mul, Module.End.mul_eq_comp] using hProjG
    calc
      Matrix.toLin' (A * G) = Matrix.toLin' A * Matrix.toLin' G := by
        rw [Matrix.toLin'_mul, Module.End.mul_eq_comp]
      _ = 1 - (1 - Matrix.toLin' A * Matrix.toLin' G) := by noncomm_ring
      _ = 1 - Matrix.toLin' Eπ := by rw [hproj]
      _ = Matrix.toLin' (1 - Eπ) := by
        simp only [map_sub, Matrix.toLin'_one, Module.End.one_eq_id]

  have hBH : B * H = 1 - Eμ := by
    apply Matrix.toLin'.injective
    have hproj : 1 - Matrix.toLin' B * Matrix.toLin' H = Matrix.toLin' Eμ := by
      simpa [B, Eμ, principalIdempotent, regularIdempotent,
        Matrix.toLin'_mul, Module.End.mul_eq_comp] using hProjH
    calc
      Matrix.toLin' (B * H) = Matrix.toLin' B * Matrix.toLin' H := by
        rw [Matrix.toLin'_mul, Module.End.mul_eq_comp]
      _ = 1 - (1 - Matrix.toLin' B * Matrix.toLin' H) := by noncomm_ring
      _ = 1 - Matrix.toLin' Eμ := by rw [hproj]
      _ = Matrix.toLin' (1 - Eμ) := by
        simp only [map_sub, Matrix.toLin'_one, Module.End.one_eq_id]

  have hEC : Eπ * C = C * Eμ := by
    ext i j
    simp only [Matrix.mul_apply, Eπ, Eμ, stationaryMeanMatrix]
    calc
      (∑ k, π k * C k j) = μ j := hCmean j
      _ = (∑ k, C i k) * μ j := by rw [hCrows i]; simp
      _ = ∑ k, C i k * μ j := by rw [← Finset.sum_mul]

  have hAC : A * C = C * B := by
    dsimp [A, B]
    calc
      (1 - P) * C = C - P * C := by
        simp only [Matrix.sub_mul, Matrix.one_mul]
      _ = C - C * Q := by rw [hintertwines]
      _ = C * (1 - Q) := by
        rw [Matrix.mul_sub, Matrix.mul_one]

  have hAGC : A * G * C = C * B * H := by
    calc
      A * G * C = (1 - Eπ) * C := by rw [hAG]
      _ = C * (1 - Eμ) := by
        calc
          (1 - Eπ) * C = C - Eπ * C := by
            simp only [Matrix.sub_mul, Matrix.one_mul]
          _ = C - C * Eμ := by rw [hEC]
          _ = C * (1 - Eμ) := by
            rw [Matrix.mul_sub, Matrix.mul_one]
      _ = C * B * H := by rw [← hBH, Matrix.mul_assoc]

  have hAGC_eq_ACH : A * G * C = A * C * H := by
    rw [hAGC, ← hAC]

  have hMeanTransport (x : κ → ℝ) :
      weightedMeanMap π (C.mulVec x) = weightedMeanMap μ x := by
    simp only [weightedMeanMap]
    calc
      (∑ i, π i * ∑ j, C i j * x j) =
          ∑ i, ∑ j, (π i * C i j) * x j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        exact (mul_assoc _ _ _).symm
      _ = ∑ j, ∑ i, (π i * C i j) * x j := by rw [Finset.sum_comm]
      _ = ∑ j, (∑ i, π i * C i j) * x j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.sum_mul]
      _ = ∑ j, μ j * x j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hCmean j]

  have hRangeA := range_laplacian_eq_weightedMean_ker P π hP hPpos hπsum hπstat
  have hRangeB := range_laplacian_eq_weightedMean_ker Q μ hQ hQpos hμsum hμstat

  have hTransport (x : κ → ℝ) :
      G.mulVec (C.mulVec x) = C.mulVec (H.mulVec x) := by
    let Aₑ : Module.End ℝ (ι → ℝ) := Matrix.toLin' A
    let Gₑ : Module.End ℝ (ι → ℝ) := Matrix.toLin' G
    let Bₑ : Module.End ℝ (κ → ℝ) := Matrix.toLin' B
    let Hₑ : Module.End ℝ (κ → ℝ) := Matrix.toLin' H
    let u : ι → ℝ := G.mulVec (C.mulVec x)
    let v : ι → ℝ := C.mulVec (H.mulVec x)
    have hu : u ∈ Aₑ.range := by
      have hmem := groupInverse_apply_mem_range Aₑ Gₑ hGend (C.mulVec x)
      simpa [u, Aₑ, Gₑ, Matrix.toLin'_apply] using hmem
    have hHx : (H.mulVec x) ∈ Bₑ.range := by
      have hmem := groupInverse_apply_mem_range Bₑ Hₑ hHend x
      simpa [Bₑ, Hₑ, Matrix.toLin'_apply] using hmem
    have hμzero : weightedMeanMap μ (H.mulVec x) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [← hRangeB]
      exact hHx
    have hv : v ∈ Aₑ.range := by
      rw [hRangeA]
      apply LinearMap.mem_ker.mpr
      rw [hMeanTransport, hμzero]
    have hsolve : Aₑ u = Aₑ v := by
      have hmatrix := congrArg (fun M : Matrix ι κ ℝ => M.mulVec x) hAGC_eq_ACH
      change A.mulVec (G.mulVec (C.mulVec x)) =
        A.mulVec (C.mulVec (H.mulVec x))
      simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc, u, v] using hmatrix
    have heq := groupInverse_solution_unique_on_range Aₑ Gₑ hGend u v hu hv hsolve
    exact heq

  ext i j
  have hentry := congrArg (fun y : ι → ℝ => y i) (hTransport (Pi.single j (1 : ℝ)))
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Pi.single_apply,
    Matrix.mulVec_single_one] using hentry

end InfoGeometry.QuantumContext.MarkovDrazin

end
