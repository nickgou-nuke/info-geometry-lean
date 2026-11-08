/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.NullConeAlgebra
import InfoGeometry.Twistor.GraphDiracParavectorShellBridge

/-!
# Pauli bitwistor polarization and the existing graph Dirac kernel

This bridge reuses the repository's Minkowski paravectors, Pauli soldering
matrices, and graph Hodge--Dirac operator. It proves that the determinant of
the sum of two null Pauli operators is their polarized cross term, and that
this determinant vanishes exactly when the existing graph Dirac operator has
a nonzero vertex-supported zero mode.
-/

namespace InfoGeometry.Twistor.BitwistorGraphDiracMassBridge

open InfoGeometry.Geometry.PauliParavectorBridge
open InfoGeometry.Geometry.NullConeAlgebra
open InfoGeometry.QuantumContext.GeneralGraphHodgeDiracKrein
open InfoGeometry.Twistor.GraphDiracParavectorShellBridge

/-- Determinant polarization on the existing Pauli matrix representation. -/
theorem pauli_sum_determinant_polarization (u v : Minkowski4) :
    Matrix.det (pauliMatrix (u + v)) =
      (((u.q + v.q + 2 * minkowskiPairing u v : ℝ)) : ℂ) := by
  rw [det_pauliMatrix, minkowski_polarization]

/-- The polarized cross term has bidegree `(1,1)` under independent
rescaling of the two homogeneous null representatives. -/
theorem minkowskiPairing_smul_smul (a b : ℝ) (u v : Minkowski4) :
    minkowskiPairing (a • u) (b • v) = a * b * minkowskiPairing u v := by
  change (a * u.t) * (b * v.t) - (a * u.x) * (b * v.x) -
      (a * u.y) * (b * v.y) - (a * u.z) * (b * v.z) = _
  unfold minkowskiPairing
  ring

/-- Vanishing of the cross term is independent of the chosen nonzero
homogeneous representatives of both null rays. -/
theorem minkowskiPairing_smul_smul_eq_zero_iff
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (u v : Minkowski4) :
    minkowskiPairing (a • u) (b • v) = 0 ↔ minkowskiPairing u v = 0 := by
  rw [minkowskiPairing_smul_smul]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hab | huv
    · exact False.elim ((mul_ne_zero ha hb) hab)
    · exact huv
  · intro h
    simp [h]

/-- A nonzero spinor in the vertex summand is a graph Dirac zero mode exactly
when the incidence matrix has a nonzero kernel vector. -/
theorem graphDirac_vertex_kernel_iff_incidence_kernel
    (B : Matrix (Fin 2) (Fin 2) ℂ) :
    (∃ ψ : Fin 2 → ℂ, ψ ≠ 0 ∧
      (graphDirac B).mulVec (Sum.elim ψ (fun _ : Fin 2 => 0)) = 0) ↔
    ∃ ψ : Fin 2 → ℂ, ψ ≠ 0 ∧ B.mulVec ψ = 0 := by
  constructor
  · rintro ⟨ψ, hψ, hD⟩
    refine ⟨ψ, hψ, ?_⟩
    have hBlock := graphDirac_mulVec_vertex B ψ
    rw [hBlock] at hD
    funext i
    have hi := congrFun hD (Sum.inr i)
    simpa using hi
  · rintro ⟨ψ, hψ, hB⟩
    refine ⟨ψ, hψ, ?_⟩
    rw [graphDirac_mulVec_vertex]
    funext i
    cases i with
    | inl i => rfl
    | inr i => simp [hB]

/-- On the sum of two null paravectors, graph Dirac has a nonzero vertex
zero mode exactly when the Pauli cross-pairing vanishes. Thus a nonzero
cross-pairing removes that null-shell zero mode. -/
theorem null_pair_graphDirac_vertex_kernel_iff_pairing_zero
    (u v : Minkowski4) (hu : u.IsNull) (hv : v.IsNull) :
    (∃ ψ : Fin 2 → ℂ, ψ ≠ 0 ∧
      (graphDirac (pauliMatrix (u + v))).mulVec
        (Sum.elim ψ (fun _ : Fin 2 => 0)) = 0) ↔
      minkowskiPairing u v = 0 := by
  rw [graphDirac_vertex_kernel_iff_incidence_kernel,
    Matrix.exists_mulVec_eq_zero_iff, pauli_sum_determinant_polarization,
    hu, hv]
  simp

end InfoGeometry.Twistor.BitwistorGraphDiracMassBridge
