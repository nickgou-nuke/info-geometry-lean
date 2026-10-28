/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GradedDMPResolution
import InfoGeometry.QuantumContext.RectangularDrazinLift

/-!
# Metric-aware continuation of rectangular Drazin transport

A literal adapter connects the two existing indexed inverse predicates.
The ambient Moore--Penrose witness is not inferred from an oblique retract.
For an isometric inclusion a separate theorem constructs its transported MP
witness using the actual conjugate-transpose-compatible corner map.
-/

namespace InfoGeometry.QuantumContext.GradedDMPTransport

open Matrix InfoGeometry.Algebra.RectangularRetract
open InfoGeometry.Canonical.DrazinMoorePenrosePartition
open InfoGeometry.Canonical.GradedDMPResolution
open InfoGeometry.Core.IdempotentCartan
open InfoGeometry.Singular.MoorePenrose

variable {R : Type*} [Ring R]

/-- An equation-preserving adapter, not a third generalized-inverse predicate. -/
theorem toCanonical {a d : R} {k : ℕ}
    (h : InfoGeometry.QuantumContext.Drazin.IsDrazinInverse a d k) :
    InfoGeometry.Canonical.Drazin.IsDrazinInverse a d k :=
  ⟨h.comm, h.drazin_one, h.index_eq⟩

variable [StarRing R]
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Isometric rectangular inclusions transport the four Penrose equations.
No such conclusion is asserted for arbitrary oblique retractions. -/
theorem mp_isometric_corner {K : Matrix n m R} (hK : Kᴴ * K = 1)
    {A M : Matrix m m R} (hM : IsMoorePenroseInverse A M) :
    IsMoorePenroseInverse (cornerHom K Kᴴ hK A) (cornerHom K Kᴴ hK M) := by
  have hstar (X : Matrix m m R) :
      star (cornerHom K Kᴴ hK X) = cornerHom K Kᴴ hK (star X) := by
    change (K * X * Kᴴ)ᴴ = K * Xᴴ * Kᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hM.aba_eq_a]
  · rw [← map_mul, ← map_mul, hM.bab_eq_b]
  · rw [← map_mul, hstar, hM.ab_adj_eq]
  · rw [← map_mul, hstar, hM.ba_adj_eq]

/-- The existing constructed ambient Drazin witness feeds the ordered MP recovery.
Here `T` and `B` abbreviate actual rectangular matrix expressions. -/
theorem lifted_recovery
    {K : Matrix n m R} {Q : Matrix m n R} {N : Matrix n n R}
    (h : Q * K = 1) (hQN : Q * N = 0) (hNK : N * K = 0)
    {A D : Matrix m m R} {k r : ℕ}
    (hD : InfoGeometry.QuantumContext.Drazin.IsDrazinInverse A D k)
    (hN : N ^ r = 0) (M : Matrix n n R)
    (hM : IsMoorePenroseInverse (cornerHom K Q h A + N) M) :
    let T := cornerHom K Q h A + N
    let B := cornerHom K Q h D
    dmpInverse T B M * T = cornerHom K Q h (A * D) ∧
      T * dualDmpInverse T B M = cornerHom K Q h (A * D) ∧
      (dmpInverse T B M = dualDmpInverse T B M ↔
        oddPart (cornerHom K Q h (A * D)) M = 0) := by
  dsimp only
  have hLift := RectangularDrazinLift.isDrazinInverse_lift h hQN hNK hD hN
  have hCanon := toCanonical hLift
  have hp : InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection
      (cornerHom K Q h A + N) (cornerHom K Q h D) = cornerHom K Q h (A * D) :=
    RectangularDrazinLift.lifted_spectralProj h hNK A D
  exact ⟨by simpa only [hp] using dmp_mul_original hCanon hM,
    by simpa only [hp] using original_mul_dualDmp hM,
    by simpa only [hp] using (dmp_eq_dual_iff_odd_zero (m := M) hCanon)⟩

end InfoGeometry.QuantumContext.GradedDMPTransport
