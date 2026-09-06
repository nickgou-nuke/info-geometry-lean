import InfoGeometry.Canonical.InverseKernelAlgebra
import InfoGeometry.Meta.Architecture
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.NoncommRing

/-!
# InfoGeometry.Canonical.DrazinCoreFlow

Exact algebra of the Drazin core projector and its complementary nilpotent
sector.

This file stays at the operator-calculus level already justified by the repo:

- the Drazin projector and its complement commute with the base operator,
- the base operator splits as core part plus complementary nilpotent part,
- the two pieces multiply to zero in both orders,
- sufficiently high powers kill the complementary projector and the nilpotent
  part.
-/

open InfoGeometry.Canonical.Drazin

namespace InfoGeometry.Canonical.Drazin.IsDrazinInverse

section Generic

variable {R : Type*} [Ring R] {a b : R} {k : ℕ}

/-- The Drazin projector commutes with the base operator on the left/right. -/
theorem projection_mul_eq_mul_projection
    (h : IsDrazinInverse a b k) :
    projection a b * a = a * projection a b := by
  unfold projection
  calc
    (a * b) * a = a * (b * a) := by simp [mul_assoc]
    _ = a * (a * b) := by rw [h.comm.symm]

/-- The Drazin projector commutes with the base operator. -/
theorem commute_projection
    (h : IsDrazinInverse a b k) :
    Commute a (projection a b) := by
  unfold Commute
  simpa using (projection_mul_eq_mul_projection (h := h)).symm

/-- The complementary Drazin projector commutes with the base operator. -/
theorem commute_complementaryProjection
    (h : IsDrazinInverse a b k) :
    Commute a (complementaryProjection a b) := by
  unfold Commute complementaryProjection projection
  have hproj : a * (a * b) = (a * b) * a := by
    simpa [projection] using (projection_mul_eq_mul_projection (h := h)).symm
  calc
    a * (1 - a * b) = a - a * (a * b) := by rw [mul_sub, mul_one]
    _ = a - (a * b) * a := by rw [hproj]
    _ = (1 - a * b) * a := by rw [sub_mul, one_mul]



/-- The core piece is also the Drazin projector followed by the base operator. -/
theorem core_eq_projection_mul
    (h : IsDrazinInverse a b k) :
    core a b = projection a b * a := by
  rw [core_eq_mul_projection]
  symm
  exact projection_mul_eq_mul_projection (h := h)



/-- The nilpotent complementary piece is also the complementary projector times the base operator. -/
theorem nilpotent_eq_complementaryProjection_mul
    (h : IsDrazinInverse a b k) :
    nilpotent a b = complementaryProjection a b * a := by
  rw [nilpotent_eq_mul_complementaryProjection]
  exact (commute_complementaryProjection (h := h)).eq

/-- The base operator kills the complementary projector after sufficiently high powers. -/
theorem pow_mul_complementaryProjection_eq_zero_of_le
    (h : IsDrazinInverse a b k) {m : ℕ} (hm : k ≤ m) :
    a ^ m * complementaryProjection a b = 0 := by
  unfold complementaryProjection projection
  have hpow : a ^ m * (a * b) = a ^ (m + 1) * b := by
    calc
      a ^ m * (a * b) = (a ^ m * a) * b := by simp [mul_assoc]
      _ = a ^ (m + 1) * b := by rw [pow_succ]
  calc
    a ^ m * (1 - a * b) = a ^ m - a ^ m * (a * b) := by
      rw [mul_sub, mul_one]
    _ = a ^ m - a ^ (m + 1) * b := by rw [hpow]
    _ = a ^ m - a ^ m := by
      rw [power_le (h := h) hm]
    _ = 0 := sub_self (a ^ m)

/-- Positive powers of the complementary projector stabilize to itself. -/
theorem complementaryProjection_pow_succ
    (h : IsDrazinInverse a b k) (m : ℕ) :
    complementaryProjection a b ^ (m + 1) = complementaryProjection a b := by
  induction m with
  | zero =>
      simp
  | succ m hm =>
      calc
        complementaryProjection a b ^ (m + 1 + 1)
            = complementaryProjection a b ^ (m + 1) * complementaryProjection a b := by
                rw [pow_succ]
        _ = complementaryProjection a b * complementaryProjection a b := by
              rw [hm]
        _ = complementaryProjection a b := complementaryProjection_is_idempotent (h := h)

/-- Positive powers of the nilpotent piece reduce to a power of the base operator times the complement. -/
theorem nilpotent_pow_succ_eq_pow_mul_complementaryProjection
    (h : IsDrazinInverse a b k) (m : ℕ) :
    nilpotent a b ^ (m + 1) = a ^ (m + 1) * complementaryProjection a b := by
  rw [nilpotent_eq_mul_complementaryProjection]
  have hcomm : Commute a (complementaryProjection a b) :=
    commute_complementaryProjection (h := h)
  calc
    (a * complementaryProjection a b) ^ (m + 1)
        = a ^ (m + 1) * complementaryProjection a b ^ (m + 1) := by
            simpa using hcomm.mul_pow (m + 1)
    _ = a ^ (m + 1) * complementaryProjection a b := by
          rw [complementaryProjection_pow_succ (h := h) m]

/-- The complementary nilpotent piece becomes zero after sufficiently high powers. -/
theorem nilpotent_pow_succ_eq_zero_of_le
    (h : IsDrazinInverse a b k) {m : ℕ} (hm : k ≤ m + 1) :
    nilpotent a b ^ (m + 1) = 0 := by
  rw [nilpotent_pow_succ_eq_pow_mul_complementaryProjection (h := h) m]
  exact pow_mul_complementaryProjection_eq_zero_of_le (h := h) hm

end Generic

section LinearCore

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
variable {A D : Module.End K V} {k : ℕ}

/--
The Drazin core at index `k` is the generalized kernel `ker(A^k)`.
-/
@[rep_depth operator]
def drazinCore (A : Module.End K V) (k : ℕ) : Submodule K V :=
  (A ^ k).ker

/--
The complementary Drazin projector maps into the generalized kernel.
-/
@[rep_depth operator]
theorem complementaryProjection_mapsTo_drazinCore
    (h : IsDrazinInverse A D k) (x : V) :
    complementaryProjection A D x ∈ drazinCore A k := by
  change (A ^ k) (complementaryProjection A D x) = 0
  have hPowMul :
      A ^ k * complementaryProjection A D = (0 : Module.End K V) := by
    calc
      A ^ k * complementaryProjection A D
          = A ^ k * (1 - A * D) := by
              rfl
      _ = A ^ k - A ^ k * (A * D) := by
            rw [mul_sub, mul_one]
      _ = A ^ k - ((A ^ k * A) * D) := by simp [mul_assoc]
      _ = A ^ k - (A ^ (k + 1) * D) := by rw [pow_succ]
      _ = A ^ k - A ^ k := by rw [h.power]
      _ = 0 := sub_self (A ^ k)
  simpa using congrArg (fun f : Module.End K V => f x) hPowMul

/--
For a Drazin witness, the complementary projector range equals the generalized
kernel `ker(A^k)`.

This is the canonical operatorial form of the "Drazin core" split.
-/
@[rep_depth operator]
theorem complementaryProjection_range_eq_drazinCore
    (h : IsDrazinInverse A D k) :
    LinearMap.range (complementaryProjection A D) = drazinCore A k := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    exact complementaryProjection_mapsTo_drazinCore (h := h) x
  · intro y hy
    refine ⟨y, ?_⟩
    have hy0 : (A ^ k) y = 0 := by
      simpa [drazinCore, LinearMap.mem_ker] using hy
    have hDpow : D = D ^ (k + 1) * A ^ k :=
      inverse_eq_pow_mul_pow (h := h) k
    have hDpow_apply : D y = (D ^ (k + 1) * A ^ k) y := by
      simpa using congrArg (fun f : Module.End K V => f y) hDpow
    have hProjZero : projection A D y = 0 := by
      calc
        projection A D y = (A * D) y := by rfl
        _ = A (D y) := rfl
        _ = A ((D ^ (k + 1) * A ^ k) y) := by rw [hDpow_apply]
        _ = ((A * D ^ (k + 1)) * A ^ k) y := by simp [mul_assoc]
        _ = (A * D ^ (k + 1)) ((A ^ k) y) := rfl
        _ = 0 := by simp [hy0]
    change (1 - projection A D) y = y
    simp [hProjZero]

/--
Open-problem alias: the Drazin projector range equals the Drazin core.

Here the projector is the complementary projector `Π = 1 - A * Aᴰ`,
whose range is the generalized-kernel core.
-/
@[rep_depth operator]
theorem drazin_projector_range_eq_core
    (h : IsDrazinInverse A D k) :
    LinearMap.range (complementaryProjection A D) = drazinCore A k :=
  complementaryProjection_range_eq_drazinCore (h := h)

/--
Open-problem L11 owner: states in the Drazin core are annihilated by the
core-defining power `A^k`, so the corresponding dissipative readout vanishes.
-/
@[rep_depth operator]
theorem dissipation_vanishes_on_drazinCore
    {ψ : V} (hψ : ψ ∈ drazinCore A k) :
    (A ^ k) ψ = 0 := by
  simpa [drazinCore, LinearMap.mem_ker] using hψ

end LinearCore
end InfoGeometry.Canonical.Drazin.IsDrazinInverse

section Certified

open InfoGeometry.Canonical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace InfoGeometry.Canonical.CertifiedInverseKernel

variable (CIK : CertifiedInverseKernel E)

/-- The Drazin-stable core projector. -/
@[rep_depth operator]
abbrev drazinCoreProj : E →L[ℝ] E :=
  CIK.spectralProjector

/-- The complementary nilpotent projector. -/
@[rep_depth operator]
abbrev nilpotentProj : E →L[ℝ] E :=
  CIK.spectralComplementaryProjector

/-- The operator restricted to the Drazin-stable core. -/
@[rep_depth operator]
def corePart : E →L[ℝ] E :=
  CIK.A * CIK.drazinCoreProj

/-- The operator restricted to the complementary nilpotent sector. -/
@[rep_depth operator]
def nilpotentPart : E →L[ℝ] E :=
  CIK.A * CIK.nilpotentProj

@[rep_depth operator, simp] theorem A_mul_drazinCoreProj_eq_drazinCoreProj_mul_A :
    CIK.A * CIK.drazinCoreProj = CIK.drazinCoreProj * CIK.A := by
  change CIK.A * IsDrazinInverse.projection CIK.A CIK.A_D =
      IsDrazinInverse.projection CIK.A CIK.A_D * CIK.A
  simpa using (IsDrazinInverse.projection_mul_eq_mul_projection (h := CIK.hDrazin)).symm

@[rep_depth operator, simp] theorem A_mul_nilpotentProj_eq_nilpotentProj_mul_A :
    CIK.A * CIK.nilpotentProj = CIK.nilpotentProj * CIK.A := by
  change CIK.A * IsDrazinInverse.complementaryProjection CIK.A CIK.A_D =
      IsDrazinInverse.complementaryProjection CIK.A CIK.A_D * CIK.A
  simpa using (IsDrazinInverse.commute_complementaryProjection (h := CIK.hDrazin)).eq

@[rep_depth operator, simp] theorem corePart_eq_drazinCoreProj_mul_A :
    CIK.corePart = CIK.drazinCoreProj * CIK.A := by
  unfold CertifiedInverseKernel.corePart
  rw [CIK.A_mul_drazinCoreProj_eq_drazinCoreProj_mul_A]

@[rep_depth operator, simp] theorem nilpotentPart_eq_nilpotentProj_mul_A :
    CIK.nilpotentPart = CIK.nilpotentProj * CIK.A := by
  unfold CertifiedInverseKernel.nilpotentPart
  rw [CIK.A_mul_nilpotentProj_eq_nilpotentProj_mul_A]

@[rep_depth operator] theorem A_eq_corePart_add_nilpotentPart :
    CIK.A = CIK.corePart + CIK.nilpotentPart := by
  unfold CertifiedInverseKernel.corePart CertifiedInverseKernel.nilpotentPart
  calc
    CIK.A = CIK.A * (CIK.drazinCoreProj + CIK.nilpotentProj) := by
      rw [CIK.spectralProjector_add_spectralComplementaryProjector]
      simp
    _ = CIK.A * CIK.drazinCoreProj + CIK.A * CIK.nilpotentProj := by
      rw [mul_add]
    _ = CIK.corePart + CIK.nilpotentPart := by rfl

@[rep_depth operator] theorem corePart_mul_nilpotentPart_eq_zero :
    CIK.corePart * CIK.nilpotentPart = 0 := by
  rw [CIK.corePart_eq_drazinCoreProj_mul_A, CIK.nilpotentPart_eq_nilpotentProj_mul_A]
  have hQA : CIK.A * CIK.nilpotentProj = CIK.nilpotentProj * CIK.A :=
    CIK.A_mul_nilpotentProj_eq_nilpotentProj_mul_A
  have hMid : CIK.A * (CIK.nilpotentProj * CIK.A) = CIK.nilpotentProj * (CIK.A * CIK.A) := by
    calc
      CIK.A * (CIK.nilpotentProj * CIK.A) = (CIK.A * CIK.nilpotentProj) * CIK.A := by
        rw [← mul_assoc]
      _ = (CIK.nilpotentProj * CIK.A) * CIK.A := by
        rw [hQA]
      _ = CIK.nilpotentProj * (CIK.A * CIK.A) := by
        rw [mul_assoc]
  calc
    (CIK.drazinCoreProj * CIK.A) * (CIK.nilpotentProj * CIK.A)
        = CIK.drazinCoreProj * (CIK.A * (CIK.nilpotentProj * CIK.A)) := by
            simp [mul_assoc]
    _ = CIK.drazinCoreProj * (CIK.nilpotentProj * (CIK.A * CIK.A)) := by
          rw [hMid]
    _ = (CIK.drazinCoreProj * CIK.nilpotentProj) * (CIK.A * CIK.A) := by
          simp [mul_assoc]
    _ = 0 := by
          rw [CIK.spectralProjector_mul_spectralComplementaryProjector]
          simp

@[rep_depth operator] theorem nilpotentPart_mul_corePart_eq_zero :
    CIK.nilpotentPart * CIK.corePart = 0 := by
  rw [CIK.nilpotentPart_eq_nilpotentProj_mul_A, CIK.corePart_eq_drazinCoreProj_mul_A]
  have hPA : CIK.A * CIK.drazinCoreProj = CIK.drazinCoreProj * CIK.A :=
    CIK.A_mul_drazinCoreProj_eq_drazinCoreProj_mul_A
  have hMid : CIK.A * (CIK.drazinCoreProj * CIK.A) = CIK.drazinCoreProj * (CIK.A * CIK.A) := by
    calc
      CIK.A * (CIK.drazinCoreProj * CIK.A) = (CIK.A * CIK.drazinCoreProj) * CIK.A := by
        rw [← mul_assoc]
      _ = (CIK.drazinCoreProj * CIK.A) * CIK.A := by
        rw [hPA]
      _ = CIK.drazinCoreProj * (CIK.A * CIK.A) := by
        rw [mul_assoc]
  calc
    (CIK.nilpotentProj * CIK.A) * (CIK.drazinCoreProj * CIK.A)
        = CIK.nilpotentProj * (CIK.A * (CIK.drazinCoreProj * CIK.A)) := by
            simp [mul_assoc]
    _ = CIK.nilpotentProj * (CIK.drazinCoreProj * (CIK.A * CIK.A)) := by
          rw [hMid]
    _ = (CIK.nilpotentProj * CIK.drazinCoreProj) * (CIK.A * CIK.A) := by
          simp [mul_assoc]
    _ = 0 := by
          rw [CIK.spectralComplementaryProjector_mul_spectralProjector]
          simp

@[rep_depth operator] theorem corePart_commute_nilpotentPart :
    Commute CIK.corePart CIK.nilpotentPart := by
  change CIK.corePart * CIK.nilpotentPart = CIK.nilpotentPart * CIK.corePart
  rw [CIK.corePart_mul_nilpotentPart_eq_zero, CIK.nilpotentPart_mul_corePart_eq_zero]

@[rep_depth operator] theorem A_pow_mul_nilpotentProj_eq_zero_of_index_le
    {m : ℕ} (hm : CIK.drazinIndex ≤ m) :
    CIK.A ^ m * CIK.nilpotentProj = 0 := by
  change CIK.A ^ m * IsDrazinInverse.complementaryProjection CIK.A CIK.A_D = 0
  simpa using
    IsDrazinInverse.pow_mul_complementaryProjection_eq_zero_of_le
      (h := CIK.hDrazin) hm

@[rep_depth operator] theorem nilpotentPart_pow_succ_eq_zero_of_index_le
    {m : ℕ} (hm : CIK.drazinIndex ≤ m + 1) :
    CIK.nilpotentPart ^ (m + 1) = 0 := by
  rw [CIK.nilpotentPart_eq_nilpotentProj_mul_A]
  have hnil :
      (IsDrazinInverse.nilpotent CIK.A CIK.A_D) ^ (m + 1) = 0 :=
    IsDrazinInverse.nilpotent_pow_succ_eq_zero_of_le
      (a := CIK.A) (b := CIK.A_D) (k := CIK.drazinIndex) (m := m) (h := CIK.hDrazin) hm
  rw [IsDrazinInverse.nilpotent_eq_complementaryProjection_mul (h := CIK.hDrazin)] at hnil
  simpa [CertifiedInverseKernel.nilpotentProj, CertifiedInverseKernel.spectralComplementaryProjector] using hnil

/--
Canonical Drazin block-split packet.

This is the Lean-level counterpart of the block intuition
`A = diag(C, N)`: `core` is the regular Drazin lane, `nilpotent` is the
singular/defect lane, and the mixed products vanish.
-/
@[rep_depth operator]
structure DrazinBlockSplitPacket where
  P_D : E →L[ℝ] E
  Q0 : E →L[ℝ] E
  core : E →L[ℝ] E
  nilpotent : E →L[ℝ] E
  P_D_eq : P_D = CIK.drazinCoreProj
  Q0_eq : Q0 = CIK.nilpotentProj
  core_eq : core = CIK.corePart
  nilpotent_eq : nilpotent = CIK.nilpotentPart
  projector_split : P_D + Q0 = 1
  base_split : CIK.A = core + nilpotent
  core_mul_nilpotent : core * nilpotent = 0
  nilpotent_mul_core : nilpotent * core = 0
  commute_core_nilpotent : Commute core nilpotent
  nilpotent_pow_zero :
    ∀ {m : ℕ}, CIK.drazinIndex ≤ m + 1 → nilpotent ^ (m + 1) = 0

/-- The canonical block-split packet attached to a certified inverse kernel. -/
@[rep_depth operator]
noncomputable def drazinBlockSplitPacket : DrazinBlockSplitPacket CIK where
  P_D := CIK.drazinCoreProj
  Q0 := CIK.nilpotentProj
  core := CIK.corePart
  nilpotent := CIK.nilpotentPart
  P_D_eq := rfl
  Q0_eq := rfl
  core_eq := rfl
  nilpotent_eq := rfl
  projector_split := by
    simp [CertifiedInverseKernel.drazinCoreProj, CertifiedInverseKernel.nilpotentProj]
  base_split := CIK.A_eq_corePart_add_nilpotentPart
  core_mul_nilpotent := CIK.corePart_mul_nilpotentPart_eq_zero
  nilpotent_mul_core := CIK.nilpotentPart_mul_corePart_eq_zero
  commute_core_nilpotent := CIK.corePart_commute_nilpotentPart
  nilpotent_pow_zero := by
    intro m hm
    exact CIK.nilpotentPart_pow_succ_eq_zero_of_index_le hm

end InfoGeometry.Canonical.CertifiedInverseKernel

end Certified
