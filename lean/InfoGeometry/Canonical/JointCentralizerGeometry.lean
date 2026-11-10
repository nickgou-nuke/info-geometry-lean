/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DualSeedCentralizer
import InfoGeometry.Canonical.LieJordanMatrixGeometry
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Relative centers and the correct trace-orthogonal centralizer

The center of a generated algebra is its intersection with the ambient
centralizer. For full matrices the ambient centralizer is trace-orthogonal
to the span of commutator images, not in general to the generators themselves.
The existing dual-seed Cartan element witnesses that distinction.

All matrix products remain in the full noncommutative matrix algebra.
The bilinear trace form is the existing `traceBilinear`, not a positive
Frobenius metric. No Apollonian realization or geometric axis is asserted.
-/

namespace InfoGeometry.Canonical.JointCentralizerGeometry

open InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Canonical.LieJordanMatrixGeometry

section Center

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- The center of a subalgebra, embedded in the ambient algebra, is the
intersection with its relative commutant. -/
theorem center_map_val (B : Subalgebra R A) :
    (Subalgebra.center R B).map B.val = B ⊓ Subalgebra.centralizer R (B : Set A) := by
  ext a
  rw [Subalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, ?_⟩
    change (x : A) ∈ Subalgebra.centralizer R (B : Set A)
    rw [Subalgebra.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val ((Subalgebra.mem_center_iff.mp hx) ⟨y, hy⟩)
  · rintro ⟨ha, hc⟩
    refine ⟨⟨a, ha⟩, ?_, rfl⟩
    rw [Subalgebra.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subalgebra.mem_centralizer_iff R).mp hc y y.property

/-- The additional hypothesis needed to identify a relative commutant with
the embedded center is precisely containment in the subalgebra. -/
theorem center_map_val_eq_centralizer_iff (B : Subalgebra R A) :
    (Subalgebra.center R B).map B.val = Subalgebra.centralizer R (B : Set A) ↔
      Subalgebra.centralizer R (B : Set A) ≤ B := by
  rw [center_map_val, inf_eq_right]

/-- Native generation and native centralization give the precise center
formula for a pair of unital subalgebras. -/
theorem center_sup_map_val (P₁ P₂ : Subalgebra R A) :
    (Subalgebra.center R (P₁ ⊔ P₂ : Subalgebra R A)).map
      (P₁ ⊔ P₂ : Subalgebra R A).val =
      (P₁ ⊔ P₂) ⊓
        (Subalgebra.centralizer R (P₁ : Set A) ⊓
          Subalgebra.centralizer R (P₂ : Set A)) := by
  rw [center_map_val, Subalgebra.centralizer_coe_sup]

end Center

section Cartan

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {d b : A}

/-- The Cartan generator fails to centralize a seed whenever doubling that
seed is nonzero. This states the exact characteristic/torsion boundary. -/
theorem phase_not_mem_jointCentralizer (h : IsDualSeedPair d b)
    (hd : (2 : ℕ) • d ≠ 0) :
    phasePolarization d b ∉ Subalgebra.centralizer R ({d, b} : Set A) := by
  intro hm
  have hc := (Subalgebra.mem_centralizer_iff R).mp hm d (Set.mem_insert d {b})
  have hlie := h.lie_phase_seed
  change phasePolarization d b * d - d * phasePolarization d b = (2 : ℕ) • d at hlie
  rw [hc, sub_self] at hlie
  exact hd hlie.symm

end Cartan

section Trace

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- Trace separation upgrades cyclic integration by parts to an exact
commutation criterion, over any commutative coefficient ring. -/
theorem trace_commutator_zero_iff (Z X : Matrix n n R) :
    (∀ Y : Matrix n n R, Matrix.trace (Z * (X * Y - Y * X)) = 0) ↔ Commute Z X := by
  have hskew (Y : Matrix n n R) :
      Matrix.trace (Z * (X * Y - Y * X)) +
        Matrix.trace ((X * Z - Z * X) * Y) = 0 :=
    InfoGeometry.Core.JordanMultiplicationClosure.trace_adjoint_identity
      (Matrix.traceAddMonoidHom n R) Matrix.trace_mul_comm X Z Y
  constructor
  · intro hz
    have hzero : X * Z - Z * X = 0 := by
      apply (traceBilinear_nondegenerate (K := R) (n := n)).1
      intro Y
      have he := hskew Y
      rw [hz Y, zero_add] at he
      exact he
    exact (sub_eq_zero.mp hzero).symm
  · intro hc Y
    have he := hskew Y
    rw [hc.eq, sub_self, zero_mul, Matrix.trace_zero, add_zero] at he
    exact he

/-- The common kernel of the commutators is exactly their trace annihilator. -/
theorem mem_centralizer_iff_trace (S : Set (Matrix n n R)) (Z : Matrix n n R) :
    Z ∈ Subalgebra.centralizer R S ↔
      ∀ X ∈ S, ∀ Y : Matrix n n R, Matrix.trace (Z * (X * Y - Y * X)) = 0 := by
  constructor
  · intro h X hX
    exact (trace_commutator_zero_iff Z X).mpr
      ((Subalgebra.mem_centralizer_iff R).mp h X hX).symm
  · intro h
    apply (Subalgebra.mem_centralizer_iff R).mpr
    intro X hX
    exact ((trace_commutator_zero_iff Z X).mp (h X hX)).eq.symm

/-- The orthogonal complement is taken against commutator images in the
whole ambient algebra, with Mathlib's right-orthogonal convention. -/
theorem centralizer_eq_trace_orthogonal (S : Set (Matrix n n R)) :
    (Subalgebra.centralizer R S).toSubmodule =
      (traceBilinear (K := R) (n := n)).orthogonal
        (Submodule.span R {W | ∃ X ∈ S, ∃ Y : Matrix n n R, X * Y - Y * X = W}) := by
  ext Z
  change Z ∈ Subalgebra.centralizer R S ↔ _
  rw [mem_centralizer_iff_trace, LinearMap.BilinForm.orthogonal,
    Submodule.mem_orthogonalBilin_span]
  constructor
  · intro h W hW
    rcases hW with ⟨X, hX, Y, rfl⟩
    rw [traceBilinear_apply, Matrix.trace_mul_comm]
    exact h X hX Y
  · intro h X hX Y
    have he := h ⟨X, hX, Y, rfl⟩
    rw [traceBilinear_apply, Matrix.trace_mul_comm] at he
    exact he

variable {d b : Matrix n n R}

/-- Reflexivity, not square-zero alone over a general ring, forces zero trace. -/
theorem dualSeed_trace_zero (h : IsDualSeedPair d b) : Matrix.trace d = 0 := by
  calc
    _ = Matrix.trace (polePlus d b * d) := congrArg Matrix.trace h.pd.symm
    _ = Matrix.trace (d * polePlus d b) := Matrix.trace_mul_comm _ _
    _ = 0 := by rw [h.dp, Matrix.trace_zero]

/-- The source line is totally isotropic. The partner line is obtained by
applying the same theorem to the reversed seed pair. -/
theorem seed_span_le_trace_orthogonal (h : IsDualSeedPair d b) :
    Submodule.span R ({d} : Set (Matrix n n R)) ≤
      (traceBilinear (K := R) (n := n)).orthogonal
        (Submodule.span R ({d} : Set (Matrix n n R))) := by
  apply Submodule.span_le.mpr
  intro X hX
  have hX' : X = d := Set.mem_singleton_iff.mp hX
  subst X
  change d ∈ (traceBilinear (K := R) (n := n)).orthogonal
    (Submodule.span R ({d} : Set (Matrix n n R)))
  rw [LinearMap.BilinForm.orthogonal, Submodule.mem_orthogonalBilin_span]
  intro Y hY
  have hY' : Y = d := Set.mem_singleton_iff.mp hY
  subst Y
  rw [traceBilinear_apply, h.d_sq, Matrix.trace_zero]

/-- The Cartan element is orthogonal to both source/sink directions for the
bilinear trace form even though it generally fails to centralize them. -/
theorem phase_mem_seed_trace_orthogonal (h : IsDualSeedPair d b) :
    phasePolarization d b ∈ (traceBilinear (K := R) (n := n)).orthogonal
      (Submodule.span R ({d, b} : Set (Matrix n n R))) := by
  rw [LinearMap.BilinForm.orthogonal, Submodule.mem_orthogonalBilin_span]
  intro X hX
  rcases Set.mem_insert_iff.mp hX with rfl | hX
  · rw [traceBilinear_apply, h.seed_mul_phase, Matrix.trace_neg, dualSeed_trace_zero h,
      neg_zero]
  · have hX' : X = b := Set.mem_singleton_iff.mp hX
    subst X
    rw [traceBilinear_apply, h.partner_mul_phase, dualSeed_trace_zero h.symm]

/-- A general separation theorem: joint centralization and orthogonality to
the two seed directions are different submodules. -/
theorem centralizer_ne_seed_trace_orthogonal (h : IsDualSeedPair d b)
    (hd : (2 : ℕ) • d ≠ 0) :
    (Subalgebra.centralizer R ({d, b} : Set (Matrix n n R))).toSubmodule ≠
      (traceBilinear (K := R) (n := n)).orthogonal
        (Submodule.span R ({d, b} : Set (Matrix n n R))) := by
  intro he
  apply phase_not_mem_jointCentralizer (R := R) h hd
  have hm := phase_mem_seed_trace_orthogonal h
  rw [← he] at hm
  exact hm

end Trace

end InfoGeometry.Canonical.JointCentralizerGeometry
