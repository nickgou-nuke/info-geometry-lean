/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.Linarith

/-!
# Real symplectic contractions by complex and para-complex operators

The two native bilinear forms are `ω.compRight I`, evaluated as `ω u (I v)`,
and `ω.compLeft K`, evaluated as `ω (K u) v`. Their algebraic compatibility
does not identify them as the same metric. Anticommutation is exactly the
condition for an antisymplectic involution to preserve the right-slot form;
positivity is a separate hypothesis.

No manifold, connection, curvature, or statistical model is constructed here.
-/

namespace InfoGeometry.Geometry.SymplecticComplexParaCompatibility

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A single nondegenerate form cannot determine both square signs through
the same left-slot contraction on a nontrivial real module. -/
theorem same_metric_incompatible_squares [Nontrivial V]
    (g : LinearMap.BilinForm ℝ V) (I K : Module.End ℝ V)
    (hg : g.Nondegenerate) (hI : I * I = -1) (hK : K * K = 1)
    (heq : g.compLeft I = g.compLeft K) : False := by
  have hIK : I = K := g.compLeft_injective hg heq
  have hid : (1 : Module.End ℝ V) = -1 := by
    calc
      (1 : Module.End ℝ V) = K * K := hK.symm
      _ = I * I := by rw [hIK]
      _ = -1 := hI
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hvneg : v = -v := by
    simpa using LinearMap.congr_fun hid v
  have htwo : (2 : ℝ) • v = 0 := by
    rw [two_smul]
    exact (congrArg (fun w : V => w + v) hvneg).trans (neg_add_cancel v)
  exact hv ((smul_eq_zero.mp htwo).resolve_left two_ne_zero)

/-- A symplectic square-minus-one operator is skew-adjoint for the form. -/
theorem complex_skew_adjoint (ω : LinearMap.BilinForm ℝ V)
    (I : Module.End ℝ V) (hI : I * I = -1)
    (hSymp : ∀ u v, ω (I u) (I v) = ω u v) (u v : V) :
    ω (I u) v = -ω u (I v) := by
  have hs : I (I v) = -v := by
    simpa using LinearMap.congr_fun hI v
  have h := hSymp u (I v)
  rw [hs, map_neg] at h
  simpa only [neg_neg] using congrArg (fun r : ℝ => -r) h

/-- An antisymplectic involution is skew-adjoint for the form. -/
theorem para_skew_adjoint (ω : LinearMap.BilinForm ℝ V)
    (K : Module.End ℝ V) (hK : K * K = 1)
    (hAnti : ∀ u v, ω (K u) (K v) = -ω u v) (u v : V) :
    ω (K u) v = -ω u (K v) := by
  have hs : K (K v) = v := by
    simpa using LinearMap.congr_fun hK v
  simpa only [hs] using hAnti u (K v)

/-- The right-slot contraction by a compatible complex operator is symmetric. -/
theorem complexMetric_symmetric (ω : LinearMap.BilinForm ℝ V)
    (I : Module.End ℝ V) (hω : ω.IsAlt) (hI : I * I = -1)
    (hSymp : ∀ u v, ω (I u) (I v) = ω u v) :
    (ω.compRight I).IsSymm := by
  refine ⟨fun u v => ?_⟩
  change ω u (I v) = ω v (I u)
  calc
    ω u (I v) = -ω (I u) v := by
      have h := complex_skew_adjoint ω I hI hSymp u v
      simpa only [neg_neg] using (congrArg (fun r : ℝ => -r) h).symm
    _ = ω v (I u) := hω.neg_eq (I u) v

/-- The left-slot contraction by an antisymplectic involution is symmetric. -/
theorem paraMetric_symmetric (ω : LinearMap.BilinForm ℝ V)
    (K : Module.End ℝ V) (hω : ω.IsAlt) (hK : K * K = 1)
    (hAnti : ∀ u v, ω (K u) (K v) = -ω u v) :
    (ω.compLeft K).IsSymm := by
  refine ⟨fun u v => ?_⟩
  change ω (K u) v = ω (K v) u
  calc
    ω (K u) v = -ω u (K v) := para_skew_adjoint ω K hK hAnti u v
    _ = ω (K v) u := hω.neg_eq u (K v)

/-- The square-minus-one identity preserves nondegeneracy under right
contraction, independently of positivity or finite dimension. -/
theorem complexMetric_nondegenerate (ω : LinearMap.BilinForm ℝ V)
    (I : Module.End ℝ V) (hω : ω.Nondegenerate) (hI : I * I = -1) :
    (ω.compRight I).Nondegenerate := by
  have hs (v : V) : I (I v) = -v := by
    simpa using LinearMap.congr_fun hI v
  constructor
  · intro u hu
    apply hω.1 u
    intro v
    have h := hu (-(I v))
    change ω u (I (-(I v))) = 0 at h
    simpa only [map_neg, hs, neg_neg] using h
  · intro v hv
    have hIv : I v = 0 := hω.2 (I v) (fun u => hv u)
    have hneg : -v = 0 := by
      calc
        -v = I (I v) := (hs v).symm
        _ = I 0 := congrArg I hIv
        _ = 0 := map_zero I
    exact neg_eq_zero.mp hneg

/-- The involution identity preserves nondegeneracy under left contraction. -/
theorem paraMetric_nondegenerate (ω : LinearMap.BilinForm ℝ V)
    (K : Module.End ℝ V) (hω : ω.Nondegenerate) (hK : K * K = 1) :
    (ω.compLeft K).Nondegenerate := by
  have hs (v : V) : K (K v) = v := by
    simpa using LinearMap.congr_fun hK v
  constructor
  · intro u hu
    have hKu : K u = 0 := hω.1 (K u) (fun v => hu v)
    calc
      u = K (K u) := (hs u).symm
      _ = K 0 := congrArg K hKu
      _ = 0 := map_zero K
  · intro v hv
    apply hω.2 v
    intro u
    have h := hv (K u)
    change ω (K (K u)) v = 0 at h
    simpa only [hs] using h

/-- With the stated left/right slot convention, the intertwiner `I * K`
has a positive sign. Anticommutation and both square identities are used. -/
theorem metric_intertwining (ω : LinearMap.BilinForm ℝ V)
    (I K : Module.End ℝ V) (hI : I * I = -1) (hK : K * K = 1)
    (hSymp : ∀ u v, ω (I u) (I v) = ω u v)
    (hIK : I * K = -(K * I)) :
    (ω.compLeft K).compLeft (I * K) = ω.compRight I := by
  ext u v
  change ω (K (I (K u))) v = ω u (I v)
  have hKK : K (K u) = u := by
    simpa using LinearMap.congr_fun hK u
  have hanti : I (K (K u)) = -(K (I (K u))) := by
    simpa using LinearMap.congr_fun hIK (K u)
  rw [hKK] at hanti
  have hKIK : K (I (K u)) = -(I u) := by
    simpa only [neg_neg] using (congrArg (fun w : V => -w) hanti).symm
  rw [hKIK]
  simp only [map_neg, LinearMap.neg_apply]
  rw [complex_skew_adjoint ω I hI hSymp u v, neg_neg]

/-- Reversing the intertwiner order changes the sign. This identity does
not require anticommutation or antisymplectic preservation by `K`. -/
theorem reverse_metric_intertwining (ω : LinearMap.BilinForm ℝ V)
    (I K : Module.End ℝ V) (hI : I * I = -1) (hK : K * K = 1)
    (hSymp : ∀ u v, ω (I u) (I v) = ω u v) :
    (ω.compLeft K).compLeft (K * I) = -(ω.compRight I) := by
  ext u v
  change ω (K (K (I u))) v = -(ω u (I v))
  have hs : K (K (I u)) = I u := by
    simpa using LinearMap.congr_fun hK (I u)
  rw [hs]
  exact complex_skew_adjoint ω I hI hSymp u v

/-- For an antisymplectic involution, preservation of the right-slot form
is equivalent to anticommutation. Positivity, alternation and a square
identity for `I` are unnecessary for this exact algebraic equivalence. -/
theorem complexMetric_isometry_iff_anticommute (ω : LinearMap.BilinForm ℝ V)
    (I K : Module.End ℝ V) (hω : ω.Nondegenerate) (hK : K * K = 1)
    (hAnti : ∀ u v, ω (K u) (K v) = -ω u v) :
    (ω.compRight I).comp K K = ω.compRight I ↔ I * K = -(K * I) := by
  constructor
  · intro hIso
    ext v
    change I (K v) = -(K (I v))
    have hzero : I (K v) + K (I v) = 0 := by
      apply hω.2
      intro u
      have h := LinearMap.congr_fun (LinearMap.congr_fun hIso (K u)) v
      change ω (K (K u)) (I (K v)) = ω (K u) (I v) at h
      have hs : K (K u) = u := by
        simpa using LinearMap.congr_fun hK u
      rw [hs, para_skew_adjoint ω K hK hAnti u (I v)] at h
      rw [map_add, h, neg_add_cancel]
    simpa using congrArg (fun w : V => w - K (I v)) hzero
  · intro hIK
    ext u v
    change ω (K u) (I (K v)) = ω u (I v)
    have hanti : I (K v) = -(K (I v)) := by
      simpa using LinearMap.congr_fun hIK v
    rw [hanti, map_neg, hAnti u (I v), neg_neg]

/-- Strict positivity excludes a commuting antisymplectic involution on
a nontrivial real module. It does not force anticommutation. -/
theorem positive_complexMetric_not_commute [Nontrivial V]
    (ω : LinearMap.BilinForm ℝ V) (I K : Module.End ℝ V)
    (hK : K * K = 1) (hAnti : ∀ u v, ω (K u) (K v) = -ω u v)
    (hPos : ∀ v, v ≠ 0 → 0 < ω v (I v)) : I * K ≠ K * I := by
  intro hComm
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hKv : K v ≠ 0 := by
    intro hz
    have hs : K (K v) = v := by
      simpa using LinearMap.congr_fun hK v
    exact hv (by simpa [hz] using hs.symm)
  have hp := hPos v hv
  have hpK := hPos (K v) hKv
  have hcomm : I (K v) = K (I v) := by
    simpa using LinearMap.congr_fun hComm v
  rw [hcomm, hAnti v (I v)] at hpK
  exact (not_lt_of_ge (neg_nonpos.mpr hp.le)) hpK

/-- The product of two skew-adjoint operators is skew-adjoint when they
anticommute. Native adjoint-pair multiplication reverses the product order. -/
theorem skewAdjoint_mul_of_anticommute (g : LinearMap.BilinForm ℝ V)
    (I K : Module.End ℝ V) (hI : LinearMap.IsSkewAdjoint g I)
    (hK : LinearMap.IsSkewAdjoint g K) (hIK : I * K = -(K * I)) :
    LinearMap.IsSkewAdjoint g (I * K) := by
  have hprod : LinearMap.IsAdjointPair g g (I * K) ((-K) * (-I)) :=
    LinearMap.IsAdjointPair.mul (f := I) (g := -I) (f' := K) (g' := -K) hI hK
  have hrev : K * I = -(I * K) := by
    simpa only [neg_neg] using
      (congrArg (fun A : Module.End ℝ V => -A) hIK).symm
  rw [neg_mul_neg, hrev] at hprod
  exact hprod

/-- For a symmetric real bilinear form, contraction by the anticommuting
skew-adjoint product is alternating. Nondegeneracy is unnecessary. -/
theorem skewAdjoint_product_leftContraction_isAlt (g : LinearMap.BilinForm ℝ V)
    (I K : Module.End ℝ V) (hg : g.IsSymm)
    (hI : LinearMap.IsSkewAdjoint g I) (hK : LinearMap.IsSkewAdjoint g K)
    (hIK : I * K = -(K * I)) : (g.compLeft (I * K)).IsAlt := by
  intro v
  change g ((I * K) v) v = 0
  have h := skewAdjoint_mul_of_anticommute g I K hI hK hIK v v
  change g ((I * K) v) v = g v (-((I * K) v)) at h
  rw [map_neg, hg.eq v ((I * K) v)] at h
  exact eq_zero_of_neg_eq h.symm

end InfoGeometry.Geometry.SymplecticComplexParaCompatibility
