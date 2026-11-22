/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Clifford.SplitQ11Projectors
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KreinProjectorLattice
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.PositiveSectorMetric
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false

namespace InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma modular_j_complex_i_anticommute :
    (modular_j (E := E)).comp (complex_i (E := E)) =
      -((complex_i (E := E)).comp (modular_j (E := E))) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext
  · simp [complex_i]
  · simp [complex_i]

noncomputable def cl11RepLin :
    (ℝ × ℝ) →ₗ[ℝ] (DoubledSpace E →L[ℝ] DoubledSpace E) where
  toFun v := v.1 • modular_j (E := E) + v.2 • complex_i (E := E)
  map_add' := by
    intro u v
    apply ContinuousLinearMap.ext
    intro w
    simp [add_smul, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro a v
    apply ContinuousLinearMap.ext
    intro w
    simp [smul_add, smul_smul]

omit [CompleteSpace E] in
lemma cl11RepLin_apply_to_doubled (a b : ℝ) (x y : E) :
    cl11RepLin (E := E) (a, b) (to_doubled x y) = to_doubled ((a - b) • y) ((a + b) • x) := by
  apply DoubledSpace.ext <;>
  simp [cl11RepLin, to_doubled, sub_eq_add_neg, add_smul]

omit [CompleteSpace E] in
lemma cl11RepLin_sq (v : ℝ × ℝ) :
    (cl11RepLin (E := E) v) * (cl11RepLin (E := E) v)
      = algebraMap ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) (InfoGeometry.Clifford.splitQ11 v) := by
  rcases v with ⟨a, b⟩
  have hab1 : (a - b) * (a + b) = a * a - b * b := by ring
  have hab2 : (a + b) * (a - b) = a * a - b * b := by ring
  apply ContinuousLinearMap.ext
  intro w
  have hw : to_doubled (WithLp.fst w) (WithLp.snd w) = w := by
    apply DoubledSpace.ext <;> simp
  rw [← hw]
  apply DoubledSpace.ext
  · calc
      WithLp.fst
          (((cl11RepLin (E := E) (a, b)) * (cl11RepLin (E := E) (a, b)))
            (to_doubled (WithLp.fst w) (WithLp.snd w)))
          = (a - b) • ((a + b) • WithLp.fst w) := by
              simp [cl11RepLin_apply_to_doubled]
      _ = ((a * a - b * b) : ℝ) • WithLp.fst w := by
              rw [smul_smul, hab1]
      _ = WithLp.fst
            (((algebraMap ℝ (DoubledSpace E →L[ℝ] DoubledSpace E))
                (InfoGeometry.Clifford.splitQ11 (a, b)))
              (to_doubled (WithLp.fst w) (WithLp.snd w))) := by
              simp [InfoGeometry.Clifford.splitQ11_apply, Algebra.algebraMap_eq_smul_one]
  · calc
      WithLp.snd
          (((cl11RepLin (E := E) (a, b)) * (cl11RepLin (E := E) (a, b)))
            (to_doubled (WithLp.fst w) (WithLp.snd w)))
          = (a + b) • ((a - b) • WithLp.snd w) := by
              simp [cl11RepLin_apply_to_doubled]
      _ = ((a * a - b * b) : ℝ) • WithLp.snd w := by
              rw [smul_smul, hab2]
      _ = WithLp.snd
            (((algebraMap ℝ (DoubledSpace E →L[ℝ] DoubledSpace E))
                (InfoGeometry.Clifford.splitQ11 (a, b)))
              (to_doubled (WithLp.fst w) (WithLp.snd w))) := by
              simp [InfoGeometry.Clifford.splitQ11_apply, Algebra.algebraMap_eq_smul_one]

noncomputable def cl11Rep :
    CliffordAlgebra InfoGeometry.Clifford.splitQ11 →ₐ[ℝ] (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  CliffordAlgebra.lift InfoGeometry.Clifford.splitQ11 ⟨cl11RepLin (E := E), cl11RepLin_sq (E := E)⟩

omit [CompleteSpace E] in
@[simp] lemma cl11Rep_ι_apply (v : ℝ × ℝ) :
    cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 v) = cl11RepLin (E := E) v := by
  simp [cl11Rep]

lemma cl11Rep_ι_one_zero :
    cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)) = modular_j (E := E) := by
  rw [cl11Rep_ι_apply]
  apply ContinuousLinearMap.ext
  intro w
  simp [cl11RepLin]

lemma cl11Rep_ι_zero_one :
    cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) = complex_i (E := E) := by
  rw [cl11Rep_ι_apply]
  apply ContinuousLinearMap.ext
  intro w
  simp [cl11RepLin]

lemma cl11Rep_ι_one_zero_sq :
    cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0))
      * cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  rw [cl11Rep_ι_apply]
  calc
    cl11RepLin (E := E) (1, 0) * cl11RepLin (E := E) (1, 0)
        = algebraMap ℝ (DoubledSpace E →L[ℝ] DoubledSpace E)
            (InfoGeometry.Clifford.splitQ11 (1, 0)) := cl11RepLin_sq (E := E) (1, 0)
    _ = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
      apply ContinuousLinearMap.ext
      intro x
      simp [InfoGeometry.Clifford.splitQ11_apply]

lemma cl11Rep_ι_zero_one_sq :
    cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1))
      * cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  rw [cl11Rep_ι_apply]
  calc
    cl11RepLin (E := E) (0, 1) * cl11RepLin (E := E) (0, 1)
        = algebraMap ℝ (DoubledSpace E →L[ℝ] DoubledSpace E)
            (InfoGeometry.Clifford.splitQ11 (0, 1)) := cl11RepLin_sq (E := E) (0, 1)
    _ = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
      apply ContinuousLinearMap.ext
      intro x
      simp [InfoGeometry.Clifford.splitQ11_apply]

lemma cl11Rep_ι_one_zero_anticommute_ι_zero_one :
    cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0))
      * cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1))
      = -(cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1))
          * cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0))) := by
  rw [cl11Rep_ι_one_zero, cl11Rep_ι_zero_one]
  exact modular_j_complex_i_anticommute (E := E)

lemma cl11Rep_pseudoscalar :
    cl11Rep (E := E)
      (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)
        * CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1))
      = spectral_epsilon (E := E) := by
  rw [map_mul, cl11Rep_ι_one_zero, cl11Rep_ι_zero_one]
  apply ContinuousLinearMap.ext
  intro v
  apply DoubledSpace.ext
  · simp [complex_i]
  · simp [complex_i]

/-- The positive projector in the finite `Cl(1,1)` sector lattice is represented
by the actual positive Krein projector on the doubled real carrier. This
identifies the algebra projector with the analytic eigenspace projector rather
than merely matching their names. -/
theorem cl11Rep_kreinSectorPlus_eq_P_plus :
    cl11Rep (E := E)
        (InfoGeometry.Canonical.KreinProjectorLattice.KreinSector.toAlg
          InfoGeometry.Canonical.KreinProjectorLattice.KreinSector.plus) =
      KreinSpace.P_plus (H := DoubledSpace E) := by
  rw [InfoGeometry.Canonical.KreinProjectorLattice.KreinSector.toAlg_plus,
    InfoGeometry.Clifford.SplitQ11Projectors.epsPlusProjector_eq_half_one_add_eps,
    map_smul, map_add, map_one]
  have heps : cl11Rep (E := E) InfoGeometry.Clifford.SplitQ11PhaseFlip.epsGen =
      spectral_epsilon (E := E) := cl11Rep_pseudoscalar
  rw [heps]
  simp [KreinSpace.P_plus, KreinSpace.kreinSplitInvolution,
    InfoGeometry.GrandUnification.ArchetypeDictionary.SplitInvolution.P_plus,
    InfoGeometry.GrandUnification.ArchetypeDictionary.peircePlus,
    jCLM_eq_spectral_epsilon]

/-- Applying the lattice's positive projector to a doubled state lands in the
positive fundamental subspace of the actual Krein space. -/
theorem cl11Rep_kreinSectorPlus_apply_mem_posSubspace (u : DoubledSpace E) :
    cl11Rep (E := E)
        (InfoGeometry.Canonical.KreinProjectorLattice.KreinSector.toAlg
          InfoGeometry.Canonical.KreinProjectorLattice.KreinSector.plus) u ∈
      KreinSpace.posSubspace (DoubledSpace E) := by
  rw [cl11Rep_kreinSectorPlus_eq_P_plus]
  exact KreinSpace.P_plus_mem_posSubspace (H := DoubledSpace E) u

/-- Exact equivalence between fixed points of the `Cl(1,1)` positive projector
`p₊ = KreinSector.toAlg .plus` and membership in `KreinSpace.posSubspace`. -/
theorem cl11Rep_kreinSectorPlus_fixed_iff_mem_posSubspace (u : DoubledSpace E) :
    cl11Rep (E := E)
        (InfoGeometry.Canonical.KreinProjectorLattice.KreinSector.toAlg
          InfoGeometry.Canonical.KreinProjectorLattice.KreinSector.plus) u = u ↔
      u ∈ KreinSpace.posSubspace (DoubledSpace E) := by
  rw [cl11Rep_kreinSectorPlus_eq_P_plus]
  exact PositiveSectorMetric.P_plus_fixed_iff_mem_posSubspace u

/-- Strict positivity of `PositiveSectorMetric.sectorMetric` on nonzero vectors
fixed by the `Cl(1,1)` positive lattice projector `p₊`. -/
theorem sectorMetric_self_pos_of_cl11Rep_kreinSectorPlus_fixed
    {x v : DoubledSpace E}
    (hx : cl11Rep (E := E)
      (InfoGeometry.Canonical.KreinProjectorLattice.KreinSector.toAlg
        InfoGeometry.Canonical.KreinProjectorLattice.KreinSector.plus) x = x)
    (hx0 : x ≠ 0)
    (hv : cl11Rep (E := E)
      (InfoGeometry.Canonical.KreinProjectorLattice.KreinSector.toAlg
        InfoGeometry.Canonical.KreinProjectorLattice.KreinSector.plus) v = v)
    (hv0 : v ≠ 0) :
    0 < PositiveSectorMetric.sectorMetric x v v :=
  PositiveSectorMetric.sectorMetric_self_pos
    ((cl11Rep_kreinSectorPlus_fixed_iff_mem_posSubspace x).mp hx) hx0
    ((cl11Rep_kreinSectorPlus_fixed_iff_mem_posSubspace v).mp hv) hv0

end InfoGeometry.Krein
