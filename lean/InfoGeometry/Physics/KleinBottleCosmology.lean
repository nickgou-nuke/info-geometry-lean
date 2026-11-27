/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.Q8MonodromySpinorCover
import InfoGeometry.Topology.BrillouinKleinBottleManifold
import InfoGeometry.Canonical.KleinBottleSewing
import InfoGeometry.Canonical.KleinBoundaryStates
import InfoGeometry.Clifford.Pin55ReflectionGlide
import InfoGeometry.Physics.KleinBottleDefects

namespace InfoGeometry.Physics.KleinBottleCosmology

open InfoGeometry.Topology.Q8MonodromySpinorCover
open InfoGeometry.Topology.BrillouinKleinBottleManifold
open InfoGeometry.Clifford.Pin55ReflectionGlide

noncomputable section

/-- Matrix-level Q₈ generators satisfy the defining square relations. -/
theorem quaternions_M_i_sq : M_i * M_i = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [InfoGeometry.Topology.Q8MonodromySpinorCover.M_i, Matrix.mul_apply]

/-- Matrix-level Q₈ generators satisfy the defining square relations. -/
theorem quaternions_M_j_sq : M_j * M_j = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [InfoGeometry.Topology.Q8MonodromySpinorCover.M_j, Matrix.mul_apply]

/-- Matrix-level Q₈ generators satisfy the defining square relations. -/
theorem quaternions_M_k_sq : M_k * M_k = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [InfoGeometry.Topology.Q8MonodromySpinorCover.M_k, Matrix.mul_apply]

/-- Matrix-level Q₈ anticommutation of two generators. -/
theorem quaternions_M_i_M_j_anticommute : M_i * M_j = -(M_j * M_i) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [InfoGeometry.Topology.Q8MonodromySpinorCover.M_i,
    InfoGeometry.Topology.Q8MonodromySpinorCover.M_j, Matrix.mul_apply]

/-- `M_i*M_j*M_k = -1` follows directly from matrix evaluation. -/
theorem quaternions_M_i_M_j_M_k : M_i * M_j * M_k = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [InfoGeometry.Topology.Q8MonodromySpinorCover.M_i,
    InfoGeometry.Topology.Q8MonodromySpinorCover.M_j,
    InfoGeometry.Topology.Q8MonodromySpinorCover.M_k, Matrix.mul_apply]

/-- Full local Q₈ relation package used by the physical Klein spinor cover story. -/
theorem quaternions_spinor_cover_relations :
    M_i * M_i = -1 ∧ M_j * M_j = -1 ∧ M_k * M_k = -1 ∧ M_i * M_j = -(M_j * M_i) ∧ M_i * M_j * M_k = -1 := by
  constructor
  · exact quaternions_M_i_sq
  constructor
  · exact quaternions_M_j_sq
  constructor
  · exact quaternions_M_k_sq
  constructor
  · exact quaternions_M_i_M_j_anticommute
  · exact quaternions_M_i_M_j_M_k

/-- Glide conjugates the vertical loop to its inverse in the finite Brillouin chart. -/
theorem brillouin_glide_conjugates_to_inverse (p : KPoint) :
    glide (yLoop (glideInv p)) = yLoopInv p := by
  ext i
  fin_cases i
  · simp [InfoGeometry.Topology.BrillouinKleinBottleManifold.glide,
      InfoGeometry.Topology.BrillouinKleinBottleManifold.glideInv,
      InfoGeometry.Topology.BrillouinKleinBottleManifold.yLoop,
      InfoGeometry.Topology.BrillouinKleinBottleManifold.yLoopInv]
  · simp [InfoGeometry.Topology.BrillouinKleinBottleManifold.glide,
      InfoGeometry.Topology.BrillouinKleinBottleManifold.glideInv,
      InfoGeometry.Topology.BrillouinKleinBottleManifold.yLoop,
      InfoGeometry.Topology.BrillouinKleinBottleManifold.yLoopInv]
    ring

/-- Klein boundary word reduction of one conjugated vertical loop. -/
theorem brillouin_boundary_word (p : KPoint) :
    glide (yLoop (glideInv (yLoop p))) = p := by
  rw [brillouin_glide_conjugates_to_inverse]
  ext i
  fin_cases i <;> simp [InfoGeometry.Topology.BrillouinKleinBottleManifold.yLoop,
    InfoGeometry.Topology.BrillouinKleinBottleManifold.yLoopInv]

/-- Reflection+half-translation glide squares to a unit translation in Split(5,5). -/
theorem pin55_glide_square_eq_translation (x : Split55) :
    InfoGeometry.Clifford.Pin55ReflectionGlide.glide (InfoGeometry.Clifford.Pin55ReflectionGlide.glide x)
      = InfoGeometry.Clifford.Pin55ReflectionGlide.translateP 1 x := by
  unfold InfoGeometry.Clifford.Pin55ReflectionGlide.glide
  rw [pinReflection_translateP_comm]
  rw [pinReflection_involutive]
  rw [translateP_add]
  norm_num

/-- Sewing symmetry implies vanishing chiral trace readout. -/
theorem sewn_boundary_chiral_index_vanishes (s : BoundaryState) (h : isSewn s) :
    chiralIndex s = 0 :=
  klein_throat_anomaly_vanishes s h

/-- `5`-`7` defect balance on the trivalent Klein/Torus topology. -/
theorem klein_bottle_five_seven_balance
  (V E F F5 F6 F7 : ℕ)
  (hEuler : V + F = E)
  (hRegular : 3 * V = 2 * E)
  (hFaces : F = F5 + F6 + F7)
  (hEdges : 2 * E = 5 * F5 + 6 * F6 + 7 * F7) :
  F5 = F7 :=
  InfoGeometry.Physics.klein_bottle_defects_balance V E F F5 F6 F7 hEuler hRegular hFaces hEdges

/-- Nonorientability reverses signed Chern data; therefore the invariant vanishes. -/
theorem orientation_reversal_forces_zero (c : ℤ) (h : c = -c) :
    c = 0 := by
  exact chern_zero_of_orientation_reversal h

/-- Full finite bridge packet for the Klein-cosmology lane. -/
theorem klein_bottle_cosmology_packet
    (p : KPoint)
    (x : Split55)
    (s : BoundaryState)
    (hSew : isSewn s) :
    (M_i * M_i = -1) ∧
      (M_j * M_j = -1) ∧
      (M_k * M_k = -1) ∧
      (M_i * M_j = -(M_j * M_i)) ∧
      (glide (yLoop (glideInv p)) = yLoopInv p) ∧
      (glide (yLoop (glideInv (yLoop p))) = p) ∧
      (InfoGeometry.Clifford.Pin55ReflectionGlide.glide
          (InfoGeometry.Clifford.Pin55ReflectionGlide.glide x)
        = InfoGeometry.Clifford.Pin55ReflectionGlide.translateP 1 x) ∧
      chiralIndex s = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact quaternions_M_i_sq
  · exact quaternions_M_j_sq
  · exact quaternions_M_k_sq
  · exact quaternions_M_i_M_j_anticommute
  · exact brillouin_glide_conjugates_to_inverse p
  · exact brillouin_boundary_word p
  · exact pin55_glide_square_eq_translation x
  · exact sewn_boundary_chiral_index_vanishes s hSew

section BoyleTurokTwoSheetedFRWBounce

/-- Minisuperspace FLRW Hamiltonian constraint with curvature `k`, cosmological constant `Λ`,
radiation density `M_rad`, scale factor `a`, and conjugate momentum `p_a`:
`H_WDW = -p_a² - k a² + (Λ / 3) a⁴ + M_rad`. -/
def frwBounceConstraint (k Λ M_rad a p_a : ℝ) : ℝ :=
  -(p_a ^ 2) - k * a ^ 2 + (Λ / 3) * a ^ 4 + M_rad

/-- Two-sheeted CPT mirror involution `(a, p_a) ↦ (-a, -p_a)` across the `a = 0` bounce seam. -/
def cptMirrorFRW (z : ℝ × ℝ) : ℝ × ℝ :=
  (-z.1, -z.2)

@[simp] theorem cptMirrorFRW_involutive (z : ℝ × ℝ) :
    cptMirrorFRW (cptMirrorFRW z) = z := by
  ext <;> simp [cptMirrorFRW]

theorem cptMirrorFRW_fixed_iff (z : ℝ × ℝ) :
    cptMirrorFRW z = z ↔ z = (0, 0) := by
  constructor
  · intro h
    ext
    · have h1 := congrArg Prod.fst h
      dsimp [cptMirrorFRW] at h1
      linarith
    · have h2 := congrArg Prod.snd h
      dsimp [cptMirrorFRW] at h2
      linarith
  · rintro rfl
    ext <;> simp [cptMirrorFRW]

/-- The FLRW Hamiltonian constraint is strictly invariant under the CPT mirror `(a, p_a) ↦ (-a, -p_a)`. -/
theorem frwBounceConstraint_cpt_invariant (k Λ M_rad a p_a : ℝ) :
    frwBounceConstraint k Λ M_rad (-a) (-p_a) =
      frwBounceConstraint k Λ M_rad a p_a := by
  unfold frwBounceConstraint
  ring

/-- At the `a = 0` bounce seam, the constraint holds iff `p_a² = M_rad`. -/
theorem frw_bounce_seam_turning_point (k Λ M_rad p_a : ℝ) :
    frwBounceConstraint k Λ M_rad 0 p_a = 0 ↔ p_a ^ 2 = M_rad := by
  unfold frwBounceConstraint
  constructor <;> intro h <;> linarith

/-- Negative radiation density forbids a real bounce solution at `a = 0`. -/
theorem frw_no_real_bounce_of_neg_radiation (k Λ M_rad p_a : ℝ) (hM : M_rad < 0) :
    frwBounceConstraint k Λ M_rad 0 p_a ≠ 0 := by
  intro h
  rw [frw_bounce_seam_turning_point] at h
  rw [← h] at hM
  linarith [sq_nonneg p_a, hM]

/-- For `M_rad ≥ 0`, the contracting/expanding seam momenta `±√M_rad` both solve the `a = 0`
bounce constraint and are swapped by `cptMirrorFRW`. -/
theorem frw_radiation_bounce_pair_cpt_mirror (k Λ M_rad : ℝ) (hM : 0 ≤ M_rad) :
    let pPlus := Real.sqrt M_rad
    let pMinus := -Real.sqrt M_rad
    frwBounceConstraint k Λ M_rad 0 pPlus = 0 ∧
    frwBounceConstraint k Λ M_rad 0 pMinus = 0 ∧
    cptMirrorFRW (0, pPlus) = (0, pMinus) := by
  intro pPlus pMinus
  refine ⟨?_, ?_, ?_⟩
  · rw [frw_bounce_seam_turning_point]
    exact Real.sq_sqrt hM
  · rw [frw_bounce_seam_turning_point]
    dsimp [pMinus]
    rw [neg_sq]
    exact Real.sq_sqrt hM
  · ext <;> simp [cptMirrorFRW, pPlus, pMinus]

/-- Even CPT-symmetric projector on two-sheeted Wheeler–DeWitt wavefunctions `ψ : ℝ → ℝ`. -/
def wdwEvenProj (ψ : ℝ → ℝ) (a : ℝ) : ℝ :=
  (ψ a + ψ (-a)) / 2

/-- Odd CPT-antisymmetric projector on two-sheeted Wheeler–DeWitt wavefunctions `ψ : ℝ → ℝ`. -/
def wdwOddProj (ψ : ℝ → ℝ) (a : ℝ) : ℝ :=
  (ψ a - ψ (-a)) / 2

/-- Idempotence, orthogonality, completeness, and DeWitt Dirichlet seam vanishing of the
even/odd CPT bounce parity projectors. -/
theorem wdw_bounce_parity_decomposition (ψ : ℝ → ℝ) (a : ℝ) :
    wdwEvenProj (wdwEvenProj ψ) a = wdwEvenProj ψ a ∧
    wdwOddProj (wdwOddProj ψ) a = wdwOddProj ψ a ∧
    wdwEvenProj (wdwOddProj ψ) a = 0 ∧
    wdwOddProj (wdwEvenProj ψ) a = 0 ∧
    wdwEvenProj ψ a + wdwOddProj ψ a = ψ a ∧
    wdwOddProj ψ 0 = 0 ∧
    wdwEvenProj ψ 0 = ψ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [wdwEvenProj, wdwOddProj] <;> ring

end BoyleTurokTwoSheetedFRWBounce

end
end InfoGeometry.Physics.KleinBottleCosmology
