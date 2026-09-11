import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TensorTowerColimit
import InfoGeometry.Canonical.TensorColimitExpectation
import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# Identification of the CPT Fractal Tower with the Generic Tensor Colimit

This module provides a theorem-level comparison surface between the specific
CPT fractal tower limit carrier (`InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit`)
and the generic tensor-colimit formalization (`TensorTowerColimit`).

It records only the checked algebraic compatibility statements in this file; it
does not assert an independent macroscopic field theorem.
-/

namespace InfoGeometry.Canonical.CPTTensorColimitIdentification

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open TensorColimitExpectation

/-!
## Algebraic Morphism Instantiations

The generic tensor colimit requires linear maps over the base ring. 
We explicitly construct the `ℝ`-linear map projections of our algebraic 
ring homomorphisms.
-/

/-- The CPT tower bonding map as an `ℝ`-algebra homomorphism. -/
noncomputable def stageBondAlg (n : ℕ) : Stage n →ₐ[ℝ] Stage (n + 1) :=
  stageEmbed n

/-- The stage transition map as an `ℝ`-linear map. -/
noncomputable def stageBondLinear (n : ℕ) : Stage n →ₗ[ℝ] Stage (n + 1) where
  toFun := stageBond n
  map_add' := map_add (stageBond n)
  map_smul' := by
    intro r x
    change stageEmbed n (r • x) = r • stageEmbed n x
    exact map_smul (stageEmbed n) r x

/-- The colimit insertion map as an `ℝ`-linear map. -/
noncomputable def ofStageLinear (n : ℕ) : Stage n →ₗ[ℝ] Limit where
  toFun := ofStage n
  map_add' := map_add (ofStage n)
  map_smul' := by
    intro r x
    -- target: ofStage n (r • x) = r • ofStage n x
    -- By definition of Algebra, scalar mult is multiplication by algebraMap
    change ofStage n (r • x) = (algebraMap ℝ Limit) r * ofStage n x
    have h1 : r • x = (algebraMap ℝ (Stage n)) r * x := Algebra.smul_def r x
    rw [h1]
    rw [ofStage_mul]
    have h2 : (algebraMap ℝ Limit) r = ofStage n ((algebraMap ℝ (Stage n)) r) := by
      -- algebraMap ℝ Limit is definitionally realAlgebraMap
      change realAlgebraMap r = ofStage n ((algebraMap ℝ (Stage n)) r)
      exact realAlgebraMap_stage n r
    rw [h2]

/-!
## Colimit Carrier Commutativity

We prove that the specific CPT tower maps satisfy the generic tensor colimit 
commutativity condition `psi_{n+1} ∘ iota_n = psi_n`.
-/

/-- The specific CPT embeddings commute appropriately to form the exact colimit cone. -/
theorem ofStageLinear_comm (n : ℕ) : 
    (ofStageLinear (n + 1)).comp (stageBondLinear n) = ofStageLinear n := by
  ext x
  change ofStage (n + 1) (stageBond n x) = ofStage n x
  exact ofStage_apply_bond n x

/-- The CPT colimit insertion as an `ℝ`-algebra homomorphism. -/
noncomputable def ofStageAlg (n : ℕ) : Stage n →ₐ[ℝ] Limit where
  toFun := ofStage n
  map_one' := map_one (ofStage n)
  map_mul' := map_mul (ofStage n)
  map_zero' := map_zero (ofStage n)
  map_add' := map_add (ofStage n)
  commutes' r := by
    rw [← realAlgebraMap_stage (n := n) (r := r)]
    rfl

/--
The CPT direct-limit carrier is the generic tensor-inductive-limit carrier
instantiated on the `Cl(1,1)` tower.

This is the theorem-level identification of the specific carrier with the
generic tensor-colimit API: the carrier object is `Limit`, and the canonical
embeddings are exactly `ofStage`.
-/
noncomputable def cptTensorInductiveLimit :
    TensorInductiveLimit (R := ℝ) (A := Stage) stageBondAlg where
  AInf := Limit
  instSemiring := inferInstance
  instAlgebra := inferInstance
  inj := ofStageAlg
  inj_compat := by
    intro n x
    exact ofStage_apply_bond n x

/-- The carrier used by the CPT tower and the generic tensor colimit is definitionally the same. -/
theorem cptTensorInductiveLimit_carrier :
    (cptTensorInductiveLimit).AInf = Limit := rfl

/-- The canonical injection of the generic tensor colimit is the CPT tower map. -/
@[simp] theorem cptTensorInductiveLimit_inj (n : ℕ) :
    (cptTensorInductiveLimit).inj n = ofStageAlg n := rfl

/-!
## Topological Protection and Limit Survival

By identifying the carriers, we immediately inherit the generic topological 
protection theorems for the CPT field algebra.
-/

/-- 
THEOREM: Protected CPT States Survive in the Macroscopic Limit.
Because the specific CPT field algebra forms a generic tensor colimit, any 
topologically protected stage state (one that never vanishes at any finite 
depth) strictly survives in the infinite-dimensional macroscopic limit.
-/
theorem cpt_protected_states_survive (n : ℕ) (x : Stage n) 
    (h_kernel : ∀ m A, ofStageLinear m A = 0 → ∃ k, iota_seq Stage stageBondLinear m k A = 0)
    (h_prot : IsTopologicallyProtected Stage stageBondLinear n x) : 
    ofStageLinear n x ≠ 0 := by
  exact protected_states_survive_colimit Stage stageBondLinear Limit ofStageLinear h_kernel n x h_prot

end InfoGeometry.Canonical.CPTTensorColimitIdentification
