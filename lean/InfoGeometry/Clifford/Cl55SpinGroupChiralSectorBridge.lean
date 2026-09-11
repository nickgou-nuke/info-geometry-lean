import InfoGeometry.Clifford.Cl55SpinGroupChiralityBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Chiral sector submodules for the matrix `Spin(5,5)` action

The preceding owner proves the projector commutation identities.  This file
packages their immediate representation-theoretic consequence as genuine
finite-dimensional `Submodule`s.  It does not yet construct restricted
monoid homomorphisms or identify these sectors with an independently defined
native carrier.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge

open Matrix
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinGroupChiralityBridge
open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.SpinorRep

def chiralPlusSector : Submodule ℝ (SpinorSpace 5) where
  carrier := {v | Matrix.mulVec chiralPlusProjector v = v}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change Matrix.mulVec chiralPlusProjector (v + w) = v + w
    rw [Matrix.mulVec_add, hv, hw]
  smul_mem' := by
    intro a v hv
    change Matrix.mulVec chiralPlusProjector (a • v) = a • v
    rw [Matrix.mulVec_smul, hv]

def chiralMinusSector : Submodule ℝ (SpinorSpace 5) where
  carrier := {v | Matrix.mulVec chiralMinusProjector v = v}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change Matrix.mulVec chiralMinusProjector (v + w) = v + w
    rw [Matrix.mulVec_add, hv, hw]
  smul_mem' := by
    intro a v hv
    change Matrix.mulVec chiralMinusProjector (a • v) = a • v
    rw [Matrix.mulVec_smul, hv]

@[simp] theorem mem_chiralPlusSector (v : SpinorSpace 5) :
    v ∈ chiralPlusSector ↔ Matrix.mulVec chiralPlusProjector v = v := Iff.rfl

@[simp] theorem mem_chiralMinusSector (v : SpinorSpace 5) :
    v ∈ chiralMinusSector ↔ Matrix.mulVec chiralMinusProjector v = v := Iff.rfl

theorem spinGroup_matrix_maps_chiralPlusSector
    (g : Spin55) {v : SpinorSpace 5} (hv : v ∈ chiralPlusSector) :
    Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v ∈ chiralPlusSector := by
  exact spinGroup_matrix_preserves_chiralPlus_vector g v hv

theorem spinGroup_matrix_maps_chiralMinusSector
    (g : Spin55) {v : SpinorSpace 5} (hv : v ∈ chiralMinusSector) :
    Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v ∈ chiralMinusSector := by
  exact spinGroup_matrix_preserves_chiralMinus_vector g v hv

theorem spinGroup_matrix_preserves_chiral_decomposition
    (g : Spin55) {vPlus vMinus : SpinorSpace 5}
    (hvPlus : vPlus ∈ chiralPlusSector) (hvMinus : vMinus ∈ chiralMinusSector) :
    Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) vPlus ∈ chiralPlusSector ∧
      Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) vMinus ∈ chiralMinusSector := by
  exact ⟨spinGroup_matrix_maps_chiralPlusSector g hvPlus,
    spinGroup_matrix_maps_chiralMinusSector g hvMinus⟩

theorem chiralSectors_disjoint :
    chiralPlusSector ⊓ chiralMinusSector = ⊥ := by
  apply le_antisymm
  · intro v hv
    have hproj := congrArg (Matrix.mulVec chiralPlusProjector) hv.2
    have hzero := congrArg (Matrix.mulVec chiralPlusProjector)
      (show Matrix.mulVec chiralMinusProjector v = v from hv.2)
    rw [Matrix.mulVec_mulVec, chiralProjectors_orthogonal] at hzero
    rw [hv.1] at hzero
    exact (show v = 0 by simpa using hzero.symm)
  · exact bot_le

theorem chiralSectors_sup_top :
    chiralPlusSector ⊔ chiralMinusSector = ⊤ := by
  refine Submodule.eq_top_iff'.2 ?_
  intro v
  rw [Submodule.mem_sup]
  refine ⟨
    Matrix.mulVec chiralPlusProjector v,
    by
      change Matrix.mulVec chiralPlusProjector (Matrix.mulVec chiralPlusProjector v) =
        Matrix.mulVec chiralPlusProjector v
      rw [Matrix.mulVec_mulVec, chiralPlusProjector_idempotent],
    Matrix.mulVec chiralMinusProjector v,
    by
      change Matrix.mulVec chiralMinusProjector (Matrix.mulVec chiralMinusProjector v) =
        Matrix.mulVec chiralMinusProjector v
      rw [Matrix.mulVec_mulVec, chiralMinusProjector_idempotent],
    by
      calc
        Matrix.mulVec chiralPlusProjector v + Matrix.mulVec chiralMinusProjector v
            = Matrix.mulVec (chiralPlusProjector + chiralMinusProjector) v := by
              rw [Matrix.add_mulVec]
        _ = Matrix.mulVec (1 : SpinorMatrix 5) v := by
              rw [chiralProjectors_complementary]
        _ = v := by
              simpa using (Matrix.one_mulVec v)⟩

theorem chiral_projector_decomposition (v : SpinorSpace 5) :
    Matrix.mulVec chiralPlusProjector v +
        Matrix.mulVec chiralMinusProjector v = v := by
  rw [← Matrix.add_mulVec, chiralProjectors_complementary]
  exact Matrix.one_mulVec v

theorem chiralPlusProjector_mem_chiralPlusSector (v : SpinorSpace 5) :
    Matrix.mulVec chiralPlusProjector v ∈ chiralPlusSector := by
  change Matrix.mulVec chiralPlusProjector
      (Matrix.mulVec chiralPlusProjector v) = Matrix.mulVec chiralPlusProjector v
  rw [Matrix.mulVec_mulVec, chiralPlusProjector_idempotent]

theorem chiralMinusProjector_mem_chiralMinusSector (v : SpinorSpace 5) :
    Matrix.mulVec chiralMinusProjector v ∈ chiralMinusSector := by
  change Matrix.mulVec chiralMinusProjector
      (Matrix.mulVec chiralMinusProjector v) = Matrix.mulVec chiralMinusProjector v
  rw [Matrix.mulVec_mulVec, chiralMinusProjector_idempotent]

theorem spinGroup_matrix_action_decomposes_chiral
    (g : Spin55) (v : SpinorSpace 5) :
    Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v =
      Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55))
          (Matrix.mulVec chiralPlusProjector v) +
      Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55))
          (Matrix.mulVec chiralMinusProjector v) := by
  have h := congrArg
    (Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)))
    (chiral_projector_decomposition v)
  simpa only [Matrix.mulVec_add] using h.symm

theorem spinGroup_matrix_projector_intertwines_plus
    (g : Spin55) (v : SpinorSpace 5) :
    Matrix.mulVec chiralPlusProjector
        (Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v) =
      Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55))
        (Matrix.mulVec chiralPlusProjector v) := by
  calc
    Matrix.mulVec chiralPlusProjector
        (Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v) =
        Matrix.mulVec (chiralPlusProjector * cl55SpinorAlgEquiv (g : Cl55)) v := by
          rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55) * chiralPlusProjector) v := by
          rw [spinGroup_matrix_commutes_chiralPlusProjector]
    _ = Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55))
        (Matrix.mulVec chiralPlusProjector v) := by
          rw [← Matrix.mulVec_mulVec]

theorem spinGroup_matrix_projector_intertwines_minus
    (g : Spin55) (v : SpinorSpace 5) :
    Matrix.mulVec chiralMinusProjector
        (Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v) =
      Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55))
        (Matrix.mulVec chiralMinusProjector v) := by
  calc
    Matrix.mulVec chiralMinusProjector
        (Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v) =
        Matrix.mulVec (chiralMinusProjector * cl55SpinorAlgEquiv (g : Cl55)) v := by
          rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55) * chiralMinusProjector) v := by
          rw [spinGroup_matrix_commutes_chiralMinusProjector]
    _ = Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55))
        (Matrix.mulVec chiralMinusProjector v) := by
          rw [← Matrix.mulVec_mulVec]

theorem chiralSectors_isCompl : IsCompl chiralPlusSector chiralMinusSector :=
  ⟨disjoint_iff.mpr chiralSectors_disjoint,
    codisjoint_iff.mpr chiralSectors_sup_top⟩

end InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge
