import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.Cl11GeometricSynthesis
import InfoGeometry.Clifford.Cl11CanonicalArchetypePoset
import InfoGeometry.Clifford.SplitQ11CausalCone
import InfoGeometry.SuperGrassmannian.MajoranaCARSuperalgebra
import Mathlib.Tactic

/-!
# Evidence-carrying noncommutative archetype graph (candidate V3)

This scratch candidate records only edges backed by declarations imported from
their Lean owners.  It keeps the synthesis volume-form projectors separate
from the diagonal Krein projectors.  It does not infer an edge from shared
terminology or from a matrix identity on a different carrier.

The graph is a finite dependency relation with proof-carrying edges.  Its
transitive closure is a partial order, and a path containing at least one
owner-witnessed edge cannot return to its starting vertex.

The candidate intentionally omits the claimed native `Cl(1,2) ≃ M₂(ℂ)` edge,
an identification of the custom coquaternion carrier with `CliffordAlgebra`,
and any analytic Sato/Fock or von Neumann completion claims.  Those need
separate owner-level constructions and are not supplied by the declarations
imported here.
-/

namespace InfoGeometry.Scratch.CanonicalNoncommutativeArchetypePosetV3

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GeometricSynthesis
open InfoGeometry.Clifford.SplitQ11CausalCone
open InfoGeometry.SuperGrassmannian.MajoranaCAR

/-- Nodes denote distinct owner carriers or theorem packages. -/
inductive Archetype where
  | nativeCl11
  | realMatrixRepresentation
  | volumeForm
  | volumePeirceProjectors
  | diagonalKreinProjectors
  | kreinNullHops
  | abstractSplitCell
  | abstractCAR
  | planarMatrixSubspaces
  | planarMultiplicationLaws
  deriving DecidableEq, Repr

/-- A strictly increasing height for every witnessed dependency edge. -/
def height : Archetype → Nat
  | .nativeCl11 => 0
  | .realMatrixRepresentation => 1
  | .volumeForm => 2
  | .volumePeirceProjectors => 3
  | .diagonalKreinProjectors => 4
  | .kreinNullHops => 5
  | .abstractSplitCell => 6
  | .abstractCAR => 7
  | .planarMatrixSubspaces => 8
  | .planarMultiplicationLaws => 9

/-- A directed edge carries the exact proposition proved at its target. -/
inductive EvidenceEdge : Archetype → Archetype → Prop where
  | clifford_matrix_equiv
      (w : Nonempty (CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11 ≃ₐ[ℝ]
        InfoGeometry.Clifford.Cl11Matrix.Mat2)) :
      EvidenceEdge .nativeCl11 .realMatrixRepresentation
  | matrix_volume_readback
      (h : InfoGeometry.Clifford.Cl11GeometricSynthesis.omega =
        InfoGeometry.Clifford.Cl11Matrix.J1) :
      EvidenceEdge .realMatrixRepresentation .volumeForm
  | volume_peirce
      (hSq : InfoGeometry.Clifford.Cl11GeometricSynthesis.omega *
        InfoGeometry.Clifford.Cl11GeometricSynthesis.omega = 1)
      (hPlus : InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus *
        InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus =
        InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus)
      (hMinus : InfoGeometry.Clifford.Cl11GeometricSynthesis.P_minus *
        InfoGeometry.Clifford.Cl11GeometricSynthesis.P_minus =
        InfoGeometry.Clifford.Cl11GeometricSynthesis.P_minus)
      (hOrth : InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus *
        InfoGeometry.Clifford.Cl11GeometricSynthesis.P_minus = 0)
      (hUnit : InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus +
        InfoGeometry.Clifford.Cl11GeometricSynthesis.P_minus =
          InfoGeometry.Clifford.Cl11GeometricSynthesis.one) :
      EvidenceEdge .volumeForm .volumePeirceProjectors
  | krein_null_hop_closure
      (h : InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullPlus *
          InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullPlus = 0 ∧
        InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullMinus *
          InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullMinus = 0 ∧
        InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullPlus *
          InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullMinus =
            InfoGeometry.Clifford.SplitQ11CausalCone.matrixKreinPlusProjector ∧
        InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullMinus *
          InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullPlus =
            InfoGeometry.Clifford.SplitQ11CausalCone.matrixKreinMinusProjector) :
      EvidenceEdge .diagonalKreinProjectors .kreinNullHops
  | split_cell_car
      (h : ∀ {R : Type*} [Ring R]
        (C : InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell R),
        InfoGeometry.SuperGrassmannian.MajoranaCAR.a C *
            InfoGeometry.SuperGrassmannian.MajoranaCAR.a_star C +
          InfoGeometry.SuperGrassmannian.MajoranaCAR.a_star C *
            InfoGeometry.SuperGrassmannian.MajoranaCAR.a C = 1) :
      EvidenceEdge .abstractSplitCell .abstractCAR
  | planar_products
      (h : ∀ a b c d : ℝ,
        InfoGeometry.Clifford.Cl11GeometricSynthesis.elliptic_elem a b *
            InfoGeometry.Clifford.Cl11GeometricSynthesis.elliptic_elem c d =
          InfoGeometry.Clifford.Cl11GeometricSynthesis.elliptic_elem
            (a * c - b * d) (a * d + b * c) ∧
        InfoGeometry.Clifford.Cl11GeometricSynthesis.hyperbolic_elem a b *
            InfoGeometry.Clifford.Cl11GeometricSynthesis.hyperbolic_elem c d =
          InfoGeometry.Clifford.Cl11GeometricSynthesis.hyperbolic_elem
            (a * c + b * d) (a * d + b * c) ∧
        InfoGeometry.Clifford.Cl11GeometricSynthesis.parabolic_elem a b *
            InfoGeometry.Clifford.Cl11GeometricSynthesis.parabolic_elem c d =
          InfoGeometry.Clifford.Cl11GeometricSynthesis.parabolic_elem
            (a * c) (a * d + b * c)) :
      EvidenceEdge .planarMatrixSubspaces .planarMultiplicationLaws

theorem clifford_matrix_equiv_edge :
    EvidenceEdge .nativeCl11 .realMatrixRepresentation :=
  .clifford_matrix_equiv ⟨InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat⟩

theorem matrix_volume_readback_edge :
    EvidenceEdge .realMatrixRepresentation .volumeForm :=
  .matrix_volume_readback
    InfoGeometry.Clifford.Cl11CanonicalArchetypePoset.synthesis_omega_eq_native

theorem volume_peirce_edge :
    EvidenceEdge .volumeForm .volumePeirceProjectors := by
  refine .volume_peirce ?_ ?_ ?_ ?_ ?_
  · simpa [InfoGeometry.Clifford.Cl11GeometricSynthesis.one] using
      InfoGeometry.Clifford.Cl11GeometricSynthesis.omega_sq
  · exact InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus_sq
  · exact InfoGeometry.Clifford.Cl11GeometricSynthesis.P_minus_sq
  · exact InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus_mul_P_minus
  · exact InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus_add_P_minus

theorem krein_null_hop_closure_edge :
    EvidenceEdge .diagonalKreinProjectors .kreinNullHops := by
  refine .krein_null_hop_closure ?_
  exact ⟨InfoGeometry.Clifford.SplitQ11CausalCone.matrix_causal_null_closure_laws.1,
    InfoGeometry.Clifford.SplitQ11CausalCone.matrix_causal_null_closure_laws.2.1,
    InfoGeometry.Clifford.SplitQ11CausalCone.matrix_causal_null_closure_laws.2.2.1,
    InfoGeometry.Clifford.SplitQ11CausalCone.matrix_causal_null_closure_laws.2.2.2.1⟩

theorem split_cell_car_edge : EvidenceEdge .abstractSplitCell .abstractCAR :=
  .split_cell_car (by
    intro R _ C
    exact InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell.car_anticommutator C)

theorem planar_products_edge :
    EvidenceEdge .planarMatrixSubspaces .planarMultiplicationLaws := by
  refine .planar_products ?_
  intro a b c d
  exact ⟨InfoGeometry.Clifford.Cl11GeometricSynthesis.elliptic_mul a b c d,
    InfoGeometry.Clifford.Cl11GeometricSynthesis.hyperbolic_mul a b c d,
    InfoGeometry.Clifford.Cl11GeometricSynthesis.parabolic_mul a b c d⟩

/-- The graph's direct dependency relation. -/
def Direct : Archetype → Archetype → Prop := EvidenceEdge

/-- Reflexive-transitive closure of witnessed owner dependencies. -/
inductive Reach : Archetype → Archetype → Prop where
  | refl (a : Archetype) : Reach a a
  | edge {a b : Archetype} (h : EvidenceEdge a b) : Reach a b
  | trans {a b c : Archetype} (hab : Reach a b) (hbc : Reach b c) :
      Reach a c

/-- A dependency path with at least one actual owner edge. -/
inductive PositivePath : Archetype → Archetype → Prop where
  | edge {a b : Archetype} (h : EvidenceEdge a b) : PositivePath a b
  | tail {a b c : Archetype} (h : PositivePath a b) (r : Reach b c) :
      PositivePath a c

theorem edge_height_lt {a b : Archetype} (h : EvidenceEdge a b) :
    height a < height b := by
  cases h <;> simp [height]

theorem reach_height_le {a b : Archetype} (h : Reach a b) :
    height a ≤ height b := by
  induction h with
  | refl a => exact Nat.le_refl _
  | edge h => exact Nat.le_of_lt (edge_height_lt h)
  | trans _ _ ih₁ ih₂ => exact Nat.le_trans ih₁ ih₂

theorem positive_path_height_lt {a b : Archetype} (h : PositivePath a b) :
    height a < height b := by
  induction h with
  | edge h => exact edge_height_lt h
  | tail h r ih => exact Nat.lt_of_lt_of_le ih (reach_height_le r)

theorem positive_path_irreflexive {a : Archetype} (h : PositivePath a a) :
    False := Nat.lt_irrefl _ (positive_path_height_lt h)

theorem reach_refl (a : Archetype) : Reach a a := .refl a

theorem reach_trans {a b c : Archetype} (hab : Reach a b) (hbc : Reach b c) :
    Reach a c := .trans hab hbc

theorem height_injective : Function.Injective height := by
  intro a b h
  cases a <;> cases b <;> simp [height] at h <;> rfl

theorem reach_antisymm {a b : Archetype} (hab : Reach a b) (hba : Reach b a) :
    a = b :=
  height_injective (Nat.le_antisymm (reach_height_le hab) (reach_height_le hba))

instance : PartialOrder Archetype where
  le := Reach
  le_refl := reach_refl
  le_trans := fun _ _ _ hab hbc => reach_trans hab hbc
  le_antisymm := fun _ _ hab hba => reach_antisymm hab hba

theorem volume_and_krein_projectors_are_distinct :
    Archetype.volumePeirceProjectors ≠ Archetype.diagonalKreinProjectors := by
  decide

end InfoGeometry.Scratch.CanonicalNoncommutativeArchetypePosetV3
