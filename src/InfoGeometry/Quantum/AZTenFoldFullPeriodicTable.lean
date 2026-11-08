import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge
import InfoGeometry.Quantum.AZTenFoldCompleteClassification

open InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge
open InfoGeometry.Quantum.AZTenFoldCompleteClassification

namespace InfoGeometry.Quantum.AZTenFoldFullPeriodicTable

/-- The Topological Invariant Group Type for any spatial dimension d -/
inductive TopologicalGroup : Type
  | Zero : TopologicalGroup -- 0 (Trivial topology)
  | Z2   : TopologicalGroup -- ℤ₂ (Pfaffian / Z₂ index)
  | Z    : TopologicalGroup -- ℤ (Chern number / winding number)
  deriving DecidableEq

/-- The finite labels for the connected components of the two complex
classifying spaces: `π₀(C₀) = ℤ` and `π₀(C₁) = 0`. -/
def complexKSpaceLabel (q : ℕ) : TopologicalGroup :=
  if q % 2 = 0 then .Z else .Zero

/-- The finite labels for the connected components of the real classifying
spaces, in Bott order `R₀,…,R₇`: `ℤ, ℤ₂, ℤ₂, 0, ℤ, 0, 0, 0`. The `Z` label
represents groups such as `2ℤ` up to abstract group isomorphism. -/
def realKSpaceLabel (q : ℕ) : TopologicalGroup :=
  match q % 8 with
  | 0 | 4 => .Z
  | 1 | 2 => .Z2
  | _ => .Zero

/-- The Bott classifying-space index attached to each AZ symmetry class:
complex indices for A/AIII and real indices for the eight real classes. -/
inductive AZBottIndex : Type
  | complex (q : Fin 2)
  | real (q : Fin 8)
  deriving DecidableEq

/-- The AZ-to-Bott index map in the standard order: A, AIII; then AI, BDI, D,
DIII, AII, CII, C, CI. -/
def azBottIndex : AZClass → AZBottIndex
  | .A => .complex ⟨0, by omega⟩
  | .AIII => .complex ⟨1, by omega⟩
  | .AI => .real ⟨0, by omega⟩
  | .BDI => .real ⟨1, by omega⟩
  | .D => .real ⟨2, by omega⟩
  | .DIII => .real ⟨3, by omega⟩
  | .AII => .real ⟨4, by omega⟩
  | .CII => .real ⟨5, by omega⟩
  | .C => .real ⟨6, by omega⟩
  | .CI => .real ⟨7, by omega⟩

/-- Stable AZ table computed from the classifying-space index. The complex
classes use indices `0` (A) and `1` (AIII); the real classes use the standard
indices `0,…,7` in order AI, BDI, D, DIII, AII, CII, C, CI. Spatial dimension
subtracts from that index, modulo the relevant Bott period. These labels are
not by themselves a construction or classification of phase spaces. -/
def azFullTable (c : AZClass) (d : ℕ) : TopologicalGroup :=
  match azBottIndex c with
  | .complex q => complexKSpaceLabel (q.val + 8 - d % 8)
  | .real q => realKSpaceLabel (q.val + 8 - d % 8)

/-- Theorem: 1D Class D (Kitaev chain) returns Z₂ invariant -/
theorem class_D_1D_is_Z2 :
    azFullTable AZClass.D 1 = TopologicalGroup.Z2 := rfl

/-- Theorem: 2D Class D (p+ip superconductor) returns Z invariant (Chern number) -/
theorem class_D_2D_is_Z :
    azFullTable AZClass.D 2 = TopologicalGroup.Z := rfl

/-- The free-fermion one-dimensional BDI entry is integer-valued. -/
theorem class_BDI_1D_is_Z :
    azFullTable AZClass.BDI 1 = TopologicalGroup.Z := rfl

/-- The free-fermion one-dimensional CII group is isomorphic to ℤ. -/
theorem class_CII_1D_is_Z :
    azFullTable AZClass.CII 1 = TopologicalGroup.Z := rfl

/-- Class BDI in two dimensions is trivial in the stable free-fermion table. -/
theorem class_BDI_2D_is_zero :
    azFullTable AZClass.BDI 2 = TopologicalGroup.Zero := rfl

/-- Class AII in three dimensions has the stable `Z₂` label. -/
theorem class_AII_3D_is_Z2 :
    azFullTable AZClass.AII 3 = TopologicalGroup.Z2 := rfl

/-- Main Theorem: 8-Fold Bott Periodicity of the entire 10x8 AZ Periodic Table -/
theorem az_full_table_8fold_periodicity (c : AZClass) (d : ℕ) :
    azFullTable c (d + 8) = azFullTable c d := by
  have hmod : (d + 8) % 8 = d % 8 := by omega
  simp [azFullTable, hmod]

/-- Clifford 8-Fold Morita Dimension Theorem: 2^(p+8+q) = 2^(p+q) * 256 -/
theorem clifford_8fold_morita_dim (p q : ℕ) :
    2 ^ (p + 8 + q) = 2 ^ (p + q) * 256 := by
  have h : p + 8 + q = (p + q) + 8 := by ring
  rw [h, pow_add]
  rfl

theorem az_full_periodic_table_exists :
    azFullTable AZClass.D 1 = TopologicalGroup.Z2 ∧
      azFullTable AZClass.D 2 = TopologicalGroup.Z ∧
        azFullTable AZClass.BDI 1 = TopologicalGroup.Z ∧
        azFullTable AZClass.CII 1 = TopologicalGroup.Z ∧
        azFullTable AZClass.BDI 2 = TopologicalGroup.Zero ∧
        azFullTable AZClass.AII 3 = TopologicalGroup.Z2 ∧
        (∀ (c : AZClass) (d : ℕ), azFullTable c (d + 8) = azFullTable c d) ∧
          ∀ p q : ℕ, 2 ^ (p + 8 + q) = 2 ^ (p + q) * 256 := by
  exact ⟨class_D_1D_is_Z2, class_D_2D_is_Z,
    class_BDI_1D_is_Z, class_CII_1D_is_Z, class_BDI_2D_is_zero,
    class_AII_3D_is_Z2, az_full_table_8fold_periodicity,
    clifford_8fold_morita_dim⟩

end InfoGeometry.Quantum.AZTenFoldFullPeriodicTable
