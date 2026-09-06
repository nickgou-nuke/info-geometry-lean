import InfoGeometry.Algebra.Zorn.G2ResidualCoordinateReadback
import InfoGeometry.Algebra.Zorn.G2FlagWordCertificate

namespace InfoGeometry.Algebra.Zorn.G2ResidualCoordinateCellOne

open InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate

@[simp] theorem residualWord_cell_one_24_at_zero :
    residualWord 1 24 0 = false := by
  rfl

@[simp] theorem residualWord_cell_one_45_at_one :
    residualWord 1 45 1 = true := by
  decide

@[simp] theorem residualWord_cell_one_73_at_two :
    residualWord 1 73 2 = true := by
  decide

@[simp] theorem residualWord_cell_one_178_at_three :
    residualWord 1 178 3 = true := by
  decide

@[simp] theorem residualWord_cell_one_45_at_three :
    residualWord 1 45 3 = false := by
  decide

@[simp] theorem residualWord_cell_one_73_at_one :
    residualWord 1 73 1 = false := by
  decide

@[simp] theorem residualWord_cell_one_178_at_one :
    residualWord 1 178 1 = true := by
  decide

@[simp] theorem residualWord_cell_one_24_at_one :
    residualWord 1 24 1 = false := by
  rfl

theorem residualWord_cell_one_24_ne_45 :
    residualWord 1 24 ≠ residualWord 1 45 := by decide

theorem residualWord_cell_one_24_ne_73 :
    residualWord 1 24 ≠ residualWord 1 73 := by decide

theorem residualWord_cell_one_24_ne_178 :
    residualWord 1 24 ≠ residualWord 1 178 := by decide

theorem residualWord_cell_one_45_ne_73 :
    residualWord 1 45 ≠ residualWord 1 73 := by decide

theorem residualWord_cell_one_45_ne_178 :
    residualWord 1 45 ≠ residualWord 1 178 := by decide

theorem residualWord_cell_one_73_ne_178 :
    residualWord 1 73 ≠ residualWord 1 178 := by decide

/- The native residual-word coordinates separate the four certified indices
   in the first nontrivial orbit cell.  Each off-diagonal leaf is a closed
   computation of the supplied native PC word, while the assembly only
   eliminates the already-known cell membership. -/
set_option maxRecDepth 100000 in
theorem residualWord_injective_on_cell_one :
    ∀ i j : Fin 189,
      i ∈ orbitCells 1 → j ∈ orbitCells 1 →
      residualWord 1 i = residualWord 1 j → i = j := by
  intro i j hi hj h
  simp [orbitCells, flagCells] at hi hj
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | exact False.elim (residualWord_cell_one_24_ne_45 h)
    | exact False.elim (residualWord_cell_one_24_ne_73 h)
    | exact False.elim (residualWord_cell_one_24_ne_178 h)
    | exact False.elim (residualWord_cell_one_45_ne_73 h)
    | exact False.elim (residualWord_cell_one_45_ne_178 h)
    | exact False.elim (residualWord_cell_one_73_ne_178 h)
    | exact False.elim (residualWord_cell_one_24_ne_45 h.symm)
    | exact False.elim (residualWord_cell_one_24_ne_73 h.symm)
    | exact False.elim (residualWord_cell_one_24_ne_178 h.symm)
    | exact False.elim (residualWord_cell_one_45_ne_73 h.symm)
    | exact False.elim (residualWord_cell_one_45_ne_178 h.symm)
    | exact False.elim (residualWord_cell_one_73_ne_178 h.symm)

theorem residualWord_cell_one_coordinate_separation :
    ∀ i j : Fin 189,
      i ∈ orbitCells 1 → j ∈ orbitCells 1 → i ≠ j →
      ∃ a : Fin 6, residualWord 1 i a ≠ residualWord 1 j a := by
  intro i j hi hj hne
  by_contra hno
  apply hne
  apply residualWord_injective_on_cell_one i j hi hj
  funext a
  by_contra ha
  exact hno ⟨a, ha⟩

end InfoGeometry.Algebra.Zorn.G2ResidualCoordinateCellOne
