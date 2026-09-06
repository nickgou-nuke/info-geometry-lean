import Mathlib
import proofs.MajoranaBraidGroup

/-!
# Exceptional Braid Topology

Formalizes the topological argument from J. Lukas K. König's thesis 
demonstrating why the Nielsen-Ninomiya fermion doubling theorem fails 
for non-Hermitian Exceptional Points.
-/

namespace ExceptionalBraid

variable {B : Type*} [Group B]

/-- 
The fundamental domain of the Brillouin Torus T². 
The total topological charge of all EPs enclosed by the torus
must equal the commutator of the enclosing paths B_x and B_y.
-/
def torus_total_charge (Bx By : B) : B :=
  Bx * By * Bx⁻¹ * By⁻¹

/-- 
In Hermitian systems, the topological invariant (Chern number) is Abelian. 
Thus, the commutator is trivial (the identity), forcing the total charge 
to be zero (Fermion Doubling).
-/
theorem hermitian_doubling (Bx By : B) (h_comm : Commute Bx By) : 
    torus_total_charge Bx By = 1 := by
  dsimp [torus_total_charge]
  have h_eq : Bx * By = By * Bx := h_comm.eq
  calc
    Bx * By * Bx⁻¹ * By⁻¹ = By * Bx * Bx⁻¹ * By⁻¹ := by rw [h_eq]
    _ = 1 := by group

/--
In non-Hermitian systems, the Braid Group is non-Abelian.
The total charge is NOT forced to be 1, allowing for unpaired 
Exceptional Points!
-/
theorem non_hermitian_unpaired (Bx By : B) (h_noncomm : ¬ Commute Bx By) :
    torus_total_charge Bx By ≠ 1 := by
  dsimp [torus_total_charge]
  intro h_eq
  have h_comm : Bx * By = By * Bx := by
    calc
      Bx * By = (Bx * By * Bx⁻¹ * By⁻¹) * (By * Bx) := by group
      _ = 1 * (By * Bx) := by rw [h_eq]
      _ = By * Bx := by group
  apply h_noncomm
  simpa using h_comm

/-- Concrete finite noncommuting adjacent Majorana braid pair. -/
theorem majorana_braid_noncommuting :
    InfoGeometry.GrandUnification.MajoranaBraidGroup.braid12 *
        InfoGeometry.GrandUnification.MajoranaBraidGroup.braid23 ≠
      InfoGeometry.GrandUnification.MajoranaBraidGroup.braid23 *
        InfoGeometry.GrandUnification.MajoranaBraidGroup.braid12 := by
  intro h
  have h_entry := congrArg
    (fun M : InfoGeometry.GrandUnification.MajoranaBraidGroup.M8Z => M 0 2) h
  simp only [InfoGeometry.GrandUnification.MajoranaBraidGroup.braid12,
    InfoGeometry.GrandUnification.MajoranaBraidGroup.braid23, Matrix.mul_apply] at h_entry
  norm_num [Fin.sum_univ_succ] at h_entry
  simp at h_entry

/-- Concrete finite adjacent Artin relation for the same Majorana braid pair. -/
theorem majorana_braid_artin :
    InfoGeometry.GrandUnification.MajoranaBraidGroup.braid12 *
        InfoGeometry.GrandUnification.MajoranaBraidGroup.braid23 *
        InfoGeometry.GrandUnification.MajoranaBraidGroup.braid12 =
      InfoGeometry.GrandUnification.MajoranaBraidGroup.braid23 *
        InfoGeometry.GrandUnification.MajoranaBraidGroup.braid12 *
        InfoGeometry.GrandUnification.MajoranaBraidGroup.braid23 := by
  exact InfoGeometry.GrandUnification.MajoranaBraidGroup.majorana_adjacent_artin

end ExceptionalBraid
