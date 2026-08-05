import InfoGeometry.Canonical.CelikCantorPauliMatrixSpan
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs

/-!
# Universal complex rank-one Clifford map

This owner turns the Pauli relations into the universal map from the
two-generator complex Clifford algebra to `M₂(ℂ)`.  The map is shown to be
surjective using the existing Pauli algebra-generation theorem, and
injective by the four-dimensional quaternion/Clifford rank calculation.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikCantorCl2UniversalHom

open InfoGeometry.Canonical.CelikCantorClifford
open InfoGeometry.Canonical.CelikCantorPauliMatrixSpan

abbrev Vec2C := ℂ × ℂ
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

noncomputable def q2 : QuadraticForm ℂ Vec2C :=
  CliffordAlgebraQuaternion.Q (1 : ℂ) (1 : ℂ)

noncomputable def celikCl2QuaternionEquiv :
    CliffordAlgebra q2 ≃ₐ[ℂ]
      QuaternionAlgebra ℂ (1 : ℂ) 0 (1 : ℂ) :=
  CliffordAlgebraQuaternion.equiv

@[simp] theorem q2_apply (v : Vec2C) :
    q2 v = v.1 ^ 2 + v.2 ^ 2 := by
  rcases v with ⟨a, b⟩
  simp [q2, CliffordAlgebraQuaternion.Q]
  ring

noncomputable def celikCl2Generator : Vec2C →ₗ[ℂ] Mat2C where
  toFun v := v.1 • U + v.2 • V
  map_add' u v := by
    simp [add_smul, add_assoc, add_left_comm, add_comm]
  map_smul' a v := by
    simp [smul_add, smul_smul]

theorem celikCl2Generator_sq (v : Vec2C) :
    celikCl2Generator v * celikCl2Generator v =
      algebraMap ℂ Mat2C (q2 v) := by
  rcases v with ⟨a, b⟩
  dsimp [celikCl2Generator]
  rw [q2_apply]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [U_sq, V_sq, UV_anticomm]
  simp [Algebra.algebraMap_eq_smul_one]
  module

noncomputable def celikCl2AlgebraHom :
    CliffordAlgebra q2 →ₐ[ℂ] Mat2C :=
  CliffordAlgebra.lift q2 ⟨celikCl2Generator,
    by intro v; simpa [Algebra.algebraMap_eq_smul_one] using
      celikCl2Generator_sq v⟩

@[simp] theorem celikCl2AlgebraHom_ι (v : Vec2C) :
    celikCl2AlgebraHom (CliffordAlgebra.ι q2 v) =
      celikCl2Generator v := by
  simp [celikCl2AlgebraHom]

@[simp] theorem celikCl2AlgebraHom_iota_first :
    celikCl2AlgebraHom (CliffordAlgebra.ι q2 (1, 0)) = U := by
  rw [celikCl2AlgebraHom_ι]
  simp [celikCl2Generator]

@[simp] theorem celikCl2AlgebraHom_iota_second :
    celikCl2AlgebraHom (CliffordAlgebra.ι q2 (0, 1)) = V := by
  rw [celikCl2AlgebraHom_ι]
  simp [celikCl2Generator]

theorem celikCl2AlgebraHom_surjective :
    Function.Surjective celikCl2AlgebraHom := by
  rw [← AlgHom.range_eq_top]
  apply top_unique
  intro A _
  have hU : U ∈ celikCl2AlgebraHom.range :=
    ⟨CliffordAlgebra.ι q2 (1, 0), celikCl2AlgebraHom_iota_first⟩
  have hV : V ∈ celikCl2AlgebraHom.range :=
    ⟨CliffordAlgebra.ι q2 (0, 1), celikCl2AlgebraHom_iota_second⟩
  have hgen : Algebra.adjoin ℂ ({U, V} : Set Mat2C) ≤
      celikCl2AlgebraHom.range := by
    refine Algebra.adjoin_le ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hU
    · exact hV
  have : A ∈ Algebra.adjoin ℂ ({U, V} : Set Mat2C) := by
    rw [algebra_adjoin_U_V_eq_top]
    trivial
  exact hgen this

theorem finrank_celikCl2 :
    Module.finrank ℂ (CliffordAlgebra q2) = 4 := by
  rw [LinearEquiv.finrank_eq celikCl2QuaternionEquiv.toLinearEquiv]
  exact QuaternionAlgebra.finrank_eq_four _ _ _

theorem finrank_mat2_complex :
    Module.finrank ℂ Mat2C = 4 := by
  simp [Mat2C, Module.finrank_matrix, Module.finrank_self]

theorem celikCl2AlgebraHom_injective :
    Function.Injective celikCl2AlgebraHom := by
  have hrank : Module.finrank ℂ (CliffordAlgebra q2) =
      Module.finrank ℂ Mat2C := by
    rw [finrank_celikCl2, finrank_mat2_complex]
  have hsurj : Function.Surjective celikCl2AlgebraHom.toLinearMap :=
    celikCl2AlgebraHom_surjective
  letI : FiniteDimensional ℂ (CliffordAlgebra q2) :=
    LinearEquiv.finiteDimensional celikCl2QuaternionEquiv.toLinearEquiv.symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mpr hsurj

noncomputable def celikCl2AlgebraEquiv :
    CliffordAlgebra q2 ≃ₐ[ℂ] Mat2C :=
  AlgEquiv.ofBijective celikCl2AlgebraHom ⟨
    celikCl2AlgebraHom_injective, celikCl2AlgebraHom_surjective⟩

@[simp] theorem celikCl2AlgebraEquiv_iota_first :
    celikCl2AlgebraEquiv (CliffordAlgebra.ι q2 (1, 0)) = U := by
  exact celikCl2AlgebraHom_iota_first

@[simp] theorem celikCl2AlgebraEquiv_iota_second :
    celikCl2AlgebraEquiv (CliffordAlgebra.ι q2 (0, 1)) = V := by
  exact celikCl2AlgebraHom_iota_second

@[simp] theorem celikCl2AlgebraEquiv_iota_mul :
    celikCl2AlgebraEquiv
      (CliffordAlgebra.ι q2 (1, 0) *
        CliffordAlgebra.ι q2 (0, 1)) = U * V := by
  simp

@[simp] theorem celikCl2AlgebraEquiv_symm_U :
    celikCl2AlgebraEquiv.symm U = CliffordAlgebra.ι q2 (1, 0) := by
  apply celikCl2AlgebraEquiv.injective
  simp

@[simp] theorem celikCl2AlgebraEquiv_symm_V :
    celikCl2AlgebraEquiv.symm V = CliffordAlgebra.ι q2 (0, 1) := by
  apply celikCl2AlgebraEquiv.injective
  simp

end InfoGeometry.Canonical.CelikCantorCl2UniversalHom
