import InfoGeometry.Clifford.KoszulFoundation
import InfoGeometry.Clifford.Cl55WittOrthogonalBasis

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Clifford.KoszulFoundation

noncomputable section

/-! A native Clifford volume element for the ordered orthogonal `Q55` basis. -/

def cl55WittBasisFin : Fin 10 → V55 :=
  ![wittBasis (Sum.inl 0), wittBasis (Sum.inl 1),
    wittBasis (Sum.inl 2), wittBasis (Sum.inl 3),
    wittBasis (Sum.inl 4), wittBasis (Sum.inr 0),
    wittBasis (Sum.inr 1), wittBasis (Sum.inr 2),
    wittBasis (Sum.inr 3), wittBasis (Sum.inr 4)]

def cl55WittVolumeList : List V55 := List.ofFn cl55WittBasisFin

noncomputable def cl55WittVolume : Cl55 :=
  cliffordVolumeElement Q55 cl55WittVolumeList

theorem cl55WittVolume_involute :
    CliffordAlgebra.involute (Q := Q55) cl55WittVolume = cl55WittVolume := by
  rw [cl55WittVolume, clifford_involute_volumeElement]
  norm_num [cl55WittVolumeList]

theorem cl55WittVolume_isUnit : IsUnit cl55WittVolume := by
  rw [cl55WittVolume, cl55WittVolumeList]
  apply List.prod_isUnit
  intro v hv
  rcases List.mem_map.mp hv with ⟨u, hu, rfl⟩
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
  apply CliffordAlgebra.isUnit_ι_of_isUnit
  apply isUnit_iff_ne_zero.mpr
  fin_cases i <;>
    norm_num [cl55WittBasisFin, wittBasis, Q55_apply, e_pos, f_neg,
      Fin.sum_univ_succ]

noncomputable def cl55WittVolumeUnit : Cl55ˣ := cl55WittVolume_isUnit.unit

@[simp] theorem cl55WittVolumeUnit_coe :
    (cl55WittVolumeUnit : Cl55) = cl55WittVolume :=
  cl55WittVolume_isUnit.unit_spec

end

end InfoGeometry.Clifford.Clifford55
