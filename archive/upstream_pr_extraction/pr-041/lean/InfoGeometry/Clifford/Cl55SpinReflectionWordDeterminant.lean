import InfoGeometry.Clifford.Cl55WittReflectionWordDeterminant
import InfoGeometry.Clifford.Cl55WittSpinOrthogonalAction

/-!
# Conditional determinant readout for native `Spin55` reflection words

This owner transports the finite even-word determinant theorem to a native
`Spin55` action only when an explicit reflection-word equality is supplied.
It does not assert that every native spin element has such a presentation.
-/

namespace InfoGeometry.Clifford.Clifford55

noncomputable section

theorem spinActionOrthogonal_mem_specialOrthogonalGroup55_of_reflection_word
    (g : Spin55) (vs : List AnisotropicVector55)
    (hword :
      spinActionOrthogonal g = quadraticReflectionWord vs)
    (heven : Even vs.length) :
    spinActionOrthogonal g ∈ (specialOrthogonalGroup55 : Subgroup orthogonalGroup55) := by
  rw [hword]
  unfold specialOrthogonalGroup55
  exact quadraticReflectionWord_det_eq_one_of_even vs heven

theorem spinActionOrthogonal_det_eq_one_of_reflection_word
    (g : Spin55) (vs : List AnisotropicVector55)
    (hword :
      spinActionOrthogonal g = quadraticReflectionWord vs)
    (heven : Even vs.length) :
    (spinActionOrthogonal g).1.det = (1 : ℝˣ) := by
  have h := quadraticReflectionWord_det_eq_one_of_even vs heven
  simpa [hword] using h

end

end InfoGeometry.Clifford.Clifford55
