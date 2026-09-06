import InfoGeometry.Clifford.Cl55ZornCARComparison

noncomputable section

namespace InfoGeometry.Clifford.SplitClifford55FockChannelLinearMap

open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.SplitClifford55ZornCARComparison

abbrev FockChannel := (Fin 3 → ℝ) × (Fin 3 → ℝ)
abbrev FockSpinorEnd :=
  InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.SpinorEnd

/-- The six-channel Fock realization of the circular creation/annihilation
coefficients.  This is a linear operator-valued map, not an associative
algebra representation of the Zorn carrier. -/
noncomputable def fockChannelMap : FockChannel →ₗ[ℝ] FockSpinorEnd where
  toFun w :=
    (∑ i : Fin 3, w.1 i • fockCreation i) +
      ∑ i : Fin 3, w.2 i • fockAnnihilation i
  map_add' w z := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul,
      Finset.sum_add_distrib]
    module
  map_smul' c w := by
    change
      (∑ i : Fin 3, (c * w.1 i) • fockCreation i) +
          ∑ i : Fin 3, (c * w.2 i) • fockAnnihilation i =
        c • ((∑ i : Fin 3, w.1 i • fockCreation i) +
          ∑ i : Fin 3, w.2 i • fockAnnihilation i)
    simp_rw [mul_smul]
    rw [smul_add, ← Finset.smul_sum, ← Finset.smul_sum]

@[simp] theorem fockChannelMap_apply (w : FockChannel) :
    fockChannelMap w =
      (∑ i : Fin 3, w.1 i • fockCreation i) +
        ∑ i : Fin 3, w.2 i • fockAnnihilation i :=
  rfl

@[simp] theorem fockChannelMap_basis_plus (i : Fin 3) :
    fockChannelMap (Pi.single i 1, 0) = fockCreation i := by
  simp [fockChannelMap, Finset.sum_eq_single i]

@[simp] theorem fockChannelMap_basis_minus (i : Fin 3) :
    fockChannelMap (0, Pi.single i 1) = fockAnnihilation i := by
  simp [fockChannelMap, Finset.sum_eq_single i]

end InfoGeometry.Clifford.SplitClifford55FockChannelLinearMap
