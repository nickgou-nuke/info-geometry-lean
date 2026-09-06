import InfoGeometry.Clifford.Cl55FockChannelLinearMap

noncomputable section

namespace InfoGeometry.Clifford.SplitClifford55FockChannelNeutralEmbedding

open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.SplitClifford55ZornCARComparison
open InfoGeometry.Clifford.SplitClifford55FockChannelLinearMap

abbrev V5 := InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.V5
abbrev NeutralSpace :=
  InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.NeutralSpace

noncomputable def channelVectorMap :
    (Fin 3 → ℝ) →ₗ[ℝ] V5 :=
  LinearMap.lsum ℝ (fun _ : Fin 3 => ℝ) ℝ
    (fun i =>
      (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight
        (basisVector (firstThreeIndex i)))

noncomputable def channelCovectorMap :
    (Fin 3 → ℝ) →ₗ[ℝ] Module.Dual ℝ V5 :=
  LinearMap.lsum ℝ (fun _ : Fin 3 => ℝ) ℝ
    (fun i =>
      (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight
        (dualBasisVector (firstThreeIndex i)))

noncomputable def channelToNeutral :
    FockChannel →ₗ[ℝ] NeutralSpace :=
  channelVectorMap.prodMap channelCovectorMap

@[simp] theorem channelVectorMap_apply (w : Fin 3 → ℝ) :
    channelVectorMap w =
      ∑ i : Fin 3, w i • basisVector (firstThreeIndex i) := by
  simp [channelVectorMap, LinearMap.lsum_apply]

@[simp] theorem channelCovectorMap_apply (w : Fin 3 → ℝ) :
    channelCovectorMap w =
      ∑ i : Fin 3, w i • dualBasisVector (firstThreeIndex i) := by
  simp [channelCovectorMap, LinearMap.lsum_apply]

theorem channelVectorMap_injective :
    Function.Injective channelVectorMap := by
  intro w z h
  funext j
  have hj := congrArg
    (fun v : V5 => dualBasisVector (firstThreeIndex j) v) h
  rw [channelVectorMap_apply, channelVectorMap_apply] at hj
  have hw :
      dualBasisVector (firstThreeIndex j)
          (∑ i : Fin 3, w i • basisVector (firstThreeIndex i)) = w j := by
    rw [map_sum]
    simp only [map_smul, dualBasisVector_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      have hne : firstThreeIndex j ≠ firstThreeIndex b := by
        intro heq
        exact hbj (firstThreeIndex_injective heq).symm
      simp [hne]
    · simp
  have hz :
      dualBasisVector (firstThreeIndex j)
          (∑ i : Fin 3, z i • basisVector (firstThreeIndex i)) = z j := by
    rw [map_sum]
    simp only [map_smul, dualBasisVector_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      have hne : firstThreeIndex j ≠ firstThreeIndex b := by
        intro heq
        exact hbj (firstThreeIndex_injective heq).symm
      simp [hne]
    · simp
  simpa [hw, hz] using hj

theorem channelCovectorMap_injective :
    Function.Injective channelCovectorMap := by
  intro w z h
  funext j
  have hj := congrArg
    (fun φ : Module.Dual ℝ V5 =>
      φ (basisVector (firstThreeIndex j))) h
  rw [channelCovectorMap_apply, channelCovectorMap_apply] at hj
  have hw :
      (∑ i : Fin 3, w i • dualBasisVector (firstThreeIndex i))
          (basisVector (firstThreeIndex j)) = w j := by
    change (∑ i : Fin 3,
      w i • dualBasisVector (firstThreeIndex i) (basisVector (firstThreeIndex j))) = w j
    simp only [dualBasisVector_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      have hne : firstThreeIndex b ≠ firstThreeIndex j := by
        intro heq
        exact hbj (firstThreeIndex_injective heq)
      simp [hne]
    · simp
  have hz :
      (∑ i : Fin 3, z i • dualBasisVector (firstThreeIndex i))
          (basisVector (firstThreeIndex j)) = z j := by
    change (∑ i : Fin 3,
      z i • dualBasisVector (firstThreeIndex i) (basisVector (firstThreeIndex j))) = z j
    simp only [dualBasisVector_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      have hne : firstThreeIndex b ≠ firstThreeIndex j := by
        intro heq
        exact hbj (firstThreeIndex_injective heq)
      simp [hne]
    · simp
  simpa [hw, hz] using hj

@[simp] theorem channelToNeutral_apply (w : FockChannel) :
    channelToNeutral w =
      (∑ i : Fin 3, w.1 i • basisVector (firstThreeIndex i),
        ∑ i : Fin 3, w.2 i • dualBasisVector (firstThreeIndex i)) := by
  simp [channelToNeutral, channelVectorMap_apply, channelCovectorMap_apply]

theorem channelToNeutral_neutralForm (w : FockChannel) :
    InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
        (channelToNeutral w) =
      ∑ i : Fin 3, w.2 i * w.1 i := by
  rw [InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled_apply,
    channelToNeutral_apply]
  change (∑ i : Fin 3, w.2 i • dualBasisVector (firstThreeIndex i))
      (∑ j : Fin 3, w.1 j • basisVector (firstThreeIndex j)) = _
  simp only [map_sum, map_smul]
  have hEval (j : Fin 3) :
      (∑ i : Fin 3, w.2 i • dualBasisVector (firstThreeIndex i))
          (basisVector (firstThreeIndex j)) = w.2 j := by
    change (∑ i : Fin 3,
      w.2 i * dualBasisVector (firstThreeIndex i)
        (basisVector (firstThreeIndex j))) = w.2 j
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij
      have hne : firstThreeIndex i ≠ firstThreeIndex j := by
        intro heq
        exact hij (firstThreeIndex_injective heq)
      simp [hne]
    · simp
  calc
    (∑ j : Fin 3, w.1 j •
        (∑ i : Fin 3, w.2 i • dualBasisVector (firstThreeIndex i))
          (basisVector (firstThreeIndex j))) =
        ∑ j : Fin 3, w.1 j • w.2 j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hEval j]
    _ = ∑ i : Fin 3, w.2 i * w.1 i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [smul_eq_mul, mul_comm]

theorem channelToNeutral_neutralPairing (w z : FockChannel) :
    neutralPairing (channelToNeutral w) (channelToNeutral z) =
      (1 / 2 : ℝ) * ∑ i : Fin 3,
        (w.2 i * z.1 i + z.2 i * w.1 i) := by
  rw [channelToNeutral_apply, channelToNeutral_apply]
  simp only [neutralPairing]
  have hEval (a b : Fin 3 → ℝ) :
      (∑ i : Fin 3, a i • dualBasisVector (firstThreeIndex i))
          (∑ j : Fin 3, b j • basisVector (firstThreeIndex j)) =
        ∑ i : Fin 3, a i * b i := by
    simp only [map_sum, map_smul, smul_eq_mul]
    have hBasis (j : Fin 3) :
        (∑ i : Fin 3, a i *
            dualBasisVector (firstThreeIndex i)
              (basisVector (firstThreeIndex j))) = a j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i hi hij
        have hne : firstThreeIndex i ≠ firstThreeIndex j := by
          intro heq
          exact hij (firstThreeIndex_injective heq)
        simp [hne]
      · simp
    calc
      ∑ j : Fin 3, b j *
          (∑ i : Fin 3, a i *
            dualBasisVector (firstThreeIndex i)
              (basisVector (firstThreeIndex j))) =
          ∑ j : Fin 3, b j * a j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hBasis j]
      _ = ∑ i : Fin 3, a i * b i := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [hEval w.2 z.1, hEval z.2 w.1]
  rw [Finset.sum_add_distrib]
  ring

theorem channelToNeutral_injective :
    Function.Injective channelToNeutral := by
  intro w z h
  apply Prod.ext
  · exact channelVectorMap_injective (congrArg Prod.fst h)
  · exact channelCovectorMap_injective (congrArg Prod.snd h)

theorem neutralActionMap_comp_channelToNeutral :
    neutralActionMap.comp channelToNeutral = fockChannelMap := by
  apply LinearMap.ext
  intro w
  rw [fockChannelMap_apply]
  change
    wedge (∑ i : Fin 3, w.1 i • basisVector (firstThreeIndex i)) +
        contract (∑ i : Fin 3, w.2 i • dualBasisVector (firstThreeIndex i)) =
      (∑ i : Fin 3, w.1 i • fockCreation i) +
        ∑ i : Fin 3, w.2 i • fockAnnihilation i
  simp only [wedge, contract, map_sum, map_smul]
  rfl

theorem neutralActionMap_injective :
    Function.Injective neutralActionMap := by
  intro w z h
  rcases w with ⟨v, φ⟩
  rcases z with ⟨u, ψ⟩
  have hv := congrArg
    (fun T : SplitClifford55ExteriorSpinor.SpinorEnd =>
      T (1 : SplitClifford55ExteriorSpinor.Spinor)) h
  change neutralAction (v, φ) (1 : SplitClifford55ExteriorSpinor.Spinor) =
    neutralAction (u, ψ) (1 : SplitClifford55ExteriorSpinor.Spinor) at hv
  have hv' : ExteriorAlgebra.ι ℝ v = ExteriorAlgebra.ι ℝ u := by
    simpa [neutralAction, wedge, contract] using hv
  have hvu : v = u := by
    have hsub : v - u = (0 : V5) := by
      apply (ExteriorAlgebra.ι_eq_zero_iff (R := ℝ) (v - u)).mp
      rw [map_sub]
      exact sub_eq_zero.mpr hv'
    exact sub_eq_zero.mp hsub
  subst u
  have hφψ : φ = ψ := by
    apply LinearMap.ext (R := ℝ)
    intro x
    have hx := congrArg
      (fun T : SplitClifford55ExteriorSpinor.SpinorEnd =>
        T (ExteriorAlgebra.ι ℝ x)) h
    change (wedge v + contract φ) (ExteriorAlgebra.ι ℝ x) =
      (wedge v + contract ψ) (ExteriorAlgebra.ι ℝ x) at hx
    rw [LinearMap.add_apply, LinearMap.add_apply] at hx
    have hφx : contract φ (ExteriorAlgebra.ι ℝ x) =
        φ x • (1 : Spinor) := by
      change CliffordAlgebra.contractLeft
          (Q := (0 : QuadraticForm ℝ V5)) φ
          (ExteriorAlgebra.ι ℝ x) = φ x • (1 : Spinor)
      simpa using
        (CliffordAlgebra.contractLeft_ι_mul
          (Q := (0 : QuadraticForm ℝ V5)) φ x (1 : Spinor))
    have hψx : contract ψ (ExteriorAlgebra.ι ℝ x) =
        ψ x • (1 : Spinor) := by
      change CliffordAlgebra.contractLeft
          (Q := (0 : QuadraticForm ℝ V5)) ψ
          (ExteriorAlgebra.ι ℝ x) = ψ x • (1 : Spinor)
      simpa using
        (CliffordAlgebra.contractLeft_ι_mul
          (Q := (0 : QuadraticForm ℝ V5)) ψ x (1 : Spinor))
    rw [hφx, hψx] at hx
    simpa using add_left_cancel hx
  exact congrArg (fun q => (v, q)) hφψ

theorem fockChannelMap_injective :
    Function.Injective fockChannelMap := by
  rw [← neutralActionMap_comp_channelToNeutral]
  exact neutralActionMap_injective.comp channelToNeutral_injective

end InfoGeometry.Clifford.SplitClifford55FockChannelNeutralEmbedding
