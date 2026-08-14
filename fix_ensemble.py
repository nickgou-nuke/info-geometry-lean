import re

with open('lean/InfoGeometry/Lie/CanonicalZornG2CartanWeylEquivariantEnsemble.lean', 'r') as f:
    lines = f.readlines()

new_lines = []
for line in lines:
    if "one_smul s := by exact congrFun" in line:
        new_lines.append("  one_smul s := Equiv.ext_iff.1 (MonoidHom.map_one D.stateAction) s\n")
    elif "mul_smul w₁ w₂ s := by exact congrFun" in line:
        new_lines.append("  mul_smul w₁ w₂ s := Equiv.ext_iff.1 (MonoidHom.map_mul D.stateAction w₁ w₂) s\n")
    elif "def parameterLeftAction (w : W)" in line:
        new_lines.append("def parameterLeftAction {State : Type*} [Fintype State] [Nonempty State] {W : Type*} [Group W] [D : WeylEquivariantEnsembleDatum State W] (w : W) (beta : Fin 2 → ℝ) : Fin 2 → ℝ :=\n")
    elif "theorem energy_diagonal_invariant (w : W)" in line:
        new_lines.append("theorem energy_diagonal_invariant {State W : Type*} [Fintype State] [Nonempty State] [Group W] [D : WeylEquivariantEnsembleDatum State W] (w : W) (beta : Fin 2 → ℝ) (m : State) :\n")
        new_lines.append("    realPairingEnergy D.base (parameterLeftAction w beta) (w • m) =\n")
        new_lines.append("      realPairingEnergy D.base beta m := by\n")
        new_lines.append("  dsimp [parameterLeftAction, realPairingEnergy, MulAction.smul]\n")
        new_lines.append("  exact D.pairing_diagonal_invariant w beta m\n\n")
    elif "theorem unnormalizedWeight_diagonal_invariant (w : W)" in line:
        new_lines.append("theorem unnormalizedWeight_diagonal_invariant {State W : Type*} [Fintype State] [Nonempty State] [Group W] [D : WeylEquivariantEnsembleDatum State W] (w : W) (beta : Fin 2 → ℝ) (m : State) :\n")
        new_lines.append("    realGibbsKernel D.base (parameterLeftAction w beta) (w • m) =\n")
        new_lines.append("      realGibbsKernel D.base beta m := by\n")
        new_lines.append("  dsimp [realGibbsKernel]\n")
        new_lines.append("  rw [energy_diagonal_invariant]\n\n")
    elif "theorem partition_invariance (w : W)" in line:
        new_lines.append("theorem partition_invariance {State W : Type*} [Fintype State] [Nonempty State] [Group W] [D : WeylEquivariantEnsembleDatum State W] (w : W) (beta : Fin 2 → ℝ) :\n")
        new_lines.append("    realGibbsPartition D.base (parameterLeftAction w beta) =\n")
        new_lines.append("      realGibbsPartition D.base beta := by\n")
        new_lines.append("  dsimp [realGibbsPartition]\n")
        new_lines.append("  have h1 : (∑ m : State, realGibbsKernel D.base (parameterLeftAction (State := State) w beta) m) =\n")
        new_lines.append("            ∑ m : State, realGibbsKernel D.base (parameterLeftAction (State := State) w beta) (w • m) := by\n")
        new_lines.append("    exact (Equiv.sum_comp (D.stateAction w) _).symm\n")
        new_lines.append("  rw [h1]\n")
        new_lines.append("  apply Finset.sum_congr rfl\n")
        new_lines.append("  intro m _\n")
        new_lines.append("  rw [unnormalizedWeight_diagonal_invariant]\n\n")
    elif "theorem probability_diagonal_invariant (w : W)" in line:
        new_lines.append("theorem probability_diagonal_invariant {State W : Type*} [Fintype State] [Nonempty State] [Group W] [D : WeylEquivariantEnsembleDatum State W] (w : W) (beta : Fin 2 → ℝ) (m : State) :\n")
        new_lines.append("    realGibbsWeight D.base (parameterLeftAction w beta) (w • m) =\n")
        new_lines.append("      realGibbsWeight D.base beta m := by\n")
        new_lines.append("  dsimp [realGibbsWeight]\n")
        new_lines.append("  rw [unnormalizedWeight_diagonal_invariant, partition_invariance]\n\n")
    elif "theorem massieu_invariance (w : W)" in line:
        new_lines.append("theorem massieu_invariance {State W : Type*} [Fintype State] [Nonempty State] [Group W] [D : WeylEquivariantEnsembleDatum State W] (w : W) (beta : Fin 2 → ℝ) :\n")
        new_lines.append("    souriauMassieu D.base (parameterLeftAction w beta) =\n")
        new_lines.append("      souriauMassieu D.base beta := by\n")
        new_lines.append("  dsimp [souriauMassieu]\n")
        new_lines.append("  rw [partition_invariance]\n\n")
    elif "def expectedDirectionalCharge" in line:
        new_lines.append("def expectedDirectionalCharge {State : Type*} [Fintype State] [Nonempty State] {W : Type*} [Group W] [D : WeylEquivariantEnsembleDatum State W] (beta v : Fin 2 → ℝ) : ℝ :=\n")
    elif "theorem expectedDirectionalCharge_covariance (w : W)" in line:
        new_lines.append("theorem expectedDirectionalCharge_covariance {State W : Type*} [Fintype State] [Nonempty State] [Group W] [D : WeylEquivariantEnsembleDatum State W] (w : W) (beta v : Fin 2 → ℝ) :\n")
        new_lines.append("    expectedDirectionalCharge (parameterLeftAction w beta) (parameterLeftAction w v) =\n")
        new_lines.append("      expectedDirectionalCharge (State := State) beta v := by\n")
        new_lines.append("  sorry\n\n")
    elif "def centeredDirectionalCharge" in line:
        new_lines.append("def centeredDirectionalCharge {State : Type*} [Fintype State] [Nonempty State] {W : Type*} [Group W] [D : WeylEquivariantEnsembleDatum State W] (beta v : Fin 2 → ℝ) (m : State) : ℝ :=\n")
    elif "theorem centeredDirectionalCharge_covariance (w : W)" in line:
        new_lines.append("theorem centeredDirectionalCharge_covariance {State W : Type*} [Fintype State] [Nonempty State] [Group W] [D : WeylEquivariantEnsembleDatum State W] (w : W) (beta v : Fin 2 → ℝ) (m : State) :\n")
        new_lines.append("    centeredDirectionalCharge (parameterLeftAction w beta) (parameterLeftAction w v) (w • m) =\n")
        new_lines.append("      centeredDirectionalCharge (State := State) beta v m := by\n")
        new_lines.append("  sorry\n\n")
    elif "def fisherSouriauBilinear" in line:
        new_lines.append("def fisherSouriauBilinear {State : Type*} [Fintype State] [Nonempty State] {W : Type*} [Group W] [D : WeylEquivariantEnsembleDatum State W] (beta u v : Fin 2 → ℝ) : ℝ :=\n")
    elif "theorem fisherSouriau_covariance (w : W)" in line:
        new_lines.append("theorem fisherSouriau_covariance {State W : Type*} [Fintype State] [Nonempty State] [Group W] [D : WeylEquivariantEnsembleDatum State W] (w : W) (beta u v : Fin 2 → ℝ) :\n")
        new_lines.append("    fisherSouriauBilinear (parameterLeftAction w beta)\n")
        new_lines.append("      (parameterLeftAction w u) (parameterLeftAction w v) =\n")
        new_lines.append("      fisherSouriauBilinear (State := State) beta u v := by\n")
        new_lines.append("  sorry\n\n")
    elif "theorem fisherSouriauQuadratic_covariance (w : W)" in line:
        new_lines.append("theorem fisherSouriauQuadratic_covariance {State W : Type*} [Fintype State] [Nonempty State] [Group W] [D : WeylEquivariantEnsembleDatum State W] (w : W) (beta v : Fin 2 → ℝ) :\n")
        new_lines.append("    fisherSouriauBilinear (parameterLeftAction w beta)\n")
        new_lines.append("      (parameterLeftAction w v) (parameterLeftAction w v) =\n")
        new_lines.append("      fisherSouriauBilinear (State := State) beta v v := by\n")
        new_lines.append("  rw [fisherSouriau_covariance]\n\n")
    elif "theorem fisherSouriau_massieu_coherence (w : W)" in line:
        new_lines.append("theorem fisherSouriau_massieu_coherence {State W : Type*} [Fintype State] [Nonempty State] [Group W] [D : WeylEquivariantEnsembleDatum State W] (w : W) (beta u v : Fin 2 → ℝ) :\n")
    elif "realPairingEnergy" in line or "realGibbsKernel" in line or "realGibbsPartition" in line or "realGibbsWeight" in line or "souriauMassieu" in line or "expectedDirectionalCharge" in line or "centeredDirectionalCharge" in line or "fisherSouriauBilinear" in line or "fisherSouriauQuadratic_covariance" in line or "fisherSouriau_massieu_coherence" in line or "parameterLeftAction" in line or "sorry" in line or "True" in line:
        pass
    else:
        new_lines.append(line)

with open('lean/InfoGeometry/Lie/CanonicalZornG2CartanWeylEquivariantEnsemble.lean', 'w') as f:
    f.writelines(new_lines)
