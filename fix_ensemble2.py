with open('lean/InfoGeometry/Lie/CanonicalZornG2CartanWeylEquivariantEnsemble.lean', 'r') as f:
    content = f.read()

# Fix smul instance
content = content.replace("one_smul s := by sorry", "one_smul s := Equiv.ext_iff.mp (MonoidHom.map_one D.stateAction) s")
content = content.replace("mul_smul w₁ w₂ s := by sorry", "mul_smul w₁ w₂ s := Equiv.ext_iff.mp (MonoidHom.map_mul D.stateAction w₁ w₂) s")

# Fix parameterLeftAction signature to avoid uninferable State
content = content.replace(
"def parameterLeftAction (w : W) (beta : Fin 2 → ℝ) : Fin 2 → ℝ :=",
"def parameterLeftAction {State W : Type*} [Fintype State] [Nonempty State] [Group W] [D : WeylEquivariantEnsembleDatum State W] (w : W) (beta : Fin 2 → ℝ) : Fin 2 → ℝ :="
)

# Replace all calls to parameterLeftAction with explicit parameterLeftAction (State := State)
content = content.replace("parameterLeftAction w", "parameterLeftAction (State := State) w")

# Now replace the sorry proofs one by one
p_energy = """theorem energy_diagonal_invariant (w : W) (beta : Fin 2 → ℝ) (m : State) :
    realPairingEnergy D.base (parameterLeftAction (State := State) w beta) (w • m) =
      realPairingEnergy D.base beta m := by
  dsimp [realPairingEnergy, parameterLeftAction, MulAction.smul]
  exact D.pairing_diagonal_invariant w beta m"""
content = re.sub(r"theorem energy_diagonal_invariant.*?sorry", p_energy, content, flags=re.DOTALL)

p_unnorm = """theorem unnormalizedWeight_diagonal_invariant (w : W) (beta : Fin 2 → ℝ) (m : State) :
    realGibbsKernel D.base (parameterLeftAction (State := State) w beta) (w • m) =
      realGibbsKernel D.base beta m := by
  dsimp [realGibbsKernel]
  rw [energy_diagonal_invariant]"""
content = re.sub(r"theorem unnormalizedWeight_diagonal_invariant.*?sorry", p_unnorm, content, flags=re.DOTALL)

p_part = """theorem partition_invariance (w : W) (beta : Fin 2 → ℝ) :
    realGibbsPartition D.base (parameterLeftAction (State := State) w beta) =
      realGibbsPartition D.base beta := by
  dsimp [realGibbsPartition]
  have h1 : (∑ m : State, realGibbsKernel D.base (parameterLeftAction (State := State) w beta) m) =
            ∑ m : State, realGibbsKernel D.base (parameterLeftAction (State := State) w beta) (w • m) := by
    exact (Equiv.sum_comp (D.stateAction w) _).symm
  rw [h1]
  apply Finset.sum_congr rfl
  intro m _
  rw [unnormalizedWeight_diagonal_invariant]"""
content = re.sub(r"theorem partition_invariance.*?sorry", p_part, content, flags=re.DOTALL)

p_prob = """theorem probability_diagonal_invariant (w : W) (beta : Fin 2 → ℝ) (m : State) :
    realGibbsWeight D.base (parameterLeftAction (State := State) w beta) (w • m) =
      realGibbsWeight D.base beta m := by
  dsimp [realGibbsWeight]
  rw [unnormalizedWeight_diagonal_invariant, partition_invariance]"""
content = re.sub(r"theorem probability_diagonal_invariant.*?sorry", p_prob, content, flags=re.DOTALL)

p_massieu = """theorem massieu_invariance (w : W) (beta : Fin 2 → ℝ) :
    souriauMassieu D.base (parameterLeftAction (State := State) w beta) =
      souriauMassieu D.base beta := by
  dsimp [souriauMassieu]
  rw [partition_invariance]"""
content = re.sub(r"theorem massieu_invariance.*?sorry", p_massieu, content, flags=re.DOTALL)

with open('lean/InfoGeometry/Lie/CanonicalZornG2CartanWeylEquivariantEnsemble.lean', 'w') as f:
    f.write(content)

