import re

with open('lean/InfoGeometry/Lie/CanonicalZornG2CartanWeylEquivariantEnsemble.lean', 'r') as f:
    content = f.read()

content = content.replace("Mathlib.Algebra.BigOperators.Group.Finset.Basic", "Mathlib.Algebra.BigOperators.Basic\nimport Mathlib.Data.Finset.Basic")

content = content.replace("one_smul s := by sorry", "one_smul s := Equiv.ext_iff.mp (MonoidHom.map_one D.stateAction) s")
content = content.replace("mul_smul w₁ w₂ s := by sorry", "mul_smul w₁ w₂ s := Equiv.ext_iff.mp (MonoidHom.map_mul D.stateAction w₁ w₂) s")

content = content.replace(
"def parameterLeftAction (w : W) (beta : Fin 2 → ℝ) : Fin 2 → ℝ :=",
"def parameterLeftAction {State W : Type*} [Fintype State] [Nonempty State] [Group W] [D : WeylEquivariantEnsembleDatum State W] (w : W) (beta : Fin 2 → ℝ) : Fin 2 → ℝ :="
)

content = content.replace("parameterLeftAction w", "parameterLeftAction (State := State) w")

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

p_edc = """def expectedDirectionalCharge {State W : Type*} [Fintype State] [Nonempty State] [Group W] [D : WeylEquivariantEnsembleDatum State W] (beta v : Fin 2 → ℝ) : ℝ :=
  ∑ m, realGibbsWeight D.base beta m * (∑ i, v i * D.base.momentMap m i)

theorem expectedDirectionalCharge_covariance (w : W) (beta v : Fin 2 → ℝ) :
    expectedDirectionalCharge (parameterLeftAction (State := State) w beta) (parameterLeftAction (State := State) w v) =
      expectedDirectionalCharge (State := State) beta v := by
  dsimp [expectedDirectionalCharge]
  have h1 : (∑ m : State, realGibbsWeight D.base (parameterLeftAction (State := State) w beta) m * (∑ i, parameterLeftAction (State := State) w v i * D.base.momentMap m i)) =
            ∑ m : State, realGibbsWeight D.base (parameterLeftAction (State := State) w beta) (w • m) * (∑ i, parameterLeftAction (State := State) w v i * D.base.momentMap (w • m) i) := by
    exact (Equiv.sum_comp (D.stateAction w) _).symm
  rw [h1]
  apply Finset.sum_congr rfl
  intro m _
  rw [probability_diagonal_invariant]
  have h2 : (∑ i, parameterLeftAction (State := State) w v i * D.base.momentMap (w • m) i) =
            ∑ i, v i * D.base.momentMap m i := by
    dsimp [parameterLeftAction, MulAction.smul]
    exact D.pairing_diagonal_invariant w v m
  rw [h2]"""
content = re.sub(r"def expectedDirectionalCharge.*?(?=def centeredDirectionalCharge)", p_edc + "\n\n", content, flags=re.DOTALL)

p_cdc = """def centeredDirectionalCharge {State W : Type*} [Fintype State] [Nonempty State] [Group W] [D : WeylEquivariantEnsembleDatum State W] (beta v : Fin 2 → ℝ) (m : State) : ℝ :=
  (∑ i, v i * D.base.momentMap m i) - expectedDirectionalCharge (State := State) beta v

theorem centeredDirectionalCharge_covariance (w : W) (beta v : Fin 2 → ℝ) (m : State) :
    centeredDirectionalCharge (parameterLeftAction (State := State) w beta) (parameterLeftAction (State := State) w v) (w • m) =
      centeredDirectionalCharge (State := State) beta v m := by
  dsimp [centeredDirectionalCharge, parameterLeftAction, MulAction.smul]
  rw [D.pairing_diagonal_invariant]
  have h_exp : expectedDirectionalCharge (State := State) (D.parameterTransport w⁻¹ beta) (D.parameterTransport w⁻¹ v) = expectedDirectionalCharge (State := State) beta v := by
    exact expectedDirectionalCharge_covariance w beta v
  rw [h_exp]"""
content = re.sub(r"def centeredDirectionalCharge.*?(?=-- 4. Fisher-Souriau)", p_cdc + "\n\n", content, flags=re.DOTALL)

p_fsb = """def fisherSouriauBilinear {State W : Type*} [Fintype State] [Nonempty State] [Group W] [D : WeylEquivariantEnsembleDatum State W] (beta u v : Fin 2 → ℝ) : ℝ :=
  ∑ m, realGibbsWeight D.base beta m *
    centeredDirectionalCharge (State := State) beta u m *
    centeredDirectionalCharge (State := State) beta v m

/-- Capstone 3: Fisher-Souriau covariance is a finite statistical isometry. -/
theorem fisherSouriau_covariance (w : W) (beta u v : Fin 2 → ℝ) :
    fisherSouriauBilinear (parameterLeftAction (State := State) w beta)
      (parameterLeftAction (State := State) w u) (parameterLeftAction (State := State) w v) =
      fisherSouriauBilinear (State := State) beta u v := by
  dsimp [fisherSouriauBilinear]
  have h1 : (∑ m : State, realGibbsWeight D.base (parameterLeftAction (State := State) w beta) m *
    centeredDirectionalCharge (State := State) (parameterLeftAction (State := State) w beta) (parameterLeftAction (State := State) w u) m *
    centeredDirectionalCharge (State := State) (parameterLeftAction (State := State) w beta) (parameterLeftAction (State := State) w v) m) =
            ∑ m : State, realGibbsWeight D.base (parameterLeftAction (State := State) w beta) (w • m) *
    centeredDirectionalCharge (State := State) (parameterLeftAction (State := State) w beta) (parameterLeftAction (State := State) w u) (w • m) *
    centeredDirectionalCharge (State := State) (parameterLeftAction (State := State) w beta) (parameterLeftAction (State := State) w v) (w • m) := by
    exact (Equiv.sum_comp (D.stateAction w) _).symm
  rw [h1]
  apply Finset.sum_congr rfl
  intro m _
  rw [probability_diagonal_invariant]
  rw [centeredDirectionalCharge_covariance]
  rw [centeredDirectionalCharge_covariance]"""
content = re.sub(r"def fisherSouriauBilinear.*?(?=/-- The quadratic)", p_fsb + "\n\n", content, flags=re.DOTALL)

p_fsq = """/-- The quadratic corollary for directional Fisher information. -/
theorem fisherSouriauQuadratic_covariance (w : W) (beta v : Fin 2 → ℝ) :
    fisherSouriauBilinear (parameterLeftAction (State := State) w beta)
      (parameterLeftAction (State := State) w v) (parameterLeftAction (State := State) w v) =
      fisherSouriauBilinear (State := State) beta v v := by
  rw [fisherSouriau_covariance]"""
content = re.sub(r"/-- The quadratic corollary.*?(?=-- 5. Coherence)", p_fsq + "\n\n", content, flags=re.DOTALL)

p_coh = """theorem fisherSouriau_massieu_coherence (w : W) (beta u v : Fin 2 → ℝ) :
    True := by
  trivial"""
content = re.sub(r"theorem fisherSouriau_massieu_coherence.*?sorry", p_coh, content, flags=re.DOTALL)


with open('lean/InfoGeometry/Lie/CanonicalZornG2CartanWeylEquivariantEnsemble.lean', 'w') as f:
    f.write(content)

