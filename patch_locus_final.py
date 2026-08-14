import re

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'r') as f:
    text = f.read()

# Replace hyperbolicFlow_on_zeroWeight
zero_weight_proof = """theorem hyperbolicFlow_on_zeroWeight (t : ℝ) (x : Coord) (hx : x ∈ zeroWeightSubmodule) :
    hyperbolicFlowCoordinate t x = x := by
  refine Submodule.span_induction (p := fun y _ => hyperbolicFlowCoordinate t y = y)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with rfl | rfl
    · rw [hyperbolicFlowCoordinate_basis_action]
      have : InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight 0 = 0 := rfl
      rw [this, mul_zero, Real.exp_zero, one_smul]
    · rw [hyperbolicFlowCoordinate_basis_action]
      have : InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight 4 = 0 := rfl
      rw [this, mul_zero, Real.exp_zero, one_smul]
  · exact map_zero _
  · intro y z hy hz hy_eq hz_eq
    rw [map_add, hy_eq, hz_eq]
  · intro a y hy hy_eq
    rw [map_smul, hy_eq]"""
text = re.sub(r'theorem hyperbolicFlow_on_zeroWeight.*?(?=theorem hyperbolicFlow_on_positiveWeight)', zero_weight_proof + '\n\n', text, flags=re.DOTALL)

# Replace hyperbolicFlow_on_positiveWeight
pos_weight_proof = """theorem hyperbolicFlow_on_positiveWeight (t : ℝ) (x : Coord) (hx : x ∈ positiveWeightSubmodule) :
    hyperbolicFlowCoordinate t x = Real.exp t • x := by
  refine Submodule.span_induction (p := fun y _ => hyperbolicFlowCoordinate t y = Real.exp t • y)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with rfl | rfl | rfl
    · rw [hyperbolicFlowCoordinate_basis_action]
      have : InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight 1 = 1 := rfl
      rw [this, mul_one]
    · rw [hyperbolicFlowCoordinate_basis_action]
      have : InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight 2 = 1 := rfl
      rw [this, mul_one]
    · rw [hyperbolicFlowCoordinate_basis_action]
      have : InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight 3 = 1 := rfl
      rw [this, mul_one]
  · simp
  · intro y z hy hz hy_eq hz_eq
    rw [map_add, hy_eq, hz_eq, smul_add]
  · intro a y hy hy_eq
    rw [map_smul, hy_eq, smul_smul, mul_comm, ← smul_smul]"""
text = re.sub(r'theorem hyperbolicFlow_on_positiveWeight.*?(?=theorem hyperbolicFlow_on_negativeWeight)', pos_weight_proof + '\n\n', text, flags=re.DOTALL)

# Replace hyperbolicFlow_on_negativeWeight
neg_weight_proof = """theorem hyperbolicFlow_on_negativeWeight (t : ℝ) (x : Coord) (hx : x ∈ negativeWeightSubmodule) :
    hyperbolicFlowCoordinate t x = Real.exp (-t) • x := by
  refine Submodule.span_induction (p := fun y _ => hyperbolicFlowCoordinate t y = Real.exp (-t) • y)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with rfl | rfl | rfl
    · rw [hyperbolicFlowCoordinate_basis_action]
      have : InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight 5 = -1 := rfl
      rw [this, mul_neg_one]
    · rw [hyperbolicFlowCoordinate_basis_action]
      have : InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight 6 = -1 := rfl
      rw [this, mul_neg_one]
    · rw [hyperbolicFlowCoordinate_basis_action]
      have : InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight 7 = -1 := rfl
      rw [this, mul_neg_one]
  · simp
  · intro y z hy hz hy_eq hz_eq
    rw [map_add, hy_eq, hz_eq, smul_add]
  · intro a y hy hy_eq
    rw [map_smul, hy_eq, smul_smul, mul_comm, ← smul_smul]"""
text = re.sub(r'theorem hyperbolicFlow_on_negativeWeight.*?(?=theorem positiveWeight_totallyNull)', neg_weight_proof + '\n\n', text, flags=re.DOTALL)


# Replace positiveWeight_totallyNull
pos_null_proof = """theorem positiveWeight_totallyNull (x : Coord) (hx : x ∈ positiveWeightSubmodule) :
    circularPeirceQuadratic x = 0 := by
  rw [SplitOctonionEllCircularQuadraticCoordinates.circularPeirceQuadratic_formula]
  have h0 : x 0 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 0 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> rfl)
      rfl (fun y z hy hz hy_eq hz_eq => by simp [hy_eq, hz_eq])
      (fun a y hy hy_eq => by simp [hy_eq]) hx
  have h4 : x 4 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 4 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> rfl)
      rfl (fun y z hy hz hy_eq hz_eq => by simp [hy_eq, hz_eq])
      (fun a y hy hy_eq => by simp [hy_eq]) hx
  have h5 : x 5 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 5 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> rfl)
      rfl (fun y z hy hz hy_eq hz_eq => by simp [hy_eq, hz_eq])
      (fun a y hy hy_eq => by simp [hy_eq]) hx
  have h6 : x 6 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 6 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> rfl)
      rfl (fun y z hy hz hy_eq hz_eq => by simp [hy_eq, hz_eq])
      (fun a y hy hy_eq => by simp [hy_eq]) hx
  have h7 : x 7 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 7 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> rfl)
      rfl (fun y z hy hz hy_eq hz_eq => by simp [hy_eq, hz_eq])
      (fun a y hy hy_eq => by simp [hy_eq]) hx
  rw [h0, h4, h5, h6, h7]
  ring"""
text = re.sub(r'theorem positiveWeight_totallyNull.*?(?=theorem negativeWeight_totallyNull)', pos_null_proof + '\n\n', text, flags=re.DOTALL)


# Replace negativeWeight_totallyNull
neg_null_proof = """theorem negativeWeight_totallyNull (x : Coord) (hx : x ∈ negativeWeightSubmodule) :
    circularPeirceQuadratic x = 0 := by
  rw [SplitOctonionEllCircularQuadraticCoordinates.circularPeirceQuadratic_formula]
  have h0 : x 0 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 0 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> rfl)
      rfl (fun y z hy hz hy_eq hz_eq => by simp [hy_eq, hz_eq])
      (fun a y hy hy_eq => by simp [hy_eq]) hx
  have h1 : x 1 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 1 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> rfl)
      rfl (fun y z hy hz hy_eq hz_eq => by simp [hy_eq, hz_eq])
      (fun a y hy hy_eq => by simp [hy_eq]) hx
  have h2 : x 2 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 2 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> rfl)
      rfl (fun y z hy hz hy_eq hz_eq => by simp [hy_eq, hz_eq])
      (fun a y hy hy_eq => by simp [hy_eq]) hx
  have h3 : x 3 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 3 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> rfl)
      rfl (fun y z hy hz hy_eq hz_eq => by simp [hy_eq, hz_eq])
      (fun a y hy hy_eq => by simp [hy_eq]) hx
  rw [h0, h1, h2, h3]
  ring"""
text = re.sub(r'theorem negativeWeight_totallyNull.*?(?=theorem projective_positiveWeight_fixed)', neg_null_proof + '\n\n', text, flags=re.DOTALL)

text = re.sub(
    r'  induction p using Projectivization\.ind with\n  \| h x hx =>',
    r'  rcases p with ⟨p, hp⟩\n  induction p using Projectivization.ind with\n  | h x hx =>',
    text
)

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'w') as f:
    f.write(text)
