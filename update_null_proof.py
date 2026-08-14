import re

with open('lean/InfoGeometry/Physics/HestenesKreinOperatorCalculus.lean', 'r') as f:
    content = f.read()

# Define the new helper lemma and the proof of exp_anticommuting_null
null_proofs = """/-- Helper: Prove that the exponential of a nilpotent operator is 1 + x -/
theorem exp_eq_add_one_of_sq_eq_zero (x : A) (h : x^2 = 0) : 
  NormedSpace.exp x = 1 + x := by
  have H : NormedSpace.exp x = ∑' (n : ℕ), (n.factorial : ℝ)⁻¹ • x ^ n :=
    congr_fun (NormedSpace.exp_eq_tsum ℝ) x
  rw [H]
  have h_pow : ∀ n ≥ 2, (n.factorial : ℝ)⁻¹ • x ^ n = 0 := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add, h, zero_mul, smul_zero]
  let f : ℕ → A := fun n => (n.factorial : ℝ)⁻¹ • x ^ n
  have h_f : ∀ n ∉ ({0, 1} : Finset ℕ), f n = 0 := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    apply h_pow
    omega
  have H2 : ∑' n, f n = ∑ n ∈ ({0, 1} : Finset ℕ), f n := tsum_eq_sum h_f
  rw [H2]
  simp [f]

theorem exp_anticommuting_null (I K : A) 
    (hI : I ^ 2 = -1) (hK : K ^ 2 = 1) (h_anti : I * K = -(K * I)) 
    (θ η : ℝ) (hq : η^2 = θ^2) :
    NormedSpace.exp (θ • I + η • K) = (1 : A) + (θ • I + η • K) := by
  apply exp_eq_add_one_of_sq_eq_zero
  have h_sq := anticommuting_mixed_square I K hI hK h_anti θ η
  rw [hq, sub_self, zero_smul] at h_sq
  exact h_sq"""

content = re.sub(r"theorem exp_anticommuting_null.*?sorry", null_proofs, content, flags=re.DOTALL)

with open('lean/InfoGeometry/Physics/HestenesKreinOperatorCalculus.lean', 'w') as f:
    f.write(content)

