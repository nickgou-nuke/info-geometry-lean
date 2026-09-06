import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.Data.ZMod.Units

namespace InfoGeometry.Arithmetic

noncomputable section

private theorem primitiveRoot_power_divisor
    {N M : ℕ} [NeZero N] [NeZero M]
    (hN : 0 < N) (hM : 0 < M) (hNM : N ∣ M) :
    IsPrimitiveRoot
      (IsCyclotomicExtension.zeta M ℚ (CyclotomicField M ℚ) ^ (M / N)) N := by
  rcases hNM with ⟨k, rfl⟩
  have hk : 0 < k := by
    by_contra hk
    simp only [not_lt, Nat.le_zero] at hk
    subst k
    simp at hM
  have hpow :=
    (IsCyclotomicExtension.zeta_spec (N * k) ℚ
      (CyclotomicField (N * k) ℚ)).pow_of_dvd
      (Nat.ne_of_gt hk) (dvd_mul_left k N)
  have h₁ : N * k / N = k := by
    simpa [Nat.mul_comm] using Nat.mul_div_left k hN
  have h₂ : N * k / k = N := by
    simpa [Nat.mul_comm] using Nat.mul_div_right N hk
  simpa [h₁, h₂] using hpow

/-- The canonical cyclotomic embedding induced by `N ∣ M` and
`ζ_N ↦ ζ_M ^ (M / N)`. -/
def cyclotomicFieldEmbedding
    {N M : ℕ} [NeZero N] [NeZero M]
    (hN : 0 < N) (hM : 0 < M) (hNM : N ∣ M) :
    CyclotomicField N ℚ →ₐ[ℚ] CyclotomicField M ℚ :=
  (IsPrimitiveRoot.embeddingsEquivPrimitiveRoots
    (IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ))
    (CyclotomicField M ℚ)
      (Polynomial.cyclotomic.irreducible_rat hN)).symm
    ⟨_, (mem_primitiveRoots hN).2 (primitiveRoot_power_divisor hN hM hNM)⟩

@[simp] theorem cyclotomicFieldEmbedding_zeta
    {N M : ℕ} [NeZero N] [NeZero M]
    (hN : 0 < N) (hM : 0 < M) (hNM : N ∣ M) :
    cyclotomicFieldEmbedding hN hM hNM
      (IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ)) =
      IsCyclotomicExtension.zeta M ℚ (CyclotomicField M ℚ) ^ (M / N) := by
  have h := Equiv.apply_symm_apply
    (IsPrimitiveRoot.embeddingsEquivPrimitiveRoots
      (IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ))
      (CyclotomicField M ℚ)
      (Polynomial.cyclotomic.irreducible_rat hN))
    (⟨_, (mem_primitiveRoots hN).2 (primitiveRoot_power_divisor hN hM hNM)⟩ :
      primitiveRoots N (CyclotomicField M ℚ))
  exact congrArg Subtype.val h

theorem cyclotomicFieldEmbedding_self
    {N : ℕ} [NeZero N] (hN : 0 < N) :
    cyclotomicFieldEmbedding hN hN (dvd_refl N) = AlgHom.id ℚ _ := by
  apply (IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)).powerBasis ℚ |>.algHom_ext
  simp [cyclotomicFieldEmbedding_zeta, Nat.div_self hN]

theorem cyclotomicFieldEmbedding_comp
    {N M L : ℕ} [NeZero N] [NeZero M] [NeZero L]
    (hN : 0 < N) (hM : 0 < M) (hL : 0 < L)
    (hNM : N ∣ M) (hML : M ∣ L) (hNL : N ∣ L)
    (hq : L / N = (L / M) * (M / N)) :
    (cyclotomicFieldEmbedding hM hL hML).comp
        (cyclotomicFieldEmbedding hN hM hNM) =
      cyclotomicFieldEmbedding hN hL hNL := by
  apply (IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)).powerBasis ℚ |>.algHom_ext
  rw [IsPrimitiveRoot.powerBasis_gen]
  rw [AlgHom.comp_apply, cyclotomicFieldEmbedding_zeta hN hM hNM,
    map_pow, cyclotomicFieldEmbedding_zeta hM hL hML,
    cyclotomicFieldEmbedding_zeta hN hL hNL]
  rw [← pow_mul, hq]

end
end InfoGeometry.Arithmetic
