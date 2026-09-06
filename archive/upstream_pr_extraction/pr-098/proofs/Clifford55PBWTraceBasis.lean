import proofs.Clifford55PBWMonomials
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Trace-dual basis certificate for the ordered `Cl(5,5)` monomials -/

noncomputable section
namespace Clifford55PBWTraceBasis

open Clifford55
open Clifford55PBWFinrank
open Clifford55PBWMonomials

/-- Complementation in the even ten-element universe preserves parity. -/
private theorem even_card_compl_iff (I : Finset (Fin 10)) :
    Even Iᶜ.card ↔ Even I.card := by
  have hcard : Iᶜ.card = 10 - I.card := by simpa using Finset.card_compl I
  have hle : I.card ≤ 10 := by simpa using Finset.card_le_univ I
  rw [hcard]
  constructor
  · rintro ⟨m, hm⟩
    use 5 - m
    omega
  · rintro ⟨m, hm⟩
    use 5 - m
    omega

/-- The ten crossing characters separate all PBW subsets. -/
theorem exists_swapExponent55_opposite_parity (I J : Finset (Fin 10))
    (hIJ : I ≠ J) :
    ∃ j : Fin 10,
      (Even (swapExponent55 j I) ∧ Odd (swapExponent55 j J)) ∨
      (Odd (swapExponent55 j I) ∧ Even (swapExponent55 j J)) := by
  by_contra hsep
  push_neg at hsep
  have hodd (j : Fin 10) :
      Odd (swapExponent55 j I) ↔ Odd (swapExponent55 j J) := by
    rcases Nat.even_or_odd (swapExponent55 j I) with hIe | hIo <;>
      rcases Nat.even_or_odd (swapExponent55 j J) with hJe | hJo
    · exact ⟨fun h => False.elim (Nat.not_even_iff_odd.mpr h hIe),
        fun h => False.elim (Nat.not_even_iff_odd.mpr h hJe)⟩
    · exact False.elim ((hsep j).1 hIe hJo)
    · exact False.elim ((hsep j).2 hIo hJe)
    · exact ⟨fun _ => hJo, fun _ => hIo⟩
  rcases Nat.even_or_odd I.card with hIe | hIo <;>
    rcases Nat.even_or_odd J.card with hJe | hJo
  · apply hIJ
    ext j
    have ht := hodd j
    simp [odd_swapExponent55_iff, hIe, hJe,
      Nat.not_odd_iff_even.mpr hIe, Nat.not_odd_iff_even.mpr hJe] at ht
    exact ht
  · have hcomp : J = Iᶜ := by
      ext j
      have ht := hodd j
      simp [odd_swapExponent55_iff, hIe, hJo,
        Nat.not_odd_iff_even.mpr hIe, Nat.not_even_iff_odd.mpr hJo] at ht ⊢
      tauto
    have : Even J.card := by rw [hcomp, even_card_compl_iff]; exact hIe
    exact False.elim (Nat.not_even_iff_odd.mpr hJo this)
  · have hcomp : I = Jᶜ := by
      ext j
      have ht := hodd j
      simp [odd_swapExponent55_iff, hIo, hJe,
        Nat.not_even_iff_odd.mpr hIo, Nat.not_odd_iff_even.mpr hJe] at ht ⊢
      tauto
    have : Even I.card := by rw [hcomp, even_card_compl_iff]; exact hJe
    exact False.elim (Nat.not_even_iff_odd.mpr hIo this)
  · apply hIJ
    ext j
    have ht := hodd j
    simp [odd_swapExponent55_iff, hIo, hJo,
      Nat.not_even_iff_odd.mpr hIo, Nat.not_even_iff_odd.mpr hJo] at ht
    tauto

/-- Distinct PBW words have a product anticommuting with some generator. -/
theorem exists_gamma55_anticommutes_monomial_mul (I J : Finset (Fin 10))
    (hIJ : I ≠ J) :
    ∃ j : Fin 10,
      gamma55 j * (cliffordMonomial55 I * cliffordMonomial55 J) =
        -((cliffordMonomial55 I * cliffordMonomial55 J) * gamma55 j) := by
  obtain ⟨j, hpar | hpar⟩ := exists_swapExponent55_opposite_parity I J hIJ
  · refine ⟨j, ?_⟩
    have hI := gamma55_mul_cliffordMonomial55 j I
    have hJ := gamma55_mul_cliffordMonomial55 j J
    rw [hpar.1.neg_one_pow, one_smul] at hI
    rw [hpar.2.neg_one_pow, neg_one_smul] at hJ
    calc
      gamma55 j * (cliffordMonomial55 I * cliffordMonomial55 J) =
          (gamma55 j * cliffordMonomial55 I) * cliffordMonomial55 J := by rw [mul_assoc]
      _ = (cliffordMonomial55 I * gamma55 j) * cliffordMonomial55 J := by rw [hI]
      _ = cliffordMonomial55 I * (gamma55 j * cliffordMonomial55 J) := by rw [mul_assoc]
      _ = cliffordMonomial55 I * (-(cliffordMonomial55 J * gamma55 j)) := by rw [hJ]
      _ = -((cliffordMonomial55 I * cliffordMonomial55 J) * gamma55 j) := by
        rw [mul_neg, neg_inj, mul_assoc]
  · refine ⟨j, ?_⟩
    have hI := gamma55_mul_cliffordMonomial55 j I
    have hJ := gamma55_mul_cliffordMonomial55 j J
    rw [hpar.1.neg_one_pow, neg_one_smul] at hI
    rw [hpar.2.neg_one_pow, one_smul] at hJ
    calc
      gamma55 j * (cliffordMonomial55 I * cliffordMonomial55 J) =
          (gamma55 j * cliffordMonomial55 I) * cliffordMonomial55 J := by rw [mul_assoc]
      _ = (-(cliffordMonomial55 I * gamma55 j)) * cliffordMonomial55 J := by rw [hI]
      _ = -(cliffordMonomial55 I * (gamma55 j * cliffordMonomial55 J)) := by
        rw [neg_mul, neg_inj, mul_assoc]
      _ = -(cliffordMonomial55 I * (cliffordMonomial55 J * gamma55 j)) := by rw [hJ]
      _ = -((cliffordMonomial55 I * cliffordMonomial55 J) * gamma55 j) := by rw [mul_assoc]

/-- Left regular representation used only for its finite-dimensional trace. -/
def leftRegular55 : Cl55 →ₐ[ℝ] Module.End ℝ Cl55 := Algebra.lmul ℝ Cl55

theorem regular_trace_zero_of_gamma_anticommutes (j : Fin 10) (x : Cl55)
    (hanti : gamma55 j * x = -(x * gamma55 j)) :
    LinearMap.trace ℝ Cl55 (leftRegular55 x) = 0 := by
  let G : Module.End ℝ Cl55 := leftRegular55 (gamma55 j)
  let X : Module.End ℝ Cl55 := leftRegular55 x
  let s : ℝ := gammaSign55 j
  have hGX : G * X = -(X * G) := by
    dsimp [G, X]
    rw [← map_mul, ← map_mul, hanti, map_neg]
  have hGG : G * G = s • 1 := by
    dsimp [G]
    rw [← map_mul, gamma55_sq]
    rw [Algebra.smul_def, mul_one]
    simp [s, leftRegular55.commutes (gammaSign55 j)]
  have hcyc := LinearMap.trace_mul_comm ℝ G (G * X)
  have hscalar : s * LinearMap.trace ℝ Cl55 X =
      -(s * LinearMap.trace ℝ Cl55 X) := by
    calc
      s * LinearMap.trace ℝ Cl55 X =
          LinearMap.trace ℝ Cl55 (s • X) := by simp
      _ = LinearMap.trace ℝ Cl55 ((G * G) * X) := by rw [hGG]; simp
      _ = LinearMap.trace ℝ Cl55 (G * (G * X)) := by rw [mul_assoc]
      _ = LinearMap.trace ℝ Cl55 ((G * X) * G) := hcyc
      _ = LinearMap.trace ℝ Cl55 ((-(X * G)) * G) := by rw [hGX]
      _ = LinearMap.trace ℝ Cl55 (-(X * (G * G))) := by
        rw [neg_mul, mul_assoc]
      _ = LinearMap.trace ℝ Cl55 (-(X * (s • 1))) := by rw [hGG]
      _ = -(s * LinearMap.trace ℝ Cl55 X) := by simp
  have hs : s ≠ 0 := gammaSign55_ne_zero j
  have htwo : (2 : ℝ) * (s * LinearMap.trace ℝ Cl55 X) = 0 := by
    linarith
  have hz : s * LinearMap.trace ℝ Cl55 X = 0 := by
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact (mul_eq_zero.mp hz).resolve_left hs

theorem distinct_monomial_product_regular_trace_zero
    (I J : Finset (Fin 10)) (hIJ : I ≠ J) :
    LinearMap.trace ℝ Cl55
      (leftRegular55 (cliffordMonomial55 I * cliffordMonomial55 J)) = 0 := by
  obtain ⟨j, hj⟩ := exists_gamma55_anticommutes_monomial_mul I J hIJ
  exact regular_trace_zero_of_gamma_anticommutes j _ hj

theorem regular_trace_algebraMap (c : ℝ) :
    LinearMap.trace ℝ Cl55 (leftRegular55 (algebraMap ℝ Cl55 c)) =
      c * 1024 := by
  rw [leftRegular55.commutes]
  rw [← mul_one (algebraMap ℝ (Module.End ℝ Cl55) c),
    ← Algebra.smul_def, LinearMap.map_smul, LinearMap.trace_one,
    cliffordAlgebra55_finrank]
  norm_num

def monomialTraceDiagonal55 (I : Finset (Fin 10)) : ℝ :=
  LinearMap.trace ℝ Cl55
    (leftRegular55 (cliffordMonomial55 I * cliffordMonomial55 I))

theorem monomialTraceDiagonal55_formula (I : Finset (Fin 10)) :
    monomialTraceDiagonal55 I =
      (((-1 : ℝ) ^ (I.card * (I.card - 1) / 2)) * I.prod gammaSign55) * 1024 := by
  unfold monomialTraceDiagonal55
  rw [cliffordMonomial55_sq, regular_trace_algebraMap]

theorem monomialTraceDiagonal55_ne_zero (I : Finset (Fin 10)) :
    monomialTraceDiagonal55 I ≠ 0 := by
  rw [monomialTraceDiagonal55_formula]
  exact mul_ne_zero (cliffordMonomial55_sq_scalar_ne_zero I) (by norm_num)

/-- Trace pairing with right multiplication by one PBW word. -/
def traceRight55 (M : Cl55) : Module.Dual ℝ Cl55 where
  toFun A := LinearMap.trace ℝ Cl55 (leftRegular55 (A * M))
  map_add' A B := by
    rw [add_mul, map_add, map_add]
  map_smul' c A := by
    rw [smul_mul_assoc, map_smul, map_smul]
    rfl

/-- The 1024 ordered native Clifford words are linearly independent. -/
theorem cliffordMonomials55_linearIndependent :
    LinearIndependent ℝ (fun I : Finset (Fin 10) => cliffordMonomial55 I) := by
  let dual : Finset (Fin 10) → Module.Dual ℝ Cl55 :=
    fun I => (monomialTraceDiagonal55 I)⁻¹ • traceRight55 (cliffordMonomial55 I)
  apply LinearIndependent.of_pairwise_dual_eq_zero_one _ dual
  · intro I J hIJ
    change (monomialTraceDiagonal55 I)⁻¹ *
      LinearMap.trace ℝ Cl55
        (leftRegular55 (cliffordMonomial55 J * cliffordMonomial55 I)) = 0
    rw [distinct_monomial_product_regular_trace_zero J I hIJ.symm, mul_zero]
  · intro I
    change (monomialTraceDiagonal55 I)⁻¹ * monomialTraceDiagonal55 I = 1
    exact inv_mul_cancel₀ (monomialTraceDiagonal55_ne_zero I)

/-- The ordered monomials are the native PBW basis of `Cl(5,5)`. -/
def cliffordMonomial55Basis :
    Module.Basis (Finset (Fin 10)) ℝ Cl55 := by
  let family : Finset (Fin 10) → Cl55 := cliffordMonomial55
  have hli : LinearIndependent ℝ family := cliffordMonomials55_linearIndependent
  have hspan : Submodule.span ℝ (Set.range family) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    calc
      Module.finrank ℝ (Submodule.span ℝ (Set.range family)) =
          Fintype.card (Finset (Fin 10)) := finrank_span_eq_card hli
      _ = 1024 := by simp
      _ = Module.finrank ℝ Cl55 := cliffordAlgebra55_finrank.symm
  exact Module.Basis.mk hli (by rw [hspan])

@[simp] theorem cliffordMonomial55Basis_apply (I : Finset (Fin 10)) :
    cliffordMonomial55Basis I = cliffordMonomial55 I := by
  simp [cliffordMonomial55Basis]

end Clifford55PBWTraceBasis
end noncomputable section
