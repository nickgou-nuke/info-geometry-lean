import proofs.ZornCliffordTraceOrthogonality
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Bijectivity of the canonical Zorn Clifford representation

This module closes the algebraic isomorphism
`CliffordAlgebra vectorQuadratic ≃ₐ[ℂ] Module.End ℂ DiracSpinor16`
by combining:

* the PBW finrank certificate (`cliffordAlgebra_vector8_finrank = 256`),
* the target finrank (`diracEnd_finrank = 256`),
* the Frobenius orthogonality of Clifford monomials (`cliffordMonomial_trace_zero`).
-/

noncomputable section

namespace ZornCliffordBijectivity

open CanonicalZornCliffordRepresentation
open CanonicalZornCliffordIsomorphism
open ZornCliffordBasisMonomials
open ZornCliffordIsomorphismClosure
open ZornCliffordPBWFinrank
open ZornCliffordTraceOrthogonality

/-- Square formula for a duplicate-free ordered gamma word. -/
private theorem basisGamma_list_prod_sq
    (L : List (Fin 8)) (hL : L.Nodup) :
    (L.map basisGamma).prod * (L.map basisGamma).prod =
      algebraMap ℂ (Module.End ℂ DiracSpinor16)
        (((-1 : ℂ) ^ (L.length * (L.length - 1) / 2)) *
          (L.map cayleySign).prod) := by
  induction L with
  | nil => simp
  | cons a L ih =>
      have haL : a ∉ L := (List.nodup_cons.mp hL).1
      have hLn : L.Nodup := (List.nodup_cons.mp hL).2
      have hcomm := basisGamma_list_prod_comm a L hLn
      rw [if_neg haL] at hcomm
      let T : Module.End ℂ DiracSpinor16 := (L.map basisGamma).prod
      let s : ℂ := (-1 : ℂ) ^ L.length
      have hcomm' : basisGamma a * T = s • (T * basisGamma a) := by
        simpa [T, s] using hcomm
      have hs : s * s = 1 := by
        dsimp [s]
        rw [← pow_add]
        exact (show Even (L.length + L.length) by simp).neg_one_pow
      have hrev : T * basisGamma a = s • (basisGamma a * T) := by
        calc
          T * basisGamma a = 1 • (T * basisGamma a) := (one_smul ℂ _).symm
          _ = (s * s) • (T * basisGamma a) := by rw [hs]
          _ = s • (s • (T * basisGamma a)) := by rw [smul_smul]
          _ = s • (basisGamma a * T) := congrArg (fun X => s • X) hcomm'.symm
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      change (basisGamma a * T) * (basisGamma a * T) = _
      rw [mul_assoc (basisGamma a), ← mul_assoc T, hrev]
      rw [smul_mul_assoc, mul_smul_comm,
        mul_assoc (basisGamma a) T T,
        ← mul_assoc (basisGamma a) (basisGamma a) (T * T), basisGamma_sq]
      rw [ih hLn]
      have hscalar :
          s * (cayleySign a *
            (((-1 : ℂ) ^ (L.length * (L.length - 1) / 2)) *
              (L.map cayleySign).prod)) =
            ((-1 : ℂ) ^ ((L.length + 1) * (L.length + 1 - 1) / 2)) *
              (cayleySign a * (L.map cayleySign).prod) := by
        dsimp [s]
        have htriangle : (L.length + 1) * L.length / 2 =
            L.length * (L.length - 1) / 2 + L.length := by
          simpa using Nat.triangle_succ L.length
        rw [htriangle, pow_add]
        ring
      simpa only [Algebra.smul_def, map_mul] using
        congrArg (algebraMap ℂ (Module.End ℂ DiracSpinor16)) hscalar

/-- The square of a Clifford monomial is a nonzero scalar multiple of the
identity.  The first factor is the sign contributed by reversing the ordered
word. -/
theorem cliffordMonomial_sq (I : Finset (Fin 8)) :
    cliffordMonomial I * cliffordMonomial I =
      algebraMap ℂ (Module.End ℂ DiracSpinor16)
        (((-1 : ℂ) ^ (I.card * (I.card - 1) / 2)) * I.prod cayleySign) := by
  have hsq := basisGamma_list_prod_sq (I.sort (· ≤ ·))
    (Finset.sort_nodup I (· ≤ ·))
  have hprod : ((I.sort (· ≤ ·)).map cayleySign).prod = I.prod cayleySign := by
    rw [← List.prod_toFinset cayleySign (Finset.sort_nodup I (· ≤ ·))]
    simp
  simpa only [cliffordMonomial, Finset.length_sort, hprod] using hsq

/-- The product of two distinct monomials is (up to sign) a nonempty monomial,
hence has zero trace. -/
theorem cliffordMonomial_mul_trace_zero (I J : Finset (Fin 8)) (h : I ≠ J) :
    LinearMap.trace ℂ _ (cliffordMonomial I * cliffordMonomial J) = 0 := by
  exact cliffordMonomial_trace_orthogonality I J h

/-- Trace pairing with right multiplication by a fixed endomorphism. -/
private def traceRight (M : Module.End ℂ DiracSpinor16) :
    Module.Dual ℂ (Module.End ℂ DiracSpinor16) where
  toFun A := LinearMap.trace ℂ _ (A * M)
  map_add' A B := by
    rw [add_mul, map_add]
  map_smul' c A := by
    rw [smul_mul_assoc, map_smul]
    rfl

/-- The diagonal coefficient in the trace Gram matrix of the monomials. -/
private def monomialTraceDiagonal (I : Finset (Fin 8)) : ℂ :=
  16 * (((-1 : ℂ) ^ (I.card * (I.card - 1) / 2)) * I.prod cayleySign)

private theorem monomialTraceDiagonal_ne_zero (I : Finset (Fin 8)) :
    monomialTraceDiagonal I ≠ 0 := by
  unfold monomialTraceDiagonal
  apply mul_ne_zero
  · norm_num
  · apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => by
        unfold cayleySign
        split <;> norm_num

private theorem trace_cliffordMonomial_sq (I : Finset (Fin 8)) :
    LinearMap.trace ℂ _ (cliffordMonomial I * cliffordMonomial I) =
      monomialTraceDiagonal I := by
  rw [cliffordMonomial_sq]
  rw [Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.trace_one,
    CanonicalZornCliffordRepresentation.diracSpinor_finrank]
  change (((-1 : ℂ) ^ (I.card * (I.card - 1) / 2)) * I.prod cayleySign) * 16 =
    monomialTraceDiagonal I
  unfold monomialTraceDiagonal
  ring

/-- The 256 Clifford monomials are linearly independent in `End ℂ DiracSpinor16`. -/
theorem cliffordMonomials_linearIndependent :
    LinearIndependent ℂ (fun I : Finset (Fin 8) => cliffordMonomial I) := by
  let dual : Finset (Fin 8) → Module.Dual ℂ (Module.End ℂ DiracSpinor16) :=
    fun I => (monomialTraceDiagonal I)⁻¹ • traceRight (cliffordMonomial I)
  apply LinearIndependent.of_pairwise_dual_eq_zero_one _ dual
  · intro I J hIJ
    change (monomialTraceDiagonal I)⁻¹ *
      LinearMap.trace ℂ _ (cliffordMonomial J * cliffordMonomial I) = 0
    rw [cliffordMonomial_mul_trace_zero J I hIJ.symm, mul_zero]
  · intro I
    change (monomialTraceDiagonal I)⁻¹ *
      LinearMap.trace ℂ _ (cliffordMonomial I * cliffordMonomial I) = 1
    rw [trace_cliffordMonomial_sq]
    exact inv_mul_cancel₀ (monomialTraceDiagonal_ne_zero I)

/-- Native Clifford word whose image is the corresponding gamma monomial. -/
private def sourceMonomial (I : Finset (Fin 8)) :
    CliffordAlgebra vectorQuadratic :=
  ((I.sort (· ≤ ·)).map
    (fun i => CliffordAlgebra.ι vectorQuadratic (sageZornBasis i))).prod

private theorem zornCliffordRepresentation_sourceMonomial
    (I : Finset (Fin 8)) :
    zornCliffordRepresentation (sourceMonomial I) = cliffordMonomial I := by
  unfold sourceMonomial cliffordMonomial
  induction I.sort (· ≤ ·) with
  | nil => simp
  | cons i L ih =>
      simp [ih, basisGamma]

/-- `zornCliffordRepresentation` is surjective: its image contains 256 linearly
independent elements in a 256-dimensional target space. -/
theorem zornCliffordRepresentation_surjective :
    Function.Surjective zornCliffordRepresentation := by
  let family : Finset (Fin 8) → Module.End ℂ DiracSpinor16 :=
    fun I => cliffordMonomial I
  have hli : LinearIndependent ℂ family := cliffordMonomials_linearIndependent
  have hcard : Fintype.card (Finset (Fin 8)) = 256 := by
    simp
  have hspan_top : Submodule.span ℂ (Set.range family) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    calc
      Module.finrank ℂ (Submodule.span ℂ (Set.range family)) =
          Fintype.card (Finset (Fin 8)) := finrank_span_eq_card hli
      _ = 256 := hcard
      _ = Module.finrank ℂ (Module.End ℂ DiracSpinor16) := diracEnd_finrank.symm
  have h_top : LinearMap.range zornCliffordRepresentation.toLinearMap = ⊤ := by
    apply top_unique
    rw [← hspan_top]
    apply Submodule.span_le.mpr
    rintro A ⟨I, rfl⟩
    exact ⟨sourceMonomial I, zornCliffordRepresentation_sourceMonomial I⟩
  exact LinearMap.range_eq_top.mp h_top

/-- `zornCliffordRepresentation` is injective: the source and target have equal
finrank 256, and the map is surjective. -/
theorem zornCliffordRepresentation_injective :
    Function.Injective zornCliffordRepresentation := by
  exact zornCliffordRepresentation_injective_iff_surjective.mpr
    zornCliffordRepresentation_surjective

/-- The canonical Zorn–Clifford representation is a bijective algebra homomorphism. -/
theorem zornCliffordRepresentation_bijective :
    Function.Bijective zornCliffordRepresentation :=
  ⟨zornCliffordRepresentation_injective, zornCliffordRepresentation_surjective⟩

/-- The native Mathlib Clifford algebra of the canonical complex Zorn quadratic
space is algebra-isomorphic to the full endomorphism algebra of its
16-dimensional Dirac module. -/
def zornCliffordFullIsomorphism :
    CliffordAlgebra vectorQuadratic ≃ₐ[ℂ] Module.End ℂ DiracSpinor16 :=
  AlgEquiv.ofBijective zornCliffordRepresentation
    zornCliffordRepresentation_bijective

end ZornCliffordBijectivity
