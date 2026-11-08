import InfoGeometry.Canonical.CelikCantorCliffordUniversal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CelikKocakPaperAllDepthClosure

/-!
# Native arbitrary-depth Clifford lift for the Çelik--Koçak operators

The finite paper generators are a pairwise anticommuting family indexed by
`Fin n ⊕ Fin n`.  This owner turns that family into an actual Mathlib
`CliffordAlgebra.lift`.  It proves existence of the algebra homomorphism; it
does not claim that the lift is an isomorphism.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.CelikKocakPaperFormalism

open InfoGeometry.Canonical.CelikKocakCantorOperators
open FunctionSpace

abbrev PaperOperator (n : ℕ) := (((Fin n) → Bool) → ℂ) →ₗ[ℂ] (((Fin n) → Bool) → ℂ)

noncomputable def paperQuadratic (n : ℕ) :
    QuadraticForm ℂ (Fin n ⊕ Fin n → ℂ) :=
  QuadraticMap.weightedSumSquares ℂ (fun _ => (1 : ℂ))

private lemma sum_sq_finset
    {A ι : Type*}
    [Semiring A] [Algebra ℂ A]
    [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (x : ι → ℂ) (g : ι → A)
    (hdiag : ∀ i, g i * g i = 1)
    (hanti : ∀ {i j}, i ≠ j → g i * g j + g j * g i = 0) :
    (∑ i ∈ s, x i • g i) * (∑ i ∈ s, x i • g i) =
      (∑ i ∈ s, x i * x i) • (1 : A) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hcross :
          (∑ i ∈ s, x i • g i) * (x a • g a) +
            (x a • g a) * (∑ i ∈ s, x i • g i) = 0 := by
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero
        intro i hi
        have h := hanti (i := i) (j := a) (by
          intro hia
          subst hia
          exact ha hi)
        calc
          (x i • g i) * (x a • g a) + (x a • g a) * (x i • g i) =
              (x i * x a) • (g i * g a + g a * g i) := by
                simp [smul_mul_assoc, mul_smul_comm, smul_smul, add_smul, mul_comm]
          _ = 0 := by rw [h]; simp
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      let u : A := ∑ i ∈ s, x i • g i
      let t : A := x a • g a
      change (t + u) * (t + u) = _
      calc
        (t + u) * (t + u) = u * u + (u * t + t * u) + t * t := by
          noncomm_ring
        _ = u * u + (u * t + t * u) + t * t := rfl
        _ = ((∑ i ∈ s, x i * x i) • (1 : A)) + 0 +
              ((x a * x a) • (1 : A)) := by
          rw [ih, hcross]
          simp [t, mul_smul_comm, smul_smul, hdiag]
        _ = (x a * x a + ∑ i ∈ s, x i * x i) • (1 : A) := by
          simp [add_smul]
          abel

noncomputable def paperGammaLinear (n : ℕ) :
    (Fin n ⊕ Fin n → ℂ) →ₗ[ℂ] PaperOperator n where
  toFun x := ∑ i, x i • paperGamma n i
  map_add' x y := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [smul_smul]

theorem paperGammaLinear_sq {n : ℕ} (x : Fin n ⊕ Fin n → ℂ) :
    paperGammaLinear n x * paperGammaLinear n x =
      (paperQuadratic n x) • (1 : PaperOperator n) := by
  simpa [paperGammaLinear, paperQuadratic,
    QuadraticMap.weightedSumSquares_apply] using
    (sum_sq_finset (s := (Finset.univ : Finset (Fin n ⊕ Fin n)))
      x (paperGamma n)
      (fun i => paperGamma_sq i)
      (fun hij => paperGamma_anticomm hij))

noncomputable def paperCliffordLift (n : ℕ) :
    CliffordAlgebra (paperQuadratic n) →ₐ[ℂ] PaperOperator n :=
  CliffordAlgebra.lift (paperQuadratic n)
    ⟨paperGammaLinear n, paperGammaLinear_sq⟩

@[simp] theorem paperCliffordLift_ι {n : ℕ} (x : Fin n ⊕ Fin n → ℂ) :
    paperCliffordLift n (CliffordAlgebra.ι (paperQuadratic n) x) =
      paperGammaLinear n x := by
  exact CliffordAlgebra.lift_ι_apply
    (paperGammaLinear n) (paperGammaLinear_sq) x

theorem paperCliffordLift_on_generator {n : ℕ} (i : Fin n ⊕ Fin n) :
    paperCliffordLift n (CliffordAlgebra.ι (paperQuadratic n) (Pi.single i 1)) =
      paperGamma n i := by
  rw [paperCliffordLift_ι]
  change (∑ k : Fin n ⊕ Fin n,
      ((Pi.single i (1 : ℂ) : Fin n ⊕ Fin n → ℂ) k) • paperGamma n k) =
    paperGamma n i
  have hsum :
      (∑ k : Fin n ⊕ Fin n,
          ((Pi.single i (1 : ℂ) : Fin n ⊕ Fin n → ℂ) k) • paperGamma n k) =
        ((Pi.single i (1 : ℂ) : Fin n ⊕ Fin n → ℂ) i) • paperGamma n i :=
    by
      simpa using
        (Fintype.sum_eq_single
          (f := fun k : Fin n ⊕ Fin n =>
            ((Pi.single i (1 : ℂ) : Fin n ⊕ Fin n → ℂ) k) • paperGamma n k) i
          (fun j hji => by
          simp [Pi.single_apply, hji, zero_smul]))
  rw [hsum]
  simp

theorem paperCliffordLift_unique {n : ℕ}
    {φ ψ : CliffordAlgebra (paperQuadratic n) →ₐ[ℂ] PaperOperator n}
    (h : ∀ x, φ (CliffordAlgebra.ι (paperQuadratic n) x) =
      ψ (CliffordAlgebra.ι (paperQuadratic n) x)) :
    φ = ψ := by
  exact InfoGeometry.Canonical.CelikCantorClifford.cliffordAlgHom_unique_of_generator_eq h

theorem paperCliffordLift_range (n : ℕ) :
    (paperCliffordLift n).range =
      Algebra.adjoin ℂ (Set.range (paperGammaLinear n)) := by
  simpa [paperCliffordLift] using
    (CliffordAlgebra.range_lift
      (Q := paperQuadratic n) (f := paperGammaLinear n)
      (cond := fun x => paperGammaLinear_sq x))

theorem paperCliffordLift_surjective_iff (n : ℕ) :
    Function.Surjective (paperCliffordLift n) ↔
      Algebra.adjoin ℂ (Set.range (paperGammaLinear n)) = ⊤ := by
  rw [← AlgHom.range_eq_top, paperCliffordLift_range]

end InfoGeometry.Canonical.CelikKocakPaperFormalism
