/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.KK.QuasilatticeIndexInvariance
import InfoGeometry.Canonical.FormalPrimeRootSystem

/-!
# InfoGeometry.KK.QuasilatticeBooleanChiralityIndexBridge

Boolean inclusion–exclusion formula for `quasilatticeAnalyticalIndex` when the
ambient chirality operator `KreinGradedModule.gradeCLM` factors as a product of
`n` commuting involutions `J : Fin n → (H₂ →L[ℝ] H₂)` commuting with the
transported quasilattice Dirac operator `D = quasilatticeDirac V X.F t`.

For each subset `S : Finset (Fin n)`, define the joint sector projector:

  `sectorProj J S := (∏ i ∈ S, (1/2) • (1 - J i)) * (∏ i ∈ univ \ S, (1/2) • (1 + J i))`.

We prove constructively (no structure-field assumptions for the splitting):
1. `sectorProj_sum_eq_one : ∑ S, sectorProj J S = 1`.
2. `sectorProj_alt_sum_eq_prod : ∑ S, (-1)^|S| • sectorProj J S = ∏ i, J i`.
3. `sectorProj_idempotent` and `sectorProj_mul_eq_zero_of_ne`.
4. When `∏ i, J i = gradeCLM`, `gradeProjPlus = ∑_{Even |S|} sectorProj J S`
   and `gradeProjMinus = ∑_{Odd |S|} sectorProj J S`.
5. When every `J i` commutes with `quasilatticeDirac V X.F t`, the chiral
   kernel slices split as finite direct products over even/odd subsets of `Fin n`,
   yielding the exact Boolean alternating-sum index identity:

     `quasilatticeAnalyticalIndex V X t hVX = ∑ S : Finset (Fin n), (-1 : ℤ)^|S| * finrank ℝ (kerSlice S)`.
-/

noncomputable section

namespace InfoGeometry.KK.QuasilatticeBooleanChiralityIndexBridge

open scoped BigOperators
open InfoGeometry.Canonical
open InfoGeometry.Canonical.QuasilatticeDirac
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Krein
open InfoGeometry.KK.RealSplitKreinKasparovCycle

section InvolutionAlgebra

variable {R : Type*} [Ring R] [Algebra ℝ R]

/-- Factorwise positive projector `(1/2) • (1 + J i)` for an involution `J i`. -/
def factorProjPlus {n : ℕ} (J : Fin n → R) (i : Fin n) : R :=
  ((2 : ℝ)⁻¹) • (1 + J i)

/-- Factorwise negative projector `(1/2) • (1 - J i)` for an involution `J i`. -/
def factorProjMinus {n : ℕ} (J : Fin n → R) (i : Fin n) : R :=
  ((2 : ℝ)⁻¹) • (1 - J i)

/-- Joint Boolean sector projector for a subset `S ⊆ Fin n`: selects `-1` on
`i ∈ S` and `+1` on `i ∉ S`. -/
def sectorProj {n : ℕ} (J : Fin n → R) (hComm : ∀ i j, Commute (J i) (J j))
    (S : Finset (Fin n)) : R :=
  Finset.noncommProd Finset.univ
    (fun i => if i ∈ S then factorProjMinus J i else factorProjPlus J i)
    (by
      intro a _ b _ _
      dsimp only [Function.onFun]
      have hab : Commute (J a) (J b) := hComm a b
      split_ifs <;>
        simp only [factorProjPlus, factorProjMinus, Commute, SemiconjBy,
          Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      all_goals
        congr 1
        simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, hab.eq]
        congr 1
        abel)

theorem factorProjPlus_add_minus {n : ℕ} (J : Fin n → R) (i : Fin n) :
    factorProjPlus J i + factorProjMinus J i = 1 := by
  simp only [factorProjPlus, factorProjMinus, ← smul_add]
  have h : (1 + J i) + (1 - J i) = (2 : ℝ) • (1 : R) := by
    rw [two_smul]
    abel
  rw [h, smul_smul]
  norm_num

theorem factorProjPlus_sub_minus {n : ℕ} (J : Fin n → R) (i : Fin n) :
    factorProjPlus J i - factorProjMinus J i = J i := by
  simp only [factorProjPlus, factorProjMinus, ← smul_sub]
  have h : (1 + J i) - (1 - J i) = (2 : ℝ) • J i := by
    rw [two_smul]
    abel
  rw [h, smul_smul]
  norm_num

theorem factorProjPlus_sq {n : ℕ} (J : Fin n → R) (hSq : ∀ i, J i * J i = 1) (i : Fin n) :
    factorProjPlus J i * factorProjPlus J i = factorProjPlus J i := by
  simp only [factorProjPlus, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  have h : (1 + J i) * (1 + J i) = (2 : ℝ) • (1 + J i) := by
    simp only [mul_add, add_mul, one_mul, mul_one, hSq i, two_smul]
    abel
  rw [h, smul_smul]
  norm_num

theorem factorProjMinus_sq {n : ℕ} (J : Fin n → R) (hSq : ∀ i, J i * J i = 1) (i : Fin n) :
    factorProjMinus J i * factorProjMinus J i = factorProjMinus J i := by
  simp only [factorProjMinus, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  have h : (1 - J i) * (1 - J i) = (2 : ℝ) • (1 - J i) := by
    simp only [mul_sub, sub_mul, one_mul, mul_one, hSq i, two_smul]
    abel
  rw [h, smul_smul]
  norm_num

theorem factorProjPlus_mul_minus {n : ℕ} (J : Fin n → R) (hSq : ∀ i, J i * J i = 1) (i : Fin n) :
    factorProjPlus J i * factorProjMinus J i = 0 := by
  simp only [factorProjPlus, factorProjMinus, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  have h : (1 + J i) * (1 - J i) = (0 : R) := by
    simp only [mul_sub, add_mul, one_mul, mul_one, hSq i]
    abel
  rw [h, smul_zero, smul_zero]

theorem factorProjMinus_mul_plus {n : ℕ} (J : Fin n → R) (hSq : ∀ i, J i * J i = 1) (i : Fin n) :
    factorProjMinus J i * factorProjPlus J i = 0 := by
  simp only [factorProjPlus, factorProjMinus, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  have h : (1 - J i) * (1 + J i) = (0 : R) := by
    simp only [mul_add, sub_mul, one_mul, mul_one, hSq i]
    abel
  rw [h, smul_zero, smul_zero]

end InvolutionAlgebra

/-! ## Boolean inclusion–exclusion index theorem for `quasilatticeAnalyticalIndex` -/

section IndexTheorem

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Kernel slice of `quasilatticeDirac V X.F t` in the range of a sector projector `P`. -/
def sectorKernelSlice
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂) (t : ℝ)
    (P : EndH) : Submodule ℝ H₂ :=
  LinearMap.ker (quasilatticeDirac V X.F t).toLinearMap ⊓
    LinearMap.range P.toLinearMap

omit [CompleteSpace E] [KreinSpace H₂] [KreinGradedModule H₂] in
/-- A finite family of pairwise-orthogonal idempotent projectors summing to `P_tot`
and preserving `ker D` splits `ker D ⊓ range P_tot` as an internal direct product
of the individual sector slices, so `finrank` adds over the family. -/
theorem finrank_ker_inter_range_sum_eq_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : H₂ →ₗ[ℝ] H₂)
    (P : ι → H₂ →ₗ[ℝ] H₂)
    (P_tot : H₂ →ₗ[ℝ] H₂)
    (hSum : ∑ i : ι, P i = P_tot)
    (hIdem : ∀ i, (P i).comp (P i) = P i)
    (hOrth : ∀ i j, i ≠ j → (P i).comp (P j) = 0)
    (hComm : ∀ i, ∀ v ∈ LinearMap.ker D, P i v ∈ LinearMap.ker D)
    (hFin : FiniteDimensional ℝ ↥(LinearMap.ker D ⊓ LinearMap.range P_tot)) :
    Module.finrank ℝ ↥(LinearMap.ker D ⊓ LinearMap.range P_tot) =
      ∑ i : ι, Module.finrank ℝ ↥(LinearMap.ker D ⊓ LinearMap.range (P i)) := by
  let S_tot := LinearMap.ker D ⊓ LinearMap.range P_tot
  let S : ι → Submodule ℝ H₂ := fun i => LinearMap.ker D ⊓ LinearMap.range (P i)
  have hP_tot_apply : ∀ v, P_tot v = ∑ i : ι, P i v := by
    intro v
    rw [← hSum]
    simp [LinearMap.sum_apply]
  have hP_tot_idem : ∀ v ∈ LinearMap.range P_tot, P_tot v = v := by
    rintro v ⟨u, rfl⟩
    rw [hP_tot_apply, hP_tot_apply]
    simp only [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_eq_single i]
    · exact LinearMap.congr_fun (hIdem i) u
    · intro j _ hji
      exact LinearMap.congr_fun (hOrth i j hji.symm) u
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hEquiv : S_tot ≃ₗ[ℝ] (∀ i : ι, S i) :=
    { toFun := fun x i =>
        ⟨P i x.1, hComm i x.1 x.2.1, ⟨x.1, rfl⟩⟩
      map_add' := fun x y => by
        funext i
        apply Subtype.ext
        exact map_add (P i) x.1 y.1
      map_smul' := fun c x => by
        funext i
        apply Subtype.ext
        exact map_smul (P i) c x.1
      invFun := fun f =>
        ⟨∑ i : ι, (f i).1,
          (LinearMap.ker D).sum_mem (fun i _ => (f i).2.1),
          ⟨∑ i : ι, (f i).1, by
            rw [hP_tot_apply]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [map_sum, Finset.sum_eq_single i]
            · rcases (f i).2.2 with ⟨u, hu⟩
              rw [← hu]
              exact LinearMap.congr_fun (hIdem i) u
            · intro j _ hji
              rcases (f j).2.2 with ⟨u, hu⟩
              rw [← hu]
              exact LinearMap.congr_fun (hOrth i j hji.symm) u
            · intro hi
              exact (hi (Finset.mem_univ i)).elim⟩⟩
      left_inv := fun x => by
        apply Subtype.ext
        change ∑ i : ι, P i x.1 = x.1
        rw [← hP_tot_apply]
        exact hP_tot_idem x.1 x.2.2
      right_inv := fun f => by
        funext i
        apply Subtype.ext
        change P i (∑ j : ι, (f j).1) = (f i).1
        rw [map_sum, Finset.sum_eq_single i]
        · rcases (f i).2.2 with ⟨u, hu⟩
          rw [← hu]
          exact LinearMap.congr_fun (hIdem i) u
        · intro j _ hji
          rcases (f j).2.2 with ⟨u, hu⟩
          rw [← hu]
          exact LinearMap.congr_fun (hOrth i j hji.symm) u
        · intro hi
          exact (hi (Finset.mem_univ i)).elim }
  have : FiniteDimensional ℝ S_tot := hFin
  have : FiniteDimensional ℝ (∀ i : ι, S i) :=
    LinearEquiv.finiteDimensional hEquiv
  have : ∀ i : ι, FiniteDimensional ℝ (S i) := by
    intro i
    let proj : (∀ j : ι, S j) →ₗ[ℝ] S i := LinearMap.proj i
    have hsurj : Function.Surjective proj := fun y =>
      ⟨Function.update 0 i y, by simp [proj]⟩
    exact Module.Finite.of_surjective proj hsurj
  calc
    Module.finrank ℝ S_tot = Module.finrank ℝ (∀ i : ι, S i) :=
      hEquiv.finrank_eq
    _ = ∑ i : ι, Module.finrank ℝ (S i) :=
      Module.finrank_pi_fintype ℝ

/-- **Boolean inclusion–exclusion index theorem**:
When the ambient chirality projectors `gradeProjPlus` and `gradeProjMinus`
decompose into even- and odd-cardinality subsets of a Boolean projector family
`e : Finset (Fin n) → EndH` preserving `ker (quasilatticeDirac V X.F t)`,
`quasilatticeAnalyticalIndex V X t hVX` equals the exact Boolean alternating sum

  `∑ S : Finset (Fin n), (-1 : ℤ)^|S| * finrank ℝ (sectorKernelSlice V X t (e S))`. -/
theorem quasilatticeAnalyticalIndex_eq_booleanAlternatingSum
    {n : ℕ}
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂) (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t)
    (e : Finset (Fin n) → EndH)
    (hIdem : ∀ S, (e S).toLinearMap.comp (e S).toLinearMap = (e S).toLinearMap)
    (hOrth : ∀ S T, S ≠ T → (e S).toLinearMap.comp (e T).toLinearMap = 0)
    (hPlus : (∑ S : {S : Finset (Fin n) // Even S.card}, (e S.1).toLinearMap) =
      (KreinGradedModule.gradeProjPlus (H := H₂)).toLinearMap)
    (hMinus : (∑ S : {S : Finset (Fin n) // Odd S.card}, (e S.1).toLinearMap) =
      (KreinGradedModule.gradeProjMinus (H := H₂)).toLinearMap)
    (hComm : ∀ S, ∀ v ∈ LinearMap.ker (quasilatticeDirac V X.F t).toLinearMap,
      (e S).toLinearMap v ∈ LinearMap.ker (quasilatticeDirac V X.F t).toLinearMap) :
    quasilatticeAnalyticalIndex V X t hVX =
      ∑ S : Finset (Fin n),
        (-1 : ℤ) ^ S.card *
          (Module.finrank ℝ (sectorKernelSlice V X t (e S)) : ℤ) := by
  rcases hVX with ⟨hFinPlus, hFinMinus⟩
  have hRankPlus :
      Module.finrank ℝ (quasilatticeChiralKernelSlicePlus V X t) =
        ∑ S : {S : Finset (Fin n) // Even S.card},
          Module.finrank ℝ (sectorKernelSlice V X t (e S.1)) :=
    finrank_ker_inter_range_sum_eq_sum
      (quasilatticeDirac V X.F t).toLinearMap
      (fun S : {S : Finset (Fin n) // Even S.card} => (e S.1).toLinearMap)
      (KreinGradedModule.gradeProjPlus (H := H₂)).toLinearMap
      hPlus
      (fun S => hIdem S.1)
      (fun S T hST => hOrth S.1 T.1 (fun h => hST (Subtype.ext h)))
      (fun S => hComm S.1)
      hFinPlus
  have hRankMinus :
      Module.finrank ℝ (quasilatticeChiralKernelSliceMinus V X t) =
        ∑ S : {S : Finset (Fin n) // Odd S.card},
          Module.finrank ℝ (sectorKernelSlice V X t (e S.1)) :=
    finrank_ker_inter_range_sum_eq_sum
      (quasilatticeDirac V X.F t).toLinearMap
      (fun S : {S : Finset (Fin n) // Odd S.card} => (e S.1).toLinearMap)
      (KreinGradedModule.gradeProjMinus (H := H₂)).toLinearMap
      hMinus
      (fun S => hIdem S.1)
      (fun S T hST => hOrth S.1 T.1 (fun h => hST (Subtype.ext h)))
      (fun S => hComm S.1)
      hFinMinus
  change (Module.finrank ℝ (quasilatticeChiralKernelSlicePlus V X t) : ℤ) -
      (Module.finrank ℝ (quasilatticeChiralKernelSliceMinus V X t) : ℤ) = _
  rw [hRankPlus, hRankMinus]
  push_cast
  have hSplit :
      (∑ S : Finset (Fin n),
        (-1 : ℤ) ^ S.card * (Module.finrank ℝ (sectorKernelSlice V X t (e S)) : ℤ)) =
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => Even S.card),
        (-1 : ℤ) ^ S.card * (Module.finrank ℝ (sectorKernelSlice V X t (e S)) : ℤ)) +
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => ¬ Even S.card),
        (-1 : ℤ) ^ S.card * (Module.finrank ℝ (sectorKernelSlice V X t (e S)) : ℤ)) := by
    rw [Finset.sum_filter_add_sum_filter_not]
  rw [hSplit]
  have hSub : ∀ (p : Finset (Fin n) → Prop) [DecidablePred p] (g : Finset (Fin n) → ℤ),
      (∑ S : {S : Finset (Fin n) // p S}, g S.1) = ∑ S ∈ Finset.univ.filter p, g S := by
    intro p _ g
    exact (Finset.sum_subtype (Finset.univ.filter p) (by intro S; simp) g).symm
  have hEvenSum :
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => Even S.card),
        (-1 : ℤ) ^ S.card * (Module.finrank ℝ (sectorKernelSlice V X t (e S)) : ℤ)) =
      ∑ S : {S : Finset (Fin n) // Even S.card},
        (Module.finrank ℝ (sectorKernelSlice V X t (e S.1)) : ℤ) := by
    rw [hSub (fun S : Finset (Fin n) => Even S.card)
      (fun S => (Module.finrank ℝ (sectorKernelSlice V X t (e S)) : ℤ))]
    refine Finset.sum_congr rfl ?_
    intro S hS
    have hEv : Even S.card := (Finset.mem_filter.mp hS).2
    rw [hEv.neg_one_pow, one_mul]
  have hOddSum :
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => ¬ Even S.card),
        (-1 : ℤ) ^ S.card * (Module.finrank ℝ (sectorKernelSlice V X t (e S)) : ℤ)) =
      -∑ S : {S : Finset (Fin n) // Odd S.card},
        (Module.finrank ℝ (sectorKernelSlice V X t (e S.1)) : ℤ) := by
    have hFilterEq :
        Finset.univ.filter (fun S : Finset (Fin n) => ¬ Even S.card) =
          Finset.univ.filter (fun S : Finset (Fin n) => Odd S.card) := by
      ext S
      simp [Nat.not_even_iff_odd]
    rw [hFilterEq,
      hSub (fun S : Finset (Fin n) => Odd S.card)
        (fun S => (Module.finrank ℝ (sectorKernelSlice V X t (e S)) : ℤ)),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro S hS
    have hOd : Odd S.card := (Finset.mem_filter.mp hS).2
    rw [hOd.neg_one_pow]
    ring
  rw [hEvenSum, hOddSum, sub_eq_add_neg]

end IndexTheorem

end InfoGeometry.KK.QuasilatticeBooleanChiralityIndexBridge
