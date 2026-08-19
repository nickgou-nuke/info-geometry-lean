import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.Algebra.CuntzSuperalgebra

/-!
# Bost-Connes Modular Automorphism Group σ_t(S_i) = p_i^{it} S_i

One-parameter group of ℂ-algebra automorphisms on CuntzAlg n.
Proved: σ_{t+s}=σ_t∘σ_s, σ_0=id, fixes projectors. Zero sorries.
-/

open InfoGeometry.Algebra.CuntzTensorQuotient
open Complex

noncomputable section

namespace InfoGeometry.Algebra.CuntzModularAutomorphism

def modularPhase (p : ℕ) (t : ℝ) : ℂ := Complex.exp (I * (t : ℂ) * Real.log (p : ℝ))
def modularPhaseInv (p : ℕ) (t : ℝ) : ℂ := Complex.exp (-(I * (t : ℂ) * Real.log (p : ℝ)))

@[simp] lemma modularPhase_zero (p : ℕ) : modularPhase p 0 = 1 := by simp [modularPhase]
@[simp] lemma modularPhaseInv_zero (p : ℕ) : modularPhaseInv p 0 = 1 := by simp [modularPhaseInv]

@[simp] lemma modularPhase_add (p : ℕ) (t s : ℝ) : modularPhase p (t + s) = modularPhase p t * modularPhase p s := by
  dsimp [modularPhase]
  have h : I * ((t + s : ℝ) : ℂ) * Real.log (p : ℝ) = (I * (t : ℂ) * Real.log (p : ℝ)) + (I * (s : ℂ) * Real.log (p : ℝ)) := by
    push_cast; ring_nf
  rw [h, Complex.exp_add]

@[simp] lemma modularPhaseInv_add (p : ℕ) (t s : ℝ) : modularPhaseInv p (t + s) = modularPhaseInv p t * modularPhaseInv p s := by
  dsimp [modularPhaseInv]
  have h : -(I * ((t + s : ℝ) : ℂ) * Real.log (p : ℝ)) = (-(I * (t : ℂ) * Real.log (p : ℝ))) + (-(I * (s : ℂ) * Real.log (p : ℝ))) := by
    push_cast; ring_nf
  rw [h, Complex.exp_add]

@[simp] lemma modularPhase_mul_inv (p : ℕ) (t : ℝ) : modularPhase p t * modularPhaseInv p t = 1 := by
  dsimp [modularPhase, modularPhaseInv]
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

noncomputable def modularOnFree (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) : CuntzFree n →ₗ[ℂ] CuntzTensor n :=
  (Finsupp.lsum ℂ) (λ (g : Fin n × Bool) =>
    (LinearMap.smulRight (LinearMap.id (R := ℂ)) (TensorAlgebra.ι ℂ (Finsupp.single g 1))).comp
      (LinearMap.mulRight ℂ (if g.2 then modularPhaseInv (primes g.1) t else modularPhase (primes g.1) t)))

lemma modularOnFree_single (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) (i : Fin n) (b : Bool) (c : ℂ) :
    modularOnFree n primes t (Finsupp.single (i, b) c) =
    (c * (if b then modularPhaseInv (primes i) t else modularPhase (primes i) t)) • gen n i b := by
  simp [modularOnFree, gen, Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, LinearMap.id_apply]

noncomputable def sigmaTensor (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) : CuntzTensor n →ₐ[ℂ] CuntzTensor n :=
  TensorAlgebra.lift ℂ (modularOnFree n primes t)

lemma sigmaTensor_S (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) (i : Fin n) :
    sigmaTensor n primes t (S n i) = modularPhase (primes i) t • S n i := by
  calc
    sigmaTensor n primes t (S n i) = modularOnFree n primes t (Finsupp.single (i, false) 1) := by
      dsimp [sigmaTensor, S, gen]; rw [TensorAlgebra.lift_ι_apply]
    _ = (1 * (if false then modularPhaseInv (primes i) t else modularPhase (primes i) t)) • gen n i false := by
      rw [modularOnFree_single]
    _ = (1 * modularPhase (primes i) t) • gen n i false := by simp
    _ = (1 * modularPhase (primes i) t) • S n i := rfl
    _ = modularPhase (primes i) t • S n i := by rw [one_mul]

lemma sigmaTensor_Sdag (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) (i : Fin n) :
    sigmaTensor n primes t (Sdag n i) = modularPhaseInv (primes i) t • Sdag n i := by
  calc
    sigmaTensor n primes t (Sdag n i) = modularOnFree n primes t (Finsupp.single (i, true) 1) := by
      dsimp [sigmaTensor, Sdag, gen]; rw [TensorAlgebra.lift_ι_apply]
    _ = (1 * (if true then modularPhaseInv (primes i) t else modularPhase (primes i) t)) • gen n i true := by
      rw [modularOnFree_single]
    _ = (1 * modularPhaseInv (primes i) t) • gen n i true := by simp
    _ = (1 * modularPhaseInv (primes i) t) • Sdag n i := rfl
    _ = modularPhaseInv (primes i) t • Sdag n i := by rw [one_mul]

@[simp] lemma sigmaTensor_zero (n : ℕ) (primes : Fin n → ℕ) :
    sigmaTensor n primes 0 = AlgHom.id ℂ (CuntzTensor n) := by
  ext v; dsimp [sigmaTensor, modularOnFree]; simp [modularPhase_zero, modularPhaseInv_zero]

lemma sigmaTensor_add_aux (n : ℕ) (primes : Fin n → ℕ) (t s : ℝ) (x : CuntzTensor n) :
    sigmaTensor n primes (t + s) x = (sigmaTensor n primes t).comp (sigmaTensor n primes s) x := by
  induction x using TensorAlgebra.induction with
  | algebraMap r => dsimp [sigmaTensor]; simp [modularPhase_add]
  | ι v =>
      refine Finsupp.induction_linear v (by simp [sigmaTensor, AlgHom.comp_apply]) ?_ ?_
      · intro v₁ v₂ hv₁ hv₂
        dsimp [sigmaTensor, AlgHom.comp_apply] at *
        simp [map_add, hv₁, hv₂]
      · intro g c; rcases g with ⟨i, b⟩; cases b with
        | false =>
            dsimp [sigmaTensor, AlgHom.comp_apply, gen]
            simp_rw [TensorAlgebra.lift_ι_apply]
            rw [modularOnFree_single, modularOnFree_single]
            rw [map_smul (TensorAlgebra.lift ℂ (modularOnFree n primes t))]
            dsimp [gen]; rw [TensorAlgebra.lift_ι_apply, modularOnFree_single]
            simp [gen, modularPhase_add, smul_smul, mul_comm, mul_left_comm, mul_assoc]
        | true =>
            dsimp [sigmaTensor, AlgHom.comp_apply, gen]
            simp_rw [TensorAlgebra.lift_ι_apply]
            rw [modularOnFree_single, modularOnFree_single]
            rw [map_smul (TensorAlgebra.lift ℂ (modularOnFree n primes t))]
            dsimp [gen]; rw [TensorAlgebra.lift_ι_apply, modularOnFree_single]
            simp [gen, modularPhaseInv_add, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  | mul x y hx hy => dsimp [sigmaTensor, AlgHom.comp_apply] at *; simp [map_mul, hx, hy]
  | add x y hx hy => dsimp [sigmaTensor, AlgHom.comp_apply] at *; simp [map_add, hx, hy]

theorem sigmaTensor_descent_condition (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) ⦃x y : CuntzTensor n⦄
    (h : CuntzRel n x y) : ((cuntzMk n).comp (sigmaTensor n primes t)) x = ((cuntzMk n).comp (sigmaTensor n primes t)) y := by
  rcases h with (⟨i, j⟩ | _)
  · dsimp [AlgHom.comp_apply]; rw [map_mul, sigmaTensor_S, sigmaTensor_Sdag, smul_mul_smul]
    by_cases hij : i = j
    · subst hij
      rw [mul_comm (modularPhaseInv (primes i) t), modularPhase_mul_inv, one_smul]
      simpa [map_one (sigmaTensor n primes t)] using
        RingQuot.mkAlgHom_rel ℂ (CuntzRel.orth i i)
    · have h0 : (cuntzMk n) (Sdag n i * S n j) = (cuntzMk n) 0 := by
        simpa [hij] using RingQuot.mkAlgHom_rel ℂ (CuntzRel.orth i j)
      calc
        (cuntzMk n) ((modularPhaseInv (primes i) t * modularPhase (primes j) t) • (Sdag n i * S n j))
            = (modularPhaseInv (primes i) t * modularPhase (primes j) t) • (cuntzMk n) (Sdag n i * S n j) := by rw [map_smul]
        _ = (modularPhaseInv (primes i) t * modularPhase (primes j) t) • (cuntzMk n) 0 := by rw [h0]
        _ = (cuntzMk n) 0 := by simp
        _ = (cuntzMk n) ((sigmaTensor n primes t) (if i = j then (1 : CuntzTensor n) else (0 : CuntzTensor n))) := by
          simp [hij]
  · dsimp [AlgHom.comp_apply]
    calc
      (cuntzMk n) (sigmaTensor n primes t (∑ i : Fin n, S n i * Sdag n i))
          = (cuntzMk n) (∑ i : Fin n, sigmaTensor n primes t (S n i * Sdag n i)) := by rw [map_sum]
      _ = (cuntzMk n) (∑ i : Fin n, sigmaTensor n primes t (S n i) * sigmaTensor n primes t (Sdag n i)) := by
        simp_rw [map_mul]
      _ = (cuntzMk n) (∑ i : Fin n, (modularPhase (primes i) t • S n i) * (modularPhaseInv (primes i) t • Sdag n i)) := by
        simp [sigmaTensor_S, sigmaTensor_Sdag]
      _ = (cuntzMk n) (∑ i : Fin n, (modularPhase (primes i) t * modularPhaseInv (primes i) t) • (S n i * Sdag n i)) := by
        refine congrArg (cuntzMk n) (Finset.sum_congr rfl (λ i _ => by rw [smul_mul_smul]))
      _ = (cuntzMk n) (∑ i : Fin n, (1 : ℂ) • (S n i * Sdag n i)) := by
        refine congrArg (cuntzMk n) (Finset.sum_congr rfl (λ i _ => by rw [modularPhase_mul_inv]))
      _ = (cuntzMk n) (∑ i : Fin n, S n i * Sdag n i) := by simp
      _ = (cuntzMk n) 1 := RingQuot.mkAlgHom_rel ℂ (CuntzRel.ranges_sum_one (n := n))
      _ = (cuntzMk n) ((sigmaTensor n primes t) 1) := by rw [map_one (sigmaTensor n primes t)]

noncomputable def sigma (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) : CuntzAlg n →ₐ[ℂ] CuntzAlg n :=
  (RingQuot.liftAlgHom ℂ) ⟨ (cuntzMk n).comp (sigmaTensor n primes t),
    sigmaTensor_descent_condition n primes t ⟩

lemma sigma_mk' (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) (x : CuntzTensor n) :
    sigma n primes t ((RingQuot.mkAlgHom ℂ (CuntzRel n)) x) = (RingQuot.mkAlgHom ℂ (CuntzRel n)) (sigmaTensor n primes t x) := by
  dsimp [sigma, cuntzMk]
  simp [RingQuot.liftAlgHom_mkAlgHom_apply, AlgHom.comp_apply]

@[simp] lemma sigma_cuntzS (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) (i : Fin n) :
    sigma n primes t (cuntzS n i) = modularPhase (primes i) t • cuntzS n i := by
  dsimp [cuntzS, cuntzMk]; rw [sigma_mk', sigmaTensor_S]; simp

@[simp] lemma sigma_cuntzSdag (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) (i : Fin n) :
    sigma n primes t (cuntzSdag n i) = modularPhaseInv (primes i) t • cuntzSdag n i := by
  dsimp [cuntzSdag, cuntzMk]; rw [sigma_mk', sigmaTensor_Sdag]; simp

@[simp] theorem sigma_fixes_projector (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) (i : Fin n) :
    sigma n primes t (cuntzS n i * cuntzSdag n i) = cuntzS n i * cuntzSdag n i := by
  calc
    sigma n primes t (cuntzS n i * cuntzSdag n i) = sigma n primes t (cuntzS n i) * sigma n primes t (cuntzSdag n i) := by rw [map_mul]
    _ = (modularPhase (primes i) t • cuntzS n i) * (modularPhaseInv (primes i) t • cuntzSdag n i) := by rw [sigma_cuntzS, sigma_cuntzSdag]
    _ = (modularPhase (primes i) t * modularPhaseInv (primes i) t) • (cuntzS n i * cuntzSdag n i) := by rw [smul_mul_smul]
    _ = (1 : ℂ) • (cuntzS n i * cuntzSdag n i) := by rw [modularPhase_mul_inv]
    _ = cuntzS n i * cuntzSdag n i := by simp

@[simp] theorem sigma_add (n : ℕ) (primes : Fin n → ℕ) (t s : ℝ) :
    sigma n primes (t + s) = (sigma n primes t).comp (sigma n primes s) := by
  apply DFunLike.ext; intro x
  rcases RingQuot.mkAlgHom_surjective ℂ (CuntzRel n) x with ⟨y, rfl⟩
  rw [AlgHom.comp_apply, sigma_mk', sigma_mk' n primes s y, sigma_mk' n primes t (sigmaTensor n primes s y),
    sigmaTensor_add_aux n primes t s y, AlgHom.comp_apply]

@[simp] theorem sigma_zero (n : ℕ) (primes : Fin n → ℕ) :
    sigma n primes (0 : ℝ) = AlgHom.id ℂ (CuntzAlg n) := by
  apply DFunLike.ext; intro x
  rcases RingQuot.mkAlgHom_surjective ℂ (CuntzRel n) x with ⟨y, rfl⟩
  rw [sigma_mk', sigmaTensor_zero]; rfl

/-!
### Automorphism upgrade

The additive flow law already proved for `sigma` supplies its inverse at
time `-t`.  Packaging that inverse as an `AlgEquiv` is an algebraic
automorphism statement only; it does not assert a C⋆-continuous modular
action or the existence of a KMS state.
-/

noncomputable def sigmaEquiv (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) :
    CuntzAlg n ≃ₐ[ℂ] CuntzAlg n :=
  AlgEquiv.ofAlgHom (sigma n primes t) (sigma n primes (-t)) (by
    rw [← sigma_add]
    simp) (by
    rw [← sigma_add]
    simp)

@[simp] theorem sigmaEquiv_apply (n : ℕ) (primes : Fin n → ℕ) (t : ℝ)
    (x : CuntzAlg n) :
    sigmaEquiv n primes t x = sigma n primes t x :=
  rfl

@[simp] theorem sigmaEquiv_apply_cuntzS (n : ℕ) (primes : Fin n → ℕ)
    (t : ℝ) (i : Fin n) :
    sigmaEquiv n primes t (cuntzS n i) =
      modularPhase (primes i) t • cuntzS n i := by
  exact sigma_cuntzS n primes t i

@[simp] theorem sigmaEquiv_fixes_projector (n : ℕ) (primes : Fin n → ℕ)
    (t : ℝ) (i : Fin n) :
    sigmaEquiv n primes t (cuntzS n i * cuntzSdag n i) =
      cuntzS n i * cuntzSdag n i := by
  exact sigma_fixes_projector n primes t i

theorem sigmaEquiv_add_apply (n : ℕ) (primes : Fin n → ℕ)
    (t s : ℝ) (x : CuntzAlg n) :
    sigmaEquiv n primes (t + s) x =
      sigmaEquiv n primes t (sigmaEquiv n primes s x) := by
  change sigma n primes (t + s) x = sigma n primes t (sigma n primes s x)
  rw [sigma_add]
  rfl

theorem sigmaEquiv_trans (n : ℕ) (primes : Fin n → ℕ) (t s : ℝ) :
    (sigmaEquiv n primes t).trans (sigmaEquiv n primes s) =
      sigmaEquiv n primes (t + s) := by
  apply AlgEquiv.ext
  intro x
  change sigma n primes s (sigma n primes t x) =
    sigma n primes (t + s) x
  have h := sigmaEquiv_add_apply n primes s t x
  simpa [add_comm] using h.symm

end InfoGeometry.Algebra.CuntzModularAutomorphism
