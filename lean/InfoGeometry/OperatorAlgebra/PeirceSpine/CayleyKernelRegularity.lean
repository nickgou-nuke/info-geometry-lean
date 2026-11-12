/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.OnShellKernel
import InfoGeometry.Singular.MoorePenroseSquareZero

/-!
# Algebraic regularity and the kernel-preserving Cayley numerator

Three-square star faithfulness makes `1 + genV` left regular without any
norm, inverse, or ambient centrality premise. On the idempotent locus,
properness of star makes the upper arrow a partial isometry. The resulting
Cayley conjugation flips the paired support and retains the unpaired cut.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The polynomial numerator of the Cayley transform. No inverse is used. -/
def cayleyKernelNumerator (P A C : B) : B :=
  1 - genV P A C + (2 : ℤ) • genJ P A C

/-- Its opposite-chirality polynomial partner. -/
def cayleyKernelNumeratorConj (P A C : B) : B :=
  1 - genV P A C - (2 : ℤ) • genJ P A C

/-- Both Cayley numerators are already in the generated Peirce ring. -/
theorem cayleyKernelNumerator_mem_generated (P A C : B) :
    cayleyKernelNumerator P A C ∈ generatedPeirceRing P A C := by
  unfold cayleyKernelNumerator
  exact (generatedPeirceRing P A C).add_mem
    ((generatedPeirceRing P A C).sub_mem (generatedPeirceRing P A C).one_mem
      (genV_mem_generatedPeirceRing P A C))
    ((generatedPeirceRing P A C).zsmul_mem (genJ_mem_generatedPeirceRing P A C) 2)

variable {P : B} (hP : P * P = P)

/-- The Pythagorean identity retains the full noncommutative corner product. -/
theorem cayleyKernelNumerator_products (hP : P * P = P) (A C : B) :
    cayleyKernelNumerator P A C * cayleyKernelNumeratorConj P A C =
      (1 + genV P A C) ^ 2 ∧
    cayleyKernelNumeratorConj P A C * cayleyKernelNumerator P A C =
      (1 + genV P A C) ^ 2 := by
  simp only [cayleyKernelNumerator, cayleyKernelNumeratorConj, pow_two, two_smul]
  constructor <;> peirce_nf hP

section Star

variable [StarRing B]

/-- The polynomial partner is the adjoint in a self-adjoint cut. -/
theorem star_cayleyKernelNumerator (hPs : star P = P) (A : B) :
    star (cayleyKernelNumerator P A (star A)) =
      cayleyKernelNumeratorConj P A (star A) := by
  simp only [cayleyKernelNumerator, cayleyKernelNumeratorConj, star_add,
    star_one, star_genV hPs, star_zsmul, star_genJ hPs, smul_neg,
    sub_eq_add_neg, star_neg]

/-- Both star products equal the same polynomial denominator square. -/
theorem cayleyKernelNumerator_star_products (hP : P * P = P) (hPs : star P = P) (A : B) :
    star (cayleyKernelNumerator P A (star A)) *
        cayleyKernelNumerator P A (star A) = (1 + genV P A (star A)) ^ 2 ∧
    cayleyKernelNumerator P A (star A) *
        star (cayleyKernelNumerator P A (star A)) = (1 + genV P A (star A)) ^ 2 := by
  rw [star_cayleyKernelNumerator hPs]
  exact ⟨(cayleyKernelNumerator_products hP A (star A)).2,
    (cayleyKernelNumerator_products hP A (star A)).1⟩

/-- Three-square cancellation implies ordinary properness of star. -/
theorem star_proper_of_three_square_faithful
    (hfaith : ∀ X Y Z : B, star X * X + star Y * Y + star Z * Z = 0 → X = 0)
    (X : B) (hX : star X * X = 0) : X = 0 := by
  apply hfaith X 0 0
  simpa only [star_zero, zero_mul, add_zero] using hX

/-- The shifted metric has no left zero divisor in a three-square faithful
star ring. This needs no idempotence assumption on the cut. -/
theorem one_add_genV_mul_eq_zero_iff (hPs : star P = P)
    (hfaith : ∀ X Y Z : B, star X * X + star Y * Y + star Z * Z = 0 → X = 0)
    (A X : B) : (1 + genV P A (star A)) * X = 0 ↔ X = 0 := by
  constructor
  · intro hX
    apply hfaith X (conePlus P A * X) (coneMinus P (star A) * X)
    have hmul := congrArg (fun Y : B => star X * Y) hX
    have hgram :
        star X * X + star (conePlus P A * X) * (conePlus P A * X) +
          star (coneMinus P (star A) * X) * (coneMinus P (star A) * X) =
        star X * ((1 + genV P A (star A)) * X) := by
      simp only [star_mul, star_conePlus hPs, star_coneMinus hPs, star_star,
        genV, anticomm]
      noncomm_ring
    rw [hgram]
    simpa only [mul_zero] using hmul
  · rintro rfl
    exact mul_zero _

/-- All powers of the shifted metric are left regular. -/
theorem one_add_genV_pow_mul_eq_zero_iff (hPs : star P = P)
    (hfaith : ∀ X Y Z : B, star X * X + star Y * Y + star Z * Z = 0 → X = 0)
    (A : B) (n : ℕ) (X : B) :
    (1 + genV P A (star A)) ^ n * X = 0 ↔ X = 0 := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [pow_succ', mul_assoc, one_add_genV_mul_eq_zero_iff hPs hfaith, hn]

/-- Multiplication by the shifted metric is injective. -/
theorem one_add_genV_mul_injective (hPs : star P = P)
    (hfaith : ∀ X Y Z : B, star X * X + star Y * Y + star Z * Z = 0 → X = 0)
    (A : B) : Function.Injective (fun X : B => (1 + genV P A (star A)) * X) := by
  intro X Y hXY
  change (1 + genV P A (star A)) * X = (1 + genV P A (star A)) * Y at hXY
  apply sub_eq_zero.mp
  apply (one_add_genV_mul_eq_zero_iff hPs hfaith A (X - Y)).mp
  rw [mul_sub, hXY, sub_self]

/-- Proper star excludes a nilpotent residual arrow on the metric's kernel. -/
theorem onShell_kernel_mul_conePlus_eq_zero (hP : P * P = P) (hPs : star P = P)
    (hproper : ∀ X : B, star X * X = 0 → X = 0) (A : B)
    (hV : genV P A (star A) * genV P A (star A) = genV P A (star A)) :
    (1 - genV P A (star A)) * conePlus P A = 0 := by
  have hkill := (onShell_kernel_cycle_products hP A (star A) hV).2.1
  have hstar : star (1 - genV P A (star A)) = 1 - genV P A (star A) := by
    rw [star_sub, star_one, star_genV hPs]
  have hnorm :
      ((1 - genV P A (star A)) * conePlus P A) *
        star ((1 - genV P A (star A)) * conePlus P A) = 0 := by
    rw [star_mul, star_conePlus hPs, hstar]
    calc
      ((1 - genV P A (star A)) * conePlus P A) *
          (coneMinus P (star A) * (1 - genV P A (star A))) =
        ((1 - genV P A (star A)) * qgtPlus P A (star A)) *
          (1 - genV P A (star A)) := by
            simp only [qgtPlus, mul_assoc]
      _ = 0 := by rw [hkill, zero_mul]
  have hz := hproper (star ((1 - genV P A (star A)) * conePlus P A))
    (by simpa only [star_star] using hnorm)
  have hz' := congrArg star hz
  simpa only [star_star, star_zero] using hz'

/-- On shell, properness proves the regularity equation; it is not assumed. -/
theorem onShell_conePlus_inner_regular (hP : P * P = P) (hPs : star P = P)
    (hproper : ∀ X : B, star X * X = 0 → X = 0) (A : B)
    (hV : genV P A (star A) * genV P A (star A) = genV P A (star A)) :
    conePlus P A * coneMinus P (star A) * conePlus P A = conePlus P A := by
  have hz := onShell_kernel_mul_conePlus_eq_zero hP hPs hproper A hV
  have heq : (1 - genV P A (star A)) * conePlus P A =
      conePlus P A - conePlus P A * coneMinus P (star A) * conePlus P A := by
    peirce_nf hP
  rw [heq] at hz
  exact (sub_eq_zero.mp hz).symm

/-- The actual Peirce arrows form a Moore-Penrose pair on shell. -/
theorem onShell_isMoorePenroseInverse (hP : P * P = P) (hPs : star P = P)
    (hproper : ∀ X : B, star X * X = 0 → X = 0) (A : B)
    (hV : genV P A (star A) * genV P A (star A) = genV P A (star A)) :
    InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
      (conePlus P A) (coneMinus P (star A)) := by
  have hn := onShell_conePlus_inner_regular hP hPs hproper A hV
  refine ⟨hn, ?_, ?_, ?_⟩
  · have hb := congrArg star hn
    simpa only [star_mul, star_conePlus hPs, star_coneMinus hPs, star_star,
      mul_assoc] using hb
  · simp only [star_mul, star_conePlus hPs, star_coneMinus hPs, star_star]
  · simp only [star_mul, star_conePlus hPs, star_coneMinus hPs, star_star]

/-- The native Moore-Penrose support theorem now applies to the submitted
Peirce arrows, retaining the residual kernel in all four products. -/
theorem onShell_kernel_annihilates_arrows (hP : P * P = P) (hPs : star P = P)
    (hproper : ∀ X : B, star X * X = 0 → X = 0) (A : B)
    (hV : genV P A (star A) * genV P A (star A) = genV P A (star A)) :
    conePlus P A * (1 - genV P A (star A)) = 0 ∧
    (1 - genV P A (star A)) * conePlus P A = 0 ∧
    coneMinus P (star A) * (1 - genV P A (star A)) = 0 ∧
    (1 - genV P A (star A)) * coneMinus P (star A) = 0 := by
  exact InfoGeometry.Singular.MoorePenroseSquareZero.null_annihilates
    (onShell_isMoorePenroseInverse hP hPs hproper A hV)
    (conePlus_mul_conePlus hP A A)

/-- The on-shell partition consists of native self-adjoint projections. -/
theorem onShell_three_star_projections (hP : P * P = P) (hPs : star P = P)
    (hproper : ∀ X : B, star X * X = 0 → X = 0) (A : B)
    (hV : genV P A (star A) * genV P A (star A) = genV P A (star A)) :
    IsStarProjection (qgtPlus P A (star A)) ∧
    IsStarProjection (qgtMinus P A (star A)) ∧
    IsStarProjection (1 - genV P A (star A)) :=
  InfoGeometry.Singular.MoorePenroseSquareZero.three_star_projections
    (onShell_isMoorePenroseInverse hP hPs hproper A hV)
    (conePlus_mul_conePlus hP A A)

/-- The numerator conjugates the seed into the flipped support plus its
original unpaired kernel corner, with the denominator cleared internally. -/
theorem onShell_cayleyKernelNumerator_partial_flip (hP : P * P = P) (hPs : star P = P)
    (hproper : ∀ X : B, star X * X = 0 → X = 0) (A : B)
    (hV : genV P A (star A) * genV P A (star A) = genV P A (star A)) :
    cayleyKernelNumerator P A (star A) * P *
        star (cayleyKernelNumerator P A (star A)) =
      (1 + genV P A (star A)) ^ 2 *
        (qgtMinus P A (star A) + P * (1 - genV P A (star A))) := by
  obtain ⟨hn, hm⟩ := (genV_idempotent_iff_qgt_idempotent hP A (star A)).mp hV
  obtain ⟨_, h0n, _, h0m⟩ := onShell_kernel_annihilates_arrows hP hPs hproper A hV
  have h0phi : (1 - genV P A (star A)) * genPhi P A (star A) = 0 := by
    simp only [genPhi, mul_add, h0n, h0m, add_zero]
  have hexp : cayleyKernelNumerator P A (star A) * P *
      cayleyKernelNumeratorConj P A (star A) =
      (1 - genV P A (star A)) * (1 - genV P A (star A)) * P +
        (4 : ℤ) • qgtMinus P A (star A) -
        (2 : ℤ) • ((1 - genV P A (star A)) * genPhi P A (star A)) := by
    simp only [cayleyKernelNumerator, cayleyKernelNumeratorConj, qgtMinus,
      two_smul]
    peirce_nf hP
  rw [star_cayleyKernelNumerator hPs, hexp, h0phi, smul_zero, sub_zero,
    onShell_kernel_idempotent A (star A) hV]
  have hPV : P * genV P A (star A) = genV P A (star A) * P := by
    peirce_nf hP
  have hVm : genV P A (star A) * qgtMinus P A (star A) =
      qgtMinus P A (star A) := by
    change (qgtPlus P A (star A) + qgtMinus P A (star A)) *
      qgtMinus P A (star A) = _
    rw [add_mul, (qgt_cycles_orthogonal hP A (star A)).1, hm, zero_add]
  have he : (1 + genV P A (star A)) ^ 2 *
      (qgtMinus P A (star A) + P * (1 - genV P A (star A))) =
      (1 - genV P A (star A)) * P + (4 : ℤ) • qgtMinus P A (star A) := by
    have hVVP : genV P A (star A) * (genV P A (star A) * P) =
        genV P A (star A) * P := by rw [← mul_assoc, hV]
    simp only [pow_two, show (4 : ℤ) • qgtMinus P A (star A) =
      qgtMinus P A (star A) + qgtMinus P A (star A) +
        qgtMinus P A (star A) + qgtMinus P A (star A) by abel]
    noncomm_ring [hPV, hV, hVm, hVVP]
  exact he.symm

end Star

end InfoGeometry.OperatorAlgebra.PeirceSpine
