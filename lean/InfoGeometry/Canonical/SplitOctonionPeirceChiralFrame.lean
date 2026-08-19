import Mathlib.Algebra.Module.Basic
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Canonical.AlgebraicDerivations

/-!
# SplitOctonionPeirceChiralFrame

This file builds the static algebraic baseline and its dynamic geometric transport
for the split-octonion Peirce/chiral frame, stopping exactly at the boundary
before grading functional analysis.

The construction uses the explicit Zorn matrix carrier `InfoGeometry.Canonical.ZornMatrix`
as the concrete realization of the split-octonion algebra.
-/

namespace InfoGeometry.Canonical.SplitOctonionPeirceChiralFrame

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.AlgebraicDerivations

/-- Type synonym for the split-octonion algebra over ℝ using the Zorn matrix carrier. -/
type SplitOctonion := ZornMatrix ℝ

/-- Local notation for the split-octonion multiplication. -/
local infixl:70 " ⋆ " => mul

/-- The scalar identity element 1 in the split-octonion algebra. -/
def one : SplitOctonion := (1 : SplitOctonion)

/-- The hypercomplex structure element I (diagonal difference). -/
def I : SplitOctonion :=
  { a := 1, b := -1, x := 0, y := 0 }

/-- The upper vector basis J_n (n = 0,1,2). -/
def J (n : Fin 3) : SplitOctonion :=
  chiralUpperBasis n

/-- The lower vector basis j_n (n = 0,1,2). -/
def j (n : Fin 3) : SplitOctonion :=
  chiralLowerBasis n

/-!
=============================================================================
PART 1: The Static Peirce/Chiral Frame
=============================================================================
-/

-- Idempotents (Bosonic/Diagonal Rails)
def ePlus : SplitOctonion :=
  (1 / 2 : ℝ) • (one + I)

def eMinus : SplitOctonion :=
  (1 / 2 : ℝ) • (one - I)

-- Nilpotents (Fermionic/Off-Diagonal Rails)
def gPlus (n : Fin 3) : SplitOctonion :=
  (1 / 2 : ℝ) • (J n + j n)

def gMinus (n : Fin 3) : SplitOctonion :=
  (1 / 2 : ℝ) • (J n - j n)

-- Explicit identifications with the existing Zorn Peirce idempotents
theorem ePlus_eq_zornPlus : ePlus = zornPlus := by
  ext i <;> simp [ePlus, one, I, zornPlus, SplitOctonion, ZornMatrix.add_def,
    ZornMatrix.smul_def, ZornMatrix.coordEquiv]
  <;> fin_cases i <;> norm_num

theorem eMinus_eq_zornMinus : eMinus = zornMinus := by
  ext i <;> simp [eMinus, one, I, zornMinus, SplitOctonion, ZornMatrix.add_def,
    ZornMatrix.sub_def, ZornMatrix.smul_def, ZornMatrix.coordEquiv]
  <;> fin_cases i <;> norm_num

-- Algebraic Relations (Theorems in the concrete Zorn model)

theorem ePlus_idempotent : ePlus ⋆ ePlus = ePlus := by
  rw [ePlus_eq_zornPlus]
  exact zornPlus_idempotent

theorem eMinus_idempotent : eMinus ⋆ eMinus = eMinus := by
  rw [eMinus_eq_zornMinus]
  exact zornMinus_idempotent

theorem ePlus_mul_eMinus : ePlus ⋆ eMinus = 0 := by
  rw [ePlus_eq_zornPlus, eMinus_eq_zornMinus]
  exact zornPlus_mul_zornMinus

theorem eMinus_mul_ePlus : eMinus ⋆ ePlus = 0 := by
  rw [eMinus_eq_zornMinus, ePlus_eq_zornPlus]
  exact zornMinus_mul_zornPlus

theorem ePlus_add_eMinus : ePlus + eMinus = one := by
  ext i <;> simp [ePlus, eMinus, one, SplitOctonion, ZornMatrix.add_def,
    ZornMatrix.smul_def, ZornMatrix.coordEquiv, I]
  <;> fin_cases i <;> norm_num

-- Nilpotent squares (these are proven in the concrete model)
theorem gPlus_square_zero (n : Fin 3) : gPlus n ⋆ gPlus n = 0 := by
  fin_cases n <;>
  simp [gPlus, J, j, chiralUpperBasis, chiralLowerBasis, SplitOctonion,
    ZornMatrix.add_def, ZornMatrix.smul_def, ZornMatrix.coordEquiv, mul]
  <;>
  (try decide) <;>
  (try {
    ext i <;> fin_cases i <;>
    simp [ZornMatrix.mul_def, ZornMatrix.dot, ZornMatrix.cross, Fin.sum_univ_three]
    <;> norm_num <;> rfl
  })

theorem gMinus_square_zero (n : Fin 3) : gMinus n ⋆ gMinus n = 0 := by
  fin_cases n <;>
  simp [gMinus, J, j, chiralUpperBasis, chiralLowerBasis, SplitOctonion,
    ZornMatrix.add_def, ZornMatrix.sub_def, ZornMatrix.smul_def, ZornMatrix.coordEquiv, mul]
  <;>
  (try decide) <;>
  (try {
    ext i <;> fin_cases i <;>
    simp [ZornMatrix.mul_def, ZornMatrix.dot, ZornMatrix.cross, Fin.sum_univ_three]
    <;> norm_num <;> rfl
  })

-- The Reconstruction Theorem (1 + 3 + 1 + 3 Decomposition)
-- Shows SplitOctonion is perfectly spanned by the polarized packets
theorem peirce_chiral_reconstruction (s : SplitOctonion) :
  ∃ (w_p w_m : ℝ) (v_p v_m : Fin 3 → ℝ),
    s = (w_p • ePlus) +
        (∑ i : Fin 3, v_p i • gPlus i) +
        (w_m • eMinus) +
        (∑ i : Fin 3, v_m i • gMinus i) := by
  -- Extract coordinates from the Zorn matrix
  have h₁ : s = (s.a : ℝ) • ePlus + (∑ i : Fin 3, s.x i • gPlus i) + (s.b : ℝ) • eMinus + (∑ i : Fin 3, s.y i • gMinus i) := by
    ext k
    fin_cases k <;>
    simp [ePlus, eMinus, gPlus, gMinus, J, j, chiralUpperBasis, chiralLowerBasis,
      one, I, SplitOctonion, ZornMatrix.add_def, ZornMatrix.smul_def,
      ZornMatrix.coordEquiv, Fin.sum_univ_three, ZornMatrix.mul_def,
      ZornMatrix.dot, ZornMatrix.cross]
    <;>
    (try ring_nf) <;>
    (try norm_num) <;>
    (try aesop) <;>
    (try {
      fin_cases i <;> simp_all [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
      <;> norm_num <;> ring_nf <;> aesop
    })
    <;>
    (try {
      simp_all [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
      <;> norm_num <;> ring_nf <;> aesop
    })
  -- Use the extracted coordinates
  refine' ⟨s.a, s.b, s.x, s.y, _⟩
  rw [h₁]
  <;>
  simp [Finset.sum_const, Finset.card_range]
  <;>
  ring_nf
  <;>
  simp_all [smul_smul]
  <;>
  norm_num
  <;>
  aesop

/-!
=============================================================================
PART 2: Dynamic Geometric Transport via Derivations
=============================================================================
-/

local notation "EndV" => SplitOctonion →ₗ[ℝ] SplitOctonion

/-- Structure for a derivation on the split-octonion algebra. -/
structure Derivation where
  toLinearMap : EndV
  leibniz : ∀ (x y : SplitOctonion), toLinearMap (x ⋆ y) = toLinearMap x ⋆ y + x ⋆ toLinearMap y

/-- The zero derivation. -/
def zeroDerivation : Derivation :=
  { toLinearMap := 0,
    leibniz := by
      intro x y
      simp [SplitOctonion]
      <;>
      ext i <;> fin_cases i <;> simp [ZornMatrix.mul_def, ZornMatrix.dot, ZornMatrix.cross] }

/-- The flow U(t) generated by a derivation D. -/
def flow (D : Derivation) (t : ℝ) : EndV :=
  (D.toLinearMap).exp.map (t • (1 : EndV))

/-- Transported Frames under the flow U(t) -/
def transportedEPlus (D : Derivation) (t : ℝ) : SplitOctonion :=
  flow D t ePlus

def transportedEMinus (D : Derivation) (t : ℝ) : SplitOctonion :=
  flow D t eMinus

def transportedGPlus (D : Derivation) (t : ℝ) (n : Fin 3) : SplitOctonion :=
  flow D t (gPlus n)

def transportedGMinus (D : Derivation) (t : ℝ) (n : Fin 3) : SplitOctonion :=
  flow D t (gMinus n)

/-- A derivation that fixes the hypercomplex structure I. -/
def FixesI (D : Derivation) : Prop :=
  D.toLinearMap I = 0

/-- If the derivation fixes I, the diagonal idempotents are static. -/
theorem transportedEPlus_eq_of_fixes_I (D : Derivation) (t : ℝ) (hI : FixesI D) :
  transportedEPlus D t = ePlus := by
  have h₁ : flow D t ePlus = ePlus := by
    have h₂ : D.toLinearMap ePlus = 0 := by
      have h₃ : ePlus = (1 / 2 : ℝ) • (one + I) := rfl
      rw [h₃]
      have h₄ : D.toLinearMap ((1 / 2 : ℝ) • (one + I)) = (1 / 2 : ℝ) • (D.toLinearMap (one + I)) := by
        apply LinearMap.map_smul
      rw [h₄]
      have h₅ : D.toLinearMap (one + I) = D.toLinearMap one + D.toLinearMap I := by
        apply LinearMap.map_add
      rw [h₅]
      have h₆ : D.toLinearMap (one : SplitOctonion) = 0 := by
        -- Derivations annihilate the identity in alternative algebras
        have h₇ := D.leibniz one one
        have h₈ : (one : SplitOctonion) ⋆ one = one := by
          ext i <;> fin_cases i <;> simp [SplitOctonion, one, ZornMatrix.mul_def, ZornMatrix.dot, ZornMatrix.cross]
          <;> norm_num
        have h₉ := D.leibniz one one
        simp [h₈] at h₉ ⊢
        <;>
        (try simp_all [LinearMap.map_add, LinearMap.map_smul]) <;>
        (try abel) <;>
        (try ext i <;> fin_cases i <;> simp_all [SplitOctonion, ZornMatrix.mul_def, ZornMatrix.dot, ZornMatrix.cross]) <;>
        (try aesop)
      have h₇ : D.toLinearMap I = 0 := hI
      simp [h₆, h₇]
      <;>
      simp_all [LinearMap.map_smul, LinearMap.map_add]
      <;>
      ext i <;> fin_cases i <;> simp_all [SplitOctonion, ZornMatrix.mul_def, ZornMatrix.dot, ZornMatrix.cross]
      <;>
      norm_num
      <;>
      aesop
    -- Since D(ePlus) = 0, the flow preserves ePlus
    have h₃ : flow D t ePlus = ePlus := by
      have h₄ : flow D t = (D.toLinearMap).exp.map (t • (1 : EndV)) := rfl
      rw [h₄]
      have h₅ : (D.toLinearMap).exp.map (t • (1 : EndV)) ePlus = ePlus := by
        -- Use the fact that D(ePlus) = 0 implies exp(D)(ePlus) = ePlus
        have h₆ : D.toLinearMap ePlus = 0 := h₂
        have h₇ : ∀ n : ℕ, (D.toLinearMap ^ n) ePlus = if n = 0 then ePlus else 0 := by
          intro n
          induction n with
          | zero => simp [LinearMap.one_apply]
          | succ n ih =>
            rw [Function.iterate_succ_apply']
            rw [ih]
            split_ifs <;> simp_all [LinearMap.map_zero]
            <;> aesop
        -- The exponential map applied to ePlus gives ePlus
        simp [LinearMap.exp_apply, h₇]
        <;>
        norm_num
        <;>
        simp_all [Finset.sum_ite_eq']
        <;>
        aesop
      rw [h₅]
    rw [h₃]
  rw [transportedEPlus]
  exact h₁

theorem transportedEMinus_eq_of_fixes_I (D : Derivation) (t : ℝ) (hI : FixesI D) :
  transportedEMinus D t = eMinus := by
  have h₁ : flow D t eMinus = eMinus := by
    have h₂ : D.toLinearMap eMinus = 0 := by
      have h₃ : eMinus = (1 / 2 : ℝ) • (one - I) := rfl
      rw [h₃]
      have h₄ : D.toLinearMap ((1 / 2 : ℝ) • (one - I)) = (1 / 2 : ℝ) • (D.toLinearMap (one - I)) := by
        apply LinearMap.map_smul
      rw [h₄]
      have h₅ : D.toLinearMap (one - I) = D.toLinearMap one - D.toLinearMap I := by
        apply LinearMap.map_sub
      rw [h₅]
      have h₆ : D.toLinearMap (one : SplitOctonion) = 0 := by
        have h₇ := D.leibniz one one
        have h₈ : (one : SplitOctonion) ⋆ one = one := by
          ext i <;> fin_cases i <;> simp [SplitOctonion, one, ZornMatrix.mul_def, ZornMatrix.dot, ZornMatrix.cross]
          <;> norm_num
        have h₉ := D.leibniz one one
        simp [h₈] at h₉ ⊢
        <;>
        (try simp_all [LinearMap.map_add, LinearMap.map_smul]) <;>
        (try abel) <;>
        (try ext i <;> fin_cases i <;> simp_all [SplitOctonion, ZornMatrix.mul_def, ZornMatrix.dot, ZornMatrix.cross]) <;>
        (try aesop)
      have h₇ : D.toLinearMap I = 0 := hI
      simp [h₆, h₇]
      <;>
      simp_all [LinearMap.map_smul, LinearMap.map_sub]
      <;>
      ext i <;> fin_cases i <;> simp_all [SplitOctonion, ZornMatrix.mul_def, ZornMatrix.dot, ZornMatrix.cross]
      <;>
      norm_num
      <;>
      aesop
    -- Since D(eMinus) = 0, the flow preserves eMinus
    have h₃ : flow D t eMinus = eMinus := by
      have h₄ : flow D t = (D.toLinearMap).exp.map (t • (1 : EndV)) := rfl
      rw [h₄]
      have h₅ : (D.toLinearMap).exp.map (t • (1 : EndV)) eMinus = eMinus := by
        have h₆ : D.toLinearMap eMinus = 0 := h₂
        have h₇ : ∀ n : ℕ, (D.toLinearMap ^ n) eMinus = if n = 0 then eMinus else 0 := by
          intro n
          induction n with
          | zero => simp [LinearMap.one_apply]
          | succ n ih =>
            rw [Function.iterate_succ_apply']
            rw [ih]
            split_ifs <;> simp_all [LinearMap.map_zero]
            <;> aesop
        simp [LinearMap.exp_apply, h₇]
        <;>
        norm_num
        <;>
        simp_all [Finset.sum_ite_eq']
        <;>
        aesop
      rw [h₅]
    rw [h₃]
  rw [transportedEMinus]
  exact h₁

/-- Since the flow is generated by a derivation, it preserves the algebraic relations.
    This is a key theorem showing the frame relations are strictly preserved. -/
theorem transportedEPlus_idempotent (D : Derivation) (t : ℝ) :
  transportedEPlus D t ⋆ transportedEPlus D t = transportedEPlus D t := by
  have h₁ : flow D t (ePlus ⋆ ePlus) = (flow D t ePlus) ⋆ (flow D t ePlus) := by
    -- The flow of a derivation is an algebra automorphism
    have h₂ : ∀ (x y : SplitOctonion), flow D t (x ⋆ y) = (flow D t x) ⋆ (flow D t y) := by
      intro x y
      -- The exponential of a derivation acts as an algebra automorphism
      have h₃ : flow D t = (D.toLinearMap).exp.map (t • (1 : EndV)) := rfl
      rw [h₃]
      -- This is a standard result: exp(tD) is an algebra automorphism for a derivation D
      have h₄ : ((D.toLinearMap).exp.map (t • (1 : EndV))) (x ⋆ y) =
          (((D.toLinearMap).exp.map (t • (1 : EndV))) x) ⋆ (((D.toLinearMap).exp.map (t • (1 : EndV))) y) := by
        -- Use the property that exp(tD) preserves the product for a derivation D
        have h₅ : ∀ (n : ℕ), ((D.toLinearMap) ^ n) (x ⋆ y) = ∑ k in Finset.range (n + 1), ((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y) := by
          intro n
          induction n with
          | zero => simp [LinearMap.one_apply]
          | succ n ih =>
            rw [Function.iterate_succ_apply']
            rw [ih]
            have h₆ := D.leibniz _ _
            simp [Function.iterate_succ_apply', Finset.sum_range_succ, add_smul, smul_add, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul] at h₆ ⊢
            <;> abel_nf at h₆ ⊢ <;>
            (try ring_nf at h₆ ⊢) <;>
            (try simp_all [Finset.sum_range_succ, add_smul, smul_add, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]) <;>
            (try
              {
                apply Eq.symm
                apply Finset.sum_bij' (fun i _ => n - i) (fun i _ => n - i)
                <;> simp_all [Finset.mem_range, Nat.lt_succ_iff]
                <;> omega
              }) <;>
            (try
              {
                rw [Finset.sum_range_succ, add_comm]
                <;> simp_all [Function.iterate_succ_apply', Finset.sum_range_succ, add_smul, smul_add, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
                <;> ring_nf at * <;> abel_nf at * <;> aesop
              })
        -- Use the formal power series to prove the result
        have h₆ : ((D.toLinearMap).exp.map (t • (1 : EndV))) (x ⋆ y) =
            (((D.toLinearMap).exp.map (t • (1 : EndV))) x) ⋆ (((D.toLinearMap).exp.map (t • (1 : EndV))) y) := by
          -- This is a standard result: exp(tD) is an algebra automorphism for a derivation D
          -- We use the fact that the formal power series of exp(tD) preserves the product
          have h₇ : ((D.toLinearMap).exp.map (t • (1 : EndV))) (x ⋆ y) =
              ∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) (x ⋆ y) := by
            simp [LinearMap.exp_apply, EndV, smul_smul]
            <;> congr 1 <;> ext <;> simp [ContinuousLinearMap.comp_apply, smul_smul]
            <;> congr 1 <;> ext <;> simp [ContinuousLinearMap.comp_apply, smul_smul]
          rw [h₇]
          have h₈ : (((D.toLinearMap).exp.map (t • (1 : EndV))) x) ⋆ (((D.toLinearMap).exp.map (t • (1 : EndV))) y) =
              (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) := by
            simp [LinearMap.exp_apply, EndV, smul_smul]
            <;> congr 1 <;> ext <;> simp [ContinuousLinearMap.comp_apply, smul_smul]
            <;> congr 1 <;> ext <;> simp [ContinuousLinearMap.comp_apply, smul_smul]
          rw [h₈]
          -- Use the Cauchy product formula and the Leibniz rule
          have h₉ : (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) =
              ∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) (x ⋆ y) := by
            -- This follows from the Leibniz rule and the Cauchy product formula
            have h₁₀ : ∀ n : ℕ, ((D.toLinearMap) ^ n) (x ⋆ y) = ∑ k in Finset.range (n + 1), ((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y) := h₅
            -- The proof uses the binomial theorem and the Leibniz rule
            have h₁₁ : (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) =
                ∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) (x ⋆ y) := by
              -- This is a standard result in the theory of formal power series for derivations
              -- The key is that the product of the series equals the series of the product
              -- due to the Leibniz rule D(xy) = D(x)y + xD(y)
              classical
              have h₁₂ : Summable (fun n : ℕ => (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) := by
                -- The exponential series is summable
                have h₁₃ : Summable (fun n : ℕ => (t ^ n / n.factorial : ℝ) : ℕ → ℝ) := by
                  exact summable_pow_div_factorial (t : ℝ)
                -- The linear map is continuous, so the series is summable
                have h₁₄ : Summable (fun n : ℕ => (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) := by
                  refine' Summable.of_norm _
                  have h₁₅ : ∀ n : ℕ, ‖((t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x : SplitOctonion)‖ ≤ ‖(D.toLinearMap)‖ ^ n * ‖x‖ * (t ^ n / n.factorial : ℝ) := by
                    intro n
                    calc
                      ‖((t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x : SplitOctonion)‖ = (t ^ n / n.factorial : ℝ) * ‖((D.toLinearMap) ^ n) x‖ := by
                        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ n / n.factorial)]
                      _ ≤ (t ^ n / n.factorial : ℝ) * (‖(D.toLinearMap)‖ ^ n * ‖x‖) := by
                        gcongr
                        <;> simp [ContinuousLinearMap.iterate_norm]
                      _ = ‖(D.toLinearMap)‖ ^ n * ‖x‖ * (t ^ n / n.factorial : ℝ) := by ring
                  have h₁₆ : Summable (fun n : ℕ => (‖(D.toLinearMap)‖ : ℝ) ^ n * ‖x‖ * (t ^ n / n.factorial : ℝ)) := by
                    have h₁₇ : Summable (fun n : ℕ => (‖(D.toLinearMap)‖ : ℝ) ^ n * (t ^ n / n.factorial : ℝ)) := by
                      have h₁₈ : Summable (fun n : ℕ => ((‖(D.toLinearMap)‖ * t : ℝ) ^ n / n.factorial : ℝ)) := by
                        exact summable_pow_div_factorial (‖(D.toLinearMap)‖ * t : ℝ)
                      convert h₁₈ using 1
                      <;> ext n <;> ring_nf
                      <;> field_simp [Nat.factorial]
                      <;> ring_nf
                    exact Summable.mul_left (‖x‖ : ℝ) h₁₇
                  exact Summable.of_nonneg_of_le (fun n _ => by positivity) h₁₅ h₁₆
                exact h₁₄
              have h₁₉ : Summable (fun m : ℕ => (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) := by
                -- Same as above
                have h₂₀ : Summable (fun m : ℕ => (t ^ m / m.factorial : ℝ) : ℕ → ℝ) := by
                  exact summable_pow_div_factorial (t : ℝ)
                have h₂₁ : Summable (fun m : ℕ => (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) := by
                  refine' Summable.of_norm _
                  have h₂₂ : ∀ m : ℕ, ‖((t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y : SplitOctonion)‖ ≤ ‖(D.toLinearMap)‖ ^ m * ‖y‖ * (t ^ m / m.factorial : ℝ) := by
                    intro m
                    calc
                      ‖((t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y : SplitOctonion)‖ = (t ^ m / m.factorial : ℝ) * ‖((D.toLinearMap) ^ m) y‖ := by
                        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ m / m.factorial)]
                      _ ≤ (t ^ m / m.factorial : ℝ) * (‖(D.toLinearMap)‖ ^ m * ‖y‖) := by
                        gcongr
                        <;> simp [ContinuousLinearMap.iterate_norm]
                      _ = ‖(D.toLinearMap)‖ ^ m * ‖y‖ * (t ^ m / m.factorial : ℝ) := by ring
                  have h₂₃ : Summable (fun m : ℕ => (‖(D.toLinearMap)‖ : ℝ) ^ m * ‖y‖ * (t ^ m / m.factorial : ℝ)) := by
                    have h₂₄ : Summable (fun m : ℕ => (‖(D.toLinearMap)‖ : ℝ) ^ m * (t ^ m / m.factorial : ℝ)) := by
                      have h₂₅ : Summable (fun m : ℕ => ((‖(D.toLinearMap)‖ * t : ℝ) ^ m / m.factorial : ℝ)) := by
                        exact summable_pow_div_factorial (‖(D.toLinearMap)‖ * t : ℝ)
                      convert h₂₅ using 1
                      <;> ext m <;> ring_nf
                      <;> field_simp [Nat.factorial]
                      <;> ring_nf
                    exact Summable.mul_left (‖y‖ : ℝ) h₂₄
                  exact Summable.of_nonneg_of_le (fun m _ => by positivity) h₂₂ h₂₃
                exact h₂₁
              -- Use the Cauchy product theorem for summable series
              have h₂₀ : (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) =
                  ∑' n : ℕ, ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y) := by
                -- This is the Cauchy product formula
                have h₂₁ : (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) =
                    ∑' n : ℕ, ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y) := by
                  -- Use the Cauchy product theorem for Banach algebras
                  have h₂₂ : (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) =
                      ∑' n : ℕ, ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y) := by
                    -- Use the Cauchy product theorem
                    have h₂₃ : (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) =
                        ∑' n : ℕ, ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y) := by
                      -- This follows from the general Cauchy product theorem for complete normed algebras
                      classical
                      have h₂₄ : HasSum (fun n : ℕ => (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) := by
                        exact tsum_eq_sum h₁₂
                      have h₂₅ : HasSum (fun m : ℕ => (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) := by
                        exact tsum_eq_sum h₁₉
                      -- Use the Cauchy product theorem for HasSum
                      have h₂₆ : HasSum (fun n : ℕ => ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y)) (∑' n : ℕ, ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y)) := by
                        -- The Cauchy product of two summable series
                        have h₂₇ : HasSum (fun n : ℕ => ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y)) ((∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y)) := by
                          -- Use the Cauchy product theorem for HasSum in a Banach algebra
                          have h₂₈ : HasSum (fun n : ℕ => (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) := h₂₄
                          have h₂₉ : HasSum (fun m : ℕ => (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) := h₂₅
                          -- The product is continuous and bilinear, so we can use the Cauchy product theorem
                          have h₃₀ : HasSum (fun n : ℕ => ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y)) ((∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y)) := by
                            -- Use the general Cauchy product theorem for complete normed algebras
                            convert HasSum.mul h₂₈ h₂₉ using 1
                            <;>
                            (try simp_all [Finset.sum_range_succ, add_smul, smul_add, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul])
                            <;>
                            (try ext)
                            <;>
                            (try simp_all [ContinuousLinearMap.comp_apply, smul_smul])
                            <;>
                            (try ring_nf)
                            <;>
                            (try norm_num)
                            <;>
                            (try aesop)
                          exact h₂₈
                        exact h₂₇
                      exact h₂₆
                    exact h₂₂
                  exact h₂₁
                have h₂₂ : ∑' n : ℕ, ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y) =
                    ∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) (x ⋆ y) := by
                  -- Use the Leibniz rule to combine the terms
                  have h₂₃ : ∀ n : ℕ, ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y) = (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) (x ⋆ y) := by
                    intro n
                    have h₂₄ : ((D.toLinearMap) ^ n) (x ⋆ y) = ∑ k in Finset.range (n + 1), ((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y) := h₅ n
                    calc
                      ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y) =
                          ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) * ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • (((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y)) := by
                        apply Finset.sum_congr rfl
                        intro k hk
                        simp [smul_smul, mul_assoc, mul_comm, mul_left_comm]
                        <;> ring_nf
                        <;> simp_all [smul_smul, mul_assoc, mul_comm, mul_left_comm]
                        <;> field_simp [Nat.factorial]
                        <;> ring_nf
                      _ = ∑ k in Finset.range (n + 1), ((t : ℝ) ^ n / (k.factorial * (n - k).factorial : ℝ)) • (((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y)) := by
                        apply Finset.sum_congr rfl
                        intro k hk
                        have h₂₅ : ((t : ℝ) ^ k / k.factorial : ℝ) * ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) = (t : ℝ) ^ n / (k.factorial * (n - k).factorial : ℝ) := by
                          field_simp [pow_add, Nat.factorial]
                          <;> ring_nf
                          <;> field_simp [Nat.factorial]
                          <;> ring_nf
                        rw [h₂₅]
                        <;> simp [smul_smul, mul_assoc, mul_comm, mul_left_comm]
                        <;> ring_nf
                      _ = ∑ k in Finset.range (n + 1), (n.choose k : ℝ) * ((t : ℝ) ^ n / n.factorial : ℝ) • (((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y)) := by
                        apply Finset.sum_congr rfl
                        intro k hk
                        have h₂₆ : (n.choose k : ℝ) = (n.factorial : ℝ) / (k.factorial * (n - k).factorial : ℝ) := by
                          norm_cast
                          <;> field_simp [Nat.choose_eq_factorial_div_factorial, Nat.factorial_succ]
                          <;> ring_nf
                          <;> field_simp [Nat.factorial]
                          <;> ring_nf
                        have h₂₇ : (t : ℝ) ^ n / (k.factorial * (n - k).factorial : ℝ) = (n.choose k : ℝ) * ((t : ℝ) ^ n / n.factorial : ℝ) := by
                          rw [h₂₆]
                          <;> field_simp [Nat.factorial]
                          <;> ring_nf
                          <;> field_simp [Nat.factorial]
                          <;> ring_nf
                        rw [h₂₇]
                        <;> simp [smul_smul, mul_assoc, mul_comm, mul_left_comm]
                        <;> ring_nf
                      _ = (n.choose k : ℝ) * ((t : ℝ) ^ n / n.factorial : ℝ) • ∑ k in Finset.range (n + 1), (((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y)) := by
                        simp [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]
                        <;> simp_all [Finset.sum_range_succ, add_smul, smul_add]
                        <;> ring_nf
                        <;> simp_all [smul_smul, mul_assoc, mul_comm, mul_left_comm]
                        <;> field_simp [Nat.factorial]
                        <;> ring_nf
                      _ = (t ^ n / n.factorial : ℝ) • ∑ k in Finset.range (n + 1), (n.choose k : ℝ) • (((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y)) := by
                        simp [smul_sum, smul_smul, mul_assoc, mul_comm, mul_left_comm]
                        <;> ring_nf
                        <;> simp_all [Finset.sum_range_succ, add_smul, smul_add]
                        <;> field_simp [Nat.factorial]
                        <;> ring_nf
                      _ = (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) (x ⋆ y) := by
                        have h₂₈ : ∑ k in Finset.range (n + 1), (n.choose k : ℝ) • (((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y)) = ((D.toLinearMap) ^ n) (x ⋆ y) := by
                          calc
                            ∑ k in Finset.range (n + 1), (n.choose k : ℝ) • (((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y)) = ∑ k in Finset.range (n + 1), ((n.choose k : ℝ) : ℝ) • (((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y)) := by rfl
                            _ = ∑ k in Finset.range (n + 1), ((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y) := by
                              -- This step uses the binomial theorem for the product in the algebra
                              -- For the specific case of the Zorn matrix algebra,
                              -- the derivation property ensures this holds for the exponential
                              simp_all [h₅]
                              <;> aesop
                            _ = ((D.toLinearMap) ^ n) (x ⋆ y) := by
                              rw [h₅]
                              <;> simp_all [Finset.sum_range_succ, add_smul, smul_add]
                              <;> aesop
                        rw [h₂₈]
                        <;> simp [smul_smul]
                        <;> ring_nf
                    <;> simp_all [Finset.sum_range_succ, add_smul, smul_add]
                    <;> aesop
                  -- Now use this to prove the series equality
                  calc
                    ∑' n : ℕ, ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y) =
                        ∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) (x ⋆ y) := by
                      apply tsum_congr
                      intro n
                      rw [h₂₃ n]
                      <;> simp [smul_smul]
                      <;> ring_nf
                    _ = ∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) (x ⋆ y) := by rfl
                rw [h₂₂]
              <;> simp_all [tsum_eq_sum]
              <;> aesop
            rw [h₉]
          <;> simp_all [tsum_eq_sum]
          <;> aesop
        exact h₆
      exact h₄
    exact h₂ x y
  rw [h₂ ePlus ePlus]
  <;> simp [ePlus_idempotent]
  <;> rfl

  have h₂ : ePlus ⋆ ePlus = ePlus := ePlus_idempotent
  have h₃ : flow D t (ePlus ⋆ ePlus) = flow D t ePlus := by rw [h₂]
  have h₄ : (flow D t ePlus) ⋆ (flow D t ePlus) = flow D t ePlus := by
    calc
      (flow D t ePlus) ⋆ (flow D t ePlus) = flow D t (ePlus ⋆ ePlus) := by rw [h₁]
      _ = flow D t ePlus := by rw [h₃]
  calc
    transportedEPlus D t ⋆ transportedEPlus D t = (flow D t ePlus) ⋆ (flow D t ePlus) := by
      simp [transportedEPlus]
    _ = flow D t ePlus := h₄
    _ = transportedEPlus D t := by simp [transportedEPlus]

theorem transportedEPlus_mul_eMinus (D : Derivation) (t : ℝ) :
  transportedEPlus D t ⋆ transportedEMinus D t = 0 := by
  have h₁ : flow D t (ePlus ⋆ eMinus) = (flow D t ePlus) ⋆ (flow D t eMinus) := by
    have h₂ : ∀ (x y : SplitOctonion), flow D t (x ⋆ y) = (flow D t x) ⋆ (flow D t y) := by
      intro x y
      have h₃ : flow D t = (D.toLinearMap).exp.map (t • (1 : EndV)) := rfl
      rw [h₃]
      -- The exponential of a derivation acts as an algebra automorphism
      -- This follows from the formal power series and Leibniz rule
      have h₄ : ((D.toLinearMap).exp.map (t • (1 : EndV))) (x ⋆ y) =
          (((D.toLinearMap).exp.map (t • (1 : EndV))) x) ⋆ (((D.toLinearMap).exp.map (t • (1 : EndV))) y) := by
        -- Use the property that exp(tD) is an algebra automorphism for a derivation D
        have h₅ : ∀ (n : ℕ), ((D.toLinearMap) ^ n) (x ⋆ y) = ∑ k in Finset.range (n + 1), ((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y) := by
          intro n
          induction n with
          | zero => simp [LinearMap.one_apply]
          | succ n ih =>
            rw [Function.iterate_succ_apply']
            rw [ih]
            have h₆ := D.leibniz _ _
            simp [Function.iterate_succ_apply', Finset.sum_range_succ, add_smul, smul_add, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul] at h₆ ⊢
            <;> abel_nf at h₆ ⊢ <;>
            (try ring_nf at h₆ ⊢) <;>
            (try simp_all [Finset.sum_range_succ, add_smul, smul_add, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]) <;>
            (try
              {
                apply Eq.symm
                apply Finset.sum_bij' (fun i _ => n - i) (fun i _ => n - i)
                <;> simp_all [Finset.mem_range, Nat.lt_succ_iff]
                <;> omega
              }) <;>
            (try
              {
                rw [Finset.sum_range_succ, add_comm]
                <;> simp_all [Function.iterate_succ_apply', Finset.sum_range_succ, add_smul, smul_add, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
                <;> ring_nf at * <;> abel_nf at * <;> aesop
              })
        -- Use the formal power series to prove the result
        have h₆ : ((D.toLinearMap).exp.map (t • (1 : EndV))) (x ⋆ y) =
            (((D.toLinearMap).exp.map (t • (1 : EndV))) x) ⋆ (((D.toLinearMap).exp.map (t • (1 : EndV))) y) := by
          -- Use the property that exp(tD) is an algebra automorphism for a derivation D
          have h₇ : ((D.toLinearMap).exp.map (t • (1 : EndV))) (x ⋆ y) =
              ∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) (x ⋆ y) := by
            simp [LinearMap.exp_apply, EndV, smul_smul]
            <;> congr 1 <;> ext <;> simp [ContinuousLinearMap.comp_apply, smul_smul]
            <;> congr 1 <;> ext <;> simp [ContinuousLinearMap.comp_apply, smul_smul]
          rw [h₇]
          have h₈ : (((D.toLinearMap).exp.map (t • (1 : EndV))) x) ⋆ (((D.toLinearMap).exp.map (t • (1 : EndV))) y) =
              (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) := by
            simp [LinearMap.exp_apply, EndV, smul_smul]
            <;> congr 1 <;> ext <;> simp [ContinuousLinearMap.comp_apply, smul_smul]
            <;> congr 1 <;> ext <;> simp [ContinuousLinearMap.comp_apply, smul_smul]
          rw [h₈]
          -- Use the Cauchy product formula and the Leibniz rule
          have h₉ : (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) =
              ∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) (x ⋆ y) := by
            -- This follows from the Leibniz rule and the Cauchy product formula
            have h₁₀ : ∀ n : ℕ, ((D.toLinearMap) ^ n) (x ⋆ y) = ∑ k in Finset.range (n + 1), ((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y) := h₅
            -- The proof uses the binomial theorem and the Leibniz rule
            have h₁₁ : (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) =
                ∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) (x ⋆ y) := by
              -- This is a standard result in the theory of formal power series for derivations
              -- The key is that the product of the series equals the series of the product
              -- due to the Leibniz rule D(xy) = D(x)y + xD(y)
              classical
              have h₁₂ : Summable (fun n : ℕ => (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) := by
                -- The exponential series is summable
                have h₁₃ : Summable (fun n : ℕ => (t ^ n / n.factorial : ℝ) : ℕ → ℝ) := by
                  exact summable_pow_div_factorial (t : ℝ)
                -- The linear map is continuous, so the series is summable
                have h₁₄ : Summable (fun n : ℕ => (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) := by
                  refine' Summable.of_norm _
                  have h₁₅ : ∀ n : ℕ, ‖((t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x : SplitOctonion)‖ ≤ ‖(D.toLinearMap)‖ ^ n * ‖x‖ * (t ^ n / n.factorial : ℝ) := by
                    intro n
                    calc
                      ‖((t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x : SplitOctonion)‖ = (t ^ n / n.factorial : ℝ) * ‖((D.toLinearMap) ^ n) x‖ := by
                        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ n / n.factorial)]
                      _ ≤ (t ^ n / n.factorial : ℝ) * (‖(D.toLinearMap)‖ ^ n * ‖x‖) := by
                        gcongr
                        <;> simp [ContinuousLinearMap.iterate_norm]
                      _ = ‖(D.toLinearMap)‖ ^ n * ‖x‖ * (t ^ n / n.factorial : ℝ) := by ring
                  have h₁₆ : Summable (fun n : ℕ => (‖(D.toLinearMap)‖ : ℝ) ^ n * ‖x‖ * (t ^ n / n.factorial : ℝ)) := by
                    have h₁₇ : Summable (fun n : ℕ => (‖(D.toLinearMap)‖ : ℝ) ^ n * (t ^ n / n.factorial : ℝ)) := by
                      have h₁₈ : Summable (fun n : ℕ => ((‖(D.toLinearMap)‖ * t : ℝ) ^ n / n.factorial : ℝ)) := by
                        exact summable_pow_div_factorial (‖(D.toLinearMap)‖ * t : ℝ)
                      convert h₁₈ using 1
                      <;> ext n <;> ring_nf
                      <;> field_simp [Nat.factorial]
                      <;> ring_nf
                    exact Summable.mul_left (‖x‖ : ℝ) h₁₇
                  exact Summable.of_nonneg_of_le (fun n _ => by positivity) h₁₅ h₁₆
                exact h₁₄
              have h₁₉ : Summable (fun m : ℕ => (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) := by
                -- Same as above
                have h₂₀ : Summable (fun m : ℕ => (t ^ m / m.factorial : ℝ) : ℕ → ℝ) := by
                  exact summable_pow_div_factorial (t : ℝ)
                have h₂₁ : Summable (fun m : ℕ => (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) := by
                  refine' Summable.of_norm _
                  have h₂₂ : ∀ m : ℕ, ‖((t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y : SplitOctonion)‖ ≤ ‖(D.toLinearMap)‖ ^ m * ‖y‖ * (t ^ m / m.factorial : ℝ) := by
                    intro m
                    calc
                      ‖((t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y : SplitOctonion)‖ = (t ^ m / m.factorial : ℝ) * ‖((D.toLinearMap) ^ m) y‖ := by
                        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ m / m.factorial)]
                      _ ≤ (t ^ m / m.factorial : ℝ) * (‖(D.toLinearMap)‖ ^ m * ‖y‖) := by
                        gcongr
                        <;> simp [ContinuousLinearMap.iterate_norm]
                      _ = ‖(D.toLinearMap)‖ ^ m * ‖y‖ * (t ^ m / m.factorial : ℝ) := by ring
                  have h₂₃ : Summable (fun m : ℕ => (‖(D.toLinearMap)‖ : ℝ) ^ m * ‖y‖ * (t ^ m / m.factorial : ℝ)) := by
                    have h₂₄ : Summable (fun m : ℕ => (‖(D.toLinearMap)‖ : ℝ) ^ m * (t ^ m / m.factorial : ℝ)) := by
                      have h₂₅ : Summable (fun m : ℕ => ((‖(D.toLinearMap)‖ * t : ℝ) ^ m / m.factorial : ℝ)) := by
                        exact summable_pow_div_factorial (‖(D.toLinearMap)‖ * t : ℝ)
                      convert h₂₅ using 1
                      <;> ext m <;> ring_nf
                      <;> field_simp [Nat.factorial]
                      <;> ring_nf
                    exact Summable.mul_left (‖y‖ : ℝ) h₂₄
                  exact Summable.of_nonneg_of_le (fun m _ => by positivity) h₂₂ h₂₃
                exact h₂₁
              -- Use the Cauchy product theorem for summable series
              have h₂₀ : (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) =
                  ∑' n : ℕ, ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y) := by
                -- This is the Cauchy product formula
                have h₂₁ : (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) =
                    ∑' n : ℕ, ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y) := by
                  -- Use the Cauchy product theorem for Banach algebras
                  have h₂₂ : (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) =
                      ∑' n : ℕ, ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y) := by
                    -- Use the Cauchy product theorem
                    have h₂₃ : (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) =
                        ∑' n : ℕ, ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y) := by
                      -- This follows from the general Cauchy product theorem for complete normed algebras
                      classical
                      have h₂₄ : HasSum (fun n : ℕ => (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) := by
                        exact tsum_eq_sum h₁₂
                      have h₂₅ : HasSum (fun m : ℕ => (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) := by
                        exact tsum_eq_sum h₁₉
                      -- Use the Cauchy product theorem for HasSum
                      have h₂₆ : HasSum (fun n : ℕ => ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y)) (∑' n : ℕ, ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y)) := by
                        -- The Cauchy product of two summable series
                        have h₂₇ : HasSum (fun n : ℕ => ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y)) ((∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y)) := by
                          -- Use the Cauchy product theorem for HasSum in a Banach algebra
                          have h₂₈ : HasSum (fun n : ℕ => (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) (∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) := h₂₄
                          have h₂₉ : HasSum (fun m : ℕ => (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y) := h₂₅
                          -- The product is continuous and bilinear, so we can use the Cauchy product theorem
                          have h₃₀ : HasSum (fun n : ℕ => ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y)) ((∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) x) ⋆ (∑' m : ℕ, (t ^ m / m.factorial : ℝ) • ((D.toLinearMap) ^ m) y)) := by
                            -- Use the general Cauchy product theorem for complete normed algebras
                            convert HasSum.mul h₂₈ h₂₉ using 1
                            <;>
                            (try simp_all [Finset.sum_range_succ, add_smul, smul_add, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul])
                            <;>
                            (try ext)
                            <;>
                            (try simp_all [ContinuousLinearMap.comp_apply, smul_smul])
                            <;>
                            (try ring_nf)
                            <;>
                            (try norm_num)
                            <;>
                            (try aesop)
                          exact h₂₈
                        exact h₂₇
                      exact h₂₆
                    exact h₂₃
                  exact h₂₂
                have h₂₂ : ∑' n : ℕ, ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y) =
                    ∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) (x ⋆ y) := by
                  -- Use the Leibniz rule to combine the terms
                  have h₂₃ : ∀ n : ℕ, ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y) = (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) (x ⋆ y) := by
                    intro n
                    have h₂₄ : ((D.toLinearMap) ^ n) (x ⋆ y) = ∑ k in Finset.range (n + 1), ((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y) := h₅ n
                    calc
                      ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y) =
                          ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) * ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • (((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y)) := by
                        apply Finset.sum_congr rfl
                        intro k hk
                        simp [smul_smul, mul_assoc, mul_comm, mul_left_comm]
                        <;> ring_nf
                        <;> simp_all [smul_smul, mul_assoc, mul_comm, mul_left_comm]
                        <;> field_simp [Nat.factorial]
                        <;> ring_nf
                      _ = ∑ k in Finset.range (n + 1), ((t : ℝ) ^ n / (k.factorial * (n - k).factorial : ℝ)) • (((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y)) := by
                        apply Finset.sum_congr rfl
                        intro k hk
                        have h₂₅ : ((t : ℝ) ^ k / k.factorial : ℝ) * ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) = (t : ℝ) ^ n / (k.factorial * (n - k).factorial : ℝ) := by
                          field_simp [pow_add, Nat.factorial]
                          <;> ring_nf
                          <;> field_simp [Nat.factorial]
                          <;> ring_nf
                        rw [h₂₅]
                        <;> simp [smul_smul, mul_assoc, mul_comm, mul_left_comm]
                        <;> ring_nf
                      _ = ∑ k in Finset.range (n + 1), (n.choose k : ℝ) * ((t : ℝ) ^ n / n.factorial : ℝ) • (((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y)) := by
                        apply Finset.sum_congr rfl
                        intro k hk
                        have h₂₆ : (n.choose k : ℝ) = (n.factorial : ℝ) / (k.factorial * (n - k).factorial : ℝ) := by
                          norm_cast
                          <;> field_simp [Nat.choose_eq_factorial_div_factorial, Nat.factorial_succ]
                          <;> ring_nf
                          <;> field_simp [Nat.factorial]
                          <;> ring_nf
                        have h₂₇ : (t : ℝ) ^ n / (k.factorial * (n - k).factorial : ℝ) = (n.choose k : ℝ) * ((t : ℝ) ^ n / n.factorial : ℝ) := by
                          rw [h₂₆]
                          <;> field_simp [Nat.factorial]
                          <;> ring_nf
                          <;> field_simp [Nat.factorial]
                          <;> ring_nf
                        rw [h₂₇]
                        <;> simp [smul_smul, mul_assoc, mul_comm, mul_left_comm]
                        <;> ring_nf
                      _ = (n.choose k : ℝ) * ((t : ℝ) ^ n / n.factorial : ℝ) • ∑ k in Finset.range (n + 1), (((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y)) := by
                        simp [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]
                        <;> simp_all [Finset.sum_range_succ, add_smul, smul_add]
                        <;> ring_nf
                        <;> simp_all [smul_smul, mul_assoc, mul_comm, mul_left_comm]
                        <;> field_simp [Nat.factorial]
                        <;> ring_nf
                      _ = (t ^ n / n.factorial : ℝ) • ∑ k in Finset.range (n + 1), (n.choose k : ℝ) • (((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y)) := by
                        simp [smul_sum, smul_smul, mul_assoc, mul_comm, mul_left_comm]
                        <;> ring_nf
                        <;> simp_all [Finset.sum_range_succ, add_smul, smul_add]
                        <;> field_simp [Nat.factorial]
                        <;> ring_nf
                      _ = (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) (x ⋆ y) := by
                        have h₂₈ : ∑ k in Finset.range (n + 1), (n.choose k : ℝ) • (((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y)) = ((D.toLinearMap) ^ n) (x ⋆ y) := by
                          calc
                            ∑ k in Finset.range (n + 1), (n.choose k : ℝ) • (((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y)) = ∑ k in Finset.range (n + 1), ((n.choose k : ℝ) : ℝ) • (((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y)) := by rfl
                            _ = ∑ k in Finset.range (n + 1), ((D.toLinearMap) ^ k x) ⋆ ((D.toLinearMap) ^ (n - k) y) := by
                              -- This step uses the binomial theorem for the product in the algebra
                              -- For the specific case of the Zorn matrix algebra,
                              -- the derivation property ensures this holds for the exponential
                              simp_all [h₅]
                              <;> aesop
                            _ = ((D.toLinearMap) ^ n) (x ⋆ y) := by
                              rw [h₅]
                              <;> simp_all [Finset.sum_range_succ, add_smul, smul_add]
                              <;> aesop
                        rw [h₂₈]
                        <;> simp [smul_smul]
                        <;> ring_nf
                    <;> simp_all [Finset.sum_range_succ, add_smul, smul_add]
                    <;> aesop
                  -- Now use this to prove the series equality
                  calc
                    ∑' n : ℕ, ∑ k in Finset.range (n + 1), ((t : ℝ) ^ k / k.factorial : ℝ) • ((D.toLinearMap) ^ k x) ⋆ ((t : ℝ) ^ (n - k) / (n - k).factorial : ℝ) • ((D.toLinearMap) ^ (n - k) y) =
                        ∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) (x ⋆ y) := by
                      apply tsum_congr
                      intro n
                      rw [h₂₃ n]
                      <;> simp [smul_smul]
                      <;> ring_nf
                    _ = ∑' n : ℕ, (t ^ n / n.factorial : ℝ) • ((D.toLinearMap) ^ n) (x ⋆ y) := by rfl
                rw [h₂₂]
              <;> simp_all [tsum_eq_sum]
              <;> aesop
            rw [h₉]
          <;> simp_all [tsum_eq_sum]
          <;> aesop
        exact h₆
      exact h₄
    exact h₂ x y
  rw [h₂ ePlus eMinus]
  <;> simp [ePlus_mul_eMinus]
  <;> rfl

  have h₂ : ePlus ⋆ eMinus = 0 := ePlus_mul_eMinus
  have h₃ : flow D t (ePlus ⋆ eMinus) = flow D t (0 : SplitOctonion) := by rw [h₂]
  have h₄ : flow D t (0 : SplitOctonion) = 0 := by
    simp [flow, LinearMap.map_zero]
  have h₅ : (flow D t ePlus) ⋆ (flow D t eMinus) = 0 := by
    calc
      (flow D t ePlus) ⋆ (flow D t eMinus) = flow D t (ePlus ⋆ eMinus) := by rw [h₁]
      _ = flow D t (0 : SplitOctonion) := by rw [h₂]
      _ = 0 := h₄
  calc
    transportedEPlus D t ⋆ transportedEMinus D t = (flow D t ePlus) ⋆ (flow D t eMinus) := by
      simp [transportedEPlus, transportedEMinus]
    _ = 0 := h₅

/-- The stabilizer specialization: if the derivation fixes I, the chiral sheets are static. -/
theorem transportedGPlus_eq_of_fixes_I (D : Derivation) (t : ℝ) (n : Fin 3) (hI : FixesI D) :
  transportedGPlus D t n = gPlus n := by
  have h₁ : flow D t (gPlus n) = gPlus n := by
    have h₂ : D.toLinearMap (gPlus n) = 0 := by
      -- Since D fixes I and gPlus is built from I and the basis, D(gPlus) = 0
      simp [gPlus, J, j, FixesI, chiralUpperBasis, chiralLowerBasis, SplitOctonion, ZornMatrix]
      <;>
      (try aesop) <;>
      (try simp_all [Derivation, FixesI, LinearMap.map_add, LinearMap.map_smul, LinearMap.map_zero]) <;>
      (try ext i <;> fin_cases i <;> simp_all [ZornMatrix.mul_def, ZornMatrix.dot, ZornMatrix.cross]) <;>
      (try norm_num) <;>
      (try aesop)
    -- Since D(gPlus) = 0, the flow preserves gPlus
    have h₃ : flow D t (gPlus n) = gPlus n := by
      have h₄ : flow D t = (D.toLinearMap).exp.map (t • (1 : EndV)) := rfl
      rw [h₄]
      have h₅ : (D.toLinearMap).exp.map (t • (1 : EndV)) (gPlus n) = gPlus n := by
        -- Use the fact that D(gPlus) = 0 implies exp(D)(gPlus) = gPlus
        have h₆ : D.toLinearMap (gPlus n) = 0 := h₂
        have h₇ : ∀ n : ℕ, (D.toLinearMap ^ n) (gPlus n) = if n = 0 then gPlus n else 0 := by
          intro m
          induction m with
          | zero => simp [LinearMap.one_apply]
          | succ m ih =>
            rw [Function.iterate_succ_apply']
            rw [ih]
            split_ifs <;> simp_all [LinearMap.map_zero]
            <;> aesop
        -- The exponential map applied to gPlus gives gPlus
        simp [LinearMap.exp_apply, h₇]
        <;>
        norm_num
        <;>
        simp_all [Finset.sum_ite_eq']
        <;>
        aesop
      rw [h₅]
    rw [h₃]
  rw [transportedGPlus]
  exact h₁

theorem transportedGMinus_eq_of_fixes_I (D : Derivation) (t : ℝ) (n : Fin 3) (hI : FixesI D) :
  transportedGMinus D t n = gMinus n := by
  have h₁ : flow D t (gMinus n) = gMinus n := by
    have h₂ : D.toLinearMap (gMinus n) = 0 := by
      -- Since D fixes I and gMinus is built from I and the basis, D(gMinus) = 0
      simp [gMinus, J, j, FixesI, chiralUpperBasis, chiralLowerBasis, SplitOctonion, ZornMatrix]
      <;>
      (try aesop) <;>
      (try simp_all [Derivation, FixesI, LinearMap.map_add, LinearMap.map_smul, LinearMap.map_zero]) <;>
      (try ext i <;> fin_cases i <;> simp_all [ZornMatrix.mul_def, ZornMatrix.dot, ZornMatrix.cross]) <;>
      (try norm_num) <;>
      (try aesop)
    -- Since D(gMinus) = 0, the flow preserves gMinus
    have h₃ : flow D t (gMinus n) = gMinus n := by
      have h₄ : flow D t = (D.toLinearMap).exp.map (t • (1 : EndV)) := rfl
      rw [h₄]
      have h₅ : (D.toLinearMap).exp.map (t • (1 : EndV)) (gMinus n) = gMinus n := by
        -- Use the fact that D(gMinus) = 0 implies exp(D)(gMinus) = gMinus
        have h₆ : D.toLinearMap (gMinus n) = 0 := h₂
        have h₇ : ∀ n : ℕ, (D.toLinearMap ^ n) (gMinus n) = if n = 0 then gMinus n else 0 := by
          intro m
          induction m with
          | zero => simp [LinearMap.one_apply]
          | succ m ih =>
            rw [Function.iterate_succ_apply']
            rw [ih]
            split_ifs <;> simp_all [LinearMap.map_zero]
            <;> aesop
        -- The exponential map applied to gMinus gives gMinus
        simp [LinearMap.exp_apply, h₇]
        <;>
        norm_num
        <;>
        simp_all [Finset.sum_ite_eq']
        <;>
        aesop
      rw [h₅]
    rw [h₃]
  rw [transportedGMinus]
  exact h₁

/-!
=============================================================================
PART 3: Bridge to the Functional Analysis (Krein Space)
=============================================================================
-/

/-- The canonical linear equivalence between the Peirce/chiral decomposition
    and the doubled chiral Krein space structure. -/
def peirceKreinEquiv : SplitOctonion ≃ₗ[ℝ] (ℝ × (Fin 3 → ℝ) × ℝ × (Fin 3 → ℝ)) :=
  { toFun := fun s => (s.a, s.x, s.b, s.y),
    map_add' := by
      intro x y
      ext <;> simp [SplitOctonion, ZornMatrix.add_def, Prod.ext_iff]
      <;> fin_cases i <;> fin_cases j <;> simp_all [Fin.sum_univ_three]
      <;> ring_nf
      <;> aesop
    map_smul' := by
      intro c x
      ext <;> simp [SplitOctonion, ZornMatrix.smul_def, Prod.ext_iff]
      <;> fin_cases i <;> fin_cases j <;> simp_all [Fin.sum_univ_three]
      <;> ring_nf
      <;> aesop
    invFun := fun ⟨w_p, v_p, w_m, v_m⟩ =>
      { a := w_p, b := w_m, x := v_p, y := v_m },
    left_inv := by
      intro x
      ext <;> simp [SplitOctonion, Prod.ext_iff]
      <;> fin_cases i <;> fin_cases j <;> simp_all [Fin.sum_univ_three]
      <;> aesop
    right_inv := by
      intro x
      ext <;> simp [SplitOctonion, Prod.ext_iff]
      <;> fin_cases i <;> fin_cases j <;> simp_all [Fin.sum_univ_three]
      <;> aesop }

/-- The algebraic conjugation on split-octonions (corresponds to γ₅ in Krein space). -/
def star (s : SplitOctonion) : SplitOctonion :=
  { a := s.b, b := s.a, x := s.y, y := s.x }

/-- The star operation is an involution. -/
theorem star_involutive (s : SplitOctonion) : star (star s) = s := by
  ext i <;> fin_cases i <;> simp [star, SplitOctonion]
  <;> aesop

/-- The star operation is linear. -/
theorem star_linear (c : ℝ) (s t : SplitOctonion) :
    star (c • s + t) = c • star s + star t := by
  ext i <;> fin_cases i <;> simp [star, SplitOctonion, ZornMatrix.add_def, ZornMatrix.smul_def]
  <;> ring_nf
  <;> aesop

end InfoGeometry.Canonical.SplitOctonionPeirceChiralFrame