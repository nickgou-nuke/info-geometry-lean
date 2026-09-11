import InfoGeometry.Canonical.SplitOctonionThreeColorChiralRelations
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitQuaternionAssociativeCoassociativeCalibrationBridge
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic

namespace InfoGeometry.Canonical

open SplitQuaternionAssociativeCoassociativeCalibrationBridge

noncomputable section

abbrev ThreeColorCoreCarrier := StandardRationalSplitOctonion

/-- The polarized generators `n₊, n₋, σ₊, σ₋` for a fixed colour. -/
def threeColorCoreGenerator (c : SplitOctonionColour) : Fin 4 → ThreeColorCoreCarrier
  | ⟨0, _⟩ => modularNPlus
  | ⟨1, _⟩ => modularNMinus
  | ⟨2, _⟩ => modularSigmaPlus c
  | ⟨3, _⟩ => modularSigmaMinus c
  | _ => 0

/-- The four-dimensional coloured core spanned by the polarized generators. -/
def threeColorCore (c : SplitOctonionColour) : Submodule ℚ ThreeColorCoreCarrier :=
  Submodule.span ℚ (Set.range (threeColorCoreGenerator c))

/-- Public alias matching the owner-level mathematical name. -/
abbrev colorCore := threeColorCore

/-- Standard basis labels `1, ℓ, u, ℓu` for a fixed colour. -/
def threeColorStandardLabel (c : SplitOctonionColour) : Fin 4 → IntegralSplitBasis
  | ⟨0, _⟩ => .one
  | ⟨1, _⟩ => .l
  | ⟨2, _⟩ =>
      match c with
      | .red => .i
      | .green => .j
      | .blue => .k
  | ⟨3, _⟩ =>
      match c with
      | .red => .il
      | .green => .jl
      | .blue => .kl
  | _ => .one

/-- The standard colour-slice generators `1, ℓ, u, ℓu`. -/
def threeColorStandardGenerator (c : SplitOctonionColour) : Fin 4 → ThreeColorCoreCarrier :=
  fun i => rationalBasis (threeColorStandardLabel c i)

/-- The standard split-quaternion core `span{1, ℓ, u, ℓu}`. -/
def threeColorStandardCore (c : SplitOctonionColour) : Submodule ℚ ThreeColorCoreCarrier :=
  Submodule.span ℚ (Set.range (threeColorStandardGenerator c))

def threeColorBasisIndex : SplitOctonionColour → IntegralSplitBasis
  | .red => .i
  | .green => .j
  | .blue => .k

def threeColorLBasisIndex : SplitOctonionColour → IntegralSplitBasis
  | .red => .il
  | .green => .jl
  | .blue => .kl

@[simp] theorem modularNPlus_mem_threeColorCore (c : SplitOctonionColour) :
    modularNPlus ∈ threeColorCore c := by
  exact Submodule.subset_span (Set.mem_range_self (⟨0, by decide⟩ : Fin 4))

@[simp] theorem modularNMinus_mem_threeColorCore (c : SplitOctonionColour) :
    modularNMinus ∈ threeColorCore c := by
  exact Submodule.subset_span (Set.mem_range_self (⟨1, by decide⟩ : Fin 4))

@[simp] theorem modularSigmaPlus_mem_threeColorCore (c : SplitOctonionColour) :
    modularSigmaPlus c ∈ threeColorCore c := by
  exact Submodule.subset_span (Set.mem_range_self (⟨2, by decide⟩ : Fin 4))

@[simp] theorem modularSigmaMinus_mem_threeColorCore (c : SplitOctonionColour) :
    modularSigmaMinus c ∈ threeColorCore c := by
  exact Submodule.subset_span (Set.mem_range_self (⟨3, by decide⟩ : Fin 4))

private theorem threeColorStandardLabel_injective
    (c : SplitOctonionColour) :
    Function.Injective (threeColorStandardLabel c) := by
  cases c <;> native_decide

private theorem threeColorStandardGenerator_linearIndependent
    (c : SplitOctonionColour) :
    LinearIndependent ℚ (threeColorStandardGenerator c) := by
  have hstd :
      LinearIndependent ℚ
        (fun b : IntegralSplitBasis => (rationalBasis b : ThreeColorCoreCarrier)) := by
    simpa [rationalBasis] using
      (Pi.linearIndependent_single_one IntegralSplitBasis ℚ)
  exact hstd.comp (threeColorStandardLabel c)
    (threeColorStandardLabel_injective c)

@[simp] theorem rationalOne_mem_threeColorStandardCore (c : SplitOctonionColour) :
    rationalBasis .one ∈ threeColorStandardCore c := by
  exact Submodule.subset_span (Set.mem_range_self (⟨0, by decide⟩ : Fin 4))

@[simp] theorem fundamentalSymmetry_mem_threeColorStandardCore (c : SplitOctonionColour) :
    fundamentalSymmetry ∈ threeColorStandardCore c := by
  exact Submodule.subset_span (Set.mem_range_self (⟨1, by decide⟩ : Fin 4))

@[simp] theorem phaseAxis_mem_threeColorStandardCore (c : SplitOctonionColour) :
    phaseAxis c ∈ threeColorStandardCore c := by
  cases c <;>
    exact Submodule.subset_span (Set.mem_range_self (⟨2, by decide⟩ : Fin 4))

@[simp] theorem modularJ_mem_threeColorStandardCore (c : SplitOctonionColour) :
    modularJ c ∈ threeColorStandardCore c := by
  rw [modularJ_eq_colourLUnit]
  cases c <;>
    exact Submodule.subset_span (Set.mem_range_self (⟨3, by decide⟩ : Fin 4))

@[simp] theorem modularNPlus_mem_threeColorStandardCore (c : SplitOctonionColour) :
    modularNPlus ∈ threeColorStandardCore c := by
  have h₁ : modularNPlus = (1 / 2 : ℚ) • (rationalBasis .one + fundamentalSymmetry) := by rfl
  rw [h₁]
  have h₂ : (rationalBasis .one : ThreeColorCoreCarrier) ∈ threeColorStandardCore c := rationalOne_mem_threeColorStandardCore c
  have h₃ : (fundamentalSymmetry : ThreeColorCoreCarrier) ∈ threeColorStandardCore c := fundamentalSymmetry_mem_threeColorStandardCore c
  have h₄ : (rationalBasis .one + fundamentalSymmetry : ThreeColorCoreCarrier) ∈ threeColorStandardCore c := (threeColorStandardCore c).add_mem h₂ h₃
  exact (threeColorStandardCore c).smul_mem _ h₄

@[simp] theorem modularNMinus_mem_threeColorStandardCore (c : SplitOctonionColour) :
    modularNMinus ∈ threeColorStandardCore c := by
  have h₁ : modularNMinus = (1 / 2 : ℚ) • (rationalBasis .one - fundamentalSymmetry) := by rfl
  rw [h₁]
  have h₂ : (rationalBasis .one : ThreeColorCoreCarrier) ∈ threeColorStandardCore c := rationalOne_mem_threeColorStandardCore c
  have h₃ : (fundamentalSymmetry : ThreeColorCoreCarrier) ∈ threeColorStandardCore c := fundamentalSymmetry_mem_threeColorStandardCore c
  have h₄ : (rationalBasis .one - fundamentalSymmetry : ThreeColorCoreCarrier) ∈ threeColorStandardCore c := (threeColorStandardCore c).sub_mem h₂ h₃
  exact (threeColorStandardCore c).smul_mem _ h₄

@[simp] theorem modularSigmaPlus_mem_threeColorStandardCore (c : SplitOctonionColour) :
    modularSigmaPlus c ∈ threeColorStandardCore c := by
  have h₁ : modularSigmaPlus c = (1 / 2 : ℚ) • (modularJ c - phaseAxis c) := by rfl
  rw [h₁]
  have h₂ : (modularJ c : ThreeColorCoreCarrier) ∈ threeColorStandardCore c := modularJ_mem_threeColorStandardCore c
  have h₃ : (phaseAxis c : ThreeColorCoreCarrier) ∈ threeColorStandardCore c := phaseAxis_mem_threeColorStandardCore c
  have h₄ : (modularJ c - phaseAxis c : ThreeColorCoreCarrier) ∈ threeColorStandardCore c := (threeColorStandardCore c).sub_mem h₂ h₃
  exact (threeColorStandardCore c).smul_mem _ h₄

@[simp] theorem modularSigmaMinus_mem_threeColorStandardCore (c : SplitOctonionColour) :
    modularSigmaMinus c ∈ threeColorStandardCore c := by
  have h₁ : modularSigmaMinus c = (1 / 2 : ℚ) • (modularJ c + phaseAxis c) := by rfl
  rw [h₁]
  have h₂ : (modularJ c : ThreeColorCoreCarrier) ∈ threeColorStandardCore c := modularJ_mem_threeColorStandardCore c
  have h₃ : (phaseAxis c : ThreeColorCoreCarrier) ∈ threeColorStandardCore c := phaseAxis_mem_threeColorStandardCore c
  have h₄ : (modularJ c + phaseAxis c : ThreeColorCoreCarrier) ∈ threeColorStandardCore c := (threeColorStandardCore c).add_mem h₂ h₃
  exact (threeColorStandardCore c).smul_mem _ h₄

theorem threeColorStandardCore_le_threeColorCore
    (c : SplitOctonionColour) :
    threeColorStandardCore c ≤ threeColorCore c := by
  refine Submodule.span_le.2 ?_
  intro x hx
  rcases hx with ⟨i, rfl⟩
  fin_cases i
  · -- rationalBasis .one = n₊ + n₋
    have h₁ : (rationalBasis (IntegralSplitBasis.one : IntegralSplitBasis) : ThreeColorCoreCarrier) ∈ threeColorCore c := by
      have h₂ : modularNPlus + modularNMinus = (rationalBasis (IntegralSplitBasis.one : IntegralSplitBasis) : ThreeColorCoreCarrier) := by
        rw [modularPolarized_one]
      have h₃ : modularNPlus ∈ threeColorCore c := modularNPlus_mem_threeColorCore c
      have h₄ : modularNMinus ∈ threeColorCore c := modularNMinus_mem_threeColorCore c
      have h₅ : modularNPlus + modularNMinus ∈ threeColorCore c := (threeColorCore c).add_mem h₃ h₄
      rw [h₂] at h₅
      exact h₅
    simpa [threeColorStandardGenerator, threeColorStandardLabel] using h₁
  · -- fundamentalSymmetry = n₊ - n₋
    have h₁ : (fundamentalSymmetry : ThreeColorCoreCarrier) ∈ threeColorCore c := by
      have h₂ : modularNPlus - modularNMinus = (fundamentalSymmetry : ThreeColorCoreCarrier) := by
        rw [modularPolarized_epsilon]
      have h₃ : modularNPlus ∈ threeColorCore c := modularNPlus_mem_threeColorCore c
      have h₄ : modularNMinus ∈ threeColorCore c := modularNMinus_mem_threeColorCore c
      have h₅ : modularNPlus - modularNMinus ∈ threeColorCore c := (threeColorCore c).sub_mem h₃ h₄
      rw [h₂] at h₅
      exact h₅
    simpa [threeColorStandardGenerator, threeColorStandardLabel] using h₁
  · -- colourUnit c = phaseAxis c = σ₋ - σ₊
    have h₁ : (rationalBasis (threeColorBasisIndex c) : ThreeColorCoreCarrier) ∈ threeColorCore c := by
      have h₂ : modularSigmaMinus c - modularSigmaPlus c = (phaseAxis c : ThreeColorCoreCarrier) := by
        rw [modularPolarized_phaseAxis]
      have h₃ : modularSigmaMinus c ∈ threeColorCore c := modularSigmaMinus_mem_threeColorCore c
      have h₄ : modularSigmaPlus c ∈ threeColorCore c := modularSigmaPlus_mem_threeColorCore c
      have h₅ : modularSigmaMinus c - modularSigmaPlus c ∈ threeColorCore c := (threeColorCore c).sub_mem h₃ h₄
      have h₆ : (phaseAxis c : ThreeColorCoreCarrier) ∈ threeColorCore c := by
        rw [h₂] at h₅
        exact h₅
      have h₇ : (phaseAxis c : ThreeColorCoreCarrier) = (colourUnit c : ThreeColorCoreCarrier) := by
        simp [phaseAxis, colourUnit]
      have h₈ : (colourUnit c : ThreeColorCoreCarrier) = (rationalBasis (threeColorBasisIndex c) : ThreeColorCoreCarrier) := by
        cases c <;> rfl
      rw [h₇, h₈] at h₆
      exact h₆
    simpa [threeColorStandardGenerator, threeColorStandardLabel] using h₁
  · -- colourLUnit c = modularJ c = σ₊ + σ₋
    have h₁ : (rationalBasis (threeColorLBasisIndex c) : ThreeColorCoreCarrier) ∈ threeColorCore c := by
      have h₂ : modularSigmaPlus c + modularSigmaMinus c = (modularJ c : ThreeColorCoreCarrier) := by
        rw [modularPolarized_modularJ]
      have h₃ : modularSigmaPlus c ∈ threeColorCore c := modularSigmaPlus_mem_threeColorCore c
      have h₄ : modularSigmaMinus c ∈ threeColorCore c := modularSigmaMinus_mem_threeColorCore c
      have h₅ : modularSigmaPlus c + modularSigmaMinus c ∈ threeColorCore c := (threeColorCore c).add_mem h₃ h₄
      have h₆ : (modularJ c : ThreeColorCoreCarrier) ∈ threeColorCore c := by
        rw [h₂] at h₅
        exact h₅
      have h₇ : (modularJ c : ThreeColorCoreCarrier) = (colourLUnit c : ThreeColorCoreCarrier) := by
        rw [modularJ_eq_colourLUnit]
      have h₈ : (colourLUnit c : ThreeColorCoreCarrier) = (rationalBasis (threeColorLBasisIndex c) : ThreeColorCoreCarrier) := by
        cases c <;> rfl
      rw [h₇, h₈] at h₆
      exact h₆
    simpa [threeColorStandardGenerator, threeColorStandardLabel] using h₁

theorem threeColorCore_le_threeColorStandardCore
    (c : SplitOctonionColour) :
    threeColorCore c ≤ threeColorStandardCore c := by
  refine Submodule.span_le.2 ?_
  intro x hx
  rcases hx with ⟨i, rfl⟩
  fin_cases i
  · exact modularNPlus_mem_threeColorStandardCore c
  · exact modularNMinus_mem_threeColorStandardCore c
  · exact modularSigmaPlus_mem_threeColorStandardCore c
  · exact modularSigmaMinus_mem_threeColorStandardCore c

theorem threeColorCore_eq_threeColorStandardCore (c : SplitOctonionColour) :
    threeColorCore c = threeColorStandardCore c :=
  le_antisymm (threeColorCore_le_threeColorStandardCore c)
    (threeColorStandardCore_le_threeColorCore c)

theorem finrank_threeColorStandardCore (c : SplitOctonionColour) :
    Module.finrank ℚ (threeColorStandardCore c) = 4 := by
  change Module.finrank ℚ (Submodule.span ℚ (Set.range (threeColorStandardGenerator c))) = 4
  rw [finrank_span_eq_card (threeColorStandardGenerator_linearIndependent c)]
  rfl

@[simp] theorem finrank_colorCore (c : SplitOctonionColour) :
    Module.finrank ℚ (colorCore c) = 4 := by
  change Module.finrank ℚ (threeColorCore c) = 4
  rw [threeColorCore_eq_threeColorStandardCore]
  exact finrank_threeColorStandardCore c

private theorem threeColorCoreGenerator_assoc
    (c : SplitOctonionColour) (p q r : Fin 4) :
    splitOctonionMulQ (splitOctonionMulQ (threeColorCoreGenerator c p)
      (threeColorCoreGenerator c q)) (threeColorCoreGenerator c r) =
      splitOctonionMulQ (threeColorCoreGenerator c p)
        (splitOctonionMulQ (threeColorCoreGenerator c q)
          (threeColorCoreGenerator c r)) := by
  fin_cases c <;> fin_cases p <;> fin_cases q <;> fin_cases r <;> native_decide

private theorem threeColorCore_mul_zero_left (x : ThreeColorCoreCarrier) :
    splitOctonionMulQ 0 x = 0 := by
  funext b; fin_cases b <;>
    simp [splitOctonionMulQ, splitQuaternionOfQ, splitQuaternionLPartQ,
      splitQuaternionConjQ, splitQuaternionAddQ, splitQuaternionMulQ,
      splitOctonionOfQuaternionPairQ]

private theorem threeColorCore_mul_zero_right (x : ThreeColorCoreCarrier) :
    splitOctonionMulQ x 0 = 0 := by
  funext b; fin_cases b <;>
    simp [splitOctonionMulQ, splitQuaternionOfQ, splitQuaternionLPartQ,
      splitQuaternionConjQ, splitQuaternionAddQ, splitQuaternionMulQ,
      splitOctonionOfQuaternionPairQ]

theorem threeColorCore_closed_mul
    (c : SplitOctonionColour) {x y : ThreeColorCoreCarrier}
    (hx : x ∈ threeColorCore c) (hy : y ∈ threeColorCore c) :
    splitOctonionMulQ x y ∈ threeColorCore c := by
  induction hx using Submodule.span_induction with
  | mem p hp =>
      rcases hp with ⟨p, rfl⟩
      induction hy using Submodule.span_induction with
      | mem q hq =>
          rcases hq with ⟨q, rfl⟩
          fin_cases p <;> fin_cases q <;> simp [threeColorCoreGenerator]
      | zero => simp [threeColorCore_mul_zero_right]
      | add y z hy hz ihy ihz =>
          rw [splitOctonionMulQ_add_right]; exact (threeColorCore c).add_mem ihy ihz
      | smul a y hy ih =>
          rw [splitOctonionMulQ_smul_right]; exact (threeColorCore c).smul_mem a ih
  | zero => simp [threeColorCore_mul_zero_left]
  | add x y hx hy ihx ihy =>
      rw [splitOctonionMulQ_add_left]; exact (threeColorCore c).add_mem ihx ihy
  | smul a x hx ih =>
      rw [splitOctonionMulQ_smul_left]; exact (threeColorCore c).smul_mem a ih

/-- Closure of the polarized colour core under the rational split-octonion product. -/
theorem colorCore_closed_mul
    (c : SplitOctonionColour) {x y : StandardRationalSplitOctonion}
    (hx : x ∈ colorCore c) (hy : y ∈ colorCore c) :
    splitOctonionMulQ x y ∈ colorCore c :=
  threeColorCore_closed_mul c hx hy

theorem threeColorCore_associative
    (c : SplitOctonionColour) {x y z : ThreeColorCoreCarrier}
    (hx : x ∈ threeColorCore c) (hy : y ∈ threeColorCore c)
    (hz : z ∈ threeColorCore c) :
    splitOctonionMulQ (splitOctonionMulQ x y) z =
      splitOctonionMulQ x (splitOctonionMulQ y z) := by
  induction hx using Submodule.span_induction with
  | mem p hp =>
      rcases hp with ⟨p, rfl⟩
      induction hy using Submodule.span_induction with
      | mem q hq =>
          rcases hq with ⟨q, rfl⟩
          induction hz using Submodule.span_induction with
          | mem r hr =>
              rcases hr with ⟨r, rfl⟩
              exact threeColorCoreGenerator_assoc c p q r
          | zero =>
              simp [threeColorCore_mul_zero_right, threeColorCore_mul_zero_left]
          | add z w hz hw ihz ihw =>
              simp only [splitOctonionMulQ_add_left, splitOctonionMulQ_add_right]
              rw [ihz, ihw]
          | smul a z hz ih =>
              simp only [splitOctonionMulQ_smul_left, splitOctonionMulQ_smul_right]
              rw [ih]
      | zero =>
          simp [threeColorCore_mul_zero_right, threeColorCore_mul_zero_left]
      | add y z hy hz ihy ihz =>
          simp only [splitOctonionMulQ_add_left, splitOctonionMulQ_add_right]
          rw [ihy, ihz]
      | smul a y hy ih =>
          simp only [splitOctonionMulQ_smul_left, splitOctonionMulQ_smul_right]
          rw [ih]
  | zero =>
      simp [threeColorCore_mul_zero_left, threeColorCore_mul_zero_right]
  | add x y hx hy ihx ihy =>
      simp only [splitOctonionMulQ_add_left, splitOctonionMulQ_add_right]
      rw [ihx, ihy]
  | smul a x hx ih =>
      simp only [splitOctonionMulQ_smul_left, splitOctonionMulQ_smul_right]
      rw [ih]

/-- Public associativity theorem under the owner-level `colorCore` name. -/
theorem colorCore_mul_assoc
    (c : SplitOctonionColour) {x y z : StandardRationalSplitOctonion}
    (hx : x ∈ colorCore c) (hy : y ∈ colorCore c) (hz : z ∈ colorCore c) :
    splitOctonionMulQ (splitOctonionMulQ x y) z =
      splitOctonionMulQ x (splitOctonionMulQ y z) :=
  threeColorCore_associative c hx hy hz

set_option maxHeartbeats 1000000 in
private theorem threeColorCoreGenerator_linearIndependent
    (c : SplitOctonionColour) :
    LinearIndependent ℚ (threeColorCoreGenerator c) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h₁ := congrFun hg (IntegralSplitBasis.one)
  have h₂ := congrFun hg (IntegralSplitBasis.l)
  have h₃ := congrFun hg (threeColorBasisIndex c)
  have h₄ := congrFun hg (threeColorLBasisIndex c)
  fin_cases c <;> fin_cases i <;>
    simp [threeColorCoreGenerator, rationalBasis, modularNPlus,
      modularNMinus, modularSigmaPlus, modularSigmaMinus, modularJ,
      phaseAxis, fundamentalSymmetry, colourUnit, colourLUnit,
      threeColorBasisIndex, threeColorLBasisIndex, Pi.smul_apply,
      splitOctonionMulQ, splitQuaternionOfQ, splitQuaternionLPartQ,
      splitQuaternionConjQ, splitQuaternionAddQ, splitQuaternionMulQ,
      splitOctonionOfQuaternionPairQ, Fin.sum_univ_succ] at h₁ h₂ h₃ h₄ ⊢ <;>
    linarith

/-- The polarized generators viewed as elements of the coloured core subtype. -/
def colorPolarizedGenerator (c : SplitOctonionColour) (i : Fin 4) : colorCore c :=
  ⟨threeColorCoreGenerator c i, Submodule.subset_span (Set.mem_range_self i)⟩

/-- The polarized generators are linearly independent in the coloured core. -/
theorem colorPolarizedGenerators_linearIndependent
    (c : SplitOctonionColour) :
    LinearIndependent ℚ (colorPolarizedGenerator c) := by
  apply LinearIndependent.of_comp (threeColorCore c).subtype
  simpa [Function.comp_def, colorPolarizedGenerator] using
    threeColorCoreGenerator_linearIndependent c

/-- The subtype polarized generators span the whole coloured core. -/
theorem colorPolarizedGenerators_span_eq_top
    (c : SplitOctonionColour) :
    Submodule.span ℚ (Set.range (colorPolarizedGenerator c)) = ⊤ := by
  have h₁ : LinearIndependent ℚ (colorPolarizedGenerator c) := colorPolarizedGenerators_linearIndependent c
  have h₂ : Fintype.card (Fin 4) = Module.finrank ℚ (colorCore c) := by
    simp [finrank_colorCore c]
  have h₃ : Submodule.span ℚ (Set.range (colorPolarizedGenerator c)) = ⊤ :=
    h₁.span_eq_top_of_card_eq_finrank h₂
  exact h₃

/-- The polarized basis on a fixed coloured split-quaternion core. -/
noncomputable def colorPolarizedBasis (c : SplitOctonionColour) :
    Module.Basis (Fin 4) ℚ (colorCore c) :=
  basisOfLinearIndependentOfCardEqFinrank
    (colorPolarizedGenerators_linearIndependent c)
    (by
      simp [finrank_colorCore c]
      <;>
      rfl)

@[simp] theorem colorPolarizedBasis_apply
    (c : SplitOctonionColour) (i : Fin 4) :
    colorPolarizedBasis c i = colorPolarizedGenerator c i := by
  exact congrFun
    (coe_basisOfLinearIndependentOfCardEqFinrank
      (colorPolarizedGenerators_linearIndependent c)
      (by simp [finrank_colorCore c] <;> rfl))
    i

end

end InfoGeometry.Canonical
