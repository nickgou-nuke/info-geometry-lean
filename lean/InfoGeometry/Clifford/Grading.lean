import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Core.Involution
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

set_option linter.unusedSectionVars false

namespace InfoGeometry.Krein

open InfoGeometry.Core

section KreinClifford

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Commutator bracket on doubled-space endomorphisms. -/
def clmComm
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  A.comp B - B.comp A

lemma clmComm_eq_lie
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    clmComm A B = ⁅A, B⁆ := by
  ext v <;> simp [clmComm, Ring.lie_def]

/-- Jordan product from the associative product on doubled-space endomorphisms. -/
noncomputable def jordanProd
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (A.comp B + B.comp A)

/-- Jordan-closed families of endomorphisms. -/
def isJordan
    (S : Set (DoubledSpace E →L[ℝ] DoubledSpace E)) : Prop :=
  ∀ {A B}, A ∈ S → B ∈ S → jordanProd A B ∈ S

/-- Derivations of the Jordan product. -/
def isDerivation
    (D : (DoubledSpace E →L[ℝ] DoubledSpace E) →
      (DoubledSpace E →L[ℝ] DoubledSpace E)) : Prop :=
  ∀ A B,
    D (jordanProd A B) = jordanProd (D A) B + jordanProd A (D B)

/-- Even operators commute with the grading involution `J`. -/
def isEven (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  (modular_j (E := E)).comp A = A.comp (modular_j (E := E))

/-- Backward-compatible alias for even operators. -/
abbrev isGradeZero (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  isEven (E := E) A

lemma jordanProd_comm
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    jordanProd A B = jordanProd B A := by
  simp [jordanProd, add_comm]

lemma comp_eq_jordan_add_half_comm
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    A.comp B
      = jordanProd A B + ((2 : ℝ)⁻¹) • clmComm A B := by
  have hhalf : (((2 : ℝ)⁻¹) + ((2 : ℝ)⁻¹)) = 1 := by norm_num
  have hsplit (x : DoubledSpace E) : x = ((2 : ℝ)⁻¹) • x + ((2 : ℝ)⁻¹) • x := by
    calc
      x = (1 : ℝ) • x := by simp
      _ = ((((2 : ℝ)⁻¹) + ((2 : ℝ)⁻¹)) : ℝ) • x := by simp [hhalf]
      _ = ((2 : ℝ)⁻¹) • x + ((2 : ℝ)⁻¹) • x := by simp [add_smul]
  apply ContinuousLinearMap.ext
  intro v
  calc
    (A.comp B) v = A (B v) := rfl
    _ = ((2 : ℝ)⁻¹) • (A (B v)) + ((2 : ℝ)⁻¹) • (A (B v)) := hsplit (A (B v))
    _ = (jordanProd A B + ((2 : ℝ)⁻¹) • clmComm A B) v := by
          simp [jordanProd, clmComm, sub_eq_add_neg, smul_add, add_assoc, add_left_comm]

lemma even_closed_comm
    {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : isEven (E := E) A)
    (hB : isEven (E := E) B) :
    isEven (E := E) (clmComm A B) := by
  unfold isEven at *
  calc
    (modular_j (E := E)).comp (clmComm A B)
        = (modular_j (E := E)).comp (A.comp B) - (modular_j (E := E)).comp (B.comp A) := by
            simp [clmComm, ContinuousLinearMap.comp_sub]
    _ = ((modular_j (E := E)).comp A).comp B - ((modular_j (E := E)).comp B).comp A := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (A.comp (modular_j (E := E))).comp B - (B.comp (modular_j (E := E))).comp A := by
          rw [hA, hB]
    _ = A.comp ((modular_j (E := E)).comp B) - B.comp ((modular_j (E := E)).comp A) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = A.comp (B.comp (modular_j (E := E))) - B.comp (A.comp (modular_j (E := E))) := by
          rw [hB, hA]
    _ = (A.comp B).comp (modular_j (E := E)) - (B.comp A).comp (modular_j (E := E)) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (clmComm A B).comp (modular_j (E := E)) := by
          simp [clmComm, ContinuousLinearMap.sub_comp]

/-- Backward-compatible name for closure of commuting endomorphisms under commutator. -/
lemma gradeZero_closed_comm
    {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : isGradeZero (E := E) A)
    (hB : isGradeZero (E := E) B) :
    isGradeZero (E := E) (clmComm A B) :=
  even_closed_comm (E := E) hA hB

/-- `+1` eigenspace predicate for the grading involution `J`. -/
def inGradePlus (v : DoubledSpace E) : Prop := modular_j (E := E) v = v

/-- `-1` eigenspace predicate for the grading involution `J`. -/
def inGradeMinus (v : DoubledSpace E) : Prop := modular_j (E := E) v = -v

/-- `modular_j` packaged as an involution on doubled vectors. -/
noncomputable def modular_jInvolution : InvolutiveAutomorphism (DoubledSpace E) where
  toFun := modular_j (E := E)
  involutive := by
    intro v
    have h := congrArg (fun f => f v) (modular_j_involution (E := E))
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h

instance modular_jInvolution_preservesLinear :
    PreservesLinear (DoubledSpace E) (modular_jInvolution (E := E)) where
  map_add := by
    intro x y
    simpa [modular_jInvolution] using (modular_j (E := E)).map_add x y
  map_smul := by
    intro a x
    simpa [modular_jInvolution] using (modular_j (E := E)).map_smul a x

/-- Grade `+` projector `(Id + J)/2`. -/
noncomputable def gradePlusPart (v : DoubledSpace E) : DoubledSpace E :=
  Projector.plus (θ := modular_jInvolution (E := E)) v

/-- Grade `-` projector `(Id - J)/2`. -/
noncomputable def gradeMinusPart (v : DoubledSpace E) : DoubledSpace E :=
  Projector.minus (θ := modular_jInvolution (E := E)) v

lemma gradePlusPart_in_plus (v : DoubledSpace E) :
    inGradePlus (E := E) (gradePlusPart (E := E) v) := by
  simpa [inGradePlus, gradePlusPart, modular_jInvolution]
    using (Projector.plus_fixed (θ := modular_jInvolution (E := E)) v)

lemma gradeMinusPart_in_minus (v : DoubledSpace E) :
    inGradeMinus (E := E) (gradeMinusPart (E := E) v) := by
  simpa [inGradeMinus, gradeMinusPart, modular_jInvolution]
    using (Projector.minus_neg_fixed (θ := modular_jInvolution (E := E)) v)

lemma grade_decomposition (v : DoubledSpace E) :
    v = gradePlusPart (E := E) v + gradeMinusPart (E := E) v := by
  simpa [gradePlusPart, gradeMinusPart] using
    (Projector.decomposition (θ := modular_jInvolution (E := E)) v)

lemma spectral_epsilon_swaps_grades_plus_to_minus
    {v : DoubledSpace E}
    (hv : inGradePlus (E := E) v) :
    inGradeMinus (E := E) (spectral_epsilon (E := E) v) := by
  unfold inGradePlus at hv
  unfold inGradeMinus
  have hanti :=
    congrArg (fun f => f v) (modular_j_spectral_epsilon_anticommute (E := E))
  calc
    modular_j (E := E) (spectral_epsilon (E := E) v)
        = -(spectral_epsilon (E := E) ((modular_j (E := E)) v)) := by
            simpa [ContinuousLinearMap.comp_apply] using hanti
    _ = -(spectral_epsilon (E := E) v) := by rw [hv]

lemma spectral_epsilon_swaps_grades_minus_to_plus
    {v : DoubledSpace E}
    (hv : inGradeMinus (E := E) v) :
    inGradePlus (E := E) (spectral_epsilon (E := E) v) := by
  unfold inGradeMinus at hv
  unfold inGradePlus
  have hanti :=
    congrArg (fun f => f v) (modular_j_spectral_epsilon_anticommute (E := E))
  calc
    modular_j (E := E) (spectral_epsilon (E := E) v)
        = -(spectral_epsilon (E := E) ((modular_j (E := E)) v)) := by
            simpa [ContinuousLinearMap.comp_apply] using hanti
    _ = -(spectral_epsilon (E := E) (-v)) := by rw [hv]
    _ = spectral_epsilon (E := E) v := by
          simpa [spectral_epsilon, _root_.WithLp.fst,
            _root_.WithLp.snd]

/-- Odd operators anticommute with the grading involution `J`. -/
def isOdd (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  (modular_j (E := E)).comp A = -(A.comp (modular_j (E := E)))

lemma isEven_iff_gradeZero (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    isEven (E := E) A ↔ isGradeZero (E := E) A := Iff.rfl

/-- Conjugation by the grading involution on endomorphisms: `σ(A) = J ∘ A ∘ J`. -/
noncomputable def gradeConj (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  (modular_j (E := E)).comp (A.comp (modular_j (E := E)))

lemma isEven_iff_gradeConj_eq
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    isEven (E := E) A ↔ gradeConj (E := E) A = A := by
  constructor
  · intro hEven
    apply ContinuousLinearMap.ext
    intro v
    have hAtJ :
        (modular_j (E := E)) (A ((modular_j (E := E)) v))
          = A ((modular_j (E := E)) ((modular_j (E := E)) v)) := by
      simpa [ContinuousLinearMap.comp_apply] using
        congrArg (fun f => f ((modular_j (E := E)) v)) hEven
    simpa [gradeConj, ContinuousLinearMap.comp_apply, modular_j_involution] using hAtJ
  · intro hConj
    apply ContinuousLinearMap.ext
    intro v
    have hAtJ :
        (modular_j (E := E)) (A ((modular_j (E := E)) ((modular_j (E := E)) v)))
          = A ((modular_j (E := E)) v) := by
      simpa [gradeConj, ContinuousLinearMap.comp_apply] using
        congrArg (fun f => f ((modular_j (E := E)) v)) hConj
    simpa [ContinuousLinearMap.comp_apply, modular_j_involution] using hAtJ

lemma isOdd_iff_gradeConj_eq_neg
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    isOdd (E := E) A ↔ gradeConj (E := E) A = -A := by
  constructor
  · intro hOdd
    apply ContinuousLinearMap.ext
    intro v
    have hAtJ :
        (modular_j (E := E)) (A ((modular_j (E := E)) v))
          = -(A ((modular_j (E := E)) ((modular_j (E := E)) v))) := by
      simpa [ContinuousLinearMap.comp_apply] using
        congrArg (fun f => f ((modular_j (E := E)) v)) hOdd
    simpa [gradeConj, ContinuousLinearMap.comp_apply, modular_j_involution] using hAtJ
  · intro hConj
    apply ContinuousLinearMap.ext
    intro v
    have hAtJ :
        (modular_j (E := E)) (A ((modular_j (E := E)) ((modular_j (E := E)) v)))
          = -A ((modular_j (E := E)) v) := by
      simpa [gradeConj, ContinuousLinearMap.comp_apply] using
        congrArg (fun f => f ((modular_j (E := E)) v)) hConj
    simpa [ContinuousLinearMap.comp_apply, modular_j_involution] using hAtJ

/-- Even endomorphisms form a Lie subalgebra under the commutator. -/
def evenLieSubalgebra :
    LieSubalgebra ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) where
  carrier := {A | isEven (E := E) A}
  zero_mem' := by
    unfold isEven
    simp
  add_mem' := by
    intro A B hA hB
    unfold isEven at *
    calc
      (modular_j (E := E)).comp (A + B)
          = (modular_j (E := E)).comp A + (modular_j (E := E)).comp B := by
              simp [ContinuousLinearMap.comp_add]
      _ = A.comp (modular_j (E := E)) + B.comp (modular_j (E := E)) := by
            rw [hA, hB]
      _ = (A + B).comp (modular_j (E := E)) := by
            simp [ContinuousLinearMap.add_comp]
  smul_mem' := by
    intro a A hA
    unfold isEven at *
    calc
      (modular_j (E := E)).comp (a • A)
          = a • ((modular_j (E := E)).comp A) := by
              simp
      _ = a • (A.comp (modular_j (E := E))) := by rw [hA]
      _ = (a • A).comp (modular_j (E := E)) := by
            simp [ContinuousLinearMap.smul_comp]
  lie_mem' := by
    intro A B hA hB
    change isEven (E := E) (clmComm A B)
    exact even_closed_comm (E := E) hA hB

/-- Odd endomorphisms form a linear subspace (submodule), but not a Lie subalgebra. -/
def oddSubmodule :
    Submodule ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) where
  carrier := {A | isOdd (E := E) A}
  zero_mem' := by
    unfold isOdd
    simp
  add_mem' := by
    intro A B hA hB
    unfold isOdd at *
    calc
      (modular_j (E := E)).comp (A + B)
          = (modular_j (E := E)).comp A + (modular_j (E := E)).comp B := by
              simp [ContinuousLinearMap.comp_add]
      _ = -(A.comp (modular_j (E := E))) + -(B.comp (modular_j (E := E))) := by
            rw [hA, hB]
      _ = -(A.comp (modular_j (E := E)) + B.comp (modular_j (E := E))) := by
            abel_nf
      _ = -((A + B).comp (modular_j (E := E))) := by
            simp [ContinuousLinearMap.add_comp]
  smul_mem' := by
    intro a A hA
    unfold isOdd at *
    calc
      (modular_j (E := E)).comp (a • A)
          = a • ((modular_j (E := E)).comp A) := by
              simp
      _ = a • (-(A.comp (modular_j (E := E)))) := by rw [hA]
      _ = -((a • A).comp (modular_j (E := E))) := by
            simp [ContinuousLinearMap.smul_comp]

/-- Bracket closure `[𝔨, 𝔨] ⊆ 𝔨` for even endomorphisms. -/
lemma bracket_even_even_mem_even
    {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : isEven (E := E) A)
    (hB : isEven (E := E) B) :
    isEven (E := E) (clmComm A B) := by
  exact even_closed_comm (E := E) hA hB

/-- Bracket closure `[𝔨, 𝔭] ⊆ 𝔭` for even/odd endomorphisms. -/
lemma bracket_even_odd_mem_odd
    {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : isEven (E := E) A)
    (hB : isOdd (E := E) B) :
    isOdd (E := E) (clmComm A B) := by
  unfold isEven isOdd at *
  calc
    (modular_j (E := E)).comp (clmComm A B)
        = (modular_j (E := E)).comp (A.comp B) - (modular_j (E := E)).comp (B.comp A) := by
            simp [clmComm, ContinuousLinearMap.comp_sub]
    _ = ((modular_j (E := E)).comp A).comp B - ((modular_j (E := E)).comp B).comp A := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (A.comp (modular_j (E := E))).comp B - (-(B.comp (modular_j (E := E)))).comp A := by
          rw [hA, hB]
    _ = A.comp ((modular_j (E := E)).comp B) - (-(B.comp (modular_j (E := E)))).comp A := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = A.comp (-(B.comp (modular_j (E := E)))) - (-(B.comp (modular_j (E := E)))).comp A := by
          rw [hB]
    _ = -(A.comp (B.comp (modular_j (E := E)))) + (B.comp (modular_j (E := E))).comp A := by
          simp
    _ = -((A.comp B).comp (modular_j (E := E))) + B.comp ((modular_j (E := E)).comp A) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = -((A.comp B).comp (modular_j (E := E))) + B.comp (A.comp (modular_j (E := E))) := by
          rw [hA]
    _ = -((A.comp B).comp (modular_j (E := E))) + (B.comp A).comp (modular_j (E := E)) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = -(((A.comp B).comp (modular_j (E := E)) - (B.comp A).comp (modular_j (E := E)))) := by
          abel_nf
    _ = -(((A.comp B - B.comp A)).comp (modular_j (E := E))) := by
          simp [ContinuousLinearMap.sub_comp]
    _ = -((clmComm A B).comp (modular_j (E := E))) := by
          rfl

/-- Bracket closure `[𝔭, 𝔭] ⊆ 𝔨` for odd endomorphisms. -/
lemma bracket_odd_odd_mem_even
    {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : isOdd (E := E) A)
    (hB : isOdd (E := E) B) :
    isEven (E := E) (clmComm A B) := by
  unfold isEven isOdd at *
  calc
    (modular_j (E := E)).comp (clmComm A B)
        = (modular_j (E := E)).comp (A.comp B) - (modular_j (E := E)).comp (B.comp A) := by
            simp [clmComm, ContinuousLinearMap.comp_sub]
    _ = ((modular_j (E := E)).comp A).comp B - ((modular_j (E := E)).comp B).comp A := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (-(A.comp (modular_j (E := E)))).comp B - (-(B.comp (modular_j (E := E)))).comp A := by
          rw [hA, hB]
    _ = -(A.comp ((modular_j (E := E)).comp B)) + B.comp ((modular_j (E := E)).comp A) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = -(A.comp (-(B.comp (modular_j (E := E))))) + B.comp (-(A.comp (modular_j (E := E)))) := by
          rw [hB, hA]
    _ = A.comp (B.comp (modular_j (E := E))) + -(B.comp (A.comp (modular_j (E := E)))) := by
          simp
    _ = A.comp (B.comp (modular_j (E := E))) - B.comp (A.comp (modular_j (E := E))) := by
          simp [sub_eq_add_neg]
    _ = (A.comp B).comp (modular_j (E := E)) - (B.comp A).comp (modular_j (E := E)) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (clmComm A B).comp (modular_j (E := E)) := by
          simp [clmComm, ContinuousLinearMap.sub_comp]

/-- Canonical triple product on the odd sector: `[[X, Y], Z]`. -/
def oddTriple
    (A B C : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  clmComm (clmComm A B) C

/-- Triple closure `[𝔭, [𝔭, 𝔭]] ⊆ 𝔭`. -/
lemma odd_triple_mem_odd
    {A B C : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : isOdd (E := E) A)
    (hB : isOdd (E := E) B)
    (hC : isOdd (E := E) C) :
    isOdd (E := E) (oddTriple A B C) := by
  unfold oddTriple
  exact bracket_even_odd_mem_odd (E := E)
    (A := clmComm A B) (B := C)
    (bracket_odd_odd_mem_even (E := E) hA hB) hC

/-- Chirality/grade projectors as endomorphisms `(Id ± J)/2`. -/
noncomputable def gradePlusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) •
    (ContinuousLinearMap.id ℝ (DoubledSpace E) + modular_j (E := E))

noncomputable def gradeMinusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) •
    (ContinuousLinearMap.id ℝ (DoubledSpace E) - modular_j (E := E))

/-- Spectral projector `(Id + ε)/2`. -/
noncomputable def spectralPlusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) •
    (ContinuousLinearMap.id ℝ (DoubledSpace E) + spectral_epsilon (E := E))

/-- Spectral projector `(Id - ε)/2`. -/
noncomputable def spectralMinusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) •
    (ContinuousLinearMap.id ℝ (DoubledSpace E) - spectral_epsilon (E := E))

@[simp] lemma gradePlusProj_apply (v : DoubledSpace E) :
    gradePlusProj (E := E) v = gradePlusPart (E := E) v := by
  unfold gradePlusPart
  simp [gradePlusProj, Projector.plus, modular_jInvolution, smul_add]

@[simp] lemma gradeMinusProj_apply (v : DoubledSpace E) :
    gradeMinusProj (E := E) v = gradeMinusPart (E := E) v := by
  unfold gradeMinusPart
  simp [gradeMinusProj, Projector.minus, modular_jInvolution]

@[simp] lemma spectralPlusProj_apply (v : DoubledSpace E) :
    spectralPlusProj (E := E) v = InfoGeometry.Krein.to_doubled v.fst 0 := by
  apply (WithLp.ofLp_injective 2)
  cases h : WithLp.ofLp v with
  | mk x y =>
      have hfst : _root_.WithLp.fst v = x := by
        simpa using congrArg Prod.fst h
      have hsnd : _root_.WithLp.snd v = y := by
        simpa using congrArg Prod.snd h
      simp [spectralPlusProj, spectral_epsilon, InfoGeometry.Krein.to_doubled,
        _root_.WithLp.fst, _root_.WithLp.snd, h,
        smul_add]
      constructor
      · calc
          ((2 : ℝ)⁻¹) • x + ((2 : ℝ)⁻¹) • _root_.WithLp.fst v
              = ((2 : ℝ)⁻¹) • x + ((2 : ℝ)⁻¹) • x := by rw [hfst]
          _ = ((((2 : ℝ)⁻¹) + ((2 : ℝ)⁻¹)) : ℝ) • x := by
                  simpa using (add_smul ((2 : ℝ)⁻¹) ((2 : ℝ)⁻¹) x).symm
          _ = (1 : ℝ) • x := by norm_num
          _ = x := by simp
      · rw [hsnd]
        simp

@[simp] lemma spectralMinusProj_apply (v : DoubledSpace E) :
    spectralMinusProj (E := E) v = InfoGeometry.Krein.to_doubled 0 v.snd := by
  apply (WithLp.ofLp_injective 2)
  cases h : WithLp.ofLp v with
  | mk x y =>
      have hfst : _root_.WithLp.fst v = x := by
        simpa using congrArg Prod.fst h
      have hsnd : _root_.WithLp.snd v = y := by
        simpa using congrArg Prod.snd h
      simp [spectralMinusProj, spectral_epsilon, InfoGeometry.Krein.to_doubled,
        _root_.WithLp.fst, _root_.WithLp.snd, h,
        smul_add, sub_eq_add_neg]
      constructor
      · rw [hfst]
        simp
      · calc
          ((2 : ℝ)⁻¹) • y + ((2 : ℝ)⁻¹) • _root_.WithLp.snd v
              = ((2 : ℝ)⁻¹) • y + ((2 : ℝ)⁻¹) • y := by rw [hsnd]
          _ = ((((2 : ℝ)⁻¹) + ((2 : ℝ)⁻¹)) : ℝ) • y := by
                  simpa using (add_smul ((2 : ℝ)⁻¹) ((2 : ℝ)⁻¹) y).symm
          _ = (1 : ℝ) • y := by norm_num
          _ = y := by simp

lemma gradePlusProj_idempotent :
    (gradePlusProj (E := E)).comp (gradePlusProj (E := E)) = gradePlusProj (E := E) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [gradePlusPart, Projector.plus_idempotent]

lemma gradeMinusProj_idempotent :
    (gradeMinusProj (E := E)).comp (gradeMinusProj (E := E)) = gradeMinusProj (E := E) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [gradeMinusPart, Projector.minus_idempotent]

lemma gradePlusProj_comp_gradeMinusProj :
    (gradePlusProj (E := E)).comp (gradeMinusProj (E := E)) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  simp [gradePlusPart, gradeMinusPart, Projector.plus_minus]

lemma gradeMinusProj_comp_gradePlusProj :
    (gradeMinusProj (E := E)).comp (gradePlusProj (E := E)) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  simp [gradePlusPart, gradeMinusPart, Projector.minus_plus]

lemma gradeProj_sum :
    gradePlusProj (E := E) + gradeMinusProj (E := E)
      = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext
  intro v
  simpa [ContinuousLinearMap.id_apply] using (grade_decomposition (E := E) v).symm

lemma spectralPlusProj_idempotent :
    (spectralPlusProj (E := E)).comp (spectralPlusProj (E := E)) = spectralPlusProj (E := E) := by
  apply ContinuousLinearMap.ext
  intro v
  apply (WithLp.ofLp_injective 2)
  simp [spectralPlusProj_apply, InfoGeometry.Krein.to_doubled,
    _root_.WithLp.fst, _root_.WithLp.snd]

lemma spectralMinusProj_idempotent :
    (spectralMinusProj (E := E)).comp (spectralMinusProj (E := E)) = spectralMinusProj (E := E) := by
  apply ContinuousLinearMap.ext
  intro v
  apply (WithLp.ofLp_injective 2)
  simp [spectralMinusProj_apply, InfoGeometry.Krein.to_doubled,
    _root_.WithLp.fst, _root_.WithLp.snd]

lemma spectralPlusProj_comp_spectralMinusProj :
    (spectralPlusProj (E := E)).comp (spectralMinusProj (E := E)) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply InfoGeometry.Krein.DoubledSpace.ext
  · simp [spectralPlusProj_apply, spectralMinusProj_apply, InfoGeometry.Krein.to_doubled,
      _root_.WithLp.fst]
  · simp [spectralPlusProj_apply, spectralMinusProj_apply, InfoGeometry.Krein.to_doubled,
      _root_.WithLp.snd]

lemma spectralMinusProj_comp_spectralPlusProj :
    (spectralMinusProj (E := E)).comp (spectralPlusProj (E := E)) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply InfoGeometry.Krein.DoubledSpace.ext
  · simp [spectralPlusProj_apply, spectralMinusProj_apply, InfoGeometry.Krein.to_doubled,
      _root_.WithLp.fst]
  · simp [spectralPlusProj_apply, spectralMinusProj_apply, InfoGeometry.Krein.to_doubled,
      _root_.WithLp.snd]

lemma spectralProj_sum :
    spectralPlusProj (E := E) + spectralMinusProj (E := E)
      = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext
  intro v
  apply InfoGeometry.Krein.DoubledSpace.ext
  · rw [ContinuousLinearMap.id_apply, spectralPlusProj_apply, spectralMinusProj_apply,
      InfoGeometry.Krein.to_doubled, _root_.WithLp.fst, _root_.WithLp.fst]
    simp [InfoGeometry.Krein.to_doubled]
  · rw [ContinuousLinearMap.id_apply, spectralPlusProj_apply, spectralMinusProj_apply,
      InfoGeometry.Krein.to_doubled, _root_.WithLp.snd, _root_.WithLp.snd]
    simp [InfoGeometry.Krein.to_doubled]

lemma projector_commutator_gradePlus_spectralPlus :
    clmComm (gradePlusProj (E := E)) (spectralPlusProj (E := E))
      = ((4 : ℝ)⁻¹) • clmComm (modular_j (E := E)) (spectral_epsilon (E := E)) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [clmComm, gradePlusProj, spectralPlusProj, sub_eq_add_neg,
    smul_add, smul_smul, add_assoc, add_left_comm, add_comm]
  have hscalar : ((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) = (4 : ℝ)⁻¹ := by norm_num
  simp [hscalar]

lemma projector_commutator_gradePlus_spectralPlus_eq_half_complex_i :
    clmComm (gradePlusProj (E := E)) (spectralPlusProj (E := E))
      = ((2 : ℝ)⁻¹) • complex_i (E := E) := by
  rw [projector_commutator_gradePlus_spectralPlus (E := E)]
  have hanti := modular_j_spectral_epsilon_anticommute (E := E)
  calc
    ((4 : ℝ)⁻¹) • clmComm (modular_j (E := E)) (spectral_epsilon (E := E))
        = ((4 : ℝ)⁻¹) •
            ((modular_j (E := E)).comp (spectral_epsilon (E := E))
              - (spectral_epsilon (E := E)).comp (modular_j (E := E))) := by
              rfl
    _ = ((4 : ℝ)⁻¹) •
          ((modular_j (E := E)).comp (spectral_epsilon (E := E))
            + (modular_j (E := E)).comp (spectral_epsilon (E := E))) := by
          rw [hanti]
          simp [sub_eq_add_neg]
    _ = ((4 : ℝ)⁻¹) • ((2 : ℝ) • ((modular_j (E := E)).comp (spectral_epsilon (E := E)))) := by
          let X : DoubledSpace E →L[ℝ] DoubledSpace E :=
            (modular_j (E := E)).comp (spectral_epsilon (E := E))
          change ((4 : ℝ)⁻¹) • (X + X) = ((4 : ℝ)⁻¹) • ((2 : ℝ) • X)
          calc
            ((4 : ℝ)⁻¹) • (X + X) = ((4 : ℝ)⁻¹ • X + (4 : ℝ)⁻¹ • X) := by
              rw [smul_add]
            _ = (((4 : ℝ)⁻¹ + (4 : ℝ)⁻¹) : ℝ) • X := by
              simpa using (add_smul ((4 : ℝ)⁻¹) ((4 : ℝ)⁻¹) X).symm
            _ = ((2 : ℝ) * (4 : ℝ)⁻¹) • X := by
              have htwo : (((4 : ℝ)⁻¹ + (4 : ℝ)⁻¹) : ℝ) = ((2 : ℝ) * (4 : ℝ)⁻¹) := by ring
              rw [htwo]
            _ = ((4 : ℝ)⁻¹ * (2 : ℝ)) • X := by
              ring_nf
            _ = ((4 : ℝ)⁻¹) • ((2 : ℝ) • X) := by
              simp [smul_smul]
    _ = ((2 : ℝ)⁻¹) • complex_i (E := E) := by
          have hscalar : ((4 : ℝ)⁻¹ * (2 : ℝ)) = (2 : ℝ)⁻¹ := by norm_num
          rw [smul_smul, hscalar]
          simpa [complex_i, InfoGeometry.Krein.complex_i]

/-- Incompatibility of geometric and spectral splittings at projector level. -/
def splittingIncompatible : Prop :=
  clmComm (gradePlusProj (E := E)) (spectralPlusProj (E := E)) ≠ 0

lemma splittingIncompatible_iff_nonzero_clifford_comm :
    splittingIncompatible (E := E)
      ↔ clmComm (modular_j (E := E)) (spectral_epsilon (E := E)) ≠ 0 := by
  unfold splittingIncompatible
  rw [projector_commutator_gradePlus_spectralPlus (E := E)]
  constructor
  · intro h hComm
    apply h
    have hzero :
        ((4 : ℝ)⁻¹) • (0 : DoubledSpace E →L[ℝ] DoubledSpace E)
          = (0 : DoubledSpace E →L[ℝ] DoubledSpace E) := by
      apply ContinuousLinearMap.ext
      intro v
      apply (WithLp.ofLp_injective 2)
      simp
    simpa [hComm] using hzero
  · intro h hProj
    apply h
    have h4 : (4 : ℝ) ≠ 0 := by norm_num
    exact smul_eq_zero.mp hProj |>.resolve_left (inv_ne_zero h4)

lemma complex_i_ne_zero [Nontrivial E] :
    complex_i (E := E) ≠ 0 := by
  intro hI
  rcases exists_ne (0 : E) with ⟨x, hx⟩
  have hAt : complex_i (E := E) (InfoGeometry.Krein.to_doubled x 0) = (0 : DoubledSpace E) := by
    simpa using congrArg (fun T => T (InfoGeometry.Krein.to_doubled x 0)) hI
  have hx0 : x = 0 := by
    simpa [complex_i, modular_j, spectral_epsilon, InfoGeometry.Krein.to_doubled] using
      congrArg _root_.WithLp.snd hAt
  exact hx hx0

lemma splittingIncompatible_of_nontrivial [Nontrivial E] :
    splittingIncompatible (E := E) := by
  intro hSplit
  have hsmul0 : ((2 : ℝ)⁻¹) • complex_i (E := E) = 0 := by
    calc
      ((2 : ℝ)⁻¹) • complex_i (E := E)
          = clmComm (gradePlusProj (E := E)) (spectralPlusProj (E := E)) := by
              simpa using
                (projector_commutator_gradePlus_spectralPlus_eq_half_complex_i (E := E)).symm
      _ = 0 := hSplit
  have hhalf : ((2 : ℝ)⁻¹) ≠ 0 := by norm_num
  have hI0 : complex_i (E := E) = 0 :=
    (smul_eq_zero.mp hsmul0).resolve_left hhalf
  exact (complex_i_ne_zero (E := E)) hI0

/-- CAR-style dictionary entry: creation-like projector (grade `+`). -/
noncomputable def creationLike : DoubledSpace E →L[ℝ] DoubledSpace E :=
  gradePlusProj (E := E)

/-- CAR-style dictionary entry: annihilation-like projector (grade `-`). -/
noncomputable def annihilationLike : DoubledSpace E →L[ℝ] DoubledSpace E :=
  gradeMinusProj (E := E)

lemma creationLike_apply (v : DoubledSpace E) :
    creationLike (E := E) v = gradePlusPart (E := E) v := by
  simp [creationLike, gradePlusProj_apply]

lemma annihilationLike_apply (v : DoubledSpace E) :
    annihilationLike (E := E) v = gradeMinusPart (E := E) v := by
  simp [annihilationLike, gradeMinusProj_apply]

lemma modular_j_comp_creationLike :
    (modular_j (E := E)).comp (creationLike (E := E)) = creationLike (E := E) := by
  rw [creationLike, gradePlusProj, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_id,
      modular_j_involution (E := E), add_comm]
  rfl

lemma modular_j_comp_annihilationLike :
    (modular_j (E := E)).comp (annihilationLike (E := E)) =
      -(annihilationLike (E := E)) := by
  rw [annihilationLike, gradeMinusProj, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
      modular_j_involution (E := E)]
  simp only [ContinuousLinearMap.map_sub]
  rw [neg_sub]
  rfl

lemma creationLike_inGradePlus (v : DoubledSpace E) :
    inGradePlus (E := E) (creationLike (E := E) v) := by
  simpa [creationLike_apply] using gradePlusPart_in_plus (E := E) v

lemma annihilationLike_inGradeMinus (v : DoubledSpace E) :
    inGradeMinus (E := E) (annihilationLike (E := E) v) := by
  simpa [annihilationLike_apply] using gradeMinusPart_in_minus (E := E) v

lemma creation_annihilation_decomposition (v : DoubledSpace E) :
    v = creationLike (E := E) v + annihilationLike (E := E) v := by
  simpa [creationLike_apply, annihilationLike_apply] using grade_decomposition (E := E) v

lemma spectral_epsilon_isOdd :
    isOdd (E := E) (spectral_epsilon (E := E)) := by
  simpa [isOdd] using modular_j_spectral_epsilon_anticommute (E := E)

end KreinClifford

end InfoGeometry.Krein

export InfoGeometry.Krein
  (clmComm clmComm_eq_lie
   jordanProd comp_eq_jordan_add_half_comm
   isEven isGradeZero isOdd
   inGradePlus inGradeMinus
   gradePlusPart gradeMinusPart
   gradePlusPart_in_plus gradeMinusPart_in_minus grade_decomposition
   gradePlusProj gradeMinusProj spectralPlusProj spectralMinusProj
   gradePlusProj_apply gradeMinusProj_apply
   gradePlusProj_idempotent gradeMinusProj_idempotent
   gradePlusProj_comp_gradeMinusProj gradeMinusProj_comp_gradePlusProj
   gradeProj_sum
   spectralPlusProj_apply spectralMinusProj_apply
   spectralPlusProj_idempotent spectralMinusProj_idempotent
   spectralPlusProj_comp_spectralMinusProj spectralMinusProj_comp_spectralPlusProj
   spectralProj_sum
   projector_commutator_gradePlus_spectralPlus
   projector_commutator_gradePlus_spectralPlus_eq_half_complex_i
   splittingIncompatible splittingIncompatible_iff_nonzero_clifford_comm
   splittingIncompatible_of_nontrivial
   creationLike annihilationLike
   creationLike_apply annihilationLike_apply
   creationLike_inGradePlus annihilationLike_inGradeMinus
   creation_annihilation_decomposition
   spectral_epsilon_isOdd)
