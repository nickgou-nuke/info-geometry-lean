import InfoGeometry.Basic
import InfoGeometry.KL
import InfoGeometry.Fenchel
import InfoGeometry.Cramer
import Mathlib
import Mathlib.Probability.Distributions.Poisson

open scoped BigOperators

noncomputable def logRNDensity
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (x : α) : ℝ :=
  Real.log (densityRatio N_func Q x)

noncomputable def relativeSurprisal
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (x : α) : ℝ :=
  -logRNDensity N_func Q x

/-- Z(τ) = ∑ Q(x) * exp(-τ * ℓ(x)). -/
noncomputable def partitionFunction
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) : ℝ :=
  ∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x)

/-- Φ(τ) = log Z(τ). -/
noncomputable def Phi
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) : ℝ :=
  Real.log (partitionFunction N_func Q τ)

/-- Rényi section: D_τ = Φ(τ)/(τ-1). -/
noncomputable def RenyiD
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) : ℝ :=
  Phi N_func Q τ / (τ - 1)

section KreinClifford

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Doubled space `E ⊕ E` (geometric doubling of primal/dual sectors). -/
abbrev DoubledSpace (E : Type*) := E × E

/-- Swap involution `J(x, y) = (y, x)`. -/
def modularJ : DoubledSpace E →L[ℝ] DoubledSpace E where
  toLinearMap :=
    { toFun := fun v => (v.2, v.1)
      map_add' := by
        intro v w
        simp
      map_smul' := by
        intro a v
        simp }
  cont := by
    continuity

/-- Sign involution `ε(x, y) = (x, -y)`. -/
def spectralEpsilon : DoubledSpace E →L[ℝ] DoubledSpace E where
  toLinearMap :=
    { toFun := fun v => (v.1, -v.2)
      map_add' := by
        intro v w
        simp [add_comm]
      map_smul' := by
        intro a v
        simp [smul_neg] }
  cont := by
    continuity

/-- `I = J ∘ ε`, the canonical third generator. -/
def complexI : DoubledSpace E →L[ℝ] DoubledSpace E :=
  modularJ.comp spectralEpsilon

/-- Abstract `Cl(1,1)` relations for a pair of endomorphisms. -/
structure Cl11Algebra
    (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop where
  j_involution : J.comp J = ContinuousLinearMap.id ℝ (DoubledSpace E)
  eps_involution : ε.comp ε = ContinuousLinearMap.id ℝ (DoubledSpace E)
  anticommute : J.comp ε = -(ε.comp J)

lemma modularJ_involution :
    modularJ (E := E).comp (modularJ (E := E)) =
      ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  ext v <;> simp [modularJ]

lemma spectralEpsilon_involution :
    spectralEpsilon (E := E).comp (spectralEpsilon (E := E)) =
      ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  ext v <;> simp [spectralEpsilon]

lemma modularJ_spectralEpsilon_anticommute :
    modularJ (E := E).comp (spectralEpsilon (E := E)) =
      -((spectralEpsilon (E := E)).comp (modularJ (E := E))) := by
  ext v <;> simp [modularJ, spectralEpsilon]

theorem modularJ_spectralEpsilon_isCl11 :
    Cl11Algebra (modularJ (E := E)) (spectralEpsilon (E := E)) := by
  refine ⟨modularJ_involution (E := E), spectralEpsilon_involution (E := E),
    modularJ_spectralEpsilon_anticommute (E := E)⟩

/-- Commutator bracket on doubled-space endomorphisms. -/
def clmComm
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  A.comp B - B.comp A

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

/-- Grade-0 (structure) operators commute with the grading involution `J`. -/
def isGradeZero (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  (modularJ (E := E)).comp A = A.comp (modularJ (E := E))

lemma jordanProd_comm
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    jordanProd A B = jordanProd B A := by
  simp [jordanProd, add_comm]

lemma comp_eq_jordan_add_half_comm
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    A.comp B
      = jordanProd A B + ((2 : ℝ)⁻¹) • clmComm A B := by
  have hhalf : (((2 : ℝ)⁻¹) + ((2 : ℝ)⁻¹)) = 1 := by norm_num
  have hsplit (x : E) : x = ((2 : ℝ)⁻¹) • x + ((2 : ℝ)⁻¹) • x := by
    calc
      x = (1 : ℝ) • x := by simp
      _ = ((((2 : ℝ)⁻¹) + ((2 : ℝ)⁻¹)) : ℝ) • x := by simp [hhalf]
      _ = ((2 : ℝ)⁻¹) • x + ((2 : ℝ)⁻¹) • x := by simp [add_smul]
  apply ContinuousLinearMap.ext
  intro v
  ext <;>
    simp [jordanProd, clmComm, sub_eq_add_neg, smul_add, add_assoc, add_left_comm]
  · exact hsplit ((A (B v)).1)
  · exact hsplit ((A (B v)).2)

lemma gradeZero_closed_comm
    {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : isGradeZero (E := E) A)
    (hB : isGradeZero (E := E) B) :
    isGradeZero (E := E) (clmComm A B) := by
  unfold isGradeZero at *
  calc
    (modularJ (E := E)).comp (clmComm A B)
        = (modularJ (E := E)).comp (A.comp B) - (modularJ (E := E)).comp (B.comp A) := by
            simp [clmComm, ContinuousLinearMap.comp_sub]
    _ = ((modularJ (E := E)).comp A).comp B - ((modularJ (E := E)).comp B).comp A := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (A.comp (modularJ (E := E))).comp B - (B.comp (modularJ (E := E))).comp A := by
          rw [hA, hB]
    _ = A.comp ((modularJ (E := E)).comp B) - B.comp ((modularJ (E := E)).comp A) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = A.comp (B.comp (modularJ (E := E))) - B.comp (A.comp (modularJ (E := E))) := by
          rw [hB, hA]
    _ = (A.comp B).comp (modularJ (E := E)) - (B.comp A).comp (modularJ (E := E)) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (clmComm A B).comp (modularJ (E := E)) := by
          simp [clmComm, ContinuousLinearMap.sub_comp]

/-- `+1` eigenspace predicate for the grading involution `J`. -/
def inGradePlus (v : DoubledSpace E) : Prop := modularJ (E := E) v = v

/-- `-1` eigenspace predicate for the grading involution `J`. -/
def inGradeMinus (v : DoubledSpace E) : Prop := modularJ (E := E) v = -v

/-- Grade `+` projector `(Id + J)/2`. -/
noncomputable def gradePlusPart (v : DoubledSpace E) : DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (v + modularJ (E := E) v)

/-- Grade `-` projector `(Id - J)/2`. -/
noncomputable def gradeMinusPart (v : DoubledSpace E) : DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (v - modularJ (E := E) v)

lemma gradePlusPart_in_plus (v : DoubledSpace E) :
    inGradePlus (E := E) (gradePlusPart (E := E) v) := by
  ext <;> simp [gradePlusPart, modularJ, add_comm]

lemma gradeMinusPart_in_minus (v : DoubledSpace E) :
    inGradeMinus (E := E) (gradeMinusPart (E := E) v) := by
  ext <;> simp [gradeMinusPart, modularJ, sub_eq_add_neg, add_comm]

lemma grade_decomposition (v : DoubledSpace E) :
    v = gradePlusPart (E := E) v + gradeMinusPart (E := E) v := by
  have hhalf : ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = 1 := by norm_num
  ext <;> simp [gradePlusPart, gradeMinusPart, modularJ, sub_eq_add_neg, add_comm,
    add_left_comm, add_assoc, smul_add]
  · calc
      v.1 = (1 : ℝ) • v.1 := by simp
      _ = (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • v.1 := by simp [hhalf]
      _ = (2 : ℝ)⁻¹ • v.1 + (2 : ℝ)⁻¹ • v.1 := by simp [add_smul]
  · calc
      v.2 = (1 : ℝ) • v.2 := by simp
      _ = (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • v.2 := by simp [hhalf]
      _ = (2 : ℝ)⁻¹ • v.2 + (2 : ℝ)⁻¹ • v.2 := by simp [add_smul]

lemma spectralEpsilon_swaps_grades_plus_to_minus
    {v : DoubledSpace E}
    (hv : inGradePlus (E := E) v) :
    inGradeMinus (E := E) (spectralEpsilon (E := E) v) := by
  rcases v with ⟨x, y⟩
  have hpair : (y, x) = (x, y) := by simpa [inGradePlus, modularJ] using hv
  have hxy : y = x := by simpa using congrArg Prod.fst hpair
  subst hxy
  simp [inGradeMinus, modularJ, spectralEpsilon]

lemma spectralEpsilon_swaps_grades_minus_to_plus
    {v : DoubledSpace E}
    (hv : inGradeMinus (E := E) v) :
    inGradePlus (E := E) (spectralEpsilon (E := E) v) := by
  rcases v with ⟨x, y⟩
  have hpair : (y, x) = (-x, -y) := by simpa [inGradeMinus, modularJ] using hv
  have hxy : y = -x := by simpa using congrArg Prod.fst hpair
  subst hxy
  simp [inGradePlus, modularJ, spectralEpsilon]

/-- Even operators commute with the grading involution `J`. -/
def isEven (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  (modularJ (E := E)).comp A = A.comp (modularJ (E := E))

/-- Odd operators anticommute with the grading involution `J`. -/
def isOdd (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  (modularJ (E := E)).comp A = -(A.comp (modularJ (E := E)))

lemma isEven_iff_gradeZero (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    isEven (E := E) A ↔ isGradeZero (E := E) A := Iff.rfl

/-- Chirality/grade projectors as endomorphisms `(Id ± J)/2`. -/
noncomputable def gradePlusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) •
    (ContinuousLinearMap.id ℝ (DoubledSpace E) + modularJ (E := E))

noncomputable def gradeMinusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) •
    (ContinuousLinearMap.id ℝ (DoubledSpace E) - modularJ (E := E))

/-- Spectral projector `(Id + ε)/2`. -/
noncomputable def spectralPlusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) •
    (ContinuousLinearMap.id ℝ (DoubledSpace E) + spectralEpsilon (E := E))

/-- Spectral projector `(Id - ε)/2`. -/
noncomputable def spectralMinusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) •
    (ContinuousLinearMap.id ℝ (DoubledSpace E) - spectralEpsilon (E := E))

lemma gradePlusProj_apply (v : DoubledSpace E) :
    gradePlusProj (E := E) v = gradePlusPart (E := E) v := by
  simp [gradePlusProj, gradePlusPart]

lemma gradeMinusProj_apply (v : DoubledSpace E) :
    gradeMinusProj (E := E) v = gradeMinusPart (E := E) v := by
  simp [gradeMinusProj, gradeMinusPart]

lemma projector_commutator_gradePlus_spectralPlus :
    clmComm (gradePlusProj (E := E)) (spectralPlusProj (E := E))
      = ((4 : ℝ)⁻¹) • clmComm (modularJ (E := E)) (spectralEpsilon (E := E)) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [clmComm, gradePlusProj, spectralPlusProj, sub_eq_add_neg,
    smul_add, smul_smul, add_assoc, add_left_comm, add_comm]
  abel_nf
  have hscalar : ((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) = (4 : ℝ)⁻¹ := by norm_num
  simp [hscalar]

lemma projector_commutator_gradePlus_spectralPlus_eq_half_complexI :
    clmComm (gradePlusProj (E := E)) (spectralPlusProj (E := E))
      = ((2 : ℝ)⁻¹) • complexI (E := E) := by
  rw [projector_commutator_gradePlus_spectralPlus (E := E)]
  have hanti := modularJ_spectralEpsilon_anticommute (E := E)
  calc
    ((4 : ℝ)⁻¹) • clmComm (modularJ (E := E)) (spectralEpsilon (E := E))
        = ((4 : ℝ)⁻¹) •
            ((modularJ (E := E)).comp (spectralEpsilon (E := E))
              - (spectralEpsilon (E := E)).comp (modularJ (E := E))) := by
              rfl
    _ = ((4 : ℝ)⁻¹) •
          ((modularJ (E := E)).comp (spectralEpsilon (E := E))
            + (modularJ (E := E)).comp (spectralEpsilon (E := E))) := by
          rw [hanti]
          simp [sub_eq_add_neg]
    _ = ((4 : ℝ)⁻¹) • ((2 : ℝ) • ((modularJ (E := E)).comp (spectralEpsilon (E := E)))) := by
          simp [two_smul]
    _ = ((2 : ℝ)⁻¹) • complexI (E := E) := by
          have hscalar : ((4 : ℝ)⁻¹ * (2 : ℝ)) = (2 : ℝ)⁻¹ := by norm_num
          simp [complexI, smul_smul, hscalar]

/-- Incompatibility of geometric and spectral splittings at projector level. -/
def splittingIncompatible : Prop :=
  clmComm (gradePlusProj (E := E)) (spectralPlusProj (E := E)) ≠ 0

lemma splittingIncompatible_iff_nonzero_clifford_comm :
    splittingIncompatible (E := E)
      ↔ clmComm (modularJ (E := E)) (spectralEpsilon (E := E)) ≠ 0 := by
  unfold splittingIncompatible
  rw [projector_commutator_gradePlus_spectralPlus (E := E)]
  constructor
  · intro h hComm
    apply h
    simp [hComm]
  · intro h hProj
    apply h
    have h4 : (4 : ℝ) ≠ 0 := by norm_num
    exact smul_eq_zero.mp hProj |>.resolve_left (inv_ne_zero h4)

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

lemma modularJ_comp_creationLike :
    (modularJ (E := E)).comp (creationLike (E := E)) = creationLike (E := E) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [creationLike, gradePlusProj, modularJ, add_comm]

lemma modularJ_comp_annihilationLike :
    (modularJ (E := E)).comp (annihilationLike (E := E)) =
      -(annihilationLike (E := E)) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [annihilationLike, gradeMinusProj, modularJ, sub_eq_add_neg, add_comm]

lemma creationLike_inGradePlus (v : DoubledSpace E) :
    inGradePlus (E := E) (creationLike (E := E) v) := by
  simpa [creationLike_apply] using gradePlusPart_in_plus (E := E) v

lemma annihilationLike_inGradeMinus (v : DoubledSpace E) :
    inGradeMinus (E := E) (annihilationLike (E := E) v) := by
  simpa [annihilationLike_apply] using gradeMinusPart_in_minus (E := E) v

lemma creation_annihilation_decomposition (v : DoubledSpace E) :
    v = creationLike (E := E) v + annihilationLike (E := E) v := by
  simpa [creationLike_apply, annihilationLike_apply] using grade_decomposition (E := E) v

lemma spectralEpsilon_isOdd :
    isOdd (E := E) (spectralEpsilon (E := E)) := by
  simpa [isOdd] using modularJ_spectralEpsilon_anticommute (E := E)

/-- Algebraic supercharge package: odd generator and its square Hamiltonian. -/
structure Supercharge where
  Q : DoubledSpace E →L[ℝ] DoubledSpace E
  odd : isOdd (E := E) Q

def superHamiltonian (S : Supercharge (E := E)) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  S.Q.comp S.Q

lemma superHamiltonian_isEven (S : Supercharge (E := E)) :
    isEven (E := E) (superHamiltonian (E := E) S) := by
  unfold isEven superHamiltonian
  calc
    (modularJ (E := E)).comp (S.Q.comp S.Q)
        = ((modularJ (E := E)).comp S.Q).comp S.Q := by
            simp [ContinuousLinearMap.comp_assoc]
    _ = (-(S.Q.comp (modularJ (E := E)))).comp S.Q := by
      rw [S.odd]
    _ = -((S.Q.comp (modularJ (E := E))).comp S.Q) := by
          simp
    _ = -(S.Q.comp ((modularJ (E := E)).comp S.Q)) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = -(S.Q.comp (-(S.Q.comp (modularJ (E := E))))) := by
      rw [S.odd]
    _ = S.Q.comp (S.Q.comp (modularJ (E := E))) := by
          simp
    _ = (S.Q.comp S.Q).comp (modularJ (E := E)) := by
          simp [ContinuousLinearMap.comp_assoc]

/-- Explicit dictionary: chirality operator is the grading involution. -/
def chiralityOperator : DoubledSpace E →L[ℝ] DoubledSpace E :=
  modularJ (E := E)

/-- Explicit dictionary: complex-structure operator derived from Clifford generators. -/
def complexStructureOperator : DoubledSpace E →L[ℝ] DoubledSpace E :=
  complexI (E := E)

/-- Endomorphism-level notion of an internal complex structure (`I^2 = -Id`). -/
def isComplexStructureOp (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  A.comp A = -(ContinuousLinearMap.id ℝ (DoubledSpace E))

lemma complexI_sq_neg_id :
    (complexI (E := E)).comp (complexI (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  apply ContinuousLinearMap.ext
  intro v
  rcases v with ⟨x, y⟩
  simp [complexI, modularJ, spectralEpsilon]

lemma complexI_isComplexStructureOp :
    isComplexStructureOp (E := E) (complexI (E := E)) :=
  complexI_sq_neg_id (E := E)

lemma neg_complexI_isComplexStructureOp :
    isComplexStructureOp (E := E) (-(complexI (E := E))) := by
  unfold isComplexStructureOp
  calc
    (-(complexI (E := E))).comp (-(complexI (E := E)))
        = (complexI (E := E)).comp (complexI (E := E)) := by
            apply ContinuousLinearMap.ext
            intro v
            rcases v with ⟨x, y⟩
            simp
    _ = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) :=
          complexI_sq_neg_id (E := E)

/-- Minimal vacuum/polarization viewpoint: choice of internal `i` among admissible
complex structures generated by the Clifford pair. -/
structure VacuumChoice where
  imag : DoubledSpace E →L[ℝ] DoubledSpace E
  imag_sq_neg_id : isComplexStructureOp (E := E) imag

def vacuumChoicePlus : VacuumChoice (E := E) where
  imag := complexI (E := E)
  imag_sq_neg_id := complexI_isComplexStructureOp (E := E)

def vacuumChoiceMinus : VacuumChoice (E := E) where
  imag := -(complexI (E := E))
  imag_sq_neg_id := neg_complexI_isComplexStructureOp (E := E)

/-- Vacuum-dependent polarization projector `(Id + imag)/2`. -/
noncomputable def vacuumPolarizationPlus
    (V : VacuumChoice (E := E)) : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) •
    (ContinuousLinearMap.id ℝ (DoubledSpace E) + V.imag)

/-- Vacuum-dependent polarization projector `(Id - imag)/2`. -/
noncomputable def vacuumPolarizationMinus
    (V : VacuumChoice (E := E)) : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) •
    (ContinuousLinearMap.id ℝ (DoubledSpace E) - V.imag)

theorem vacuumChoice_switch_swaps_polarizations_plus :
    vacuumPolarizationPlus (E := E) (vacuumChoicePlus (E := E))
      = vacuumPolarizationMinus (E := E) (vacuumChoiceMinus (E := E)) := by
  apply ContinuousLinearMap.ext
  intro v
  rcases v with ⟨x, y⟩
  simp [vacuumPolarizationPlus, vacuumPolarizationMinus,
    vacuumChoicePlus, vacuumChoiceMinus, sub_eq_add_neg]

theorem vacuumChoice_switch_swaps_polarizations_minus :
    vacuumPolarizationMinus (E := E) (vacuumChoicePlus (E := E))
      = vacuumPolarizationPlus (E := E) (vacuumChoiceMinus (E := E)) := by
  apply ContinuousLinearMap.ext
  intro v
  rcases v with ⟨x, y⟩
  simp [vacuumPolarizationPlus, vacuumPolarizationMinus,
    vacuumChoicePlus, vacuumChoiceMinus, sub_eq_add_neg]

/-- Projectivization dictionary: two nonzero vectors represent the same ray
iff they differ by a nonzero real scalar. -/
def SameRayDoubled (v w : DoubledSpace E) : Prop :=
  ∃ a : ℝ, a ≠ 0 ∧ w = a • v

lemma sameRay_refl {v : DoubledSpace E} : SameRayDoubled v v := by
  refine ⟨1, by norm_num, ?_⟩
  simp

lemma sameRay_symm {v w : DoubledSpace E} :
    SameRayDoubled v w → SameRayDoubled w v := by
  rintro ⟨a, ha, rfl⟩
  refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
  calc
    v = (a⁻¹ * a) • v := by simp [ha]
    _ = a⁻¹ • (a • v) := by simp [smul_smul]

lemma sameRay_trans {u v w : DoubledSpace E} :
    SameRayDoubled u v → SameRayDoubled v w → SameRayDoubled u w := by
  rintro ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
  simp [smul_smul, mul_comm]

/-- Setoid for projectivized doubled states (rays). -/
def sameRaySetoid : Setoid (DoubledSpace E) where
  r := SameRayDoubled
  iseqv := ⟨
    by intro x; exact sameRay_refl (E := E),
    by intro x y hxy; exact sameRay_symm (E := E) hxy,
    by intro x y z hxy hyz; exact sameRay_trans (E := E) hxy hyz
  ⟩

/-- Projective states: quotient of doubled states by nonzero real rescaling. -/
def ProjectiveState : Type _ := Quotient (sameRaySetoid (E := E))

/-- Canonical projection from a doubled state to its projective ray class. -/
def projectivize (v : DoubledSpace E) : ProjectiveState (E := E) :=
  Quotient.mk'' v

lemma sameRayDoubled_map
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    {v w : DoubledSpace E} :
    SameRayDoubled (E := E) v w →
      SameRayDoubled (E := E) (A v) (A w) := by
  rintro ⟨a, ha, hw⟩
  refine ⟨a, ha, ?_⟩
  rw [hw]
  simp

/-- Any linear endomorphism descends to projective rays. -/
def projectiveMap
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    ProjectiveState (E := E) → ProjectiveState (E := E) :=
  Quotient.map (fun v => A v) (by
    intro v w hvw
    exact sameRayDoubled_map (E := E) A hvw)

lemma projectiveMap_mk
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (v : DoubledSpace E) :
    projectiveMap (E := E) A (projectivize (E := E) v)
      = projectivize (E := E) (A v) := rfl

/-- Grade-preserving (even) endomorphisms descend to projective states. -/
def projectiveMapEven
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (_hA : isEven (E := E) A) :
    ProjectiveState (E := E) → ProjectiveState (E := E) :=
  projectiveMap (E := E) A

lemma projectiveMapEven_mk
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven (E := E) A)
    (v : DoubledSpace E) :
    projectiveMapEven (E := E) A hA (projectivize (E := E) v)
      = projectivize (E := E) (A v) := rfl

lemma projectiveMap_id :
    projectiveMap (E := E) (ContinuousLinearMap.id ℝ (DoubledSpace E))
      = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro v
  rfl

lemma projectiveMap_comp
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    projectiveMap (E := E) (A.comp B)
      = (projectiveMap (E := E) A) ∘ (projectiveMap (E := E) B) := by
  funext q
  refine Quotient.inductionOn q ?_
  intro v
  rfl

lemma projectiveMapEven_id
    (hId : isEven (E := E) (ContinuousLinearMap.id ℝ (DoubledSpace E))) :
    projectiveMapEven (E := E) (ContinuousLinearMap.id ℝ (DoubledSpace E)) hId = id :=
  projectiveMap_id (E := E)

lemma projectiveMapEven_comp
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven (E := E) A)
    (hB : isEven (E := E) B) :
    projectiveMapEven (E := E) (A.comp B)
      (by
        unfold isEven at *
        calc
          (modularJ (E := E)).comp (A.comp B)
              = ((modularJ (E := E)).comp A).comp B := by
                  simp [ContinuousLinearMap.comp_assoc]
          _ = (A.comp (modularJ (E := E))).comp B := by rw [hA]
          _ = A.comp ((modularJ (E := E)).comp B) := by
                simp [ContinuousLinearMap.comp_assoc]
          _ = A.comp (B.comp (modularJ (E := E))) := by rw [hB]
          _ = (A.comp B).comp (modularJ (E := E)) := by
                simp [ContinuousLinearMap.comp_assoc])
      = (projectiveMapEven (E := E) A hA) ∘ (projectiveMapEven (E := E) B hB) :=
  projectiveMap_comp (E := E) A B

/-- Minimal prequantum line-bundle data (scalarized): symplectic scale `ω`,
curvature scale `F`, and conversion constant `ℏ` with relation `F = ω / ℏ`. -/
structure PrequantumData where
  omegaScale : ℝ
  curvatureScale : ℝ
  hbar : ℝ
  hbar_ne_zero : hbar ≠ 0
  curvature_law : curvatureScale = omegaScale / hbar

theorem PrequantumData.curvature_mul_hbar_eq_omega
    (P : PrequantumData) :
    P.curvatureScale * P.hbar = P.omegaScale := by
  rw [P.curvature_law]
  field_simp [P.hbar_ne_zero]

theorem PrequantumData.omega_eq_hbar_mul_curvature
    (P : PrequantumData) :
    P.omegaScale = P.hbar * P.curvatureScale := by
  have h := P.curvature_mul_hbar_eq_omega
  linarith

/-- Rescaling `ℏ` by `c` rescales curvature by `1/c` at fixed symplectic scale. -/
noncomputable def PrequantumData.rescaleHbar
    (P : PrequantumData) (c : ℝ) (hc : c ≠ 0) : PrequantumData where
  omegaScale := P.omegaScale
  curvatureScale := P.curvatureScale / c
  hbar := c * P.hbar
  hbar_ne_zero := mul_ne_zero hc P.hbar_ne_zero
  curvature_law := by
    rw [P.curvature_law]
    field_simp [hc, P.hbar_ne_zero]

theorem PrequantumData.rescaleHbar_curvature
    (P : PrequantumData) (c : ℝ) (hc : c ≠ 0) :
    (P.rescaleHbar c hc).curvatureScale = P.curvatureScale / c := rfl

theorem PrequantumData.rescaleHbar_hbar
    (P : PrequantumData) (c : ℝ) (hc : c ≠ 0) :
    (P.rescaleHbar c hc).hbar = c * P.hbar := rfl

/-- Bundle-level packaging over projective spinor rays. -/
structure ProjectivePrequantumBundle where
  base : ProjectiveState (E := E)
  data : PrequantumData

/-- Scalarized holonomy scale attached to prequantum connection data. -/
def PrequantumData.holonomyScale (P : PrequantumData) : ℝ :=
  P.curvatureScale

theorem PrequantumData.holonomyScale_eq_omega_over_hbar
    (P : PrequantumData) :
    P.holonomyScale = P.omegaScale / P.hbar :=
  P.curvature_law

lemma supercharge_maps_plus_to_minus
    (S : Supercharge (E := E))
    {v : DoubledSpace E}
    (hv : inGradePlus (E := E) v) :
    inGradeMinus (E := E) (S.Q v) := by
  have hoddv : modularJ (E := E) (S.Q v) = -S.Q (modularJ (E := E) v) := by
    have h := congrArg (fun T => T v) S.odd
    simpa [ContinuousLinearMap.comp_apply] using h
  unfold inGradeMinus
  calc
    modularJ (E := E) (S.Q v) = -S.Q (modularJ (E := E) v) := hoddv
    _ = -S.Q v := by rw [hv]

lemma supercharge_maps_minus_to_plus
    (S : Supercharge (E := E))
    {v : DoubledSpace E}
    (hv : inGradeMinus (E := E) v) :
    inGradePlus (E := E) (S.Q v) := by
  have hoddv : modularJ (E := E) (S.Q v) = -S.Q (modularJ (E := E) v) := by
    have h := congrArg (fun T => T v) S.odd
    simpa [ContinuousLinearMap.comp_apply] using h
  unfold inGradePlus
  calc
    modularJ (E := E) (S.Q v) = -S.Q (modularJ (E := E) v) := hoddv
    _ = S.Q v := by
          rw [hv]
          simp

/-- Dilation operator extracted from the commutator `[J, ε]`. -/
noncomputable def dilationOperator : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • clmComm (modularJ (E := E)) (spectralEpsilon (E := E))

theorem clmComm_modularJ_spectralEpsilon :
    clmComm (modularJ (E := E)) (spectralEpsilon (E := E))
      = (2 : ℝ) • complexI (E := E) := by
  ext v <;> simp [clmComm, complexI, modularJ, spectralEpsilon, two_smul, sub_eq_add_neg]

theorem dilationOperator_eq_complexI :
    dilationOperator (E := E) = complexI (E := E) := by
  rw [dilationOperator, clmComm_modularJ_spectralEpsilon]
  simp [smul_smul]

/-- Algebraic closure relation `[I, J] = -2 ε`. -/
theorem clmComm_complexI_modularJ :
    clmComm (complexI (E := E)) (modularJ (E := E))
      = (-2 : ℝ) • spectralEpsilon (E := E) := by
  ext v <;> simp [clmComm, complexI, modularJ, spectralEpsilon, two_smul, sub_eq_add_neg]

/-- Algebraic closure relation `[I, ε] = 2 J`. -/
theorem clmComm_complexI_spectralEpsilon :
    clmComm (complexI (E := E)) (spectralEpsilon (E := E))
      = (2 : ℝ) • modularJ (E := E) := by
  ext v <;> simp [clmComm, complexI, modularJ, spectralEpsilon, two_smul, sub_eq_add_neg]

section Metric

variable [InnerProductSpace ℝ E]

/-- Indefinite Hessian pairing on the doubled space. -/
def hessianIndefiniteForm (v w : DoubledSpace E) : ℝ :=
  inner ℝ v.1 w.2 + inner ℝ w.1 v.2

omit [NormedSpace ℝ E] in
lemma hessianIndefiniteForm_symm (v w : DoubledSpace E) :
    hessianIndefiniteForm (E := E) v w = hessianIndefiniteForm (E := E) w v := by
  simp [hessianIndefiniteForm, add_comm]

omit [NormedSpace ℝ E] in
lemma hessianIndefiniteForm_isotropic_primal (x : E) :
    hessianIndefiniteForm (E := E) (x, (0 : E)) (x, (0 : E)) = 0 := by
  simp [hessianIndefiniteForm]

omit [NormedSpace ℝ E] in
lemma hessianIndefiniteForm_isotropic_dual (ξ : E) :
    hessianIndefiniteForm (E := E) ((0 : E), ξ) ((0 : E), ξ) = 0 := by
  simp [hessianIndefiniteForm]

/-- Metric-preserving endomorphisms of the doubled neutral space. -/
def preservesMetric (U : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  ∀ v w, hessianIndefiniteForm (E := E) (U v) (U w) = hessianIndefiniteForm (E := E) v w

/-- Metric-reversing endomorphisms of the doubled neutral space. -/
def antiPreservesMetric (U : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  ∀ v w, hessianIndefiniteForm (E := E) (U v) (U w) = -hessianIndefiniteForm (E := E) v w

/-- Infinitesimal isometries for the neutral Hessian form (Lie algebra condition). -/
def IsInfinitesimalIsometry (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  ∀ v w,
    hessianIndefiniteForm (E := E) (A v) w +
      hessianIndefiniteForm (E := E) v (A w) = 0

/-- Continuous automorphisms preserving the neutral Hessian pairing. -/
structure KreinIsometry where
  U : DoubledSpace E ≃L[ℝ] DoubledSpace E
  isometry : preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E)

/-- Continuous automorphisms reversing the neutral Hessian pairing. -/
structure KreinAntiIsometry where
  U : DoubledSpace E ≃L[ℝ] DoubledSpace E
  antiIsometry : antiPreservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E)

/-- Orthogonal isometries of the doubled neutral form `hessianIndefiniteForm`
(`O(hessianIndefiniteForm)`, finite-dimensional model of `O(n,n)`). -/
def HessianOrthogonalGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [InnerProductSpace ℝ E] : Type _ :=
  {U : DoubledSpace E ≃L[ℝ] DoubledSpace E //
    preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E)}

lemma preservesMetric_id :
    preservesMetric (E := E) (ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  intro v w
  simp

lemma preservesMetric_comp
    {U V : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hU : preservesMetric (E := E) U)
    (hV : preservesMetric (E := E) V) :
    preservesMetric (E := E) (U.comp V) := by
  intro v w
  calc
    hessianIndefiniteForm (E := E) ((U.comp V) v) ((U.comp V) w)
        = hessianIndefiniteForm (E := E) (U (V v)) (U (V w)) := by rfl
    _ = hessianIndefiniteForm (E := E) (V v) (V w) := hU (V v) (V w)
    _ = hessianIndefiniteForm (E := E) v w := hV v w

lemma preservesMetric_symm
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (hU : preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E)) :
    preservesMetric (E := E) (U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) := by
  intro v w
  have h := hU (U.symm v) (U.symm w)
  simpa using h.symm

lemma preservesMetric_equiv_comp
    (U V : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (hU : preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E))
    (hV : preservesMetric (E := E) (V : DoubledSpace E →L[ℝ] DoubledSpace E)) :
    preservesMetric (E := E)
      ((U : DoubledSpace E →L[ℝ] DoubledSpace E).comp
        (V : DoubledSpace E →L[ℝ] DoubledSpace E)) := by
  exact preservesMetric_comp (E := E) hU hV

def HessianOrthogonalGroup.one : HessianOrthogonalGroup E :=
  ⟨ContinuousLinearEquiv.refl ℝ (DoubledSpace E), preservesMetric_id (E := E)⟩

def HessianOrthogonalGroup.comp
    (U V : HessianOrthogonalGroup E) :
    HessianOrthogonalGroup E := by
  refine ⟨U.1.trans V.1, ?_⟩
  intro v w
  change hessianIndefiniteForm (E := E) (V.1 (U.1 v)) (V.1 (U.1 w))
      = hessianIndefiniteForm (E := E) v w
  calc
    hessianIndefiniteForm (E := E) (V.1 (U.1 v)) (V.1 (U.1 w))
        = hessianIndefiniteForm (E := E) (U.1 v) (U.1 w) := V.2 (U.1 v) (U.1 w)
    _ = hessianIndefiniteForm (E := E) v w := U.2 v w

def HessianOrthogonalGroup.inv
    (U : HessianOrthogonalGroup E) :
    HessianOrthogonalGroup E :=
  ⟨U.1.symm, preservesMetric_symm (E := E) U.1 U.2⟩

lemma modularJ_preservesMetric :
    preservesMetric (E := E) (modularJ (E := E)) := by
  intro v w
  simp [hessianIndefiniteForm, modularJ, real_inner_comm, add_comm]

lemma spectralEpsilon_antiPreservesMetric :
    antiPreservesMetric (E := E) (spectralEpsilon (E := E)) := by
  intro v w
  simp [hessianIndefiniteForm, spectralEpsilon]
  ring

lemma spectralEpsilon_infinitesimalIsometry :
    IsInfinitesimalIsometry (E := E) (spectralEpsilon (E := E)) := by
  intro v w
  simp [hessianIndefiniteForm, spectralEpsilon]
  ring

lemma infinitesimalIsometry_closed_comm
    {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : IsInfinitesimalIsometry (E := E) A)
    (hB : IsInfinitesimalIsometry (E := E) B) :
    IsInfinitesimalIsometry (E := E) (clmComm A B) := by
  intro v w
  have hsplit₁ :
      hessianIndefiniteForm (E := E) ((clmComm A B) v) w
        = hessianIndefiniteForm (E := E) (A (B v)) w
          - hessianIndefiniteForm (E := E) (B (A v)) w := by
    simp [clmComm, hessianIndefiniteForm, sub_eq_add_neg,
      inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
      add_assoc, add_left_comm, add_comm]
  have hsplit₂ :
      hessianIndefiniteForm (E := E) v ((clmComm A B) w)
        = hessianIndefiniteForm (E := E) v (A (B w))
          - hessianIndefiniteForm (E := E) v (B (A w)) := by
    simp [clmComm, hessianIndefiniteForm, sub_eq_add_neg,
      inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
      add_assoc, add_left_comm, add_comm]
  have hA1 : hessianIndefiniteForm (E := E) (A (B v)) w
      = -hessianIndefiniteForm (E := E) (B v) (A w) := by
    linarith [hA (B v) w]
  have hB1 : hessianIndefiniteForm (E := E) (B (A v)) w
      = -hessianIndefiniteForm (E := E) (A v) (B w) := by
    linarith [hB (A v) w]
  have hA2 : hessianIndefiniteForm (E := E) v (A (B w))
      = -hessianIndefiniteForm (E := E) (A v) (B w) := by
    linarith [hA v (B w)]
  have hB2 : hessianIndefiniteForm (E := E) v (B (A w))
      = -hessianIndefiniteForm (E := E) (B v) (A w) := by
    linarith [hB v (A w)]
  rw [hsplit₁, hsplit₂, hA1, hB1, hA2, hB2]
  ring

/-- Swap involution as a continuous linear equivalence. -/
def modularJEquiv : DoubledSpace E ≃L[ℝ] DoubledSpace E where
  toLinearEquiv :=
    { toFun := fun v => (v.2, v.1)
      invFun := fun v => (v.2, v.1)
      left_inv := by intro v; rfl
      right_inv := by intro v; rfl
      map_add' := by intro v w; simp
      map_smul' := by intro a v; simp }
  continuous_toFun := by continuity
  continuous_invFun := by continuity

/-- Sign involution as a continuous linear equivalence. -/
def spectralEpsilonEquiv : DoubledSpace E ≃L[ℝ] DoubledSpace E where
  toLinearEquiv :=
    { toFun := fun v => (v.1, -v.2)
      invFun := fun v => (v.1, -v.2)
      left_inv := by intro v; simp
      right_inv := by intro v; simp
      map_add' := by intro v w; simp [add_comm]
      map_smul' := by intro a v; simp [smul_neg] }
  continuous_toFun := by continuity
  continuous_invFun := by continuity

def modularJKreinIsometry : KreinIsometry (E := E) where
  U := modularJEquiv (E := E)
  isometry := by
    simpa [modularJEquiv] using modularJ_preservesMetric (E := E)

def modularJHessianOrthogonal : HessianOrthogonalGroup E :=
  ⟨modularJEquiv (E := E), by
    simpa [modularJEquiv] using modularJ_preservesMetric (E := E)⟩

def spectralEpsilonKreinAntiIsometry : KreinAntiIsometry (E := E) where
  U := spectralEpsilonEquiv (E := E)
  antiIsometry := by
    simpa [spectralEpsilonEquiv] using spectralEpsilon_antiPreservesMetric (E := E)

end Metric

section Automorphisms

/-- Conjugation action of `U` on doubled-space endomorphisms. -/
noncomputable def conjugateCLM
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  (U : DoubledSpace E →L[ℝ] DoubledSpace E).comp
    (A.comp (U.symm : DoubledSpace E →L[ℝ] DoubledSpace E))

lemma conjugateCLM_comp
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    conjugateCLM (E := E) U (A.comp B) =
      (conjugateCLM (E := E) U A).comp (conjugateCLM (E := E) U B) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [conjugateCLM, ContinuousLinearMap.comp_apply]

lemma conjugateCLM_id
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E) :
    conjugateCLM (E := E) U (ContinuousLinearMap.id ℝ (DoubledSpace E)) =
      ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [conjugateCLM]

lemma conjugateCLM_neg
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    conjugateCLM (E := E) U (-A) = -(conjugateCLM (E := E) U A) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [conjugateCLM]

/-- Conjugation by a continuous linear equivalence preserves `Cl(1,1)` relations. -/
theorem Cl11Algebra.conjugate
    {J ε : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hCl : Cl11Algebra J ε)
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E) :
    Cl11Algebra (conjugateCLM (E := E) U J) (conjugateCLM (E := E) U ε) := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      (conjugateCLM (E := E) U J).comp (conjugateCLM (E := E) U J)
          = conjugateCLM (E := E) U (J.comp J) := by
              symm
              exact conjugateCLM_comp (E := E) U J J
      _ = conjugateCLM (E := E) U (ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
            rw [hCl.j_involution]
      _ = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
            exact conjugateCLM_id (E := E) U
  · calc
      (conjugateCLM (E := E) U ε).comp (conjugateCLM (E := E) U ε)
          = conjugateCLM (E := E) U (ε.comp ε) := by
              symm
              exact conjugateCLM_comp (E := E) U ε ε
      _ = conjugateCLM (E := E) U (ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
            rw [hCl.eps_involution]
      _ = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
            exact conjugateCLM_id (E := E) U
  · calc
      (conjugateCLM (E := E) U J).comp (conjugateCLM (E := E) U ε)
          = conjugateCLM (E := E) U (J.comp ε) := by
              symm
              exact conjugateCLM_comp (E := E) U J ε
      _ = conjugateCLM (E := E) U (-(ε.comp J)) := by
            rw [hCl.anticommute]
      _ = -(conjugateCLM (E := E) U (ε.comp J)) := by
            exact conjugateCLM_neg (E := E) U (ε.comp J)
      _ = -((conjugateCLM (E := E) U ε).comp (conjugateCLM (E := E) U J)) := by
            rw [conjugateCLM_comp (E := E) U ε J]

/-- `U` preserves Clifford structure if it sends each `Cl(1,1)` pair to another `Cl(1,1)` pair
by conjugation. -/
def preservesClifford
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  Cl11Algebra J ε →
    Cl11Algebra (conjugateCLM (E := E) U J) (conjugateCLM (E := E) U ε)

lemma preservesClifford_of_conjugate
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) :
    preservesClifford (E := E) U J ε := by
  intro hCl
  exact hCl.conjugate (E := E) U

section MetricTransport

variable [InnerProductSpace ℝ E]

lemma preservesMetric_apply_symm_left
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (hU : preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E))
    (v w : DoubledSpace E) :
    hessianIndefiniteForm (E := E) v ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w)
      = hessianIndefiniteForm (E := E) (U v) w := by
  have h := hU v ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w)
  simpa using h.symm

lemma preservesMetric_apply_symm_right
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (hU : preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E))
    (v w : DoubledSpace E) :
    hessianIndefiniteForm (E := E) ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v) w
      = hessianIndefiniteForm (E := E) v (U w) := by
  have h := hU ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v) w
  simpa using h.symm

lemma infinitesimalIsometry_conjugate
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (hU : preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E))
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : IsInfinitesimalIsometry A) :
    IsInfinitesimalIsometry (conjugateCLM (E := E) U A) := by
  intro v w
  change hessianIndefiniteForm (E := E)
      ((U : DoubledSpace E →L[ℝ] DoubledSpace E)
        (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v))) w
      +
      hessianIndefiniteForm (E := E) v
      ((U : DoubledSpace E →L[ℝ] DoubledSpace E)
        (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w)))
      = 0
  calc
    hessianIndefiniteForm (E := E)
        ((U : DoubledSpace E →L[ℝ] DoubledSpace E)
          (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v))) w
      +
      hessianIndefiniteForm (E := E) v
        ((U : DoubledSpace E →L[ℝ] DoubledSpace E)
          (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w)))
        = hessianIndefiniteForm (E := E)
            (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v))
            ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w)
          + hessianIndefiniteForm (E := E)
            ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v)
            (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w)) := by
              have hL :
                  hessianIndefiniteForm (E := E)
                    ((U : DoubledSpace E →L[ℝ] DoubledSpace E)
                      (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v))) w
                    = hessianIndefiniteForm (E := E)
                        (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v))
                        ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w) := by
                simpa using
                  (preservesMetric_apply_symm_left (E := E) U hU
                    (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v)) w).symm
              have hR :
                  hessianIndefiniteForm (E := E) v
                    ((U : DoubledSpace E →L[ℝ] DoubledSpace E)
                      (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w)))
                    = hessianIndefiniteForm (E := E)
                        ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v)
                        (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w)) := by
                simpa using
                  (preservesMetric_apply_symm_right (E := E) U hU v
                    (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w))).symm
              rw [hL, hR]
    _ = 0 := hA _ _

end MetricTransport

section Dynamics

variable [InnerProductSpace ℝ E]

/-- Interface for a one-parameter flow obtained from a finite-dimensional exponential map model.
This packages the semigroup law, identity at `0`, and metric preservation. -/
structure FiniteDimensionalExponentialFlow
    [FiniteDimensional ℝ E]
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) where
  flow : ℝ → DoubledSpace E ≃L[ℝ] DoubledSpace E
  flow_zero : flow 0 = ContinuousLinearEquiv.refl ℝ (DoubledSpace E)
  flow_add : ∀ s t, flow (s + t) = (flow s).trans (flow t)
  generator_infinitesimal : IsInfinitesimalIsometry A
  flow_preservesMetric :
    ∀ t, preservesMetric (E := E) (flow t : DoubledSpace E →L[ℝ] DoubledSpace E)

theorem flow_isometry
    [FiniteDimensional ℝ E]
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (t : ℝ) :
    preservesMetric (E := E) (F.flow t : DoubledSpace E →L[ℝ] DoubledSpace E) :=
  F.flow_preservesMetric t

/-- Orbit of a point under a one-parameter flow. -/
noncomputable def flowOrbit
    [FiniteDimensional ℝ E]
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (v0 : DoubledSpace E) (t : ℝ) : DoubledSpace E :=
  F.flow t v0

lemma flowOrbit_zero
    [FiniteDimensional ℝ E]
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (v0 : DoubledSpace E) :
    flowOrbit (E := E) F v0 0 = v0 := by
  simp [flowOrbit, F.flow_zero]

lemma flowOrbit_add
    [FiniteDimensional ℝ E]
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (v0 : DoubledSpace E) (s t : ℝ) :
    flowOrbit (E := E) F v0 (s + t)
      = flowOrbit (E := E) F (flowOrbit (E := E) F v0 s) t := by
  simp [flowOrbit, F.flow_add]

/-- Time-evolved endomorphism via conjugation by the flow. -/
noncomputable def flowConjugate
    [FiniteDimensional ℝ E]
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (B : DoubledSpace E →L[ℝ] DoubledSpace E)
    (t : ℝ) : DoubledSpace E →L[ℝ] DoubledSpace E :=
  conjugateCLM (E := E) (F.flow t) B

lemma flowConjugate_infinitesimal
    [FiniteDimensional ℝ E]
    {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (hB : IsInfinitesimalIsometry (E := E) B)
    (t : ℝ) :
    IsInfinitesimalIsometry (E := E) (flowConjugate (E := E) F B t) := by
  exact infinitesimalIsometry_conjugate
    (U := F.flow t) (hU := F.flow_preservesMetric t) hB

/-- Orbit representation of a flow trajectory by an infinitesimal-isometry generator. -/
theorem natural_gradient_is_orbit_interface
    [FiniteDimensional ℝ E]
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (initial : DoubledSpace E) :
    ∃ G, IsInfinitesimalIsometry (E := E) G ∧
      ∀ t, flowOrbit (E := E) F initial t = F.flow t initial := by
  refine ⟨A, F.generator_infinitesimal, ?_⟩
  intro t
  rfl

end Dynamics

section NoAxiomSanity

variable [InnerProductSpace ℝ E]

/-- Sanity witness: commutator closure is available as a theorem term. -/
theorem noAxiom_witness_infinitesimal_closed_comm
    {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : IsInfinitesimalIsometry (E := E) A)
    (hB : IsInfinitesimalIsometry (E := E) B) :
    IsInfinitesimalIsometry (E := E) (clmComm A B) :=
  infinitesimalIsometry_closed_comm (E := E) hA hB

omit [InnerProductSpace ℝ E] in
/-- Sanity witness: flow-level metric preservation theorem is available. -/
theorem noAxiom_witness_flow_isometry
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (t : ℝ) :
    preservesMetric (E := E) (F.flow t : DoubledSpace E →L[ℝ] DoubledSpace E) :=
  flow_isometry (E := E) F t

omit [InnerProductSpace ℝ E] in
/-- Sanity witness: infinitesimal structure is transported along flow conjugation. -/
theorem noAxiom_witness_flowConjugate_infinitesimal
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (hB : IsInfinitesimalIsometry (E := E) B)
    (t : ℝ) :
    IsInfinitesimalIsometry (E := E) (flowConjugate (E := E) F B t) :=
  flowConjugate_infinitesimal (E := E) F hB t

end NoAxiomSanity

end Automorphisms
end KreinClifford

/-- Tilted probability kernel (requires Z(τ) ≠ 0). -/
noncomputable def tiltedProb
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
    (_hZ : partitionFunction N_func Q τ ≠ 0)
    (x : α) : ℝ :=
  (Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x)) /
    (partitionFunction N_func Q τ)

/-- U(τ) = E_{μ_τ}[log r]. -/
noncomputable def internalEnergy
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
    (hZ : partitionFunction N_func Q τ ≠ 0) : ℝ :=
  ∑ x, tiltedProb N_func Q τ hZ x * logRNDensity N_func Q x

/-- F(τ) = Φ(τ)/τ. -/
noncomputable def freeEnergy
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) : ℝ :=
  Phi N_func Q τ / τ

/-- S(τ) = τ U(τ) - Φ(τ). -/
noncomputable def entropyAtTau
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
  (hZ : partitionFunction N_func Q τ ≠ 0) : ℝ :=
  τ * internalEnergy N_func Q τ hZ - Phi N_func Q τ

lemma hasDerivAt_partitionFunction
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) :
    HasDerivAt (partitionFunction N_func Q)
      (∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
        logRNDensity N_func Q x) τ := by
  classical
  unfold partitionFunction
  change HasDerivAt
    (fun t : ℝ => ∑ x, Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x))
    (∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
      logRNDensity N_func Q x) τ
  refine HasDerivAt.fun_sum ?_
  intro x hx
  have hlin :
      HasDerivAt (fun t : ℝ => -t * relativeSurprisal N_func Q x)
        (logRNDensity N_func Q x) τ := by
    have hlin0 :
        HasDerivAt (fun t : ℝ => -t * relativeSurprisal N_func Q x)
          (-relativeSurprisal N_func Q x) τ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_id τ).neg.mul_const (relativeSurprisal N_func Q x))
    simpa [relativeSurprisal] using hlin0
  have hexp :
      HasDerivAt (fun t : ℝ => Real.exp (-t * relativeSurprisal N_func Q x))
        (Real.exp (-τ * relativeSurprisal N_func Q x) *
          logRNDensity N_func Q x) τ := by
    exact (Real.hasDerivAt_exp (-τ * relativeSurprisal N_func Q x)).comp τ hlin
  simpa [mul_assoc, mul_left_comm, mul_comm] using hexp.const_mul (Q.prob x)

theorem deriv_partitionFunction
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) :
    deriv (partitionFunction N_func Q) τ =
      ∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
        logRNDensity N_func Q x := by
  exact (hasDerivAt_partitionFunction N_func Q τ).deriv

theorem dPhi_eq_internalEnergy
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
    (hZ : partitionFunction N_func Q τ ≠ 0) :
    deriv (Phi N_func Q) τ = internalEnergy N_func Q τ hZ := by
  have hlog :
      HasDerivAt (Phi N_func Q)
        ((∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
            logRNDensity N_func Q x) /
          partitionFunction N_func Q τ) τ := by
    simpa [Phi] using (hasDerivAt_partitionFunction N_func Q τ).log hZ
  calc
    deriv (Phi N_func Q) τ
        = ((∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
            logRNDensity N_func Q x) /
          partitionFunction N_func Q τ) := hlog.deriv
    _ = ∑ x,
          ((Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x)) /
            partitionFunction N_func Q τ) *
            logRNDensity N_func Q x := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl ?_
          intro x hx
          ring
    _ = internalEnergy N_func Q τ hZ := by
          simp [internalEnergy, tiltedProb, mul_comm]

lemma hasDerivAt_partitionFunctionLogMoment
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) :
    HasDerivAt
      (fun t => ∑ x, Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x) *
        logRNDensity N_func Q x)
      (∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
        (logRNDensity N_func Q x) ^ 2) τ := by
  classical
  refine HasDerivAt.fun_sum ?_
  intro x hx
  have hlin :
      HasDerivAt (fun t : ℝ => -t * relativeSurprisal N_func Q x)
        (logRNDensity N_func Q x) τ := by
    have hlin0 :
        HasDerivAt (fun t : ℝ => -t * relativeSurprisal N_func Q x)
          (-relativeSurprisal N_func Q x) τ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_id τ).neg.mul_const (relativeSurprisal N_func Q x))
    simpa [relativeSurprisal] using hlin0
  have hexp :
      HasDerivAt (fun t : ℝ => Real.exp (-t * relativeSurprisal N_func Q x))
        (Real.exp (-τ * relativeSurprisal N_func Q x) *
          logRNDensity N_func Q x) τ := by
    exact (Real.hasDerivAt_exp (-τ * relativeSurprisal N_func Q x)).comp τ hlin
  have hfactor :
      HasDerivAt
        (fun t : ℝ => Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x))
        (Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
          logRNDensity N_func Q x) τ := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hexp.const_mul (Q.prob x)
  have hterm :
      HasDerivAt
        (fun t : ℝ => Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x) *
          logRNDensity N_func Q x)
        ((Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
          logRNDensity N_func Q x) * logRNDensity N_func Q x) τ := by
    simpa [mul_assoc] using hfactor.mul_const (logRNDensity N_func Q x)
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hterm

theorem deriv_partitionFunctionLogMoment
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) :
    deriv
      (fun t => ∑ x, Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x) *
        logRNDensity N_func Q x) τ
      = ∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
          (logRNDensity N_func Q x) ^ 2 := by
  exact (hasDerivAt_partitionFunctionLogMoment N_func Q τ).deriv

theorem deriv_Phi_eq_partition_ratio
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0) :
    deriv (Phi N_func Q) =
      fun t =>
        (∑ x, Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x) *
          logRNDensity N_func Q x) / partitionFunction N_func Q t := by
  funext t
  have hlog :
      HasDerivAt (Phi N_func Q)
        ((∑ x, Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x) *
            logRNDensity N_func Q x) /
          partitionFunction N_func Q t) t := by
    simpa [Phi] using (hasDerivAt_partitionFunction N_func Q t).log (hZ t)
  exact hlog.deriv

noncomputable def varianceLogRNDensity
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
    (hZ : partitionFunction N_func Q τ ≠ 0) : ℝ :=
  (∑ x, tiltedProb N_func Q τ hZ x * (logRNDensity N_func Q x) ^ 2) -
    (internalEnergy N_func Q τ hZ) ^ 2

theorem d2Phi_eq_varianceLogRNDensity
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0)
    (τ : ℝ) :
    deriv (fun t => deriv (Phi N_func Q) t) τ =
      varianceLogRNDensity N_func Q τ (hZ τ) := by
  let Z : ℝ → ℝ := partitionFunction N_func Q
  let M1 : ℝ → ℝ := fun t =>
    ∑ x, Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x) *
      logRNDensity N_func Q x
  let M2 : ℝ → ℝ := fun t =>
    ∑ x, Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x) *
      (logRNDensity N_func Q x) ^ 2
  have hderivPhi : deriv (Phi N_func Q) = fun t => M1 t / Z t := by
    simpa [M1, Z] using deriv_Phi_eq_partition_ratio N_func Q hZ
  calc
    deriv (fun t => deriv (Phi N_func Q) t) τ
        = deriv (fun t => M1 t / Z t) τ := by
            simp [hderivPhi]
    _ = (deriv M1 τ * Z τ - M1 τ * deriv Z τ) / (Z τ) ^ 2 := by
          refine deriv_fun_div ?_ ?_ ?_
          · exact (hasDerivAt_partitionFunctionLogMoment N_func Q τ).differentiableAt
          · exact (hasDerivAt_partitionFunction N_func Q τ).differentiableAt
          · simpa [Z] using hZ τ
    _ = ((M2 τ) * Z τ - M1 τ * M1 τ) / (Z τ) ^ 2 := by
          rw [(hasDerivAt_partitionFunctionLogMoment N_func Q τ).deriv]
          rw [(hasDerivAt_partitionFunction N_func Q τ).deriv]
    _ = M2 τ / Z τ - (M1 τ / Z τ) ^ 2 := by
          have hZτ : Z τ ≠ 0 := by simpa [Z] using hZ τ
          field_simp [hZτ]
    _ = varianceLogRNDensity N_func Q τ (hZ τ) := by
          have hM2 :
              M2 τ / Z τ =
                ∑ x, tiltedProb N_func Q τ (hZ τ) x * (logRNDensity N_func Q x) ^ 2 := by
            unfold M2 Z partitionFunction
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro x hx
            simp [tiltedProb, partitionFunction]
            ring
          have hM1 : M1 τ / Z τ = internalEnergy N_func Q τ (hZ τ) := by
            unfold M1 Z partitionFunction internalEnergy
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro x hx
            simp [tiltedProb, partitionFunction]
            ring
          simp [varianceLogRNDensity, hM2, hM1]

lemma partitionFunction_nonneg
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) :
    0 ≤ partitionFunction N_func Q τ := by
  unfold partitionFunction
  refine Finset.sum_nonneg ?_
  intro x hx
  exact mul_nonneg (Q.nonneg x) (by positivity)

lemma tiltedProb_sum_one
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
    (hZ : partitionFunction N_func Q τ ≠ 0) :
    ∑ x, tiltedProb N_func Q τ hZ x = 1 := by
  unfold tiltedProb
  calc
    ∑ x,
        (Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x)) /
          partitionFunction N_func Q τ
        = (∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x)) /
            partitionFunction N_func Q τ := by
              rw [Finset.sum_div]
    _ = partitionFunction N_func Q τ / partitionFunction N_func Q τ := by
          simp [partitionFunction]
    _ = 1 := by
          exact div_self hZ

lemma Phi_zero
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α) :
    Phi N_func Q 0 = 0 := by
  unfold Phi partitionFunction
  simp [Q.sum_one]

lemma qexp_term_eq_empirical_of_supportMatches
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_support : SupportMatches N_func Q)
    (x : α) :
    Q.prob x * Real.exp (-(1 : ℝ) * relativeSurprisal N_func Q x) =
      empiricalDistribution N_func x := by
  let P : α → ℝ := empiricalDistribution N_func
  by_cases hqx : Q.prob x = 0
  · have hPx0 : P x = 0 := (h_support x).2 hqx
    simp [P, hqx, hPx0]
  · have hPx0 : P x ≠ 0 := by
      intro hPx
      exact hqx ((h_support x).1 hPx)
    have hP_nonneg : 0 ≤ P x := by
      unfold P empiricalDistribution
      exact div_nonneg (by positivity) (by positivity)
    have hP_pos : 0 < P x := lt_of_le_of_ne hP_nonneg (Ne.symm hPx0)
    have hq_pos : 0 < Q.prob x := lt_of_le_of_ne (Q.nonneg x) (Ne.symm hqx)
    have hratio_pos : 0 < P x / Q.prob x := div_pos hP_pos hq_pos
    have hexp_log : Real.exp (Real.log (P x / Q.prob x)) = P x / Q.prob x := by
      exact Real.exp_log hratio_pos
    calc
      Q.prob x * Real.exp (-(1 : ℝ) * relativeSurprisal N_func Q x)
          = Q.prob x * Real.exp (Real.log (P x / Q.prob x)) := by
              simp [P, relativeSurprisal, logRNDensity, densityRatio]
      _ = Q.prob x * (P x / Q.prob x) := by rw [hexp_log]
      _ = P x := by
            field_simp [hqx]
      _ = empiricalDistribution N_func x := by
            rfl

lemma partitionFunction_one_eq_one_of_supportMatches
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_nontrivial : EmpiricalNontrivial N_func)
    (h_support : SupportMatches N_func Q) :
    partitionFunction N_func Q 1 = 1 := by
  let P : α → ℝ := empiricalDistribution N_func
  calc
    partitionFunction N_func Q 1
        = ∑ x, Q.prob x * Real.exp (-(1 : ℝ) * relativeSurprisal N_func Q x) := by
          rfl
    _ = ∑ x, P x := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simpa [P] using
            qexp_term_eq_empirical_of_supportMatches N_func Q h_support x
    _ = 1 := by
          simpa [P] using empirical_sum_one N_func h_nontrivial

lemma Phi_one_of_supportMatches
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_nontrivial : EmpiricalNontrivial N_func)
    (h_support : SupportMatches N_func Q) :
    Phi N_func Q 1 = 0 := by
  have hZ1 : partitionFunction N_func Q 1 = 1 :=
    partitionFunction_one_eq_one_of_supportMatches N_func Q h_nontrivial h_support
  unfold Phi
  simp [hZ1]

lemma tiltedProb_one_eq_empirical_of_supportMatches
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_nontrivial : EmpiricalNontrivial N_func)
    (h_support : SupportMatches N_func Q)
    (hZ1 : partitionFunction N_func Q 1 ≠ 0)
    (x : α) :
    tiltedProb N_func Q 1 hZ1 x = empiricalDistribution N_func x := by
  have hterm :
      Q.prob x * Real.exp (-(1 : ℝ) * relativeSurprisal N_func Q x) =
        empiricalDistribution N_func x := by
    exact qexp_term_eq_empirical_of_supportMatches N_func Q h_support x
  have hterm' :
      Q.prob x * Real.exp (-relativeSurprisal N_func Q x) =
        empiricalDistribution N_func x := by
    simpa using hterm
  have hpart : partitionFunction N_func Q 1 = 1 := by
    exact partitionFunction_one_eq_one_of_supportMatches N_func Q h_nontrivial h_support
  unfold tiltedProb
  rw [hpart]
  simp [hterm']

lemma internalEnergy_one_eq_KL_of_supportMatches
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_nontrivial : EmpiricalNontrivial N_func)
    (h_support : SupportMatches N_func Q)
    (hZ1 : partitionFunction N_func Q 1 ≠ 0) :
    internalEnergy N_func Q 1 hZ1 = KLdivergence N_func Q := by
  have htilt :
      ∀ x, tiltedProb N_func Q 1 hZ1 x = empiricalDistribution N_func x := by
    intro x
    exact tiltedProb_one_eq_empirical_of_supportMatches
      N_func Q h_nontrivial h_support hZ1 x
  calc
    internalEnergy N_func Q 1 hZ1
        = ∑ x, empiricalDistribution N_func x * Real.log (densityRatio N_func Q x) := by
          unfold internalEnergy logRNDensity
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [htilt x]
    _ = KLdivergence N_func Q := by
          unfold KLdivergence entropyExpectation surprisal
          have hsum :
              (∑ x, empiricalDistribution N_func x * (-Real.log (densityRatio N_func Q x)))
                = ∑ x, -(empiricalDistribution N_func x *
                    Real.log (densityRatio N_func Q x)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring
          rw [hsum, Finset.sum_neg_distrib]
          ring

lemma deriv_Phi_one_eq_KL_of_supportMatches
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_nontrivial : EmpiricalNontrivial N_func)
    (h_support : SupportMatches N_func Q)
    (hZ1 : partitionFunction N_func Q 1 ≠ 0) :
    deriv (Phi N_func Q) 1 = KLdivergence N_func Q := by
  calc
    deriv (Phi N_func Q) 1 = internalEnergy N_func Q 1 hZ1 := by
      exact dPhi_eq_internalEnergy N_func Q 1 hZ1
    _ = KLdivergence N_func Q := by
      exact internalEnergy_one_eq_KL_of_supportMatches
        N_func Q h_nontrivial h_support hZ1

theorem bregmanDiv_Phi_zero_one_eq_KL_of_supportMatches
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_nontrivial : EmpiricalNontrivial N_func)
    (h_support : SupportMatches N_func Q)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0) :
    bregmanDiv (Phi N_func Q) 0 1 = KLdivergence N_func Q := by
  have hPhi0 : Phi N_func Q 0 = 0 := Phi_zero N_func Q
  have hPhi1 : Phi N_func Q 1 = 0 :=
    Phi_one_of_supportMatches N_func Q h_nontrivial h_support
  have hderiv : deriv (Phi N_func Q) 1 = KLdivergence N_func Q :=
    deriv_Phi_one_eq_KL_of_supportMatches N_func Q h_nontrivial h_support (hZ 1)
  unfold bregmanDiv
  simp [hPhi0, hPhi1, hderiv]

theorem KL_eq_bregmanDiv_Phi_zero_one_of_supportMatches
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_nontrivial : EmpiricalNontrivial N_func)
    (h_support : SupportMatches N_func Q)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0) :
    KLdivergence N_func Q = bregmanDiv (Phi N_func Q) 0 1 := by
  symm
  exact bregmanDiv_Phi_zero_one_eq_KL_of_supportMatches
    N_func Q h_nontrivial h_support hZ

/-
Dictionary (discrete tilt model ↔ Gaussian/SPD cone model)
-----------------------------------------------------------

This file proves the discrete identity

`KLdivergence N_func Q = bregmanDiv (Phi N_func Q) 0 1`

under support/nondegeneracy assumptions (see
`KL_eq_bregmanDiv_Phi_zero_one_of_supportMatches`).

The Gaussian/SPD analogue is the standard matrix identity on `SPD(n)`:

* Cone potential: `F(Σ) := -log det Σ`.
* Bregman divergence:
  `D_F(Σ ‖ Λ) = F(Σ) - F(Λ) - ⟪∇F(Λ), Σ - Λ⟫`
  (Frobenius pairing `⟪A,B⟫ = tr (A B)`).
* Closed form:
  `D_F(Σ ‖ Λ) = tr(Λ⁻¹ Σ) - log det(Λ⁻¹ Σ) - n`.
* Gaussian KL (zero mean):
  `KL(𝓝(0,Σ) ‖ 𝓝(0,Λ)) = (1/2) * D_F(Σ ‖ Λ)`.

So the correspondence is:

* `Phi` (log-partition potential along tilt) ↔ cone potential/log-normalizer role.
* `bregmanDiv` ↔ Bregman divergence generated by that potential.
* `KLdivergence` ↔ relative entropy; in SPD/Gaussian form, equal to `1/2` times
  the Bregman divergence of `-log det`.

This comment is a roadmap marker: discrete and Jordan/SPD viewpoints are the same
template (potential → gradient/Hessian → Bregman/KL), expressed in different state spaces.
-/

/-
Theorem targets (future formalization milestones)
-------------------------------------------------

Commented skeletons for the Gaussian/SPD side, to sit next to the discrete results above.

-- theorem gaussian_KL_eq_half_bregman_logdet
--     {n : ℕ} (Σ Λ : Matrix (Fin n) (Fin n) ℝ)
--     (hΣ : Σ ∈ Matrix.PosDef) (hΛ : Λ ∈ Matrix.PosDef) :
--     gaussianKL0 Σ Λ = (1 / 2 : ℝ) * spdBregmanLogDet Σ Λ := by
--   sorry

-- theorem spd_bregman_logdet_closed_form
--     {n : ℕ} (Σ Λ : Matrix (Fin n) (Fin n) ℝ)
--     (hΣ : Σ ∈ Matrix.PosDef) (hΛ : Λ ∈ Matrix.PosDef) :
--     spdBregmanLogDet Σ Λ
--       = Matrix.trace (Λ⁻¹ ⬝ Σ) - Real.log (Matrix.det (Λ⁻¹ ⬝ Σ)) - n := by
--   sorry

-- theorem discrete_to_spd_dictionary
--     : True := by
--   /- records: `Phi` ↔ log-normalizer/potential,
--      `bregmanDiv` ↔ potential-generated divergence,
--      `KLdivergence` ↔ relative entropy (Gaussian: half logdet-Bregman). -/
--   trivial
-/

/-
DAG (machine-readable, proof-architecture)
format: yaml
version: 1
items:
  - id: N1
    name: empirical_sum_one
    depends_on: []
    status: implemented
  - id: N2
    name: kl_pointwise_ge_sub
    depends_on: []
    status: implemented
  - id: N3
    name: KL_nonneg
    depends_on: [N1, N2]
    status: implemented
  - id: N4
    name: KL_eq_zero_iff
    depends_on: [N1, N2]
    status: implemented
  - id: N5
    name: partitionFunction
    depends_on: []
    status: implemented
  - id: N6
    name: Phi
    depends_on: [N5]
    status: implemented
  - id: N7
    name: dPhi_eq_internalEnergy
    depends_on: [N6]
    status: implemented
  - id: N8
    name: bregmanDiv
    depends_on: []
    status: implemented
  - id: N9
    name: bregmanDiv_three_point
    depends_on: [N8]
    status: implemented
  - id: N10
    name: bregmanDiv_pythagorean_ineq
    depends_on: [N9]
    status: implemented
  - id: N11
    name: bregmanDiv_Phi_zero_one_eq_KL_of_supportMatches
    depends_on: [N6, N8, N7]
    status: implemented
  - id: N12
    name: cramerRateOn
    depends_on: []
    status: implemented
  - id: N13
    name: KL_le_cramerRateOn_derivPhi_one_of_supportMatches
    depends_on: [N12, N6]
    status: implemented
  - id: N14
    name: modularJ_spectralEpsilon_isCl11
    depends_on: []
    status: implemented
  - id: N15
    name: complexI_sq_neg_id
    depends_on: [N14]
    status: implemented
  - id: N16
    name: superHamiltonian_isEven
    depends_on: [N15]
    status: implemented
  - id: N17
    name: sameRaySetoid
    depends_on: []
    status: implemented
  - id: N18
    name: PrequantumData
    depends_on: [N17]
    status: implemented
  - id: N19
    name: dilationOperator_eq_complexI
    depends_on: [N14]
    status: implemented
  - id: N20
    name: infinitesimalIsometry_closed_comm
    depends_on: []
    status: implemented
-/

/-
Module DAG (machine-readable, release planning)
format: yaml
version: 1
items:
  - id: M1
    name: FiniteProbabilityCore
    depends_on: []
    status: implemented
  - id: M2
    name: TiltedRNAndBregman
    depends_on: [M1]
    status: implemented
  - id: M3
    name: ConvexDualityAndRate
    depends_on: [M2, M1]
    status: implemented
  - id: M4
    name: Cl11DoubledGeometry
    depends_on: []
    status: implemented
  - id: M5
    name: SUSYProjectivePrequantum
    depends_on: [M4, M6]
    status: implemented
  - id: M6
    name: KreinMetricSymmetry
    depends_on: [M4]
    status: implemented
  - id: M7
    name: GaussianTargets
    depends_on: [M2, M3]
    status: planned
notes:
  - M2 and M4 are largely orthogonal tracks and can be released independently.
  - M7 depends on analytic strengthening (SPD positivity/invertibility hypotheses).
-/

/-
Minimal Axiom Basis (machine-readable)
format: yaml
version: 1
items:
  - id: A1
    name: FiniteProb
    depends_on: []
    status: implemented
  - id: A2
    name: LogSupport
    depends_on: [A1]
    status: implemented
  - id: A3
    name: ConvexDualFiniteLF
    depends_on: [A2]
    status: implemented
  - id: A4
    name: DoubledLinearCl11
    depends_on: []
    status: implemented
  - id: A5
    name: KreinMetric
    depends_on: [A4]
    status: implemented
  - id: A6
    name: GaussianSPDTarget
    depends_on: [A2, A3]
    status: planned
-/

/-
Publishable Packs (machine-readable)
format: yaml
version: 1
items:
  - id: P1
    name: Finite KL Core
    depends_on: [A1, A2]
    status: ready
  - id: P2
    name: Tilted Potential and Bregman Bridge
    depends_on: [A1, A2]
    status: ready
  - id: P3
    name: Finite Cramer/Fenchel Layer
    depends_on: [A3]
    status: ready
  - id: P4
    name: Cl(1,1) Doubled Geometry
    depends_on: [A4]
    status: ready
  - id: P5
    name: Krein Metric Symmetry
    depends_on: [A4, A5]
    status: ready
  - id: P6
    name: Gaussian SPD Target Stub
    depends_on: [A6]
    status: planned
-/

section GaussianTargets

/-
Roadmap note (SPD intent):

The following symbolic definitions are meant to model the Gaussian/SPD formulas
on covariance matrices `Σ, Λ ∈ SPD(n)`. At this stage we keep them hypothesis-free
so the file remains lightweight and compilable.

Where positivity/invertibility hypotheses will enter explicitly:

-- theorem gaussian_KL_eq_half_bregman_logdet_of_spd
--   {n : ℕ} (SigmaMat LambdaMat : Matrix (Fin n) (Fin n) ℝ)
--   (hSigmaPD : SigmaMat.PosDef) (hLambdaPD : LambdaMat.PosDef) :
--   gaussianKL0 SigmaMat LambdaMat
--     = (1 / 2 : ℝ) * spdBregmanLogDet SigmaMat LambdaMat := by
--   -- uses: invertibility from `hLambdaPD`, positivity of determinant/log argument,
--   -- and the standard closed form for zero-mean Gaussian KL.
--   sorry
-/

/-- First symbolic log-det Bregman expression on square real matrices.
No SPD/invertibility side conditions are imposed yet; those are future refinements. -/
noncomputable def spdBregmanLogDet
  {n : ℕ} (_SigmaMat _LambdaMat : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace (_LambdaMat⁻¹ * _SigmaMat)
    - Real.log (Matrix.det (_LambdaMat⁻¹ * _SigmaMat))
    - (n : ℝ)

/-- First symbolic zero-mean Gaussian KL expression (tied to log-det Bregman form). -/
noncomputable def gaussianKL0
  {n : ℕ} (_SigmaMat _LambdaMat : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (1 / 2 : ℝ) * spdBregmanLogDet _SigmaMat _LambdaMat

/-- Milestone stub: Gaussian KL equals half log-det Bregman (placeholder model). -/
theorem gaussian_KL_eq_half_bregman_logdet
  {n : ℕ} (SigmaMat LambdaMat : Matrix (Fin n) (Fin n) ℝ) :
  gaussianKL0 SigmaMat LambdaMat = (1 / 2 : ℝ) * spdBregmanLogDet SigmaMat LambdaMat := by
  simp [gaussianKL0, spdBregmanLogDet]

end GaussianTargets

theorem KL_le_cramerRateOn_derivPhi_one_of_supportMatches
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_nontrivial : EmpiricalNontrivial N_func)
    (h_support : SupportMatches N_func Q)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0)
    (Θ : Finset ℝ)
    (hΘ : Θ.Nonempty)
    (h1 : (1 : ℝ) ∈ Θ) :
    KLdivergence N_func Q ≤
      cramerRateOn Θ hΘ (Phi N_func Q) (deriv (Phi N_func Q) 1) := by
  have hEval :
      deriv (Phi N_func Q) 1 * (1 : ℝ) - Phi N_func Q 1
        ≤ cramerRateOn Θ hΘ (Phi N_func Q) (deriv (Phi N_func Q) 1) := by
    exact le_cramerRateOn Θ hΘ (Phi N_func Q) (deriv (Phi N_func Q) 1) 1 h1
  have hPhi1 : Phi N_func Q 1 = 0 :=
    Phi_one_of_supportMatches N_func Q h_nontrivial h_support
  have hKL : deriv (Phi N_func Q) 1 = KLdivergence N_func Q :=
    deriv_Phi_one_eq_KL_of_supportMatches N_func Q h_nontrivial h_support (hZ 1)
  simpa [hPhi1, hKL] using hEval

theorem KL_eq_cramerRateOn_derivPhi_one_of_supportMatches_of_maximizer_one
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_nontrivial : EmpiricalNontrivial N_func)
    (h_support : SupportMatches N_func Q)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0)
    (Θ : Finset ℝ)
    (hΘ : Θ.Nonempty)
    (h1 : (1 : ℝ) ∈ Θ)
    (hmax :
      ∀ θ, θ ∈ Θ →
        deriv (Phi N_func Q) 1 * θ - Phi N_func Q θ
          ≤ deriv (Phi N_func Q) 1 * (1 : ℝ) - Phi N_func Q 1) :
    KLdivergence N_func Q =
      cramerRateOn Θ hΘ (Phi N_func Q) (deriv (Phi N_func Q) 1) := by
  have hLower :
      KLdivergence N_func Q ≤
        cramerRateOn Θ hΘ (Phi N_func Q) (deriv (Phi N_func Q) 1) :=
    KL_le_cramerRateOn_derivPhi_one_of_supportMatches
      N_func Q h_nontrivial h_support hZ Θ hΘ h1
  have hUpperEval :
      cramerRateOn Θ hΘ (Phi N_func Q) (deriv (Phi N_func Q) 1)
        ≤ deriv (Phi N_func Q) 1 * (1 : ℝ) - Phi N_func Q 1 := by
    unfold cramerRateOn
    exact Finset.sup'_le (s := Θ)
      (f := fun θ => deriv (Phi N_func Q) 1 * θ - Phi N_func Q θ) hΘ (by
        intro θ hθ
        exact hmax θ hθ)
  have hPhi1 : Phi N_func Q 1 = 0 :=
    Phi_one_of_supportMatches N_func Q h_nontrivial h_support
  have hKL : deriv (Phi N_func Q) 1 = KLdivergence N_func Q :=
    deriv_Phi_one_eq_KL_of_supportMatches N_func Q h_nontrivial h_support (hZ 1)
  have hUpper :
      cramerRateOn Θ hΘ (Phi N_func Q) (deriv (Phi N_func Q) 1)
        ≤ KLdivergence N_func Q := by
    simpa [hPhi1, hKL] using hUpperEval
  exact le_antisymm hLower hUpper

theorem KL_bregman_three_point_decomposition_of_supportMatches
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_nontrivial : EmpiricalNontrivial N_func)
    (h_support : SupportMatches N_func Q)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0)
    (τ : ℝ) :
    KLdivergence N_func Q
      = bregmanDiv (Phi N_func Q) 0 τ
        + bregmanDiv (Phi N_func Q) τ 1
        + (deriv (Phi N_func Q) τ - deriv (Phi N_func Q) 1) * (0 - τ) := by
  calc
    KLdivergence N_func Q
        = bregmanDiv (Phi N_func Q) 0 1 :=
            KL_eq_bregmanDiv_Phi_zero_one_of_supportMatches
              N_func Q h_nontrivial h_support hZ
    _ = bregmanDiv (Phi N_func Q) 0 τ
          + bregmanDiv (Phi N_func Q) τ 1
          + (deriv (Phi N_func Q) τ - deriv (Phi N_func Q) 1) * (0 - τ) := by
          simpa using bregmanDiv_three_point (Phi N_func Q) 0 τ 1

theorem KL_pythagorean_ineq_of_supportMatches
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_nontrivial : EmpiricalNontrivial N_func)
    (h_support : SupportMatches N_func Q)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0)
    (τ : ℝ)
    (hproj : 0 ≤ (deriv (Phi N_func Q) τ - deriv (Phi N_func Q) 1) * (0 - τ)) :
    KLdivergence N_func Q
      ≥ bregmanDiv (Phi N_func Q) 0 τ + bregmanDiv (Phi N_func Q) τ 1 := by
  calc
    KLdivergence N_func Q
        = bregmanDiv (Phi N_func Q) 0 1 :=
            KL_eq_bregmanDiv_Phi_zero_one_of_supportMatches
              N_func Q h_nontrivial h_support hZ
    _ ≥ bregmanDiv (Phi N_func Q) 0 τ + bregmanDiv (Phi N_func Q) τ 1 := by
          exact bregmanDiv_pythagorean_ineq (Phi N_func Q) 0 τ 1 hproj

theorem KL_pythagorean_eq_of_supportMatches
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_nontrivial : EmpiricalNontrivial N_func)
    (h_support : SupportMatches N_func Q)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0)
    (τ : ℝ)
    (horth :
      (deriv (Phi N_func Q) τ - deriv (Phi N_func Q) 1) * (0 - τ) = 0) :
    KLdivergence N_func Q
      = bregmanDiv (Phi N_func Q) 0 τ + bregmanDiv (Phi N_func Q) τ 1 := by
  calc
    KLdivergence N_func Q
        = bregmanDiv (Phi N_func Q) 0 τ
            + bregmanDiv (Phi N_func Q) τ 1
            + (deriv (Phi N_func Q) τ - deriv (Phi N_func Q) 1) * (0 - τ) :=
          KL_bregman_three_point_decomposition_of_supportMatches
            N_func Q h_nontrivial h_support hZ τ
    _ = bregmanDiv (Phi N_func Q) 0 τ + bregmanDiv (Phi N_func Q) τ 1 := by
          rw [horth]
          ring

lemma tiltedProb_nonneg
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
    (hZ : partitionFunction N_func Q τ ≠ 0)
    (x : α) :
    0 ≤ tiltedProb N_func Q τ hZ x := by
  unfold tiltedProb
  exact div_nonneg
    (mul_nonneg (Q.nonneg x) (by positivity))
    (partitionFunction_nonneg N_func Q τ)

lemma varianceLogRNDensity_nonneg
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
    (hZ : partitionFunction N_func Q τ ≠ 0) :
    0 ≤ varianceLogRNDensity N_func Q τ hZ := by
  let μ : α → ℝ := tiltedProb N_func Q τ hZ
  let L : α → ℝ := logRNDensity N_func Q
  have hμ_nonneg : ∀ x ∈ (Finset.univ : Finset α), 0 ≤ μ x := by
    intro x hx
    simpa [μ] using tiltedProb_nonneg N_func Q τ hZ x
  have hμ_sum : ∑ x ∈ (Finset.univ : Finset α), μ x = 1 := by
    simpa [μ] using tiltedProb_sum_one N_func Q τ hZ
  have hsq_convex : ConvexOn ℝ Set.univ (fun t : ℝ => t ^ (2 : ℕ)) := by
    exact (Even.strictConvexOn_pow (n := 2) (by decide) (by decide)).convexOn
  have hJ :
      (∑ x ∈ (Finset.univ : Finset α), μ x • L x) ^ (2 : ℕ) ≤
        ∑ x ∈ (Finset.univ : Finset α), μ x • (L x ^ (2 : ℕ)) := by
    exact hsq_convex.map_sum_le
      (t := (Finset.univ : Finset α))
      (w := μ)
      (p := L)
      hμ_nonneg
      hμ_sum
      (by intro x hx; simp)
  have hUle :
      (internalEnergy N_func Q τ hZ) ^ 2 ≤
        ∑ x, tiltedProb N_func Q τ hZ x * (logRNDensity N_func Q x) ^ 2 := by
    simpa [μ, L, internalEnergy, smul_eq_mul] using hJ
  unfold varianceLogRNDensity
  linarith

lemma varianceLogRNDensity_eq_sum_sq
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
    (hZ : partitionFunction N_func Q τ ≠ 0) :
    varianceLogRNDensity N_func Q τ hZ =
      ∑ x, tiltedProb N_func Q τ hZ x *
        (logRNDensity N_func Q x - internalEnergy N_func Q τ hZ) ^ 2 := by
  let μ : α → ℝ := tiltedProb N_func Q τ hZ
  let L : α → ℝ := logRNDensity N_func Q
  let U : ℝ := internalEnergy N_func Q τ hZ
  have hU : U = ∑ x, μ x * L x := by
    rfl
  have hμ : ∑ x, μ x = 1 := by
    simpa [μ] using tiltedProb_sum_one N_func Q τ hZ
  have hsq :
      (∑ x, μ x * (L x - U) ^ 2) = (∑ x, μ x * (L x) ^ 2) - U ^ 2 := by
    calc
      (∑ x, μ x * (L x - U) ^ 2)
          = ∑ x, (μ x * (L x) ^ 2 - (2 * U) * (μ x * L x) + μ x * U ^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
      _ = (∑ x, μ x * (L x) ^ 2) - (∑ x, (2 * U) * (μ x * L x)) + (∑ x, μ x * U ^ 2) := by
            rw [Finset.sum_add_distrib]
            rw [Finset.sum_sub_distrib]
      _ = (∑ x, μ x * (L x) ^ 2) - (2 * U) * (∑ x, μ x * L x) + (∑ x, μ x) * U ^ 2 := by
            rw [(Finset.mul_sum (Finset.univ : Finset α)
            (fun x => μ x * L x) (2 * U)).symm]
            rw [Finset.sum_mul]
      _ = (∑ x, μ x * (L x) ^ 2) - (2 * U) * U + 1 * U ^ 2 := by
            rw [hU, hμ]
      _ = (∑ x, μ x * (L x) ^ 2) - U ^ 2 := by
            ring
  unfold varianceLogRNDensity
  have hleft :
      ∑ x, tiltedProb N_func Q τ hZ x *
        (logRNDensity N_func Q x - internalEnergy N_func Q τ hZ) ^ 2
        = (∑ x, μ x * (L x) ^ 2) - U ^ 2 := by
    simpa [μ, L, U] using hsq
  have hright :
      (∑ x, tiltedProb N_func Q τ hZ x * (logRNDensity N_func Q x) ^ 2) -
        (internalEnergy N_func Q τ hZ) ^ 2
        = (∑ x, μ x * (L x) ^ 2) - U ^ 2 := by
    simp [μ, L, U]
  exact hright.trans hleft.symm

/-- Fisher metric along the exponential tilt arc `τ ↦ μ_τ`.
It is the variance of `log(dP̂/dQ)` under the tilted law. -/
noncomputable def fisherMetricAlongExponentialPath
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
    (hZ : partitionFunction N_func Q τ ≠ 0) : ℝ :=
  varianceLogRNDensity N_func Q τ hZ

theorem d2Phi_eq_fisherMetricAlongExponentialPath
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0)
    (τ : ℝ) :
    deriv (fun t => deriv (Phi N_func Q) t) τ =
      fisherMetricAlongExponentialPath N_func Q τ (hZ τ) := by
  simpa [fisherMetricAlongExponentialPath] using
    d2Phi_eq_varianceLogRNDensity N_func Q hZ τ

/-- Fisher metric at `τ = 0`, i.e. variance of `log(dP̂/dQ)` under `Q`. -/
noncomputable def fisherMetricAtZero
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α) : ℝ :=
  ∑ x, Q.prob x *
    (logRNDensity N_func Q x - ∑ y, Q.prob y * logRNDensity N_func Q y) ^ 2

lemma tiltedProb_zero_eq_prob
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (hZ0 : partitionFunction N_func Q 0 ≠ 0)
    (x : α) :
    tiltedProb N_func Q 0 hZ0 x = Q.prob x := by
  have hpart : partitionFunction N_func Q 0 = 1 := by
    unfold partitionFunction
    simp [Q.sum_one]
  unfold tiltedProb
  rw [hpart]
  simp

lemma internalEnergy_zero_eq_expectationQ
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (hZ0 : partitionFunction N_func Q 0 ≠ 0) :
    internalEnergy N_func Q 0 hZ0 =
      ∑ x, Q.prob x * logRNDensity N_func Q x := by
  unfold internalEnergy
  refine Finset.sum_congr rfl ?_
  intro x hx
  simp [tiltedProb_zero_eq_prob N_func Q hZ0 x]

lemma fisherMetricAlongExponentialPath_zero_eq_fisherMetricAtZero
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (hZ0 : partitionFunction N_func Q 0 ≠ 0) :
    fisherMetricAlongExponentialPath N_func Q 0 hZ0 = fisherMetricAtZero N_func Q := by
  unfold fisherMetricAlongExponentialPath fisherMetricAtZero
  calc
    varianceLogRNDensity N_func Q 0 hZ0
        = ∑ x, tiltedProb N_func Q 0 hZ0 x *
            (logRNDensity N_func Q x - internalEnergy N_func Q 0 hZ0) ^ 2 := by
            exact varianceLogRNDensity_eq_sum_sq N_func Q 0 hZ0
    _ = ∑ x, Q.prob x *
          (logRNDensity N_func Q x - internalEnergy N_func Q 0 hZ0) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [tiltedProb_zero_eq_prob N_func Q hZ0 x]
    _ = ∑ x, Q.prob x *
          (logRNDensity N_func Q x -
            ∑ y, Q.prob y * logRNDensity N_func Q y) ^ 2 := by
          simp [internalEnergy_zero_eq_expectationQ N_func Q hZ0]
    _ = fisherMetricAtZero N_func Q := by
          rfl

theorem d2Phi_zero_eq_fisherMetricAtZero
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0) :
    deriv (fun t => deriv (Phi N_func Q) t) 0 = fisherMetricAtZero N_func Q := by
  calc
    deriv (fun t => deriv (Phi N_func Q) t) 0
        = fisherMetricAlongExponentialPath N_func Q 0 (hZ 0) := by
            exact d2Phi_eq_fisherMetricAlongExponentialPath N_func Q hZ 0
    _ = fisherMetricAtZero N_func Q := by
          exact fisherMetricAlongExponentialPath_zero_eq_fisherMetricAtZero N_func Q (hZ 0)

lemma tiltedProb_pos_of_fullSupport
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_full : FullSupport Q)
    (τ : ℝ)
    (hZ : partitionFunction N_func Q τ ≠ 0)
    (x : α) :
    0 < tiltedProb N_func Q τ hZ x := by
  have hZ_nonneg : 0 ≤ partitionFunction N_func Q τ :=
    partitionFunction_nonneg N_func Q τ
  have hZ_pos : 0 < partitionFunction N_func Q τ :=
    lt_of_le_of_ne hZ_nonneg (by simpa [eq_comm] using hZ)
  unfold tiltedProb
  exact div_pos (mul_pos (h_full x) (Real.exp_pos _)) hZ_pos

lemma sum_weighted_sq_eq_zero_iff
    {α : Type*} [Fintype α]
    (μ g : α → ℝ)
    (hμ_pos : ∀ x, 0 < μ x) :
    (∑ x, μ x * (g x) ^ 2 = 0) ↔ ∀ x, g x = 0 := by
  constructor
  · intro hsum
    have hterm_nonneg : ∀ x ∈ (Finset.univ : Finset α), 0 ≤ μ x * (g x) ^ 2 := by
      intro x hx
      exact mul_nonneg (le_of_lt (hμ_pos x)) (sq_nonneg (g x))
    have hterm_zero :
        ∀ x ∈ (Finset.univ : Finset α), μ x * (g x) ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).1 hsum
    intro x
    have hmul_zero : μ x * (g x) ^ 2 = 0 := hterm_zero x (Finset.mem_univ x)
    have hsq_zero : (g x) ^ 2 = 0 :=
      (mul_eq_zero.mp hmul_zero).resolve_left (ne_of_gt (hμ_pos x))
    exact sq_eq_zero_iff.mp hsq_zero
  · intro hg
    refine Finset.sum_eq_zero ?_
    intro x hx
    simp [hg x]

lemma varianceLogRNDensity_eq_zero_iff_logRNDensity_const
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_full : FullSupport Q)
    (τ : ℝ)
    (hZ : partitionFunction N_func Q τ ≠ 0) :
    varianceLogRNDensity N_func Q τ hZ = 0 ↔
      ∀ x, logRNDensity N_func Q x = internalEnergy N_func Q τ hZ := by
  let μ : α → ℝ := tiltedProb N_func Q τ hZ
  let g : α → ℝ := fun x => logRNDensity N_func Q x - internalEnergy N_func Q τ hZ
  have hμ_pos : ∀ x, 0 < μ x := by
    intro x
    simpa [μ] using tiltedProb_pos_of_fullSupport N_func Q h_full τ hZ x
  have hsq_zero :
      (∑ x, μ x * (g x) ^ 2 = 0) ↔ ∀ x, g x = 0 :=
    sum_weighted_sq_eq_zero_iff μ g hμ_pos
  have hvar_sq :
      varianceLogRNDensity N_func Q τ hZ =
        ∑ x, μ x * (g x) ^ 2 := by
    simpa [μ, g] using varianceLogRNDensity_eq_sum_sq N_func Q τ hZ
  constructor
  · intro hVar
    have hg_zero : ∀ x, g x = 0 := by
      exact hsq_zero.1 (by simpa [hvar_sq] using hVar)
    intro x
    have hx : g x = 0 := hg_zero x
    linarith [hx]
  · intro hconst
    have hg_zero : ∀ x, g x = 0 := by
      intro x
      linarith [hconst x]
    have hsum_zero : ∑ x, μ x * (g x) ^ 2 = 0 := hsq_zero.2 hg_zero
    simpa [hvar_sq] using hsum_zero

lemma varianceLogRNDensity_eq_zero_of_empirical_eq
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
    (hZ : partitionFunction N_func Q τ ≠ 0)
    (hPQ : ∀ x, empiricalDistribution N_func x = Q.prob x) :
    varianceLogRNDensity N_func Q τ hZ = 0 := by
  have hlog_zero : ∀ x, logRNDensity N_func Q x = 0 := by
    intro x
    unfold logRNDensity densityRatio
    rw [hPQ x]
    by_cases hqx : Q.prob x = 0
    · simp [hqx]
    · simp [hqx]
  have hU_zero : internalEnergy N_func Q τ hZ = 0 := by
    unfold internalEnergy
    refine Finset.sum_eq_zero ?_
    intro x hx
    simp [hlog_zero x]
  have hsum_zero :
      ∑ x, tiltedProb N_func Q τ hZ x * (logRNDensity N_func Q x) ^ 2 = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    simp [hlog_zero x]
  unfold varianceLogRNDensity
  simp [hU_zero, hsum_zero]

lemma logRNDensity_const_implies_empirical_eq_of_fullSupport
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_nontrivial : EmpiricalNontrivial N_func)
    (h_full : FullSupport Q)
    (c : ℝ)
    (hconst : ∀ x, logRNDensity N_func Q x = c) :
    ∀ x, empiricalDistribution N_func x = Q.prob x := by
  let P : α → ℝ := empiricalDistribution N_func
  by_cases hc0 : c = 0
  · have hlog_zero : ∀ x, Real.log (densityRatio N_func Q x) = 0 := by
      intro x
      simpa [logRNDensity, hc0] using hconst x
    have hKL_zero : KLdivergence N_func Q = 0 := by
      unfold KLdivergence entropyExpectation surprisal
      simp [hlog_zero]
    exact (KL_eq_zero_iff N_func Q h_nontrivial h_full).1 hKL_zero
  · have hsumP : ∑ x, P x = 1 := by
      simpa [P] using empirical_sum_one N_func h_nontrivial
    have hsumQ : ∑ x, Q.prob x = 1 := Q.sum_one
    have hratio_eq : ∀ x, densityRatio N_func Q x = Real.exp c := by
      intro x
      have hratio_ne_zero : densityRatio N_func Q x ≠ 0 := by
        intro hratio0
        have hlog0 : logRNDensity N_func Q x = 0 := by
          simp [logRNDensity, hratio0]
        exact hc0 (by simpa [hlog0] using (hconst x).symm)
      have hratio_nonneg : 0 ≤ densityRatio N_func Q x := by
        unfold densityRatio
        exact div_nonneg
          (by
            unfold empiricalDistribution
            exact div_nonneg (by positivity) (by positivity))
          (le_of_lt (h_full x))
      have hratio_pos : 0 < densityRatio N_func Q x :=
        lt_of_le_of_ne hratio_nonneg (by simpa [eq_comm] using hratio_ne_zero)
      have hExp : Real.exp (logRNDensity N_func Q x) = Real.exp c := by
        simp [hconst x]
      calc
        densityRatio N_func Q x
            = Real.exp (logRNDensity N_func Q x) := by
                simp [logRNDensity, Real.exp_log hratio_pos]
        _ = Real.exp c := hExp
    have hP_eq : ∀ x, P x = Real.exp c * Q.prob x := by
      intro x
      have hq_ne : Q.prob x ≠ 0 := ne_of_gt (h_full x)
      have hratio : P x / Q.prob x = Real.exp c := by
        simpa [P, densityRatio] using hratio_eq x
      exact (div_eq_iff hq_ne).1 hratio
    have hexp_one : Real.exp c = 1 := by
      calc
        Real.exp c = ∑ x, P x := by
          calc
            Real.exp c = Real.exp c * 1 := by ring
            _ = Real.exp c * (∑ x, Q.prob x) := by simp [hsumQ]
            _ = ∑ x, Real.exp c * Q.prob x := by
                  rw [(Finset.mul_sum (Finset.univ : Finset α)
            (fun x => Q.prob x) (Real.exp c)).symm]
            _ = ∑ x, P x := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  symm
                  exact hP_eq x
        _ = 1 := hsumP
    have hc_zero : c = 0 := (Real.exp_eq_one_iff c).1 hexp_one
    exact False.elim (hc0 hc_zero)

theorem d2Phi_eq_zero_iff_logRNDensity_const_of_fullSupport
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_full : FullSupport Q)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0)
    (τ : ℝ) :
    deriv (fun t => deriv (Phi N_func Q) t) τ = 0 ↔
      ∀ x, logRNDensity N_func Q x = internalEnergy N_func Q τ (hZ τ) := by
  have hder2 :
      deriv (fun t => deriv (Phi N_func Q) t) τ =
        varianceLogRNDensity N_func Q τ (hZ τ) := by
    exact d2Phi_eq_varianceLogRNDensity N_func Q hZ τ
  constructor
  · intro hcurv
    have hvar_zero : varianceLogRNDensity N_func Q τ (hZ τ) = 0 := by
      simpa [hder2] using hcurv
    exact (varianceLogRNDensity_eq_zero_iff_logRNDensity_const
      N_func Q h_full τ (hZ τ)).1 hvar_zero
  · intro hconst
    have hvar_zero : varianceLogRNDensity N_func Q τ (hZ τ) = 0 :=
      (varianceLogRNDensity_eq_zero_iff_logRNDensity_const
        N_func Q h_full τ (hZ τ)).2 hconst
    simpa [hder2] using hvar_zero

theorem d2Phi_eq_zero_iff_empirical_eq_of_fullSupport
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_nontrivial : EmpiricalNontrivial N_func)
    (h_full : FullSupport Q)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0)
    (τ : ℝ) :
    deriv (fun t => deriv (Phi N_func Q) t) τ = 0 ↔
      ∀ x, empiricalDistribution N_func x = Q.prob x := by
  constructor
  · intro hcurv
    have hconst :
        ∀ x, logRNDensity N_func Q x = internalEnergy N_func Q τ (hZ τ) :=
      (d2Phi_eq_zero_iff_logRNDensity_const_of_fullSupport
        N_func Q h_full hZ τ).1 hcurv
    exact logRNDensity_const_implies_empirical_eq_of_fullSupport
      N_func Q h_nontrivial h_full _ hconst
  · intro hPQ
    have hvar_zero : varianceLogRNDensity N_func Q τ (hZ τ) = 0 :=
      varianceLogRNDensity_eq_zero_of_empirical_eq N_func Q τ (hZ τ) hPQ
    simpa [d2Phi_eq_varianceLogRNDensity N_func Q hZ τ] using hvar_zero

lemma differentiable_Phi
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0) :
    Differentiable ℝ (Phi N_func Q) := by
  intro t
  have hlog :
      HasDerivAt (Phi N_func Q)
        ((∑ x, Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x) *
            logRNDensity N_func Q x) /
          partitionFunction N_func Q t) t := by
    simpa [Phi] using (hasDerivAt_partitionFunction N_func Q t).log (hZ t)
  exact hlog.differentiableAt

lemma differentiable_deriv_Phi
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0) :
    Differentiable ℝ (deriv (Phi N_func Q)) := by
  have hderiv :
      deriv (Phi N_func Q) =
        fun t =>
          (∑ x, Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x) *
            logRNDensity N_func Q x) / partitionFunction N_func Q t := by
    exact deriv_Phi_eq_partition_ratio N_func Q hZ
  intro t
  rw [hderiv]
  exact ((hasDerivAt_partitionFunctionLogMoment N_func Q t).differentiableAt).div
    ((hasDerivAt_partitionFunction N_func Q t).differentiableAt) (hZ t)

theorem Phi_convex
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0) :
    ConvexOn ℝ Set.univ (Phi N_func Q) := by
  refine convexOn_univ_of_deriv2_nonneg
    (differentiable_Phi N_func Q hZ)
    (differentiable_deriv_Phi N_func Q hZ)
    ?_
  intro t
  have hder2 :
      (deriv^[2]) (Phi N_func Q) t =
        varianceLogRNDensity N_func Q t (hZ t) := by
    simpa [Function.iterate_succ_apply'] using
      d2Phi_eq_varianceLogRNDensity N_func Q hZ t
  have hvar_nonneg : 0 ≤ varianceLogRNDensity N_func Q t (hZ t) := by
    exact varianceLogRNDensity_nonneg N_func Q t (hZ t)
  simpa [hder2] using hvar_nonneg

theorem KL_nonneg_via_convex
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_nontrivial : EmpiricalNontrivial N_func)
    (h_support : SupportMatches N_func Q)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0) :
    0 ≤ KLdivergence N_func Q := by
  have hconv : ConvexOn ℝ Set.univ (Phi N_func Q) := Phi_convex N_func Q hZ
  have hslope :
      slope (Phi N_func Q) 0 1 ≤ deriv (Phi N_func Q) 1 := by
    exact hconv.slope_le_deriv (by simp) (by simp) (by norm_num)
      ((differentiable_Phi N_func Q hZ) 1)
  have hslope_zero : slope (Phi N_func Q) 0 1 = 0 := by
    have hPhi0 : Phi N_func Q 0 = 0 := Phi_zero N_func Q
    have hPhi1 : Phi N_func Q 1 = 0 :=
      Phi_one_of_supportMatches N_func Q h_nontrivial h_support
    simp [slope_def_field, hPhi0, hPhi1]
  have hderiv_nonneg : 0 ≤ deriv (Phi N_func Q) 1 := by
    calc
      0 = slope (Phi N_func Q) 0 1 := by simp [hslope_zero]
      _ ≤ deriv (Phi N_func Q) 1 := hslope
  have hderiv_eq_KL : deriv (Phi N_func Q) 1 = KLdivergence N_func Q := by
    exact deriv_Phi_one_eq_KL_of_supportMatches N_func Q h_nontrivial h_support (hZ 1)
  simpa [hderiv_eq_KL] using hderiv_nonneg

section MeasureTheoreticKL

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- Canonical measure-theoretic KL divergence.
This is Mathlib's `InformationTheory.klDiv`, valued in `ℝ≥0∞`. -/
noncomputable def KLDivergence (μ ν : Measure α) : ℝ≥0∞ :=
  InformationTheory.klDiv μ ν

lemma KLDivergence_of_ac_of_integrable
    (μ ν : Measure α)
    (h_ac : μ ≪ ν)
    (h_int : Integrable (MeasureTheory.llr μ ν) μ) :
    KLDivergence μ ν =
      ENNReal.ofReal (∫ x, MeasureTheory.llr μ ν x ∂μ + ν.real Set.univ - μ.real Set.univ) := by
  simpa [KLDivergence] using InformationTheory.klDiv_of_ac_of_integrable h_ac h_int

@[simp] lemma KLDivergence_of_not_ac
    (μ ν : Measure α)
    (h_not_ac : ¬ μ ≪ ν) :
    KLDivergence μ ν = ∞ := by
  simpa [KLDivergence] using InformationTheory.klDiv_of_not_ac (μ := μ) (ν := ν) h_not_ac

lemma KLDivergence_ne_top_iff
    (μ ν : Measure α) :
    KLDivergence μ ν ≠ ∞ ↔
      μ ≪ ν ∧ Integrable (MeasureTheory.llr μ ν) μ := by
  simpa [KLDivergence] using InformationTheory.klDiv_ne_top_iff (μ := μ) (ν := ν)

open Classical in
lemma KLDivergence_eq_lintegral_klFun
    (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    KLDivergence μ ν =
      if _h_ac : μ ≪ ν then
        ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((μ.rnDeriv ν x).toReal)) ∂ν
      else ∞ := by
  simpa [KLDivergence] using InformationTheory.klDiv_eq_lintegral_klFun (μ := μ) (ν := ν)

lemma KLDivergence_eq_zero_iff
    (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    KLDivergence μ ν = 0 ↔ μ = ν := by
  simpa [KLDivergence] using InformationTheory.klDiv_eq_zero_iff (μ := μ) (ν := ν)

end MeasureTheoreticKL

section GeneralMeasurableExponentialFamily

open MeasureTheory
open scoped ENNReal

variable {Θ X : Type*} [MeasurableSpace X]

/-- General measurable exponential-family template:
`dμ_θ = exp(T(θ, x) - A(θ)) dν`. -/
structure MeasurableExponentialFamily (Θ X : Type*) [MeasurableSpace X] where
  base : Measure X
  stat : Θ → X → ℝ
  logPartition : Θ → ℝ
  measurable_stat : ∀ θ, Measurable (stat θ)

/-- Pointwise exponential-family density (as a real-valued kernel). -/
noncomputable def MeasurableExponentialFamily.density
    (F : MeasurableExponentialFamily Θ X) (θ : Θ) (x : X) : ℝ :=
  Real.exp (F.stat θ x - F.logPartition θ)

/-- The measure at parameter `θ` obtained by weighting the base measure. -/
noncomputable def MeasurableExponentialFamily.measure
    (F : MeasurableExponentialFamily Θ X) (θ : Θ) : Measure X :=
  F.base.withDensity (fun x => ENNReal.ofReal (F.density θ x))

end GeneralMeasurableExponentialFamily

section FiniteExponentialFamily

variable {α : Type*} [Fintype α]

/-- Partition function `Z(θ)` for a one-dimensional finite exponential family. -/
noncomputable def expFamilyPartition
    (Q : ProbabilityDist α) (T : α → ℝ) (θ : ℝ) : ℝ :=
  ∑ x, Q.prob x * Real.exp (θ * T x)

/-- Log-partition potential `A(θ) = log Z(θ)`. -/
noncomputable def expFamilyLogPartition
    (Q : ProbabilityDist α) (T : α → ℝ) (θ : ℝ) : ℝ :=
  Real.log (expFamilyPartition Q T θ)

/-- Exponential-family probability kernel. -/
noncomputable def expFamilyProb
    (Q : ProbabilityDist α) (T : α → ℝ) (θ : ℝ) (x : α) : ℝ :=
  (Q.prob x * Real.exp (θ * T x)) / expFamilyPartition Q T θ

/-- Mean of the sufficient statistic under `P_θ`. -/
noncomputable def expFamilyStatMean
    (Q : ProbabilityDist α) (T : α → ℝ) (θ : ℝ) : ℝ :=
  ∑ x, expFamilyProb Q T θ x * T x

/-- KL divergence between two parameters inside the same exponential family. -/
noncomputable def expFamilyKL
    (Q : ProbabilityDist α) (T : α → ℝ) (θ η : ℝ) : ℝ :=
  ∑ x, expFamilyProb Q T θ x *
    Real.log (expFamilyProb Q T θ x / expFamilyProb Q T η x)

lemma expFamilyPartition_pos
    (Q : ProbabilityDist α) (T : α → ℝ)
    (hQ : FullSupport Q) (θ : ℝ) :
    0 < expFamilyPartition Q T θ := by
  classical
  unfold expFamilyPartition
  have h_nonneg :
      ∀ x ∈ (Finset.univ : Finset α), 0 ≤ Q.prob x * Real.exp (θ * T x) := by
    intro x hx
    exact mul_nonneg (Q.nonneg x) (le_of_lt (Real.exp_pos _))
  have h_nonempty : (Finset.univ : Finset α).Nonempty := by
    by_contra hEmpty
    have huniv : (Finset.univ : Finset α) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hEmpty
    have hsum0 : (∑ x, Q.prob x) = 0 := by simp [huniv]
    linarith [Q.sum_one, hsum0]
  rcases h_nonempty with ⟨x0, hx0⟩
  have h_pos : 0 < Q.prob x0 * Real.exp (θ * T x0) :=
    mul_pos (hQ x0) (Real.exp_pos _)
  exact Finset.sum_pos' h_nonneg ⟨x0, hx0, h_pos⟩

lemma hasDerivAt_expFamilyPartition
    (Q : ProbabilityDist α) (T : α → ℝ) (θ : ℝ) :
    HasDerivAt (expFamilyPartition Q T)
      (∑ x, Q.prob x * Real.exp (θ * T x) * T x) θ := by
  classical
  unfold expFamilyPartition
  change HasDerivAt
    (fun t : ℝ => ∑ x, Q.prob x * Real.exp (t * T x))
    (∑ x, Q.prob x * Real.exp (θ * T x) * T x) θ
  refine HasDerivAt.fun_sum ?_
  intro x hx
  have hlin : HasDerivAt (fun t : ℝ => t * T x) (T x) θ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_id θ).mul_const (T x)
  have hexp :
      HasDerivAt (fun t : ℝ => Real.exp (t * T x))
        (Real.exp (θ * T x) * T x) θ := by
    exact (Real.hasDerivAt_exp (θ * T x)).comp θ hlin
  simpa [mul_assoc, mul_left_comm, mul_comm] using hexp.const_mul (Q.prob x)

lemma expFamilyProb_sum_one
    (Q : ProbabilityDist α) (T : α → ℝ)
    (hQ : FullSupport Q) (θ : ℝ) :
    ∑ x, expFamilyProb Q T θ x = 1 := by
  have hZ : expFamilyPartition Q T θ ≠ 0 :=
    ne_of_gt (expFamilyPartition_pos Q T hQ θ)
  unfold expFamilyProb
  calc
    ∑ x, (Q.prob x * Real.exp (θ * T x)) / expFamilyPartition Q T θ
        = (∑ x, Q.prob x * Real.exp (θ * T x)) / expFamilyPartition Q T θ := by
            rw [Finset.sum_div]
    _ = expFamilyPartition Q T θ / expFamilyPartition Q T θ := by
          simp [expFamilyPartition]
    _ = 1 := by
          exact div_self hZ

theorem deriv_expFamilyLogPartition_eq_statMean
    (Q : ProbabilityDist α) (T : α → ℝ)
    (hQ : FullSupport Q) (θ : ℝ) :
    deriv (expFamilyLogPartition Q T) θ = expFamilyStatMean Q T θ := by
  have hZ : expFamilyPartition Q T θ ≠ 0 :=
    ne_of_gt (expFamilyPartition_pos Q T hQ θ)
  have hlog :
      HasDerivAt (expFamilyLogPartition Q T)
        ((∑ x, Q.prob x * Real.exp (θ * T x) * T x) /
          expFamilyPartition Q T θ) θ := by
    simpa [expFamilyLogPartition] using
      (hasDerivAt_expFamilyPartition Q T θ).log hZ
  calc
    deriv (expFamilyLogPartition Q T) θ
        = ((∑ x, Q.prob x * Real.exp (θ * T x) * T x) /
            expFamilyPartition Q T θ) := hlog.deriv
    _ = expFamilyStatMean Q T θ := by
          unfold expFamilyStatMean expFamilyProb
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl ?_
          intro x hx
          ring

lemma expFamilyProb_log_ratio
    (Q : ProbabilityDist α) (T : α → ℝ)
    (hQ : FullSupport Q) (θ η : ℝ) (x : α) :
    Real.log (expFamilyProb Q T θ x / expFamilyProb Q T η x) =
      (θ - η) * T x - expFamilyLogPartition Q T θ + expFamilyLogPartition Q T η := by
  have hq_pos : 0 < Q.prob x := hQ x
  have hZθ_pos : 0 < expFamilyPartition Q T θ := expFamilyPartition_pos Q T hQ θ
  have hZη_pos : 0 < expFamilyPartition Q T η := expFamilyPartition_pos Q T hQ η
  have hpθ_pos : 0 < expFamilyProb Q T θ x := by
    unfold expFamilyProb
    exact div_pos (mul_pos hq_pos (Real.exp_pos _)) hZθ_pos
  have hpη_pos : 0 < expFamilyProb Q T η x := by
    unfold expFamilyProb
    exact div_pos (mul_pos hq_pos (Real.exp_pos _)) hZη_pos
  have hlogθ :
      Real.log (expFamilyProb Q T θ x) =
        Real.log (Q.prob x) + θ * T x - expFamilyLogPartition Q T θ := by
    have hnum_pos : 0 < Q.prob x * Real.exp (θ * T x) :=
      mul_pos hq_pos (Real.exp_pos _)
    have hnum_ne : Q.prob x * Real.exp (θ * T x) ≠ 0 := ne_of_gt hnum_pos
    have hZθ_ne : expFamilyPartition Q T θ ≠ 0 := ne_of_gt hZθ_pos
    calc
      Real.log (expFamilyProb Q T θ x)
          = Real.log (Q.prob x * Real.exp (θ * T x)) -
              Real.log (expFamilyPartition Q T θ) := by
                unfold expFamilyProb
                rw [Real.log_div hnum_ne hZθ_ne]
      _ = Real.log (Q.prob x) + θ * T x - expFamilyLogPartition Q T θ := by
            rw [Real.log_mul (ne_of_gt hq_pos) (by positivity)]
            simp [expFamilyLogPartition]
  have hlogη :
      Real.log (expFamilyProb Q T η x) =
        Real.log (Q.prob x) + η * T x - expFamilyLogPartition Q T η := by
    have hnum_pos : 0 < Q.prob x * Real.exp (η * T x) :=
      mul_pos hq_pos (Real.exp_pos _)
    have hnum_ne : Q.prob x * Real.exp (η * T x) ≠ 0 := ne_of_gt hnum_pos
    have hZη_ne : expFamilyPartition Q T η ≠ 0 := ne_of_gt hZη_pos
    calc
      Real.log (expFamilyProb Q T η x)
          = Real.log (Q.prob x * Real.exp (η * T x)) -
              Real.log (expFamilyPartition Q T η) := by
                unfold expFamilyProb
                rw [Real.log_div hnum_ne hZη_ne]
      _ = Real.log (Q.prob x) + η * T x - expFamilyLogPartition Q T η := by
            rw [Real.log_mul (ne_of_gt hq_pos) (by positivity)]
            simp [expFamilyLogPartition]
  calc
    Real.log (expFamilyProb Q T θ x / expFamilyProb Q T η x)
        = Real.log (expFamilyProb Q T θ x) - Real.log (expFamilyProb Q T η x) := by
            rw [Real.log_div (ne_of_gt hpθ_pos) (ne_of_gt hpη_pos)]
    _ = (θ - η) * T x - expFamilyLogPartition Q T θ + expFamilyLogPartition Q T η := by
          rw [hlogθ, hlogη]
          ring

lemma expFamilyKL_eq_affine_gap
    (Q : ProbabilityDist α) (T : α → ℝ)
    (hQ : FullSupport Q) (θ η : ℝ) :
    expFamilyKL Q T θ η =
      (θ - η) * expFamilyStatMean Q T θ
        - expFamilyLogPartition Q T θ + expFamilyLogPartition Q T η := by
  have hsum1 : ∑ x, expFamilyProb Q T θ x = 1 :=
    expFamilyProb_sum_one Q T hQ θ
  unfold expFamilyKL expFamilyStatMean
  calc
    ∑ x, expFamilyProb Q T θ x *
      Real.log (expFamilyProb Q T θ x / expFamilyProb Q T η x)
        = ∑ x, expFamilyProb Q T θ x *
            ((θ - η) * T x - expFamilyLogPartition Q T θ + expFamilyLogPartition Q T η) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              rw [expFamilyProb_log_ratio Q T hQ θ η x]
    _ = ∑ x, ((θ - η) * (expFamilyProb Q T θ x * T x) +
          expFamilyProb Q T θ x *
            (-expFamilyLogPartition Q T θ + expFamilyLogPartition Q T η)) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          ring
    _ = (θ - η) * (∑ x, expFamilyProb Q T θ x * T x) +
          (∑ x, expFamilyProb Q T θ x) *
            (-expFamilyLogPartition Q T θ + expFamilyLogPartition Q T η) := by
          rw [Finset.sum_add_distrib]
          rw [(Finset.mul_sum (Finset.univ : Finset α)
            (fun x => expFamilyProb Q T θ x * T x) (θ - η)).symm]
          rw [Finset.sum_mul]
    _ = (θ - η) * (∑ x, expFamilyProb Q T θ x * T x) +
          1 * (-expFamilyLogPartition Q T θ + expFamilyLogPartition Q T η) := by
          simp [hsum1]
    _ = (θ - η) * expFamilyStatMean Q T θ
          - expFamilyLogPartition Q T θ + expFamilyLogPartition Q T η := by
          simp [expFamilyStatMean]
          ring

/-- Orientation theorem:
for this finite exponential family, `KL(P_θ || P_η) = B_A(η, θ)`. -/
theorem expFamilyKL_eq_bregman_logPartition
    (Q : ProbabilityDist α) (T : α → ℝ)
    (hQ : FullSupport Q) (θ η : ℝ) :
    expFamilyKL Q T θ η =
      bregmanDiv (expFamilyLogPartition Q T) η θ := by
  have hKL :
      expFamilyKL Q T θ η =
        (θ - η) * expFamilyStatMean Q T θ
          - expFamilyLogPartition Q T θ + expFamilyLogPartition Q T η :=
    expFamilyKL_eq_affine_gap Q T hQ θ η
  have hderiv :
      deriv (expFamilyLogPartition Q T) θ = expFamilyStatMean Q T θ :=
    deriv_expFamilyLogPartition_eq_statMean Q T hQ θ
  calc
    expFamilyKL Q T θ η
        = (θ - η) * expFamilyStatMean Q T θ
            - expFamilyLogPartition Q T θ + expFamilyLogPartition Q T η := hKL
    _ = expFamilyLogPartition Q T η - expFamilyLogPartition Q T θ -
          deriv (expFamilyLogPartition Q T) θ * (η - θ) := by
          rw [hderiv]
          ring
    _ = bregmanDiv (expFamilyLogPartition Q T) η θ := by
          simp [bregmanDiv]

end FiniteExponentialFamily

section PoissonExponentialFamily

open ProbabilityTheory
open MeasureTheory

/-- Natural-parameter to rate map for Poisson (`λ = exp θ`). -/
noncomputable def poissonRateOfTheta (θ : ℝ) : NNReal :=
  ⟨Real.exp θ, le_of_lt (Real.exp_pos θ)⟩

/-- Poisson PMF in natural coordinates. -/
noncomputable def poissonPMFTheta (θ : ℝ) : PMF ℕ :=
  ProbabilityTheory.poissonPMF (poissonRateOfTheta θ)

/-- Poisson measure in natural coordinates. -/
noncomputable def poissonMeasureTheta (θ : ℝ) : Measure ℕ :=
  ProbabilityTheory.poissonMeasure (poissonRateOfTheta θ)

/-- Poisson log-partition potential in natural coordinates (`A(θ)=exp θ`). -/
noncomputable def poissonLogPartition (θ : ℝ) : ℝ :=
  Real.exp θ

/-- Poisson KL written in natural coordinates (`θ, η`). -/
noncomputable def poissonKLNatural (θ η : ℝ) : ℝ :=
  Real.exp θ * (θ - η) + Real.exp η - Real.exp θ

/-- Poisson KL in rate coordinates (`λ₁, λ₂`). -/
noncomputable def poissonKLClosedForm (lam1 lam2 : ℝ) : ℝ :=
  lam1 * Real.log (lam1 / lam2) + lam2 - lam1

theorem poissonKLNatural_eq_bregman :
    ∀ θ η : ℝ,
      poissonKLNatural θ η = bregmanDiv poissonLogPartition η θ := by
  intro θ η
  unfold poissonKLNatural bregmanDiv poissonLogPartition
  simp
  ring

theorem poissonKLClosedForm_eq_bregman
    {lam1 lam2 : ℝ}
    (hlam1 : 0 < lam1)
    (hlam2 : 0 < lam2) :
    poissonKLClosedForm lam1 lam2 =
      bregmanDiv poissonLogPartition (Real.log lam2) (Real.log lam1) := by
  have hlog_div : Real.log (lam1 / lam2) = Real.log lam1 - Real.log lam2 := by
    rw [Real.log_div (ne_of_gt hlam1) (ne_of_gt hlam2)]
  calc
    poissonKLClosedForm lam1 lam2
        = lam1 * (Real.log lam1 - Real.log lam2) + lam2 - lam1 := by
            simp [poissonKLClosedForm, hlog_div]
    _ = lam2 - lam1 - lam1 * (Real.log lam2 - Real.log lam1) := by
          ring
    _ = bregmanDiv poissonLogPartition (Real.log lam2) (Real.log lam1) := by
          unfold bregmanDiv poissonLogPartition
          simp [Real.exp_log hlam1, Real.exp_log hlam2]

end PoissonExponentialFamily

section GrandCanonical

variable {α : Type*} [Fintype α]

/-- Grand-canonical partition function
`Ξ(β, μ) = ∑ exp(-β (E - μ N))`. -/
noncomputable def grandCanonicalPartition
    (E N : α → ℝ) (β μ : ℝ) : ℝ :=
  ∑ x, Real.exp (-β * (E x - μ * N x))

/-- Grand Massieu potential `Ψ = log Ξ`. -/
noncomputable def grandMassieuPotential
    (E N : α → ℝ) (β μ : ℝ) : ℝ :=
  Real.log (grandCanonicalPartition E N β μ)

/-- Grand-canonical Gibbs weight at fixed `(β, μ)`. -/
noncomputable def grandCanonicalProb
    (E N : α → ℝ) (β μ : ℝ)
    (_hXi : grandCanonicalPartition E N β μ ≠ 0)
    (x : α) : ℝ :=
  Real.exp (-β * (E x - μ * N x)) / grandCanonicalPartition E N β μ

lemma hasDerivAt_grandCanonicalPartition_beta
    (E N : α → ℝ) (β μ : ℝ) :
    HasDerivAt (fun t => grandCanonicalPartition E N t μ)
      (∑ x, Real.exp (-β * (E x - μ * N x)) * (-(E x - μ * N x))) β := by
  classical
  unfold grandCanonicalPartition
  refine HasDerivAt.fun_sum ?_
  intro x hx
  have hlin :
      HasDerivAt (fun t : ℝ => -t * (E x - μ * N x))
        (-(E x - μ * N x)) β := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id β).neg.mul_const (E x - μ * N x))
  exact (Real.hasDerivAt_exp (-β * (E x - μ * N x))).comp β hlin

theorem deriv_grandCanonicalPartition_beta
    (E N : α → ℝ) (β μ : ℝ) :
    deriv (fun t => grandCanonicalPartition E N t μ) β =
      ∑ x, Real.exp (-β * (E x - μ * N x)) * (-(E x - μ * N x)) := by
  exact (hasDerivAt_grandCanonicalPartition_beta E N β μ).deriv

theorem deriv_grandMassieuPotential_beta
    (E N : α → ℝ) (β μ : ℝ)
    (hXi : grandCanonicalPartition E N β μ ≠ 0) :
    deriv (fun t => grandMassieuPotential E N t μ) β =
      ∑ x, grandCanonicalProb E N β μ hXi x * (-(E x - μ * N x)) := by
  have hlog :
      HasDerivAt (fun t => grandMassieuPotential E N t μ)
        ((∑ x, Real.exp (-β * (E x - μ * N x)) * (-(E x - μ * N x))) /
          grandCanonicalPartition E N β μ) β := by
    simpa [grandMassieuPotential] using
      (hasDerivAt_grandCanonicalPartition_beta E N β μ).log hXi
  calc
    deriv (fun t => grandMassieuPotential E N t μ) β
        = ((∑ x, Real.exp (-β * (E x - μ * N x)) * (-(E x - μ * N x))) /
            grandCanonicalPartition E N β μ) := hlog.deriv
    _ = ∑ x, grandCanonicalProb E N β μ hXi x * (-(E x - μ * N x)) := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp [grandCanonicalProb, mul_comm]
          ring

lemma hasDerivAt_grandCanonicalPartition_mu
    (E N : α → ℝ) (β μ : ℝ) :
    HasDerivAt (fun t => grandCanonicalPartition E N β t)
      (∑ x, Real.exp (-β * (E x - μ * N x)) * (β * N x)) μ := by
  classical
  unfold grandCanonicalPartition
  refine HasDerivAt.fun_sum ?_
  intro x hx
  have hlin :
      HasDerivAt (fun t : ℝ => -β * (E x - t * N x))
        (β * N x) μ := by
    have hEq :
        (fun t : ℝ => -β * (E x - t * N x)) =
          (fun t : ℝ => (β * N x) * t + (-β * E x)) := by
      funext t
      ring
    rw [hEq]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id μ).const_mul (β * N x)).add_const (-β * E x))
  exact (Real.hasDerivAt_exp (-β * (E x - μ * N x))).comp μ hlin

theorem deriv_grandCanonicalPartition_mu
    (E N : α → ℝ) (β μ : ℝ) :
    deriv (fun t => grandCanonicalPartition E N β t) μ =
      ∑ x, Real.exp (-β * (E x - μ * N x)) * (β * N x) := by
  exact (hasDerivAt_grandCanonicalPartition_mu E N β μ).deriv

theorem deriv_grandMassieuPotential_mu
    (E N : α → ℝ) (β μ : ℝ)
    (hXi : grandCanonicalPartition E N β μ ≠ 0) :
    deriv (fun t => grandMassieuPotential E N β t) μ =
      ∑ x, grandCanonicalProb E N β μ hXi x * (β * N x) := by
  have hlog :
      HasDerivAt (fun t => grandMassieuPotential E N β t)
        ((∑ x, Real.exp (-β * (E x - μ * N x)) * (β * N x)) /
          grandCanonicalPartition E N β μ) μ := by
    simpa [grandMassieuPotential] using
      (hasDerivAt_grandCanonicalPartition_mu E N β μ).log hXi
  calc
    deriv (fun t => grandMassieuPotential E N β t) μ
        = ((∑ x, Real.exp (-β * (E x - μ * N x)) * (β * N x)) /
            grandCanonicalPartition E N β μ) := hlog.deriv
    _ = ∑ x, grandCanonicalProb E N β μ hXi x * (β * N x) := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp [grandCanonicalProb, mul_comm]
          ring

theorem deriv_grandMassieuPotential_mu_eq_beta_mul_meanN
    (E N : α → ℝ) (β μ : ℝ)
    (hXi : grandCanonicalPartition E N β μ ≠ 0) :
  deriv (fun t => grandMassieuPotential E N β t) μ =
      β * ∑ x, grandCanonicalProb E N β μ hXi x * N x := by
  calc
  deriv (fun t => grandMassieuPotential E N β t) μ
        = ∑ x, grandCanonicalProb E N β μ hXi x * (β * N x) := by
            exact deriv_grandMassieuPotential_mu E N β μ hXi
    _ = β * ∑ x, grandCanonicalProb E N β μ hXi x * N x := by
          have hsum :
              ∑ x, grandCanonicalProb E N β μ hXi x * (β * N x) =
                ∑ x, β * (grandCanonicalProb E N β μ hXi x * N x) := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  ring
          rw [hsum]
          rw [(Finset.mul_sum (Finset.univ : Finset α)
            (fun x => grandCanonicalProb E N β μ hXi x * N x) β).symm]

/-- Grand-canonical partition is strictly positive on nonempty finite state spaces. -/
lemma grandCanonicalPartition_pos
    [Nonempty α]
    (E N : α → ℝ) (β μ : ℝ) :
    0 < grandCanonicalPartition E N β μ := by
  classical
  unfold grandCanonicalPartition
  have hpos :
      ∀ x ∈ (Finset.univ : Finset α), 0 < Real.exp (-β * (E x - μ * N x)) := by
    intro x hx
    exact Real.exp_pos _
  have hsum :
      0 < ∑ x ∈ (Finset.univ : Finset α), Real.exp (-β * (E x - μ * N x)) := by
    exact Finset.sum_pos hpos Finset.univ_nonempty
  simpa using hsum

lemma grandCanonicalPartition_ne_zero
    [Nonempty α]
    (E N : α → ℝ) (β μ : ℝ) :
    grandCanonicalPartition E N β μ ≠ 0 :=
  ne_of_gt (grandCanonicalPartition_pos E N β μ)

lemma grandCanonicalProb_nonneg
    [Nonempty α]
    (E N : α → ℝ) (β μ : ℝ) (x : α) :
    0 ≤ grandCanonicalProb E N β μ (grandCanonicalPartition_ne_zero E N β μ) x := by
  unfold grandCanonicalProb
  exact div_nonneg (by positivity) (le_of_lt (grandCanonicalPartition_pos E N β μ))

lemma grandCanonicalProb_sum_one
    [Nonempty α]
    (E N : α → ℝ) (β μ : ℝ) :
    ∑ x, grandCanonicalProb E N β μ (grandCanonicalPartition_ne_zero E N β μ) x = 1 := by
  unfold grandCanonicalProb
  calc
    ∑ x, Real.exp (-β * (E x - μ * N x)) / grandCanonicalPartition E N β μ
        = (∑ x, Real.exp (-β * (E x - μ * N x))) / grandCanonicalPartition E N β μ := by
            rw [Finset.sum_div]
    _ = grandCanonicalPartition E N β μ / grandCanonicalPartition E N β μ := by
          simp [grandCanonicalPartition]
    _ = 1 := by
          exact div_self (grandCanonicalPartition_ne_zero E N β μ)

/-- Centered Hamiltonian `H(x) = E(x) - μ N(x)` at fixed chemical potential `μ`. -/
noncomputable def grandHamiltonian
    (E N : α → ℝ) (μ : ℝ) (x : α) : ℝ :=
  E x - μ * N x

/-- Mean of an observable under the grand-canonical law. -/
noncomputable def grandMean
    [Nonempty α]
    (E N : α → ℝ) (β μ : ℝ) (f : α → ℝ) : ℝ :=
  ∑ x, grandCanonicalProb E N β μ (grandCanonicalPartition_ne_zero E N β μ) x * f x

/-- Variance of an observable under the grand-canonical law. -/
noncomputable def grandVariance
    [Nonempty α]
    (E N : α → ℝ) (β μ : ℝ) (f : α → ℝ) : ℝ :=
  grandMean E N β μ (fun x => (f x) ^ 2) - (grandMean E N β μ f) ^ 2

/-- Covariance of two observables under the grand-canonical law. -/
noncomputable def grandCovariance
    [Nonempty α]
    (E N : α → ℝ) (β μ : ℝ) (f g : α → ℝ) : ℝ :=
  grandMean E N β μ (fun x => f x * g x) -
    grandMean E N β μ f * grandMean E N β μ g

lemma grandVariance_nonneg
    [Nonempty α]
    (E N : α → ℝ) (β μ : ℝ) (f : α → ℝ) :
    0 ≤ grandVariance E N β μ f := by
  let p : α → ℝ := fun x =>
    grandCanonicalProb E N β μ (grandCanonicalPartition_ne_zero E N β μ) x
  have hp_nonneg : ∀ x ∈ (Finset.univ : Finset α), 0 ≤ p x := by
    intro x hx
    simpa [p] using grandCanonicalProb_nonneg E N β μ x
  have hp_sum : ∑ x ∈ (Finset.univ : Finset α), p x = 1 := by
    simpa [p] using grandCanonicalProb_sum_one E N β μ
  have hsq_convex : ConvexOn ℝ Set.univ (fun t : ℝ => t ^ (2 : ℕ)) := by
    exact (Even.strictConvexOn_pow (n := 2) (by decide) (by decide)).convexOn
  have hJ :
      (∑ x ∈ (Finset.univ : Finset α), p x • f x) ^ (2 : ℕ) ≤
        ∑ x ∈ (Finset.univ : Finset α), p x • (f x ^ (2 : ℕ)) := by
    exact hsq_convex.map_sum_le
      (t := (Finset.univ : Finset α))
      (w := p)
      (p := f)
      hp_nonneg
      hp_sum
      (by intro x hx; simp)
  have hmean_sq_le :
      (grandMean E N β μ f) ^ 2 ≤ grandMean E N β μ (fun x => (f x) ^ 2) := by
    simpa [grandMean, p, smul_eq_mul] using hJ
  unfold grandVariance
  linarith

lemma hasDerivAt_grandCanonicalPartition_betaMoment
    (E N : α → ℝ) (β μ : ℝ) :
    HasDerivAt
      (fun t => ∑ x, Real.exp (-t * (E x - μ * N x)) * (-(E x - μ * N x)))
      (∑ x, (Real.exp (-β * (E x - μ * N x)) * (-(E x - μ * N x))) *
        (-(E x - μ * N x))) β := by
  classical
  refine HasDerivAt.fun_sum ?_
  intro x hx
  have hlin :
      HasDerivAt (fun t : ℝ => -t * (E x - μ * N x))
        (-(E x - μ * N x)) β := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id β).neg.mul_const (E x - μ * N x))
  have hexp :
      HasDerivAt (fun t : ℝ => Real.exp (-t * (E x - μ * N x)))
        (Real.exp (-β * (E x - μ * N x)) * (-(E x - μ * N x))) β := by
    exact (Real.hasDerivAt_exp (-β * (E x - μ * N x))).comp β hlin
  have hterm :
      HasDerivAt
        (fun t : ℝ => Real.exp (-t * (E x - μ * N x)) * (-(E x - μ * N x)))
        ((Real.exp (-β * (E x - μ * N x)) * (-(E x - μ * N x))) *
          (-(E x - μ * N x))) β := by
    simpa [mul_assoc] using hexp.mul_const (-(E x - μ * N x))
  simpa [mul_assoc, mul_left_comm, mul_comm] using hterm

theorem deriv_grandMassieuPotential_beta_eq_ratio
    [Nonempty α]
    (E N : α → ℝ) (μ : ℝ) :
    deriv (fun t => grandMassieuPotential E N t μ) =
      fun t =>
        (∑ x, Real.exp (-t * (E x - μ * N x)) * (-(E x - μ * N x))) /
          grandCanonicalPartition E N t μ := by
  funext t
  have hXi : grandCanonicalPartition E N t μ ≠ 0 :=
    grandCanonicalPartition_ne_zero E N t μ
  have hlog :
      HasDerivAt (fun s => grandMassieuPotential E N s μ)
        ((∑ x, Real.exp (-t * (E x - μ * N x)) * (-(E x - μ * N x))) /
          grandCanonicalPartition E N t μ) t := by
    simpa [grandMassieuPotential] using
      (hasDerivAt_grandCanonicalPartition_beta E N t μ).log hXi
  exact hlog.deriv

theorem d2_grandMassieuPotential_beta_eq_varianceHamiltonian
    [Nonempty α]
    (E N : α → ℝ) (β μ : ℝ) :
    deriv (fun t => deriv (fun s => grandMassieuPotential E N s μ) t) β =
      grandVariance E N β μ (grandHamiltonian E N μ) := by
  let Z : ℝ → ℝ := fun t => grandCanonicalPartition E N t μ
  let M1 : ℝ → ℝ := fun t =>
    ∑ x, Real.exp (-t * (E x - μ * N x)) * (-(E x - μ * N x))
  let M2 : ℝ → ℝ := fun t =>
    ∑ x, Real.exp (-t * (E x - μ * N x)) * (-(E x - μ * N x)) *
      (-(E x - μ * N x))
  have hderiv :
      deriv (fun t => grandMassieuPotential E N t μ) = fun t => M1 t / Z t := by
    simpa [M1, Z] using deriv_grandMassieuPotential_beta_eq_ratio E N μ
  calc
    deriv (fun t => deriv (fun s => grandMassieuPotential E N s μ) t) β
        = deriv (fun t => M1 t / Z t) β := by
        simp [hderiv]
    _ = (deriv M1 β * Z β - M1 β * deriv Z β) / (Z β) ^ 2 := by
          refine deriv_fun_div ?_ ?_ ?_
          · exact (hasDerivAt_grandCanonicalPartition_betaMoment E N β μ).differentiableAt
          · exact (hasDerivAt_grandCanonicalPartition_beta E N β μ).differentiableAt
          · simpa [Z] using grandCanonicalPartition_ne_zero E N β μ
    _ = ((M2 β) * Z β - M1 β * M1 β) / (Z β) ^ 2 := by
          rw [(hasDerivAt_grandCanonicalPartition_betaMoment E N β μ).deriv]
          rw [(hasDerivAt_grandCanonicalPartition_beta E N β μ).deriv]
    _ = M2 β / Z β - (M1 β / Z β) ^ 2 := by
          have hZβ : Z β ≠ 0 := by
            simpa [Z] using grandCanonicalPartition_ne_zero E N β μ
          field_simp [hZβ]
    _ = grandVariance E N β μ (grandHamiltonian E N μ) := by
          have hM2 :
              M2 β / Z β =
                grandMean E N β μ (fun x => (grandHamiltonian E N μ x) ^ 2) := by
            unfold M2 Z grandMean grandCanonicalPartition grandCanonicalProb grandHamiltonian
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro x hx
            set a : ℝ := Real.exp (-β * (E x - μ * N x))
            set h : ℝ := E x - μ * N x
            set z : ℝ := grandCanonicalPartition E N β μ
            change (a * (-h) * (-h)) / z = (a / z) * h ^ 2
            ring
          have hM1 :
              M1 β / Z β = grandMean E N β μ (fun x => -(grandHamiltonian E N μ x)) := by
            unfold M1 Z grandMean grandCanonicalPartition grandCanonicalProb grandHamiltonian
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro x hx
            set a : ℝ := Real.exp (-β * (E x - μ * N x))
            set h : ℝ := E x - μ * N x
            set z : ℝ := grandCanonicalPartition E N β μ
            change (a * (-h)) / z = (a / z) * (-h)
            ring
          have hM1neg :
              grandMean E N β μ (fun x => -(grandHamiltonian E N μ x)) =
                -grandMean E N β μ (grandHamiltonian E N μ) := by
            unfold grandMean
            calc
              ∑ x, grandCanonicalProb E N β μ (grandCanonicalPartition_ne_zero E N β μ) x *
                (-(grandHamiltonian E N μ x))
                  = ∑ x, -(grandCanonicalProb E N β μ
                      (grandCanonicalPartition_ne_zero E N β μ) x *
                      grandHamiltonian E N μ x) := by
                        refine Finset.sum_congr rfl ?_
                        intro x hx
                        ring
              _ = -∑ x, grandCanonicalProb E N β μ (grandCanonicalPartition_ne_zero E N β μ) x *
                    grandHamiltonian E N μ x := by
                      rw [Finset.sum_neg_distrib]
          unfold grandVariance
          rw [hM2, hM1, hM1neg]
          ring

lemma hasDerivAt_grandCanonicalPartition_muMoment
    (E N : α → ℝ) (β μ : ℝ) :
    HasDerivAt
      (fun t => ∑ x, Real.exp (-β * (E x - t * N x)) * (β * N x))
      (∑ x, Real.exp (-β * (E x - μ * N x)) * (β * N x) ^ 2) μ := by
  classical
  refine HasDerivAt.fun_sum ?_
  intro x hx
  have hlin :
      HasDerivAt (fun t : ℝ => -β * (E x - t * N x))
        (β * N x) μ := by
    have hEq :
        (fun t : ℝ => -β * (E x - t * N x)) =
          (fun t : ℝ => (β * N x) * t + (-β * E x)) := by
      funext t
      ring
    rw [hEq]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id μ).const_mul (β * N x)).add_const (-β * E x))
  have hexp :
      HasDerivAt (fun t : ℝ => Real.exp (-β * (E x - t * N x)))
        (Real.exp (-β * (E x - μ * N x)) * (β * N x)) μ := by
    exact (Real.hasDerivAt_exp (-β * (E x - μ * N x))).comp μ hlin
  have hterm :
      HasDerivAt
        (fun t : ℝ => Real.exp (-β * (E x - t * N x)) * (β * N x))
        ((Real.exp (-β * (E x - μ * N x)) * (β * N x)) * (β * N x)) μ := by
    simpa [mul_assoc] using hexp.mul_const (β * N x)
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hterm

theorem deriv_grandMassieuPotential_mu_eq_ratio
    [Nonempty α]
    (E N : α → ℝ) (β : ℝ) :
    deriv (fun t => grandMassieuPotential E N β t) =
      fun t =>
        (∑ x, Real.exp (-β * (E x - t * N x)) * (β * N x)) /
          grandCanonicalPartition E N β t := by
  funext t
  have hXi : grandCanonicalPartition E N β t ≠ 0 :=
    grandCanonicalPartition_ne_zero E N β t
  have hlog :
      HasDerivAt (fun s => grandMassieuPotential E N β s)
        ((∑ x, Real.exp (-β * (E x - t * N x)) * (β * N x)) /
          grandCanonicalPartition E N β t) t := by
    simpa [grandMassieuPotential] using
      (hasDerivAt_grandCanonicalPartition_mu E N β t).log hXi
  exact hlog.deriv

theorem d2_grandMassieuPotential_mu_eq_varianceBetaN
    [Nonempty α]
    (E N : α → ℝ) (β μ : ℝ) :
  deriv (fun t => deriv (fun s => grandMassieuPotential E N β s) t) μ =
      grandVariance E N β μ (fun x => β * N x) := by
  let Z : ℝ → ℝ := fun t => grandCanonicalPartition E N β t
  let M1 : ℝ → ℝ := fun t =>
    ∑ x, Real.exp (-β * (E x - t * N x)) * (β * N x)
  let M2 : ℝ → ℝ := fun t =>
    ∑ x, Real.exp (-β * (E x - t * N x)) * (β * N x) ^ 2
  have hderiv :
      deriv (fun t => grandMassieuPotential E N β t) = fun t => M1 t / Z t := by
    simpa [M1, Z] using deriv_grandMassieuPotential_mu_eq_ratio E N β
  calc
    deriv (fun t => deriv (fun s => grandMassieuPotential E N β s) t) μ
        = deriv (fun t => M1 t / Z t) μ := by
        simp [hderiv]
    _ = (deriv M1 μ * Z μ - M1 μ * deriv Z μ) / (Z μ) ^ 2 := by
          refine deriv_fun_div ?_ ?_ ?_
          · exact (hasDerivAt_grandCanonicalPartition_muMoment E N β μ).differentiableAt
          · exact (hasDerivAt_grandCanonicalPartition_mu E N β μ).differentiableAt
          · exact grandCanonicalPartition_ne_zero E N β μ
    _ = ((M2 μ) * Z μ - M1 μ * M1 μ) / (Z μ) ^ 2 := by
          rw [(hasDerivAt_grandCanonicalPartition_muMoment E N β μ).deriv]
          rw [(hasDerivAt_grandCanonicalPartition_mu E N β μ).deriv]
    _ = M2 μ / Z μ - (M1 μ / Z μ) ^ 2 := by
          have hZμ : Z μ ≠ 0 := grandCanonicalPartition_ne_zero E N β μ
          field_simp [hZμ]
    _ = grandVariance E N β μ (fun x => β * N x) := by
          have hM2 :
              M2 μ / Z μ =
                grandMean E N β μ (fun x => (β * N x) ^ 2) := by
            unfold M2 Z grandMean grandCanonicalPartition grandCanonicalProb
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro x hx
            set a : ℝ := Real.exp (-β * (E x - μ * N x))
            set b : ℝ := β * N x
            set z : ℝ := grandCanonicalPartition E N β μ
            change (a * b ^ 2) / z = (a / z) * b ^ 2
            ring
          have hM1 :
              M1 μ / Z μ = grandMean E N β μ (fun x => β * N x) := by
            unfold M1 Z grandMean grandCanonicalPartition grandCanonicalProb
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro x hx
            set a : ℝ := Real.exp (-β * (E x - μ * N x))
            set b : ℝ := β * N x
            set z : ℝ := grandCanonicalPartition E N β μ
            change (a * b) / z = (a / z) * b
            ring
          simp [grandVariance, hM2, hM1]

theorem d2_grandMassieuPotential_mu_eq_beta_sq_varianceN
    [Nonempty α]
    (E N : α → ℝ) (β μ : ℝ) :
    deriv (fun t => deriv (fun s => grandMassieuPotential E N β s) t) μ =
      β ^ 2 * grandVariance E N β μ N := by
  have hvarβN :
      deriv (fun t => deriv (fun s => grandMassieuPotential E N β s) t) μ =
        grandVariance E N β μ (fun x => β * N x) :=
    d2_grandMassieuPotential_mu_eq_varianceBetaN E N β μ
  rw [hvarβN]
  unfold grandVariance grandMean
  let p : α → ℝ := fun x =>
    grandCanonicalProb E N β μ (grandCanonicalPartition_ne_zero E N β μ) x
  have hsq :
      ∑ x, p x * (β * N x) ^ 2 = β ^ 2 * ∑ x, p x * (N x) ^ 2 := by
    calc
      ∑ x, p x * (β * N x) ^ 2 = ∑ x, β ^ 2 * (p x * (N x) ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        ring
      _ = β ^ 2 * ∑ x, p x * (N x) ^ 2 := by
        rw [(Finset.mul_sum (Finset.univ : Finset α)
            (fun x => p x * (N x) ^ 2) (β ^ 2)).symm]
  have hlin :
      (∑ x, p x * (β * N x)) ^ 2 = β ^ 2 * (∑ x, p x * N x) ^ 2 := by
    have hsum :
        ∑ x, p x * (β * N x) = β * ∑ x, p x * N x := by
      calc
        ∑ x, p x * (β * N x) = ∑ x, β * (p x * N x) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          ring
        _ = β * ∑ x, p x * N x := by
          rw [(Finset.mul_sum (Finset.univ : Finset α) (fun x => p x * N x) β).symm]
    rw [hsum]
    ring
  rw [hsq, hlin]
  ring

  lemma hasDerivAt_grandCanonicalPartition_betaNumerator_mu
    (E N : α → ℝ) (β μ : ℝ) :
    HasDerivAt
      (fun t => ∑ x, Real.exp (-β * (E x - t * N x)) * (-(E x - t * N x)))
      (∑ x, (Real.exp (-β * (E x - μ * N x)) * (β * N x) * (μ * N x - E x) +
        Real.exp (-β * (E x - μ * N x)) * N x)) μ := by
  classical
  refine HasDerivAt.fun_sum ?_
  intro x hx
  have hlinExp :
      HasDerivAt (fun t : ℝ => -β * (E x - t * N x))
        (β * N x) μ := by
    have hEq :
        (fun t : ℝ => -β * (E x - t * N x)) =
          (fun t : ℝ => (β * N x) * t + (-β * E x)) := by
      funext t
      ring
    rw [hEq]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id μ).const_mul (β * N x)).add_const (-β * E x))
  have hexp :
      HasDerivAt (fun t : ℝ => Real.exp (-β * (E x - t * N x)))
        (Real.exp (-β * (E x - μ * N x)) * (β * N x)) μ := by
    exact (Real.hasDerivAt_exp (-β * (E x - μ * N x))).comp μ hlinExp
  have hlinHam :
      HasDerivAt (fun t : ℝ => -(E x - t * N x)) (N x) μ := by
    have hEq :
        (fun t : ℝ => -(E x - t * N x)) =
          (fun t : ℝ => (N x) * t + (-E x)) := by
      funext t
      ring
    rw [hEq]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id μ).const_mul (N x)).add_const (-E x))
  have hmul :
      HasDerivAt
        (fun t : ℝ => Real.exp (-β * (E x - t * N x)) * (-(E x - t * N x)))
        ((Real.exp (-β * (E x - μ * N x)) * (β * N x)) * (-(E x - μ * N x)) +
          Real.exp (-β * (E x - μ * N x)) * N x) μ := by
    exact hexp.mul hlinHam
  simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using hmul

lemma grandMean_neg
    [Nonempty α]
    (E N : α → ℝ) (β μ : ℝ) (f : α → ℝ) :
    grandMean E N β μ (fun x => -f x) = -grandMean E N β μ f := by
  unfold grandMean
  calc
    ∑ x, grandCanonicalProb E N β μ (grandCanonicalPartition_ne_zero E N β μ) x * (-f x)
        = ∑ x, -(grandCanonicalProb E N β μ (grandCanonicalPartition_ne_zero E N β μ) x * f x) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring
    _ = -∑ x, grandCanonicalProb E N β μ (grandCanonicalPartition_ne_zero E N β μ) x * f x := by
          rw [Finset.sum_neg_distrib]

theorem d2_grandMassieuPotential_beta_mu_eq_meanN_sub_cov
    [Nonempty α]
    (E N : α → ℝ) (β μ : ℝ) :
    deriv (fun t => deriv (fun s => grandMassieuPotential E N s t) β) μ =
      grandMean E N β μ N -
        grandCovariance E N β μ (grandHamiltonian E N μ) (fun x => β * N x) := by
  let Z : ℝ → ℝ := fun t => grandCanonicalPartition E N β t
  let M1 : ℝ → ℝ := fun t =>
    ∑ x, Real.exp (-β * (E x - t * N x)) * (-(E x - t * N x))
  let M1' : ℝ → ℝ := fun t =>
    ∑ x, (Real.exp (-β * (E x - t * N x)) * (β * N x) * (t * N x - E x) +
      Real.exp (-β * (E x - t * N x)) * N x)
  let MZ : ℝ → ℝ := fun t =>
    ∑ x, Real.exp (-β * (E x - t * N x)) * (β * N x)
  have hderiv :
      (fun t => deriv (fun s => grandMassieuPotential E N s t) β) =
        fun t => M1 t / Z t := by
    funext t
    have hslice : deriv (fun s => grandMassieuPotential E N s t) =
        fun s =>
          (∑ x, Real.exp (-s * (E x - t * N x)) * (-(E x - t * N x))) /
            grandCanonicalPartition E N s t := by
      exact deriv_grandMassieuPotential_beta_eq_ratio E N t
    simpa [M1, Z] using congrArg (fun f => f β) hslice
  calc
    deriv (fun t => deriv (fun s => grandMassieuPotential E N s t) β) μ
        = deriv (fun t => M1 t / Z t) μ := by
            simp [hderiv]
    _ = (deriv M1 μ * Z μ - M1 μ * deriv Z μ) / (Z μ) ^ 2 := by
          refine deriv_fun_div ?_ ?_ ?_
          · exact (hasDerivAt_grandCanonicalPartition_betaNumerator_mu E N β μ).differentiableAt
          · simpa [Z] using (hasDerivAt_grandCanonicalPartition_mu E N β μ).differentiableAt
          · simpa [Z] using grandCanonicalPartition_ne_zero E N β μ
    _ = ((M1' μ) * Z μ - M1 μ * MZ μ) / (Z μ) ^ 2 := by
          rw [(hasDerivAt_grandCanonicalPartition_betaNumerator_mu E N β μ).deriv]
          rw [show deriv Z μ = MZ μ by
            simpa [Z, MZ] using (hasDerivAt_grandCanonicalPartition_mu E N β μ).deriv]
    _ = M1' μ / Z μ - (M1 μ / Z μ) * (MZ μ / Z μ) := by
          have hZμ : Z μ ≠ 0 := by
            simpa [Z] using grandCanonicalPartition_ne_zero E N β μ
          field_simp [hZμ]
    _ = grandMean E N β μ N
          - grandCovariance E N β μ (grandHamiltonian E N μ) (fun x => β * N x) := by
          have hM1' :
              M1' μ / Z μ =
                grandMean E N β μ
                  (fun x => N x + (β * N x) * (-(grandHamiltonian E N μ x))) := by
            unfold M1' Z grandMean grandCanonicalPartition grandCanonicalProb grandHamiltonian
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro x hx
            set a : ℝ := Real.exp (-β * (E x - μ * N x))
            set z : ℝ := grandCanonicalPartition E N β μ
            change (a * (β * N x) * (μ * N x - E x) + a * N x) / z =
              (a / z) * (N x + (β * N x) * (-(E x - μ * N x)))
            ring
          have hM1 :
              M1 μ / Z μ =
                grandMean E N β μ (fun x => -(grandHamiltonian E N μ x)) := by
            unfold M1 Z grandMean grandCanonicalPartition grandCanonicalProb grandHamiltonian
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro x hx
            set a : ℝ := Real.exp (-β * (E x - μ * N x))
            set h : ℝ := E x - μ * N x
            set z : ℝ := grandCanonicalPartition E N β μ
            change (a * (-h)) / z = (a / z) * (-h)
            ring
          have hMZ :
              MZ μ / Z μ = grandMean E N β μ (fun x => β * N x) := by
            unfold MZ Z grandMean grandCanonicalPartition grandCanonicalProb
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro x hx
            set a : ℝ := Real.exp (-β * (E x - μ * N x))
            set b : ℝ := β * N x
            set z : ℝ := grandCanonicalPartition E N β μ
            change (a * b) / z = (a / z) * b
            ring
          have hsplit :
              grandMean E N β μ
                (fun x => N x + (β * N x) * (-(grandHamiltonian E N μ x)))
                = grandMean E N β μ N
                  - grandMean E N β μ
                    (fun x => grandHamiltonian E N μ x * (β * N x)) := by
            unfold grandMean
            calc
              ∑ x, grandCanonicalProb E N β μ (grandCanonicalPartition_ne_zero E N β μ) x *
                (N x + (β * N x) * (-(grandHamiltonian E N μ x)))
                  = ∑ x, (grandCanonicalProb E N β μ
                      (grandCanonicalPartition_ne_zero E N β μ) x * N x -
                      grandCanonicalProb E N β μ
                        (grandCanonicalPartition_ne_zero E N β μ) x *
                        (grandHamiltonian E N μ x * (β * N x))) := by
                          refine Finset.sum_congr rfl ?_
                          intro x hx
                          ring
              _ = (∑ x, grandCanonicalProb E N β μ
                    (grandCanonicalPartition_ne_zero E N β μ) x * N x) -
                    (∑ x, grandCanonicalProb E N β μ
                      (grandCanonicalPartition_ne_zero E N β μ) x *
                      (grandHamiltonian E N μ x * (β * N x))) := by
                        rw [Finset.sum_sub_distrib]
          have hnegH :
              grandMean E N β μ (fun x => -(grandHamiltonian E N μ x)) =
                -grandMean E N β μ (grandHamiltonian E N μ) := by
            simpa using grandMean_neg E N β μ (grandHamiltonian E N μ)
          unfold grandCovariance
          rw [hM1', hM1, hMZ, hsplit, hnegH]
          ring

theorem d2_grandMassieuPotential_beta_mu_eq_neg_covariance
    [Nonempty α]
    (E N : α → ℝ) (β μ : ℝ)
    (hN : grandMean E N β μ N = 0) :
    deriv (fun t => deriv (fun s => grandMassieuPotential E N s t) β) μ =
      -grandCovariance E N β μ (grandHamiltonian E N μ) (fun x => β * N x) := by
  rw [d2_grandMassieuPotential_beta_mu_eq_meanN_sub_cov E N β μ, hN]
  ring

theorem grandMassieu_hessian_identities
    [Nonempty α]
    (E N : α → ℝ) (β μ : ℝ) :
    (deriv (fun t => deriv (fun s => grandMassieuPotential E N s μ) t) β =
      grandVariance E N β μ (grandHamiltonian E N μ)) ∧
    (deriv (fun t => deriv (fun s => grandMassieuPotential E N β s) t) μ =
      grandVariance E N β μ (fun x => β * N x)) := by
  refine ⟨d2_grandMassieuPotential_beta_eq_varianceHamiltonian E N β μ,
    d2_grandMassieuPotential_mu_eq_varianceBetaN E N β μ⟩

theorem grandMassieu_hessian_fisher_identities
    [Nonempty α]
    (E N : α → ℝ) (β μ : ℝ) :
    (deriv (fun t => deriv (fun s => grandMassieuPotential E N s μ) t) β =
      grandVariance E N β μ (grandHamiltonian E N μ)) ∧
    (deriv (fun t => deriv (fun s => grandMassieuPotential E N s t) β) μ =
      grandMean E N β μ N -
        grandCovariance E N β μ (grandHamiltonian E N μ) (fun x => β * N x)) ∧
    (deriv (fun t => deriv (fun s => grandMassieuPotential E N β s) t) μ =
      β ^ 2 * grandVariance E N β μ N) := by
  refine ⟨d2_grandMassieuPotential_beta_eq_varianceHamiltonian E N β μ,
    d2_grandMassieuPotential_beta_mu_eq_meanN_sub_cov E N β μ,
    d2_grandMassieuPotential_mu_eq_beta_sq_varianceN E N β μ⟩

lemma differentiable_grandMassieuPotential_beta
    [Nonempty α]
    (E N : α → ℝ) (μ : ℝ) :
    Differentiable ℝ (fun t => grandMassieuPotential E N t μ) := by
  intro t
  have hlog :
      HasDerivAt (fun s => grandMassieuPotential E N s μ)
        ((∑ x, Real.exp (-t * (E x - μ * N x)) * (-(E x - μ * N x))) /
          grandCanonicalPartition E N t μ) t := by
    simpa [grandMassieuPotential] using
      (hasDerivAt_grandCanonicalPartition_beta E N t μ).log
        (grandCanonicalPartition_ne_zero E N t μ)
  exact hlog.differentiableAt

lemma differentiable_deriv_grandMassieuPotential_beta
    [Nonempty α]
    (E N : α → ℝ) (μ : ℝ) :
    Differentiable ℝ (deriv (fun t => grandMassieuPotential E N t μ)) := by
  have hderiv :
      deriv (fun t => grandMassieuPotential E N t μ) =
        fun t =>
          (∑ x, Real.exp (-t * (E x - μ * N x)) * (-(E x - μ * N x))) /
            grandCanonicalPartition E N t μ := by
    exact deriv_grandMassieuPotential_beta_eq_ratio E N μ
  intro t
  rw [hderiv]
  exact ((hasDerivAt_grandCanonicalPartition_betaMoment E N t μ).differentiableAt).div
    ((hasDerivAt_grandCanonicalPartition_beta E N t μ).differentiableAt)
    (grandCanonicalPartition_ne_zero E N t μ)

theorem grandMassieuPotential_convex_in_beta
    [Nonempty α]
    (E N : α → ℝ) (μ : ℝ) :
    ConvexOn ℝ Set.univ (fun t => grandMassieuPotential E N t μ) := by
  refine convexOn_univ_of_deriv2_nonneg
    (differentiable_grandMassieuPotential_beta E N μ)
    (differentiable_deriv_grandMassieuPotential_beta E N μ)
    ?_
  intro t
  have hder2 :
      (deriv^[2]) (fun s => grandMassieuPotential E N s μ) t =
        grandVariance E N t μ (grandHamiltonian E N μ) := by
    simpa [Function.iterate_succ_apply'] using
      d2_grandMassieuPotential_beta_eq_varianceHamiltonian E N t μ
  have hnonneg :
      0 ≤ grandVariance E N t μ (grandHamiltonian E N μ) := by
    exact grandVariance_nonneg E N t μ (grandHamiltonian E N μ)
  simpa [hder2] using hnonneg

theorem grandMassieuPotential_convex_in_mu
    [Nonempty α]
    (E N : α → ℝ) (β : ℝ) :
    ConvexOn ℝ Set.univ (fun t => grandMassieuPotential E N β t) := by
  refine convexOn_univ_of_deriv2_nonneg
    (by
      intro t
      have hlog :
          HasDerivAt (fun s => grandMassieuPotential E N β s)
            ((∑ x, Real.exp (-β * (E x - t * N x)) * (β * N x)) /
              grandCanonicalPartition E N β t) t := by
        simpa [grandMassieuPotential] using
          (hasDerivAt_grandCanonicalPartition_mu E N β t).log
            (grandCanonicalPartition_ne_zero E N β t)
      exact hlog.differentiableAt)
    (by
      have hderiv :
          deriv (fun t => grandMassieuPotential E N β t) =
            fun t =>
              (∑ x, Real.exp (-β * (E x - t * N x)) * (β * N x)) /
                grandCanonicalPartition E N β t := by
        exact deriv_grandMassieuPotential_mu_eq_ratio E N β
      intro t
      rw [hderiv]
      exact ((hasDerivAt_grandCanonicalPartition_muMoment E N β t).differentiableAt).div
        ((hasDerivAt_grandCanonicalPartition_mu E N β t).differentiableAt)
        (grandCanonicalPartition_ne_zero E N β t))
    ?_
  intro t
  have hder2 :
      (deriv^[2]) (fun s => grandMassieuPotential E N β s) t =
        grandVariance E N β t (fun x => β * N x) := by
    simpa [Function.iterate_succ_apply'] using
      d2_grandMassieuPotential_mu_eq_varianceBetaN E N β t
  have hnonneg :
      0 ≤ grandVariance E N β t (fun x => β * N x) := by
    exact grandVariance_nonneg E N β t (fun x => β * N x)
  simpa [hder2] using hnonneg

/-- Two-parameter coordinate Bregman divergence (`y` is expansion point). -/
noncomputable def bregmanDiv2
    (F : ℝ → ℝ → ℝ) (x y : ℝ × ℝ) : ℝ :=
  F x.1 x.2 - F y.1 y.2
    - deriv (fun t => F t y.2) y.1 * (x.1 - y.1)
    - deriv (fun t => F y.1 t) y.2 * (x.2 - y.2)

/-- Natural two-parameter partition `Z(θ,ν)=∑ exp(θE+νN)`. -/
noncomputable def grandNaturalPartition
    (E N : α → ℝ) (θ ν : ℝ) : ℝ :=
  ∑ x, Real.exp (θ * E x + ν * N x)

/-- Natural Massieu potential `Ψ(θ,ν)=log Z(θ,ν)`. -/
noncomputable def grandNaturalPotential
    (E N : α → ℝ) (θ ν : ℝ) : ℝ :=
  Real.log (grandNaturalPartition E N θ ν)

/-- Natural exponential-family probability kernel. -/
noncomputable def grandNaturalProb
    [Nonempty α]
    (E N : α → ℝ) (θ ν : ℝ) (x : α) : ℝ :=
  Real.exp (θ * E x + ν * N x) / grandNaturalPartition E N θ ν

/-- KL on natural parameters. -/
noncomputable def grandNaturalKL
    [Nonempty α]
    (E N : α → ℝ) (θ1 ν1 θ2 ν2 : ℝ) : ℝ :=
  ∑ x, grandNaturalProb E N θ1 ν1 x *
    Real.log (grandNaturalProb E N θ1 ν1 x / grandNaturalProb E N θ2 ν2 x)

lemma grandNaturalPartition_pos
    [Nonempty α]
    (E N : α → ℝ) (θ ν : ℝ) :
    0 < grandNaturalPartition E N θ ν := by
  classical
  unfold grandNaturalPartition
  have hpos :
      ∀ x ∈ (Finset.univ : Finset α), 0 < Real.exp (θ * E x + ν * N x) := by
    intro x hx
    exact Real.exp_pos _
  have hsum :
      0 < ∑ x ∈ (Finset.univ : Finset α), Real.exp (θ * E x + ν * N x) := by
    exact Finset.sum_pos hpos Finset.univ_nonempty
  simpa using hsum

theorem grandNaturalKL_eq_bregman
    [Nonempty α]
    (E N : α → ℝ) (θ1 ν1 θ2 ν2 : ℝ) :
    grandNaturalKL E N θ1 ν1 θ2 ν2 =
      bregmanDiv2 (grandNaturalPotential E N) (θ2, ν2) (θ1, ν1) := by
  have hZ1 : grandNaturalPartition E N θ1 ν1 ≠ 0 := ne_of_gt (grandNaturalPartition_pos E N θ1 ν1)
  have hZ2 : grandNaturalPartition E N θ2 ν2 ≠ 0 := ne_of_gt (grandNaturalPartition_pos E N θ2 ν2)
  have hderivθ :
      deriv (fun t => grandNaturalPotential E N t ν1) θ1 =
        ∑ x, grandNaturalProb E N θ1 ν1 x * E x := by
    have hpart :
        HasDerivAt (fun t => grandNaturalPartition E N t ν1)
          (∑ x, Real.exp (θ1 * E x + ν1 * N x) * E x) θ1 := by
      classical
      unfold grandNaturalPartition
      refine HasDerivAt.fun_sum ?_
      intro x hx
      have hlin : HasDerivAt (fun t : ℝ => t * E x + ν1 * N x) (E x) θ1 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          ((hasDerivAt_id θ1).mul_const (E x)).add_const (ν1 * N x)
      exact (Real.hasDerivAt_exp (θ1 * E x + ν1 * N x)).comp θ1 hlin
    have hlog :
        HasDerivAt (fun t => grandNaturalPotential E N t ν1)
          ((∑ x, Real.exp (θ1 * E x + ν1 * N x) * E x) /
            grandNaturalPartition E N θ1 ν1) θ1 := by
      simpa [grandNaturalPotential] using hpart.log hZ1
    calc
      deriv (fun t => grandNaturalPotential E N t ν1) θ1
          = ((∑ x, Real.exp (θ1 * E x + ν1 * N x) * E x) /
              grandNaturalPartition E N θ1 ν1) := hlog.deriv
      _ = ∑ x, grandNaturalProb E N θ1 ν1 x * E x := by
            unfold grandNaturalProb
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring
  have hderivν :
      deriv (fun t => grandNaturalPotential E N θ1 t) ν1 =
        ∑ x, grandNaturalProb E N θ1 ν1 x * N x := by
    have hpart :
        HasDerivAt (fun t => grandNaturalPartition E N θ1 t)
          (∑ x, Real.exp (θ1 * E x + ν1 * N x) * N x) ν1 := by
      classical
      unfold grandNaturalPartition
      refine HasDerivAt.fun_sum ?_
      intro x hx
      have hlin : HasDerivAt (fun t : ℝ => θ1 * E x + t * N x) (N x) ν1 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (hasDerivAt_id ν1).mul_const (N x) |>.const_add (θ1 * E x)
      exact (Real.hasDerivAt_exp (θ1 * E x + ν1 * N x)).comp ν1 hlin
    have hlog :
        HasDerivAt (fun t => grandNaturalPotential E N θ1 t)
          ((∑ x, Real.exp (θ1 * E x + ν1 * N x) * N x) /
            grandNaturalPartition E N θ1 ν1) ν1 := by
      simpa [grandNaturalPotential] using hpart.log hZ1
    calc
      deriv (fun t => grandNaturalPotential E N θ1 t) ν1
          = ((∑ x, Real.exp (θ1 * E x + ν1 * N x) * N x) /
              grandNaturalPartition E N θ1 ν1) := hlog.deriv
      _ = ∑ x, grandNaturalProb E N θ1 ν1 x * N x := by
            unfold grandNaturalProb
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring
  have hlogratio :
      ∀ x,
        Real.log (grandNaturalProb E N θ1 ν1 x / grandNaturalProb E N θ2 ν2 x) =
          (θ1 - θ2) * E x + (ν1 - ν2) * N x
            - grandNaturalPotential E N θ1 ν1 + grandNaturalPotential E N θ2 ν2 := by
    intro x
    have hp1 : 0 < grandNaturalProb E N θ1 ν1 x := by
      unfold grandNaturalProb
      exact div_pos (Real.exp_pos _) (grandNaturalPartition_pos E N θ1 ν1)
    have hp2 : 0 < grandNaturalProb E N θ2 ν2 x := by
      unfold grandNaturalProb
      exact div_pos (Real.exp_pos _) (grandNaturalPartition_pos E N θ2 ν2)
    calc
      Real.log (grandNaturalProb E N θ1 ν1 x / grandNaturalProb E N θ2 ν2 x)
          = Real.log (grandNaturalProb E N θ1 ν1 x) -
              Real.log (grandNaturalProb E N θ2 ν2 x) := by
                rw [Real.log_div (ne_of_gt hp1) (ne_of_gt hp2)]
      _ = ((θ1 * E x + ν1 * N x) - grandNaturalPotential E N θ1 ν1) -
            ((θ2 * E x + ν2 * N x) - grandNaturalPotential E N θ2 ν2) := by
            unfold grandNaturalProb grandNaturalPotential
            rw [Real.log_div (by positivity) hZ1]
            rw [Real.log_div (by positivity) hZ2]
            simp
      _ = (θ1 - θ2) * E x + (ν1 - ν2) * N x
            - grandNaturalPotential E N θ1 ν1 + grandNaturalPotential E N θ2 ν2 := by
            ring
  have hsum1 :
      ∑ x, grandNaturalProb E N θ1 ν1 x = 1 := by
    unfold grandNaturalProb
    calc
      ∑ x, Real.exp (θ1 * E x + ν1 * N x) / grandNaturalPartition E N θ1 ν1
          = (∑ x, Real.exp (θ1 * E x + ν1 * N x)) / grandNaturalPartition E N θ1 ν1 := by
              rw [Finset.sum_div]
      _ = grandNaturalPartition E N θ1 ν1 / grandNaturalPartition E N θ1 ν1 := by
            simp [grandNaturalPartition]
      _ = 1 := by exact div_self hZ1
  unfold grandNaturalKL bregmanDiv2
  calc
    ∑ x, grandNaturalProb E N θ1 ν1 x *
      Real.log (grandNaturalProb E N θ1 ν1 x / grandNaturalProb E N θ2 ν2 x)
        = ∑ x, grandNaturalProb E N θ1 ν1 x *
            ((θ1 - θ2) * E x + (ν1 - ν2) * N x
              - grandNaturalPotential E N θ1 ν1 + grandNaturalPotential E N θ2 ν2) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              rw [hlogratio x]
    _ = ∑ x, ((θ1 - θ2) * (grandNaturalProb E N θ1 ν1 x * E x) +
          (ν1 - ν2) * (grandNaturalProb E N θ1 ν1 x * N x) +
          grandNaturalProb E N θ1 ν1 x *
            (-grandNaturalPotential E N θ1 ν1 + grandNaturalPotential E N θ2 ν2)) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          ring
    _ = (∑ x, (θ1 - θ2) * (grandNaturalProb E N θ1 ν1 x * E x)) +
          (∑ x, (ν1 - ν2) * (grandNaturalProb E N θ1 ν1 x * N x)) +
          (∑ x, grandNaturalProb E N θ1 ν1 x *
            (-grandNaturalPotential E N θ1 ν1 + grandNaturalPotential E N θ2 ν2)) := by
          rw [Finset.sum_add_distrib]
          rw [Finset.sum_add_distrib]
    _ = (θ1 - θ2) * (∑ x, grandNaturalProb E N θ1 ν1 x * E x) +
          (ν1 - ν2) * (∑ x, grandNaturalProb E N θ1 ν1 x * N x) +
          (∑ x, grandNaturalProb E N θ1 ν1 x) *
            (-grandNaturalPotential E N θ1 ν1 + grandNaturalPotential E N θ2 ν2) := by
          rw [(Finset.mul_sum (Finset.univ : Finset α)
            (fun x => grandNaturalProb E N θ1 ν1 x * E x) (θ1 - θ2)).symm]
          rw [(Finset.mul_sum (Finset.univ : Finset α)
            (fun x => grandNaturalProb E N θ1 ν1 x * N x) (ν1 - ν2)).symm]
          rw [Finset.sum_mul]
    _ = (θ1 - θ2) * (∑ x, grandNaturalProb E N θ1 ν1 x * E x) +
          (ν1 - ν2) * (∑ x, grandNaturalProb E N θ1 ν1 x * N x) +
          1 * (-grandNaturalPotential E N θ1 ν1 + grandNaturalPotential E N θ2 ν2) := by
          simp [hsum1]
    _ = grandNaturalPotential E N θ2 ν2 - grandNaturalPotential E N θ1 ν1
          - deriv (fun t => grandNaturalPotential E N t ν1) θ1 * (θ2 - θ1)
          - deriv (fun t => grandNaturalPotential E N θ1 t) ν1 * (ν2 - ν1) := by
          rw [hderivθ, hderivν]
          ring

/-- `KL = Bregman` orientation in `(β,μ)` via natural coordinates
`(θ,ν)=(-β,βμ)`. -/
theorem grandCanonicalKL_eq_bregman_via_natural
    [Nonempty α]
    (E N : α → ℝ) (β1 μ1 β2 μ2 : ℝ) :
    grandNaturalKL E N (-β1) (β1 * μ1) (-β2) (β2 * μ2) =
      bregmanDiv2 (grandNaturalPotential E N)
        ((-β2), (β2 * μ2)) ((-β1), (β1 * μ1)) := by
  simpa using grandNaturalKL_eq_bregman E N (-β1) (β1 * μ1) (-β2) (β2 * μ2)

end GrandCanonical

section JordanConeCore

/-- Minimal Euclidean Jordan algebra package used as a geometric bridge layer.
This is intentionally lightweight: product axioms + determinant/trace observables. -/
structure EuclideanJordanAlgebra where
  V : Type*
  instAddCommGroup : AddCommGroup V
  instModule : Module ℝ V
  instNormedAddCommGroup : NormedAddCommGroup V
  instNormedSpace : NormedSpace ℝ V
  instInner : InnerProductSpace ℝ V
  prod : V → V → V
  unit : V
  det : V → ℝ
  tr : V → ℝ
  comm : ∀ x y, prod x y = prod y x
  jordan_identity : ∀ x y, prod (prod x x) (prod x y) = prod x (prod (prod x x) y
)

attribute [instance] EuclideanJordanAlgebra.instAddCommGroup
attribute [instance] EuclideanJordanAlgebra.instModule
attribute [instance] EuclideanJordanAlgebra.instNormedAddCommGroup
attribute [instance] EuclideanJordanAlgebra.instNormedSpace
attribute [instance] EuclideanJordanAlgebra.instInner

/-- Jordan symmetric cone candidate: positivity domain of the Jordan determinant. -/
def symmetricCone (J : EuclideanJordanAlgebra) : Set J.V :=
  {x | 0 < J.det x}

/-- Canonical Jordan potential used in symmetric-cone information geometry. -/
noncomputable def jordanPotential (J : EuclideanJordanAlgebra) (x : J.V) : ℝ :=
  -Real.log (J.det x)

lemma mem_symmetricCone_iff
    (J : EuclideanJordanAlgebra)
    (x : J.V) :
    x ∈ symmetricCone J ↔ 0 < J.det x := Iff.rfl

/-- Optional geometric axioms upgrading the determinant-positive domain to a
full symmetric-cone layer. -/
structure SymmetricConeLayer (J : EuclideanJordanAlgebra) : Prop where
  open_cone : IsOpen (symmetricCone J)
  convex_cone : Convex ℝ (symmetricCone J)
  unit_mem : J.unit ∈ symmetricCone J

/-- Packaged bridge object: Jordan algebra + its cone layer + potential. -/
structure JordanConeGeometry where
  J : EuclideanJordanAlgebra
  cone : SymmetricConeLayer J

noncomputable def JordanConeGeometry.potential (G : JordanConeGeometry) : G.J.V → ℝ :=
  jordanPotential G.J

end JordanConeCore

section SPDLogDetBridge

open Matrix

/-- Symmetric positive-determinant cone model on square real matrices.
This is the lightweight entry point for the SPD/Jordan bridge. -/
def spdCone (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | A.IsSymm ∧ 0 < Matrix.det A}

lemma mem_spdCone_iff
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ spdCone n ↔ A.IsSymm ∧ 0 < Matrix.det A := Iff.rfl

/-- Log-determinant potential on the SPD cone model. -/
noncomputable def spdLogDetPotential
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  -Real.log (Matrix.det A)

/-- Closed-form Bregman expression associated to the log-det potential. -/
noncomputable def spdBregmanLogDetClosedForm
    {n : ℕ}
    (SigmaMat LambdaMat : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace (LambdaMat⁻¹ * SigmaMat)
    - Real.log (Matrix.det (LambdaMat⁻¹ * SigmaMat)) - n

/-- Closed-form zero-mean Gaussian KL in matrix coordinates (packaged). -/
noncomputable def gaussianKL0ClosedForm
    {n : ℕ}
    (SigmaMat LambdaMat : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (1 / 2 : ℝ) * spdBregmanLogDetClosedForm SigmaMat LambdaMat

theorem gaussianKL0ClosedForm_eq_half_bregman
    {n : ℕ}
    (SigmaMat LambdaMat : Matrix (Fin n) (Fin n) ℝ) :
    gaussianKL0ClosedForm SigmaMat LambdaMat
      = (1 / 2 : ℝ) * spdBregmanLogDetClosedForm SigmaMat LambdaMat := by
  simp [gaussianKL0ClosedForm]

/-- Congruence action preserves the SPD cone model when `M` is invertible
(`det M ≠ 0`). -/
theorem spdCone_congr_mem
    {n : ℕ}
    (A M : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ spdCone n)
    (hM : Matrix.det M ≠ 0) :
    (M.transpose * A * M) ∈ spdCone n := by
  rcases hA with ⟨hAsymm, hAdet⟩
  refine ⟨?_, ?_⟩
  · unfold Matrix.IsSymm at *
    calc
      (M.transpose * A * M)ᵀ = M.transpose * Aᵀ * M := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = M.transpose * A * M := by rw [hAsymm]
  · have hdetMt : Matrix.det M.transpose = Matrix.det M := by
      exact Matrix.det_transpose M
    have hdet_congr :
        Matrix.det (M.transpose * A * M)
          = Matrix.det M.transpose * Matrix.det A * Matrix.det M := by
      calc
        Matrix.det (M.transpose * A * M)
            = Matrix.det (M.transpose * A) * Matrix.det M := by
                simp [Matrix.det_mul]
        _ = (Matrix.det M.transpose * Matrix.det A) * Matrix.det M := by
                simp [Matrix.det_mul]
    rw [hdet_congr, hdetMt]
    have hpowpos : 0 < (Matrix.det M) ^ 2 := sq_pos_of_ne_zero hM
    have hprod : 0 < Matrix.det A * (Matrix.det M) ^ 2 :=
      mul_pos hAdet hpowpos
    have hEq : Matrix.det M * Matrix.det A * Matrix.det M
        = Matrix.det A * (Matrix.det M) ^ 2 := by
      ring
    simpa [hEq] using hprod

end SPDLogDetBridge

section SymmetricSpaceArchitecture

/-
Symmetric-space layer (machine-readable, architecture targets)
format: yaml
version: 1
items:
  - id: S1
    name: CartanDecompositionTarget
    depends_on: [M6]
    status: planned
  - id: S2
    name: LeviCivitaConnectionTarget
    depends_on: [S1]
    status: planned
  - id: S3
    name: CurvatureIdentificationTarget
    depends_on: [S2]
    status: planned
  - id: S4
    name: SpinLiftTarget
    depends_on: [S1]
    status: planned
  - id: S5
    name: ProjectiveDynamicsBridgeTarget
    depends_on: [N17, N18, S1]
    status: planned
  - id: S6
    name: LogDetInvariantPotentialTarget
    depends_on: [N6, S2, S3]
    status: planned
-/

/-- Minimal architectural placeholder: a Cartan decomposition package on a carrier `G`. -/
structure CartanDecompositionTarget (G : Type*) where
  k : Set G
  p : Set G
  decompositionWitness : Prop

/-- Minimal architectural placeholder: Levi-Civita layer on a manifold carrier `M`. -/
structure LeviCivitaTarget (M : Type*) where
  nabla : M → M → M
  torsionFreeWitness : Prop
  metricCompatibleWitness : Prop

/-- Minimal architectural placeholder: spin-lift layer over a structure group carrier `G`. -/
structure SpinLiftTarget (G : Type*) where
  liftWitness : Prop

/-- Minimal target proposition for the global symmetric-space layer. -/
def SymmetricSpaceGlobalLayer (G M : Type*) : Prop :=
  ∃ (_cartan : CartanDecompositionTarget G)
    (_lc : LeviCivitaTarget M)
    (_spin : SpinLiftTarget G), True

/-- Compression theorem: the global layer is exactly Cartan + Levi-Civita + spin lift data. -/
theorem symmetricSpaceGlobalLayer_iff
    (G M : Type*) :
    SymmetricSpaceGlobalLayer G M ↔
      ∃ (_cartan : CartanDecompositionTarget G)
        (_lc : LeviCivitaTarget M)
        (_spin : SpinLiftTarget G), True := by
  simp [SymmetricSpaceGlobalLayer]

/-- Assembly lemma: packaging the three targets yields the global layer. -/
theorem mk_symmetricSpaceGlobalLayer
    {G M : Type*}
    (cartan : CartanDecompositionTarget G)
    (lc : LeviCivitaTarget M)
    (spin : SpinLiftTarget G) :
    SymmetricSpaceGlobalLayer G M := by
  simpa [SymmetricSpaceGlobalLayer] using (show ∃ (_cartan : CartanDecompositionTarget G)
    (_lc : LeviCivitaTarget M)
    (_spin : SpinLiftTarget G), True from ⟨cartan, lc, spin, trivial⟩)

/-- Elimination lemma: any global layer instance unpacks into the three core targets. -/
theorem symmetricSpaceGlobalLayer_unpack
    {G M : Type*}
    (h : SymmetricSpaceGlobalLayer G M) :
    ∃ (_cartan : CartanDecompositionTarget G)
      (_lc : LeviCivitaTarget M)
      (_spin : SpinLiftTarget G), True := by
  simpa [SymmetricSpaceGlobalLayer] using h

/-- Target theorem (S1): precise Cartan-data hypotheses assemble a Cartan target package. -/
theorem S1_cartanDecompositionTarget_exists
    {G : Type*}
    (k p : Set G)
    (hDecomposition : Prop) :
    ∃ cartan : CartanDecompositionTarget G,
      cartan.k = k ∧ cartan.p = p ∧ cartan.decompositionWitness = hDecomposition := by
  refine ⟨⟨k, p, hDecomposition⟩, rfl, rfl, rfl⟩

/-- Target theorem (S2): precise connection hypotheses assemble a Levi-Civita target package. -/
theorem S2_leviCivitaTarget_exists
    {M : Type*}
    (nabla : M → M → M)
    (hTorsionFree : Prop)
    (hMetricCompatible : Prop) :
    ∃ lc : LeviCivitaTarget M,
      lc.nabla = nabla ∧
      lc.torsionFreeWitness = hTorsionFree ∧
      lc.metricCompatibleWitness = hMetricCompatible := by
  refine ⟨⟨nabla, hTorsionFree, hMetricCompatible⟩, rfl, rfl, rfl⟩

/-- Target theorem (S4): precise spin-lift witness hypothesis assembles a spin target package. -/
theorem S4_spinLiftTarget_exists
    {G : Type*}
    (hSpinLift : Prop) :
    ∃ spin : SpinLiftTarget G,
      spin.liftWitness = hSpinLift := by
  exact ⟨⟨hSpinLift⟩, rfl⟩

/-- Fourth tightening theorem: explicit bridge assembling `S1 + S2 + S4` into the global layer. -/
theorem assemble_S1_S2_S4_to_globalLayer
    {G M : Type*}
    (k p : Set G)
    (hDecomposition : Prop)
    (nabla : M → M → M)
    (hTorsionFree : Prop)
    (hMetricCompatible : Prop)
    (hSpinLift : Prop) :
    SymmetricSpaceGlobalLayer G M := by
  have hS1 : ∃ cartan : CartanDecompositionTarget G,
      cartan.k = k ∧ cartan.p = p ∧ cartan.decompositionWitness = hDecomposition :=
    S1_cartanDecompositionTarget_exists (G := G) k p hDecomposition
  have hS2 : ∃ lc : LeviCivitaTarget M,
      lc.nabla = nabla ∧
      lc.torsionFreeWitness = hTorsionFree ∧
      lc.metricCompatibleWitness = hMetricCompatible :=
    S2_leviCivitaTarget_exists (M := M) nabla hTorsionFree hMetricCompatible
  have hS4 : ∃ spin : SpinLiftTarget G,
      spin.liftWitness = hSpinLift :=
    S4_spinLiftTarget_exists (G := G) hSpinLift
  rcases hS1 with ⟨cartan, -, -, -⟩
  rcases hS2 with ⟨lc, -, -, -⟩
  rcases hS4 with ⟨spin, -⟩
  exact mk_symmetricSpaceGlobalLayer cartan lc spin

/-- Converse tightening theorem: any global layer yields recoverable `S1/S2/S4` witness triples. -/
theorem recover_S1_S2_S4_from_globalLayer
    {G M : Type*}
    (hGlobal : SymmetricSpaceGlobalLayer G M) :
    ∃ (k p : Set G) (hDecomposition : Prop)
      (nabla : M → M → M)
      (hTorsionFree hMetricCompatible hSpinLift : Prop),
      (∃ cartan : CartanDecompositionTarget G,
        cartan.k = k ∧ cartan.p = p ∧ cartan.decompositionWitness = hDecomposition) ∧
      (∃ lc : LeviCivitaTarget M,
        lc.nabla = nabla ∧
        lc.torsionFreeWitness = hTorsionFree ∧
        lc.metricCompatibleWitness = hMetricCompatible) ∧
      (∃ spin : SpinLiftTarget G,
        spin.liftWitness = hSpinLift) := by
  rcases symmetricSpaceGlobalLayer_unpack (G := G) (M := M) hGlobal with ⟨cartan, lc, spin, _⟩
  refine ⟨cartan.k, cartan.p, cartan.decompositionWitness,
    lc.nabla, lc.torsionFreeWitness, lc.metricCompatibleWitness, spin.liftWitness, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact S1_cartanDecompositionTarget_exists
      (G := G) cartan.k cartan.p cartan.decompositionWitness
  · exact S2_leviCivitaTarget_exists
      (M := M) lc.nabla lc.torsionFreeWitness lc.metricCompatibleWitness
  · exact S4_spinLiftTarget_exists (G := G) spin.liftWitness

end SymmetricSpaceArchitecture
