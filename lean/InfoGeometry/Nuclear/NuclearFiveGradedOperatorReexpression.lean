/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Exceptional.FreudenthalFiveGradedLieClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.TwoSectorSpectralOscillation
import InfoGeometry.Physics.NuclearFiveGradeKantorComponentBridge
import InfoGeometry.External.Virasoro.FiveGradedDecomposition
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Algebra.Lie.OfAssociative

noncomputable section

open InfoGeometry.Exceptional.Freudenthal
open InfoGeometry.Physics.TwoSector

namespace InfoGeometry.Nuclear.FiveGraded

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-!
# Re-expression of Nuclear Operators in Terms of the 5-Graded Symmetry Algebra

This module establishes the explicit, kernel-checked re-expression dictionary mapping the standard
operators of nuclear physics into the canonical 5-graded Lie carrier:

$$\mathfrak{g} = \mathfrak{g}_{-2} \oplus \mathfrak{g}_{-1} \oplus (\mathfrak{g}_0^{\text{symp}} \oplus \mathbb{R} H) \oplus \mathfrak{g}_{+1} \oplus \mathfrak{g}_{+2}$$

### The Exact Operator Dictionary:

1. **Pairing / Monopole Seniority Operators (Grades $\pm 2$)**:
   - Pairing Creation: $P^\dagger := E_+ \in \mathfrak{g}_{+2}$
   - Pairing Annihilation: $P := E_- \in \mathfrak{g}_{-2}$
   - Commutator: $[P^\dagger, P] = H \in \mathfrak{g}_0$ (seniority number operator)
   - Ladder relations: $[H, P^\dagger] = +2 P^\dagger$, $[H, P] = -2 P$.

2. **Quasiparticle / RPA Phonon Operators (Grades $\pm 1$)**:
   - Fermionic Quasiparticle Annihilation: $\alpha(x) := \operatorname{injChargeMinus}(x) \in \mathfrak{g}_{-1}$
   - Fermionic Quasiparticle Creation: $\alpha^\dagger(y) := \operatorname{injChargePlus}(y) \in \mathfrak{g}_{+1}$
   - Heisenberg Pairing Condensation:
     $[\alpha(x), \alpha(y)] = 2\omega(x, y) P \in \mathfrak{g}_{-2}$
     $[\alpha^\dagger(x), \alpha^\dagger(y)] = 2\omega(x, y) P^\dagger \in \mathfrak{g}_{+2}$
   - Mixed Quasiparticle Bracket:
     $[\alpha(x), \alpha^\dagger(y)] = \operatorname{injSympZero}(\operatorname{mixedSymplecticBracket}(x, y)) + \omega(x, y) H \in \mathfrak{g}_0$.

3. **Degree-0 Symmetries: Euler Grading & Isospin/Spin (Grade $0$)**:
   - Grading / Occupation Euler Operator: $N_{\text{grade}} := H \in \mathfrak{g}_0$
   - Symplectic / Isospin Multi-pole Symmetries: $T_0 \in \mathfrak{g}_0^{\text{symp}}$
   - Commutation: $[N_{\text{grade}}, T_0] = 0$.

4. **Two-Level Chiral Doublet / Tunnelling Realization**:
   - The off-diagonal coupling is the scale component $\Delta(x, y) = \omega(x, y)$, yielding the physical gap $\Delta E = 2|\omega(x, y)|$.

All proofs in this module are complete in native Lean 4 with 0 `sorry`s and 0 axioms.
-/

/-! ### 1. Pairing Operators (Grades $\pm 2$) -/

/-- Nuclear pairing creation operator $P^\dagger := E_+ \in \mathfrak{g}_{+2}$. -/
def pairingCreation (c : ℝ := 1) : FiveGradedCarrier D :=
  genEplus D c

/-- Nuclear pairing annihilation operator $P := E_- \in \mathfrak{g}_{-2}$. -/
def pairingAnnihilation (c : ℝ := 1) : FiveGradedCarrier D :=
  genEminus D c

/-- Nuclear seniority / quasiparticle Euler grading operator $N_{\text{grade}} := H \in \mathfrak{g}_0$. -/
def gradingOperator (h : ℝ := 1) : FiveGradedCarrier D :=
  genHscale D h

/-- **Theorem**: The commutator of pairing creation and annihilation generates the seniority scale operator:
    $[P^\dagger, P] = N_{\text{grade}}$. -/
theorem pairing_commutator_eq_grading :
    fiveGradedBracket D (pairingCreation D 1) (pairingAnnihilation D 1) =
    gradingOperator D 1 := by
  exact extreme_grade_bracket_eq_scale D

/-- **Theorem**: The seniority grading operator acts with eigenvalue $+2$ on pairing creation:
    $[N_{\text{grade}}, P^\dagger] = 2 P^\dagger$. -/
theorem grading_action_on_pairingCreation :
    fiveGradedBracket D (gradingOperator D 1) (pairingCreation D 1) =
    pairingCreation D 2 := by
  exact scale_action_gradePlus2 D

/-- **Theorem**: The seniority grading operator acts with eigenvalue $-2$ on pairing annihilation:
    $[N_{\text{grade}}, P] = -2 P$. -/
theorem grading_action_on_pairingAnnihilation :
    fiveGradedBracket D (gradingOperator D 1) (pairingAnnihilation D 1) =
    pairingAnnihilation D (-2) := by
  exact scale_action_gradeMinus2 D

/-! ### 2. Quasiparticle Creation and Annihilation (Grades $\pm 1$) -/

/-- Quasiparticle annihilation operator $\alpha(x) := \operatorname{injChargeMinus}(x) \in \mathfrak{g}_{-1}$. -/
def qpAnnihilation (x : FreudenthalCharge J) : FiveGradedCarrier D :=
  injChargeMinus D x

/-- Quasiparticle creation operator $\alpha^\dagger(y) := \operatorname{injChargePlus}(y) \in \mathfrak{g}_{+1}$. -/
def qpCreation (y : FreudenthalCharge J) : FiveGradedCarrier D :=
  injChargePlus D y

/-- **Theorem**: Annihilation pairing commutator produces the pairing annihilation operator:
    $[\alpha(x), \alpha(y)] = 2\omega(x, y) P$. -/
theorem qpAnnihilation_pairing_condensation (x y : FreudenthalCharge J) :
    fiveGradedBracket D (qpAnnihilation D x) (qpAnnihilation D y) =
    pairingAnnihilation D (2 * FreudenthalCharge.symplecticForm D x y) := by
  exact bracket_minus1_minus1 D x y

/-- **Theorem**: Creation pairing commutator produces the pairing creation operator:
    $[\alpha^\dagger(x), \alpha^\dagger(y)] = 2\omega(x, y) P^\dagger$. -/
theorem qpCreation_pairing_condensation (x y : FreudenthalCharge J) :
    fiveGradedBracket D (qpCreation D x) (qpCreation D y) =
    pairingCreation D (2 * FreudenthalCharge.symplecticForm D x y) := by
  exact bracket_plus1_plus1 D x y

/-- **Theorem**: Seniority grading eigenvalue on quasiparticle creation is $+1$:
    $[N_{\text{grade}}, \alpha^\dagger(y)] = +1 \alpha^\dagger(y)$. -/
theorem grading_action_on_qpCreation (y : FreudenthalCharge J) :
    fiveGradedBracket D (gradingOperator D 1) (qpCreation D y) =
    qpCreation D y := by
  exact scale_action_gradePlus1 D y

/-- **Theorem**: Seniority grading eigenvalue on quasiparticle annihilation is $-1$:
    $[N_{\text{grade}}, \alpha(x)] = -1 \alpha(x)$. -/
theorem grading_action_on_qpAnnihilation (x : FreudenthalCharge J) :
    fiveGradedBracket D (gradingOperator D 1) (qpAnnihilation D x) =
    qpAnnihilation D (-x) := by
  exact scale_action_gradeMinus1 D x

/-! ### 3. Mixed Quasiparticle Bracket & Scale Extraction -/

/-- Mixed quasiparticle bracket scale component extraction. -/
def mixedScaleCoupling (x y : FreudenthalCharge J) : ℝ :=
  FreudenthalCharge.symplecticForm D x y

/-- **Theorem**: The zero-scale component of the mixed quasiparticle bracket $[\alpha(x), \alpha^\dagger(y)]$
    is precisely the coupling $\omega(x, y)$. -/
theorem mixed_qp_scale_component (x y : FreudenthalCharge J) :
    (fiveGradedBracket D (qpAnnihilation D x) (qpCreation D y)).zero_scale =
    mixedScaleCoupling D x y := by
  dsimp [fiveGradedBracket, qpAnnihilation, qpCreation, mixedScaleCoupling, injChargeMinus, injChargePlus]
  simp

/-! ### 4. Degree-0 Multi-Pole / Isospin Symmetries -/

/-- Degree-0 multi-pole / isospin operator injection $T_0 \in \mathfrak{g}_0^{\text{symp}}$. -/
def multipoleOperator (T : SymplecticTKKZero D) : FiveGradedCarrier D :=
  injSympZero D T

/-- **Theorem**: Grading operator commutes with all degree-0 multi-pole / isospin operators:
    $[N_{\text{grade}}, T_0] = 0$. -/
theorem grading_commutes_multipole (T : SymplecticTKKZero D) :
    fiveGradedBracket D (gradingOperator D 1) (multipoleOperator D T) = 0 := by
  exact scale_action_gradeZeroSymp D T

/-! ### 5. Grand Synthesis: 5-Graded Nuclear Operator Re-expression -/

/-
🏆 **GRAND SYNTHESIS: Nuclear Operator Re-expression in the 5-Graded Symmetry Carrier**

Unifies:
1. Pairing Lie closure: $[P^\dagger, P] = N_{\text{grade}}$, $[N, P^\dagger] = +2 P^\dagger$, $[N, P] = -2 P$.
2. Quasiparticle pairing condensation: $[\alpha(x), \alpha(y)] = 2\omega(x, y) P$, $[\alpha^\dagger(x), \alpha^\dagger(y)] = 2\omega(x, y) P^\dagger$.
3. Quasiparticle grading eigenvalues: $[N, \alpha^\dagger(y)] = +\alpha^\dagger(y)$, $[N, \alpha(x)] = -\alpha(x)$.
4. Mixed transversal scale extraction: $\pi_{\text{scale}}([\alpha(x), \alpha^\dagger(y)]) = \omega(x, y)$.
5. Multipole / isospin degree-0 invariance: $[N, T_0] = 0$.
-/
end InfoGeometry.Nuclear.FiveGraded

/-! ## Concrete `VirasoroProject.FiveGradedAlgebra ℝ` Instance on `M4R` & Exact CAR↔Freudenthal Comparison -/

namespace InfoGeometry.Nuclear.FiveGraded

open InfoGeometry.Canonical
open InfoGeometry.Canonical.SplitCliffordTwoModeCAR hiding M4R
open InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
open InfoGeometry.Physics.NuclearTwoModeFiveGradeSubmodules
open InfoGeometry.Physics.NuclearFiveGradeKantorComponentBridge

private def weight4 : Fin 4 → ℤ := ![-1, 0, 0, 1]

private theorem comm_gradingOperator_entry (X : M4R) (i j : Fin 4) :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator X i j =
      ((weight4 i - weight4 j : ℤ) : ℝ) * X i j := by
  rw [gradingOperator_eq_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp only [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, Matrix.sub_apply,
      Matrix.mul_apply, Fin.sum_univ_four, weight4] <;>
    norm_num <;> ring

/-- Entrywise characterization of the concrete adjoint eigenspace `gradeSpace k` in `M4R`. -/
theorem mem_gradeSpace_iff_entry (k : ℤ) (X : M4R) :
    X ∈ gradeSpace k ↔ ∀ i j : Fin 4, weight4 i - weight4 j ≠ k → X i j = 0 := by
  rw [mem_gradeSpace]
  unfold HasGrade
  constructor
  · intro h i j hij
    have he := congrFun (congrFun h i) j
    rw [comm_gradingOperator_entry] at he
    change ((weight4 i - weight4 j : ℤ) : ℝ) * X i j = (k : ℝ) * X i j at he
    have hdiff : ((weight4 i - weight4 j : ℤ) : ℝ) - (k : ℝ) ≠ 0 := by
      rw [← Int.cast_sub]
      exact Int.cast_ne_zero.mpr (sub_ne_zero.mpr hij)
    have hprod : (((weight4 i - weight4 j : ℤ) : ℝ) - (k : ℝ)) * X i j = 0 := by
      linarith
    exact (mul_eq_zero.mp hprod).resolve_left hdiff
  · intro h
    ext i j
    rw [comm_gradingOperator_entry]
    by_cases hij : weight4 i - weight4 j = k
    · rw [hij]; rfl
    · have h0 := h i j hij
      simp [h0]

/-- Graded submodule family on `M4R` indexed by `Fin 5` (`k ↦ gradeSpace (k - 2)`). -/
def m4rGrade (k : Fin 5) : Submodule ℝ M4R :=
  gradeSpace ((k : ℤ) - 2)

/-- Explicit grade projection onto the `k`-th summand of `M4R`. -/
def m4rGradeProj (k : Fin 5) (X : M4R) : M4R :=
  Matrix.of fun i j => if weight4 i - weight4 j = (k : ℤ) - 2 then X i j else 0

theorem m4rGradeProj_mem (k : Fin 5) (X : M4R) :
    m4rGradeProj k X ∈ m4rGrade k := by
  dsimp only [m4rGrade]
  rw [mem_gradeSpace_iff_entry]
  intro i j hij
  simp [m4rGradeProj, hij]

theorem sum_m4rGradeProj (X : M4R) :
    ∑ k : Fin 5, m4rGradeProj k X = X := by
  ext i j
  rw [Matrix.sum_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_five, m4rGradeProj, weight4]

theorem m4rGrade_sum_eq_zero_imp (f : ∀ k : Fin 5, m4rGrade k)
    (hsum : ∑ k : Fin 5, (f k : M4R) = 0) :
    ∀ k : Fin 5, f k = 0 := by
  intro k
  apply Subtype.ext
  ext i j
  by_cases hik : weight4 i - weight4 j = (k : ℤ) - 2
  · have hsum_ij := congrFun (congrFun hsum i) j
    rw [Matrix.sum_apply, Matrix.zero_apply] at hsum_ij
    have hother : ∀ k' : Fin 5, k' ≠ k → ((f k' : M4R) i j) = 0 := by
      intro k' hk'
      have hmem := (mem_gradeSpace_iff_entry ((k' : ℤ) - 2) (f k' : M4R)).mp (f k').2
      apply hmem i j
      rw [hik]
      intro h_eq
      apply hk'
      ext
      omega
    rw [Finset.sum_eq_single k (fun k' _ hk' => hother k' hk')
      (fun hm => False.elim (hm (Finset.mem_univ k)))] at hsum_ij
    exact hsum_ij
  · exact (mem_gradeSpace_iff_entry ((k : ℤ) - 2) (f k : M4R)).mp (f k).2 i j hik

/-- Concrete `VirasoroProject.FiveGradedAlgebra ℝ` instance on `M4R`. -/
def m4rFiveGradedAlgebra : VirasoroProject.FiveGradedAlgebra ℝ where
  algebra := M4R
  instLieRing := LieRing.ofAssociativeRing
  instLieAlgebra := LieAlgebra.ofAssociativeAlgebra
  grade := m4rGrade
  directSum := by
    constructor
    · intro x y hxy
      have hsub : DirectSum.coeAddMonoidHom m4rGrade (x - y) = 0 := by
        rw [map_sub, hxy, sub_self]
      have hsum : ∑ k : Fin 5, ((x - y) k : M4R) = 0 := by
        rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum] at hsub
        have hsub' : ∑ k ∈ (x - y).support, ((x - y) k : M4R) = 0 := hsub
        rw [Finset.sum_subset (Finset.subset_univ (x - y).support) (fun k _ hk => by
          rw [DFinsupp.notMem_support_iff.mp hk]; rfl)] at hsub'
        exact hsub'
      have hzero := m4rGrade_sum_eq_zero_imp (fun k => (x - y) k) hsum
      apply sub_eq_zero.mp
      exact DFinsupp.ext fun k => Subtype.ext (congrArg Subtype.val (hzero k))
    · intro X
      refine ⟨∑ k : Fin 5, DirectSum.of (fun k => ↥(m4rGrade k)) k
        ⟨m4rGradeProj k X, m4rGradeProj_mem k X⟩, ?_⟩
      simp only [map_sum, DirectSum.coeAddMonoidHom_of]
      exact sum_m4rGradeProj X
  bracket_zero := by
    intro i j hij x hx y hy
    have hmem : ⁅x, y⁆ ∈ gradeSpace (((i : ℤ) - 2) + ((j : ℤ) - 2)) :=
      lie_mem_grade_add hx hy
    rw [mem_gradeSpace_iff_entry] at hmem
    ext a b
    apply hmem a b
    fin_cases a <;> fin_cases b <;> dsimp [weight4] <;> omega
  bracket_compat := by
    intro i j k hijk x hx y hy
    have hmem : ⁅x, y⁆ ∈ gradeSpace (((i : ℤ) - 2) + ((j : ℤ) - 2)) :=
      lie_mem_grade_add hx hy
    have hidx : ((i : ℤ) - 2) + ((j : ℤ) - 2) = (k : ℤ) - 2 := by omega
    rw [hidx] at hmem
    exact hmem

theorem m4rGrade_directSum : DirectSum.IsInternal m4rGrade :=
  m4rFiveGradedAlgebra.directSum

/-! ### Concrete `CubicJordanDatum PUnit.{1}` Model and Grade-Preserving Map `Φ : FiveGradedCarrier D →ₗ[ℝ] M4R` -/

/-- Minimal concrete cubic Jordan datum on `PUnit`, isolating the 2-dimensional charge sector
`FreudenthalCharge PUnit.{1} ≅ ℝ × ℝ` with canonical symplectic pairing `α₁ β₂ - β₁ α₂`. -/
def punitCubicJordanDatum : CubicJordanDatum PUnit.{1} where
  traceBilin := 0
  trace_comm _ _ := rfl
  normCubic _ := 0
  adjointQuad _ := PUnit.unit
  normTrilin := 0
  normTrilin_swap₁₂ _ _ _ := rfl
  normTrilin_swap₂₃ _ _ _ := rfl
  normTrilin_self _ := rfl

section ConcreteBridge

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

instance (D : CubicJordanDatum J) : AddCommGroup (FiveGradedCarrier D) where
  add u v := ⟨u.minus2 + v.minus2, u.minus1 + v.minus1, u.zero_symp + v.zero_symp,
    u.zero_scale + v.zero_scale, u.plus1 + v.plus1, u.plus2 + v.plus2⟩
  add_assoc := FiveGradedCarrier.add_assoc D
  zero := ⟨0, 0, 0, 0, 0, 0⟩
  zero_add u := by apply FiveGradedCarrier.ext <;> simp
  add_zero u := by apply FiveGradedCarrier.ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg u := ⟨-u.minus2, -u.minus1, -u.zero_symp, -u.zero_scale, -u.plus1, -u.plus2⟩
  neg_add_cancel u := by apply FiveGradedCarrier.ext <;> simp
  add_comm u v := by apply FiveGradedCarrier.ext <;> simp [add_comm]
  sub u v := ⟨u.minus2 - v.minus2, u.minus1 - v.minus1, u.zero_symp - v.zero_symp,
    u.zero_scale - v.zero_scale, u.plus1 - v.plus1, u.plus2 - v.plus2⟩
  sub_eq_add_neg u v := by apply FiveGradedCarrier.ext <;> exact _root_.sub_eq_add_neg _ _

instance (D : CubicJordanDatum J) : Module ℝ (FiveGradedCarrier D) where
  smul r u := ⟨r * u.minus2, r • u.minus1, r • u.zero_symp,
    r * u.zero_scale, r • u.plus1, r * u.plus2⟩
  one_smul u := by apply FiveGradedCarrier.ext <;> simp
  mul_smul r s u := by apply FiveGradedCarrier.ext <;> simp [mul_assoc, mul_smul]
  smul_zero r := by apply FiveGradedCarrier.ext <;> simp
  smul_add r u v := by apply FiveGradedCarrier.ext <;> simp [mul_add, smul_add]
  add_smul r s u := by apply FiveGradedCarrier.ext <;> simp [add_mul, add_smul]
  zero_smul u := by apply FiveGradedCarrier.ext <;> simp

private def eAlpha : FreudenthalCharge PUnit.{1} := ⟨1, 0, PUnit.unit, PUnit.unit⟩
private def eBeta : FreudenthalCharge PUnit.{1} := ⟨0, 1, PUnit.unit, PUnit.unit⟩

/-- Embed the `sp(2, ℝ)` symplectic zero-grade algebra `SymplecticTKKZero punitCubicJordanDatum`
into the `(1, 2)` seniority-1 block of `gradeSpace 0 ⊂ M4R`. -/
def sympToM4R (T : SymplecticTKKZero punitCubicJordanDatum) : M4R :=
  !![0, 0, 0, 0;
     0, (T.1 eBeta).beta, (T.1 eAlpha).beta, 0;
     0, (T.1 eBeta).alpha, (T.1 eAlpha).alpha, 0;
     0, 0, 0, 0]

theorem sympToM4R_mem_gradeZero (T : SymplecticTKKZero punitCubicJordanDatum) :
    sympToM4R T ∈ gradeSpace 0 := by
  rw [mem_gradeSpace_iff_entry]
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd (by decide : weight4 _ - weight4 _ = 0) hij
    | simp [sympToM4R]

theorem sympToM4R_isCommutatorComponent (T : SymplecticTKKZero punitCubicJordanDatum) :
    IsCommutatorComponent InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator (sympToM4R T) 0 := by
  simpa using (mem_gradeSpace_iff_isCommutatorComponent 0 (sympToM4R T)).1
    (sympToM4R_mem_gradeZero T)

private lemma symplectic_trace_zero (T : SymplecticTKKZero punitCubicJordanDatum) :
    (T.1 eAlpha).alpha + (T.1 eBeta).beta = 0 := by
  have h := T.property eAlpha eBeta
  simpa [FreudenthalCharge.symplecticForm, eAlpha, eBeta] using h

private lemma charge_punit_decomp (x : FreudenthalCharge PUnit.{1}) :
    x = x.alpha • eAlpha + x.beta • eBeta := by
  ext <;> simp [eAlpha, eBeta]

private def mkMid4 (a b c d : ℝ) : M4R :=
  !![0, 0, 0, 0;
     0, a, b, 0;
     0, c, d, 0;
     0, 0, 0, 0]

private lemma mkMid4_add (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) :
    mkMid4 (a₁ + a₂) (b₁ + b₂) (c₁ + c₂) (d₁ + d₂) =
      mkMid4 a₁ b₁ c₁ d₁ + mkMid4 a₂ b₂ c₂ d₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkMid4]

private lemma mkMid4_smul (r a b c d : ℝ) :
    mkMid4 (r * a) (r * b) (r * c) (r * d) = r • mkMid4 a b c d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkMid4]

private lemma mkMid4_neg (a b c d : ℝ) :
    -mkMid4 a b c d = mkMid4 (-a) (-b) (-c) (-d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkMid4]

private lemma mkMid4_zero : mkMid4 0 0 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkMid4]

private lemma six_sum_add (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ : M4R) :
    (a₁ + a₂) + (b₁ + b₂) + (c₁ + c₂) + (d₁ + d₂) + (e₁ + e₂) + (f₁ + f₂) =
      (a₁ + b₁ + c₁ + d₁ + e₁ + f₁) + (a₂ + b₂ + c₂ + d₂ + e₂ + f₂) := by
  abel

private lemma six_sum_smul (r : ℝ) (a b c d e f : M4R) :
    (r • a) + (r • b) + (r • c) + (r • d) + (r • e) + (r • f) =
      r • (a + b + c + d + e + f) := by
  simp only [smul_add]

private lemma sympToM4R_eq_mkMid4 (T : SymplecticTKKZero punitCubicJordanDatum) :
    sympToM4R T =
      mkMid4 (T.1 eBeta).beta (T.1 eAlpha).beta (T.1 eBeta).alpha (T.1 eAlpha).alpha := rfl

private lemma sympToM4R_add (T U : SymplecticTKKZero punitCubicJordanDatum) :
    sympToM4R (T + U) = sympToM4R T + sympToM4R U := by
  have h11 : ((T + U).1 eBeta).beta = (T.1 eBeta).beta + (U.1 eBeta).beta := by
    rw [← beta_add]; rfl
  have h12 : ((T + U).1 eAlpha).beta = (T.1 eAlpha).beta + (U.1 eAlpha).beta := by
    rw [← beta_add]; rfl
  have h21 : ((T + U).1 eBeta).alpha = (T.1 eBeta).alpha + (U.1 eBeta).alpha := by
    rw [← alpha_add]; rfl
  have h22 : ((T + U).1 eAlpha).alpha = (T.1 eAlpha).alpha + (U.1 eAlpha).alpha := by
    rw [← alpha_add]; rfl
  rw [sympToM4R_eq_mkMid4 (T + U), sympToM4R_eq_mkMid4 T, sympToM4R_eq_mkMid4 U,
    h11, h12, h21, h22]
  exact mkMid4_add _ _ _ _ _ _ _ _

private lemma sympToM4R_smul (r : ℝ) (T : SymplecticTKKZero punitCubicJordanDatum) :
    sympToM4R (r • T) = r • sympToM4R T := by
  have h11 : ((r • T).1 eBeta).beta = r * (T.1 eBeta).beta := by
    rw [← beta_smul]; rfl
  have h12 : ((r • T).1 eAlpha).beta = r * (T.1 eAlpha).beta := by
    rw [← beta_smul]; rfl
  have h21 : ((r • T).1 eBeta).alpha = r * (T.1 eBeta).alpha := by
    rw [← alpha_smul]; rfl
  have h22 : ((r • T).1 eAlpha).alpha = r * (T.1 eAlpha).alpha := by
    rw [← alpha_smul]; rfl
  rw [sympToM4R_eq_mkMid4 (r • T), sympToM4R_eq_mkMid4 T, h11, h12, h21, h22]
  exact mkMid4_smul _ _ _ _ _

/-- Explicit grade-preserving linear map `Φ : FiveGradedCarrier punitCubicJordanDatum →ₗ[ℝ] M4R`.
Maps `pairingCreation ↦ pairCreation`, `pairingAnnihilation ↦ pairAnnihilation`,
`gradingOperator ↦ InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator`,
`qpCreation` / `qpAnnihilation` into `gradeSpace (±1)`, and `multipoleOperator` into `gradeSpace 0`. -/
def Phi : FiveGradedCarrier punitCubicJordanDatum →ₗ[ℝ] M4R where
  toFun u :=
    u.minus2 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation +
      (u.minus1.beta • a1 - u.minus1.alpha • a2) +
      sympToM4R u.zero_symp +
      u.zero_scale • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
      (u.plus1.alpha • a1Dag + u.plus1.beta • a2Dag) +
      u.plus2 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation
  map_add' u v := by
    change
      (u.minus2 + v.minus2) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation +
        ((u.minus1 + v.minus1).beta • a1 - (u.minus1 + v.minus1).alpha • a2) +
        sympToM4R (u.zero_symp + v.zero_symp) +
        (u.zero_scale + v.zero_scale) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
        ((u.plus1 + v.plus1).alpha • a1Dag + (u.plus1 + v.plus1).beta • a2Dag) +
        (u.plus2 + v.plus2) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation =
      (u.minus2 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation +
        (u.minus1.beta • a1 - u.minus1.alpha • a2) +
        sympToM4R u.zero_symp +
        u.zero_scale • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
        (u.plus1.alpha • a1Dag + u.plus1.beta • a2Dag) +
        u.plus2 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation) +
      (v.minus2 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation +
        (v.minus1.beta • a1 - v.minus1.alpha • a2) +
        sympToM4R v.zero_symp +
        v.zero_scale • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
        (v.plus1.alpha • a1Dag + v.plus1.beta • a2Dag) +
        v.plus2 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation)
    rw [alpha_add, beta_add, alpha_add, beta_add, sympToM4R_add]
    simp only [add_smul]
    have hm1 : (u.minus1.beta • a1 + v.minus1.beta • a1) - (u.minus1.alpha • a2 + v.minus1.alpha • a2) =
        (u.minus1.beta • a1 - u.minus1.alpha • a2) + (v.minus1.beta • a1 - v.minus1.alpha • a2) := by
      abel
    have hp1 : (u.plus1.alpha • a1Dag + v.plus1.alpha • a1Dag) + (u.plus1.beta • a2Dag + v.plus1.beta • a2Dag) =
        (u.plus1.alpha • a1Dag + u.plus1.beta • a2Dag) + (v.plus1.alpha • a1Dag + v.plus1.beta • a2Dag) := by
      abel
    rw [hm1, hp1]
    exact six_sum_add _ _ _ _ _ _ _ _ _ _ _ _
  map_smul' r u := by
    change
      (r * u.minus2) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation +
        ((r • u.minus1).beta • a1 - (r • u.minus1).alpha • a2) +
        sympToM4R (r • u.zero_symp) +
        (r * u.zero_scale) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
        ((r • u.plus1).alpha • a1Dag + (r • u.plus1).beta • a2Dag) +
        (r * u.plus2) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation =
      r • (u.minus2 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation +
        (u.minus1.beta • a1 - u.minus1.alpha • a2) +
        sympToM4R u.zero_symp +
        u.zero_scale • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
        (u.plus1.alpha • a1Dag + u.plus1.beta • a2Dag) +
        u.plus2 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation)
    rw [alpha_smul, beta_smul, alpha_smul, beta_smul, sympToM4R_smul]
    simp only [mul_smul]
    have hm1 : r • (u.minus1.beta • a1) - r • (u.minus1.alpha • a2) =
        r • (u.minus1.beta • a1 - u.minus1.alpha • a2) := (smul_sub r _ _).symm
    have hp1 : r • (u.plus1.alpha • a1Dag) + r • (u.plus1.beta • a2Dag) =
        r • (u.plus1.alpha • a1Dag + u.plus1.beta • a2Dag) := (smul_add r _ _).symm
    rw [hm1, hp1]
    exact six_sum_smul r _ _ _ _ _ _

private lemma sympToM4R_zero : sympToM4R 0 = 0 := by
  have h11 : ((0 : SymplecticTKKZero punitCubicJordanDatum).1 eBeta).beta = 0 := rfl
  have h12 : ((0 : SymplecticTKKZero punitCubicJordanDatum).1 eAlpha).beta = 0 := rfl
  have h21 : ((0 : SymplecticTKKZero punitCubicJordanDatum).1 eBeta).alpha = 0 := rfl
  have h22 : ((0 : SymplecticTKKZero punitCubicJordanDatum).1 eAlpha).alpha = 0 := rfl
  rw [sympToM4R_eq_mkMid4 0, h11, h12, h21, h22]
  exact mkMid4_zero

private lemma charge_zero_alpha : (0 : FreudenthalCharge PUnit.{1}).alpha = 0 := rfl
private lemma charge_zero_beta : (0 : FreudenthalCharge PUnit.{1}).beta = 0 := rfl

@[simp] theorem Phi_pairingCreation (c : ℝ) :
    Phi (pairingCreation punitCubicJordanDatum c) =
      c • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation := by
  change (0 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation +
      ((0 : FreudenthalCharge PUnit.{1}).beta • a1 -
        (0 : FreudenthalCharge PUnit.{1}).alpha • a2) +
      sympToM4R 0 +
      (0 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
      ((0 : FreudenthalCharge PUnit.{1}).alpha • a1Dag +
        (0 : FreudenthalCharge PUnit.{1}).beta • a2Dag) +
      c • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation =
    c • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation
  simp [sympToM4R_zero, charge_zero_alpha, charge_zero_beta]

@[simp] theorem Phi_pairingAnnihilation (c : ℝ) :
    Phi (pairingAnnihilation punitCubicJordanDatum c) =
      c • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation := by
  change c • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation +
      ((0 : FreudenthalCharge PUnit.{1}).beta • a1 -
        (0 : FreudenthalCharge PUnit.{1}).alpha • a2) +
      sympToM4R 0 +
      (0 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
      ((0 : FreudenthalCharge PUnit.{1}).alpha • a1Dag +
        (0 : FreudenthalCharge PUnit.{1}).beta • a2Dag) +
      (0 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation =
    c • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation
  simp [sympToM4R_zero, charge_zero_alpha, charge_zero_beta]

@[simp] theorem Phi_gradingOperator (h : ℝ) :
    Phi (gradingOperator punitCubicJordanDatum h) =
      h • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator := by
  change (0 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation +
      ((0 : FreudenthalCharge PUnit.{1}).beta • a1 -
        (0 : FreudenthalCharge PUnit.{1}).alpha • a2) +
      sympToM4R 0 +
      h • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
      ((0 : FreudenthalCharge PUnit.{1}).alpha • a1Dag +
        (0 : FreudenthalCharge PUnit.{1}).beta • a2Dag) +
      (0 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation =
    h • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator
  simp [sympToM4R_zero, charge_zero_alpha, charge_zero_beta]

@[simp] theorem Phi_qpCreation (y : FreudenthalCharge PUnit.{1}) :
    Phi (qpCreation punitCubicJordanDatum y) =
      y.alpha • a1Dag + y.beta • a2Dag := by
  change (0 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation +
      ((0 : FreudenthalCharge PUnit.{1}).beta • a1 -
        (0 : FreudenthalCharge PUnit.{1}).alpha • a2) +
      sympToM4R 0 +
      (0 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
      (y.alpha • a1Dag + y.beta • a2Dag) +
      (0 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation =
    y.alpha • a1Dag + y.beta • a2Dag
  simp [sympToM4R_zero, charge_zero_alpha, charge_zero_beta]

@[simp] theorem Phi_qpAnnihilation (x : FreudenthalCharge PUnit.{1}) :
    Phi (qpAnnihilation punitCubicJordanDatum x) =
      x.beta • a1 - x.alpha • a2 := by
  change (0 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation +
      (x.beta • a1 - x.alpha • a2) +
      sympToM4R 0 +
      (0 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
      ((0 : FreudenthalCharge PUnit.{1}).alpha • a1Dag +
        (0 : FreudenthalCharge PUnit.{1}).beta • a2Dag) +
      (0 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation =
    x.beta • a1 - x.alpha • a2
  simp [sympToM4R_zero, charge_zero_alpha, charge_zero_beta]

@[simp] theorem Phi_multipoleOperator (T : SymplecticTKKZero punitCubicJordanDatum) :
    Phi (multipoleOperator punitCubicJordanDatum T) = sympToM4R T := by
  change (0 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation +
      ((0 : FreudenthalCharge PUnit.{1}).beta • a1 -
        (0 : FreudenthalCharge PUnit.{1}).alpha • a2) +
      sympToM4R T +
      (0 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
      ((0 : FreudenthalCharge PUnit.{1}).alpha • a1Dag +
        (0 : FreudenthalCharge PUnit.{1}).beta • a2Dag) +
      (0 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation =
    sympToM4R T
  simp [charge_zero_alpha, charge_zero_beta]

/-- `Phi` preserves all five grades and `IsCommutatorComponent` weights. -/
theorem Phi_preserves_grades (c h : ℝ)
    (x y : FreudenthalCharge PUnit.{1}) (T : SymplecticTKKZero punitCubicJordanDatum) :
    (Phi (pairingAnnihilation punitCubicJordanDatum c) ∈ m4rGrade 0 ∧
      IsCommutatorComponent InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator
        (Phi (pairingAnnihilation punitCubicJordanDatum c)) (-2 : ℝ)) ∧
    (Phi (qpAnnihilation punitCubicJordanDatum x) ∈ m4rGrade 1 ∧
      IsCommutatorComponent InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator
        (Phi (qpAnnihilation punitCubicJordanDatum x)) (-1 : ℝ)) ∧
    (Phi (gradingOperator punitCubicJordanDatum h) ∈ m4rGrade 2 ∧
      IsCommutatorComponent InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator
        (Phi (gradingOperator punitCubicJordanDatum h)) 0) ∧
    (Phi (multipoleOperator punitCubicJordanDatum T) ∈ m4rGrade 2 ∧
      IsCommutatorComponent InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator
        (Phi (multipoleOperator punitCubicJordanDatum T)) 0) ∧
    (Phi (qpCreation punitCubicJordanDatum y) ∈ m4rGrade 3 ∧
      IsCommutatorComponent InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator
        (Phi (qpCreation punitCubicJordanDatum y)) 1) ∧
    (Phi (pairingCreation punitCubicJordanDatum c) ∈ m4rGrade 4 ∧
      IsCommutatorComponent InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator
        (Phi (pairingCreation punitCubicJordanDatum c)) 2) := by
  have hm2 : Phi (pairingAnnihilation punitCubicJordanDatum c) ∈ gradeSpace (-2) := by
    rw [Phi_pairingAnnihilation]
    exact (gradeSpace (-2)).smul_mem c ((mem_gradeSpace _ _).2 pairAnnihilation_grade)
  have hm1 : Phi (qpAnnihilation punitCubicJordanDatum x) ∈ gradeSpace (-1) := by
    rw [Phi_qpAnnihilation]
    exact (gradeSpace (-1)).sub_mem
      ((gradeSpace (-1)).smul_mem x.beta ((mem_gradeSpace _ _).2 a1_grade))
      ((gradeSpace (-1)).smul_mem x.alpha ((mem_gradeSpace _ _).2 a2_grade))
  have h0h : Phi (gradingOperator punitCubicJordanDatum h) ∈ gradeSpace 0 := by
    rw [Phi_gradingOperator]
    refine (gradeSpace 0).smul_mem h ?_
    rw [mem_gradeSpace]
    simp [HasGrade, InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm]
  have h0T : Phi (multipoleOperator punitCubicJordanDatum T) ∈ gradeSpace 0 := by
    rw [Phi_multipoleOperator]
    exact sympToM4R_mem_gradeZero T
  have hp1 : Phi (qpCreation punitCubicJordanDatum y) ∈ gradeSpace 1 := by
    rw [Phi_qpCreation]
    exact (gradeSpace 1).add_mem
      ((gradeSpace 1).smul_mem y.alpha ((mem_gradeSpace _ _).2 a1Dag_grade))
      ((gradeSpace 1).smul_mem y.beta ((mem_gradeSpace _ _).2 a2Dag_grade))
  have hp2 : Phi (pairingCreation punitCubicJordanDatum c) ∈ gradeSpace 2 := by
    rw [Phi_pairingCreation]
    exact (gradeSpace 2).smul_mem c ((mem_gradeSpace _ _).2 pairCreation_grade)
  refine ⟨⟨hm2, ?_⟩, ⟨hm1, ?_⟩, ⟨h0h, ?_⟩, ⟨h0T, ?_⟩, ⟨hp1, ?_⟩, ⟨hp2, ?_⟩⟩
  · simpa using (mem_gradeSpace_iff_isCommutatorComponent (-2) _).1 hm2
  · simpa using (mem_gradeSpace_iff_isCommutatorComponent (-1) _).1 hm1
  · simpa using (mem_gradeSpace_iff_isCommutatorComponent 0 _).1 h0h
  · simpa using (mem_gradeSpace_iff_isCommutatorComponent 0 _).1 h0T
  · simpa using (mem_gradeSpace_iff_isCommutatorComponent 1 _).1 hp1
  · simpa using (mem_gradeSpace_iff_isCommutatorComponent 2 _).1 hp2

private lemma comm_add_left_m4r (X Y Z : M4R) :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm (X + Y) Z =
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm X Z +
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm Y Z := by
  simp [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, add_mul, mul_add]
  abel

private lemma comm_sub_left_m4r (X Y Z : M4R) :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm (X - Y) Z =
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm X Z -
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm Y Z := by
  simp [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, sub_mul, mul_sub]
  abel

private lemma comm_sub_right_m4r (X Y Z : M4R) :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm X (Y - Z) =
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm X Y -
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm X Z := by
  simp [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, sub_mul, mul_sub]
  abel

private def H0_m4r : M4R := mkMid4 1 0 0 (-1)
private def E12_m4r : M4R := mkMid4 0 1 0 0
private def E21_m4r : M4R := mkMid4 0 0 1 0

private lemma mkMid4_traceless_decomp (a b c d : ℝ) (h : d + a = 0) :
    mkMid4 a b c d = a • H0_m4r + b • E12_m4r + c • E21_m4r := by
  have hd : d = -a := eq_neg_of_add_eq_zero_left h
  subst hd
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkMid4, H0_m4r, E12_m4r, E21_m4r]

private lemma comm_H0_a1Dag :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm H0_m4r a1Dag = -a1Dag := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, H0_m4r, mkMid4, a1Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma comm_E12_a1Dag :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm E12_m4r a1Dag = a2Dag := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, E12_m4r, mkMid4, a1Dag,
      a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

private lemma comm_E21_a1Dag :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm E21_m4r a1Dag = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, E21_m4r, mkMid4, a1Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma comm_H0_a2Dag :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm H0_m4r a2Dag = a2Dag := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, H0_m4r, mkMid4, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma comm_E12_a2Dag :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm E12_m4r a2Dag = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, E12_m4r, mkMid4, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma comm_E21_a2Dag :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm E21_m4r a2Dag = a1Dag := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, E21_m4r, mkMid4, a1Dag,
      a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

private lemma comm_H0_a1 :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm H0_m4r a1 = a1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, H0_m4r, mkMid4, a1,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma comm_E12_a1 :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm E12_m4r a1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, E12_m4r, mkMid4, a1,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma comm_E21_a1 :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm E21_m4r a1 = -a2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, E21_m4r, mkMid4, a1, a2,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma comm_H0_a2 :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm H0_m4r a2 = -a2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, H0_m4r, mkMid4, a2,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma comm_E12_a2 :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm E12_m4r a2 = -a1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, E12_m4r, mkMid4, a1, a2,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma comm_E21_a2 :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm E21_m4r a2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, E21_m4r, mkMid4, a2,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma comm_a1_a1Dag_eq :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm a1 a1Dag =
      (1 : M4R) - (2 : ℝ) • number1 := by
  have h1 : number1 = !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
    unfold number1
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [a1, a1Dag, Matrix.mul_apply, Fin.sum_univ_four]
  rw [h1]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, a1, a1Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma comm_a2_a2Dag_eq :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm a2 a2Dag =
      (1 : M4R) - (2 : ℝ) • number2 := by
  have h2 : number2 = !![0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1] := by
    unfold number2
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [a2, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]
  rw [h2]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, a2, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma comm_a1_a2Dag_mkMid4 :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm a1 a2Dag = mkMid4 0 (-2) 0 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, mkMid4, a1, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma comm_a2_a1Dag_mkMid4 :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm a2 a1Dag = mkMid4 0 0 (-2) 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm, mkMid4, a2, a1Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma car_diag1_decomp :
    (1 : M4R) - (2 : ℝ) • number1 =
      -InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator + mkMid4 1 0 0 (-1) := by
  have h1 : number1 = !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
    unfold number1
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [a1, a1Dag, Matrix.mul_apply, Fin.sum_univ_four]
  rw [gradingOperator_eq_diagonal, h1]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [mkMid4]

private lemma car_diag2_decomp :
    (1 : M4R) - (2 : ℝ) • number2 =
      -InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator + mkMid4 (-1) 0 0 1 := by
  have h2 : number2 = !![0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1] := by
    unfold number2
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [a2, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]
  rw [gradingOperator_eq_diagonal, h2]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [mkMid4]

/-- Exact bracket preservation on the `sl₂` core `{-2, 0, +2}`. -/
theorem Phi_preserves_sl2_core :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
        (Phi (pairingCreation punitCubicJordanDatum 1))
        (Phi (pairingAnnihilation punitCubicJordanDatum 1)) =
      Phi (fiveGradedBracket punitCubicJordanDatum
        (pairingCreation punitCubicJordanDatum 1)
        (pairingAnnihilation punitCubicJordanDatum 1)) ∧
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
        (Phi (gradingOperator punitCubicJordanDatum 1))
        (Phi (pairingCreation punitCubicJordanDatum 1)) =
      Phi (fiveGradedBracket punitCubicJordanDatum
        (gradingOperator punitCubicJordanDatum 1)
        (pairingCreation punitCubicJordanDatum 1)) ∧
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
        (Phi (gradingOperator punitCubicJordanDatum 1))
        (Phi (pairingAnnihilation punitCubicJordanDatum 1)) =
      Phi (fiveGradedBracket punitCubicJordanDatum
        (gradingOperator punitCubicJordanDatum 1)
        (pairingAnnihilation punitCubicJordanDatum 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [pairing_commutator_eq_grading, Phi_pairingCreation, Phi_pairingAnnihilation,
      Phi_gradingOperator, one_smul, one_smul, one_smul, pair_extreme_bracket]
  · rw [grading_action_on_pairingCreation, Phi_gradingOperator, Phi_pairingCreation,
      one_smul, one_smul, grading_pairCreation, Phi_pairingCreation]
  · rw [grading_action_on_pairingAnnihilation, Phi_gradingOperator, Phi_pairingAnnihilation,
      one_smul, one_smul, grading_pairAnnihilation, Phi_pairingAnnihilation]

/-- Exact Heisenberg `g_{+1} × g_{+1} → g_{+2}` bracket preservation (`[a1Dag, a2Dag] = 2 • pairCreation`),
and CAR-sign-flipped `g_{-1} × g_{-1} → g_{-2}` bracket (`[a1, a2] = -2 • pairAnnihilation`). -/
theorem Phi_heisenberg_brackets (x y : FreudenthalCharge PUnit.{1}) :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
        (Phi (qpCreation punitCubicJordanDatum x))
        (Phi (qpCreation punitCubicJordanDatum y)) =
      Phi (fiveGradedBracket punitCubicJordanDatum
        (qpCreation punitCubicJordanDatum x)
        (qpCreation punitCubicJordanDatum y)) ∧
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
        (Phi (qpAnnihilation punitCubicJordanDatum x))
        (Phi (qpAnnihilation punitCubicJordanDatum y)) =
      -Phi (fiveGradedBracket punitCubicJordanDatum
        (qpAnnihilation punitCubicJordanDatum x)
        (qpAnnihilation punitCubicJordanDatum y)) := by
  have hsymp : FreudenthalCharge.symplecticForm punitCubicJordanDatum x y =
      x.alpha * y.beta - x.beta * y.alpha := by
    simp [FreudenthalCharge.symplecticForm, punitCubicJordanDatum]
  constructor
  · rw [qpCreation_pairing_condensation, Phi_qpCreation, Phi_qpCreation, Phi_pairingCreation,
      hsymp]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm,
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
        a1Dag, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]; try ring)
  · rw [qpAnnihilation_pairing_condensation, Phi_qpAnnihilation, Phi_qpAnnihilation,
      Phi_pairingAnnihilation, hsymp]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm,
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation,
        a1, a2, Matrix.mul_apply, Fin.sum_univ_four]; try ring)

private lemma symplecticForm_zero_left (D : CubicJordanDatum J) (x : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D 0 x = 0 := by
  change (0 : ℝ) * x.beta - (0 : ℝ) * x.alpha + (D.traceBilin 0) x.y - (D.traceBilin 0) x.x = 0
  simp

private lemma symplecticForm_zero_right (D : CubicJordanDatum J) (x : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D x 0 = 0 := by
  change x.alpha * (0 : ℝ) - x.beta * (0 : ℝ) + (D.traceBilin x.x) 0 - (D.traceBilin x.y) 0 = 0
  simp

private lemma mixedSymplecticBracket_zero_left (D : CubicJordanDatum J) (x : FreudenthalCharge J) :
    mixedSymplecticBracket D 0 x = 0 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  have h0a : (0 : FreudenthalCharge J).alpha = 0 := rfl
  have h0b : (0 : FreudenthalCharge J).beta = 0 := rfl
  have h0x : (0 : FreudenthalCharge J).x = 0 := rfl
  have h0y : (0 : FreudenthalCharge J).y = 0 := rfl
  rw [show (0 : SymplecticTKKZero D).1 z = 0 from rfl]
  apply FreudenthalCharge.ext <;>
    simp [h0a, h0b, h0x, h0y]

private lemma mixedSymplecticBracket_zero_right (D : CubicJordanDatum J) (x : FreudenthalCharge J) :
    mixedSymplecticBracket D x 0 = 0 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  have h0a : (0 : FreudenthalCharge J).alpha = 0 := rfl
  have h0b : (0 : FreudenthalCharge J).beta = 0 := rfl
  have h0x : (0 : FreudenthalCharge J).x = 0 := rfl
  have h0y : (0 : FreudenthalCharge J).y = 0 := rfl
  rw [show (0 : SymplecticTKKZero D).1 z = 0 from rfl]
  apply FreudenthalCharge.ext <;>
    simp [h0a, h0b, h0x, h0y]

/-- Exact `g_0` multipole Lie algebra homomorphism and action on `g_{±1}`. -/
theorem Phi_preserves_multipole_brackets
    (T U : SymplecticTKKZero punitCubicJordanDatum)
    (x y : FreudenthalCharge PUnit.{1}) :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
        (Phi (multipoleOperator punitCubicJordanDatum T))
        (Phi (multipoleOperator punitCubicJordanDatum U)) =
      Phi (fiveGradedBracket punitCubicJordanDatum
        (multipoleOperator punitCubicJordanDatum T)
        (multipoleOperator punitCubicJordanDatum U)) ∧
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
        (Phi (multipoleOperator punitCubicJordanDatum T))
        (Phi (qpCreation punitCubicJordanDatum y)) =
      Phi (fiveGradedBracket punitCubicJordanDatum
        (multipoleOperator punitCubicJordanDatum T)
        (qpCreation punitCubicJordanDatum y)) ∧
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
        (Phi (multipoleOperator punitCubicJordanDatum T))
        (Phi (qpAnnihilation punitCubicJordanDatum x)) =
      Phi (fiveGradedBracket punitCubicJordanDatum
        (multipoleOperator punitCubicJordanDatum T)
        (qpAnnihilation punitCubicJordanDatum x)) := by
  have hT := symplectic_trace_zero T
  have hT_act : ∀ z : FreudenthalCharge PUnit.{1},
      T.1 z = z.alpha • T.1 eAlpha + z.beta • T.1 eBeta := by
    intro z
    calc
      T.1 z = T.1 (z.alpha • eAlpha + z.beta • eBeta) := by
        rw [← charge_punit_decomp z]
      _ = z.alpha • T.1 eAlpha + z.beta • T.1 eBeta := by
        rw [map_add, map_smul, map_smul]
  have hU_act : ∀ z : FreudenthalCharge PUnit.{1},
      U.1 z = z.alpha • U.1 eAlpha + z.beta • U.1 eBeta := by
    intro z
    calc
      U.1 z = U.1 (z.alpha • eAlpha + z.beta • eBeta) := by
        rw [← charge_punit_decomp z]
      _ = z.alpha • U.1 eAlpha + z.beta • U.1 eBeta := by
        rw [map_add, map_smul, map_smul]
  have hT_alpha : ∀ z : FreudenthalCharge PUnit.{1},
      (T.1 z).alpha = z.alpha * (T.1 eAlpha).alpha + z.beta * (T.1 eBeta).alpha := by
    intro z; rw [hT_act z, alpha_add, alpha_smul, alpha_smul]
  have hT_beta : ∀ z : FreudenthalCharge PUnit.{1},
      (T.1 z).beta = z.alpha * (T.1 eAlpha).beta + z.beta * (T.1 eBeta).beta := by
    intro z; rw [hT_act z, beta_add, beta_smul, beta_smul]
  have hU_alpha : ∀ z : FreudenthalCharge PUnit.{1},
      (U.1 z).alpha = z.alpha * (U.1 eAlpha).alpha + z.beta * (U.1 eBeta).alpha := by
    intro z; rw [hU_act z, alpha_add, alpha_smul, alpha_smul]
  have hU_beta : ∀ z : FreudenthalCharge PUnit.{1},
      (U.1 z).beta = z.alpha * (U.1 eAlpha).beta + z.beta * (U.1 eBeta).beta := by
    intro z; rw [hU_act z, beta_add, beta_smul, beta_smul]
  refine ⟨?_, ?_, ?_⟩
  · have hfb : fiveGradedBracket punitCubicJordanDatum
        (multipoleOperator punitCubicJordanDatum T)
        (multipoleOperator punitCubicJordanDatum U) =
        multipoleOperator punitCubicJordanDatum ⁅T, U⁆ := by
      apply FiveGradedCarrier.ext <;>
        dsimp [fiveGradedBracket, multipoleOperator, injSympZero] <;>
        (try simp only [add_zero, sub_zero, sub_self, neg_zero, smul_zero, mul_zero,
          map_zero, symplecticForm_zero_left, mixedSymplecticBracket_zero_left])
    rw [hfb, Phi_multipoleOperator, Phi_multipoleOperator, Phi_multipoleOperator,
      sympToM4R_eq_mkMid4, sympToM4R_eq_mkMid4, sympToM4R_eq_mkMid4]
    have h11 : ((⁅T, U⁆ : SymplecticTKKZero punitCubicJordanDatum).1 eBeta).beta =
        (T.1 (U.1 eBeta)).beta - (U.1 (T.1 eBeta)).beta := by
      rw [show (⁅T, U⁆ : SymplecticTKKZero punitCubicJordanDatum).1 = T.1 * U.1 - U.1 * T.1 from rfl]
      rfl
    have h12 : ((⁅T, U⁆ : SymplecticTKKZero punitCubicJordanDatum).1 eAlpha).beta =
        (T.1 (U.1 eAlpha)).beta - (U.1 (T.1 eAlpha)).beta := by
      rw [show (⁅T, U⁆ : SymplecticTKKZero punitCubicJordanDatum).1 = T.1 * U.1 - U.1 * T.1 from rfl]
      rfl
    have h21 : ((⁅T, U⁆ : SymplecticTKKZero punitCubicJordanDatum).1 eBeta).alpha =
        (T.1 (U.1 eBeta)).alpha - (U.1 (T.1 eBeta)).alpha := by
      rw [show (⁅T, U⁆ : SymplecticTKKZero punitCubicJordanDatum).1 = T.1 * U.1 - U.1 * T.1 from rfl]
      rfl
    have h22 : ((⁅T, U⁆ : SymplecticTKKZero punitCubicJordanDatum).1 eAlpha).alpha =
        (T.1 (U.1 eAlpha)).alpha - (U.1 (T.1 eAlpha)).alpha := by
      rw [show (⁅T, U⁆ : SymplecticTKKZero punitCubicJordanDatum).1 = T.1 * U.1 - U.1 * T.1 from rfl]
      rfl
    rw [h11, h12, h21, h22,
      hT_beta (U.1 eBeta), hU_beta (T.1 eBeta),
      hT_beta (U.1 eAlpha), hU_beta (T.1 eAlpha),
      hT_alpha (U.1 eBeta), hU_alpha (T.1 eBeta),
      hT_alpha (U.1 eAlpha), hU_alpha (T.1 eAlpha)]
    generalize (T.1 eBeta).beta = t11
    generalize (T.1 eAlpha).beta = t12
    generalize (T.1 eBeta).alpha = t21
    generalize (T.1 eAlpha).alpha = t22
    generalize (U.1 eBeta).beta = u11
    generalize (U.1 eAlpha).beta = u12
    generalize (U.1 eBeta).alpha = u21
    generalize (U.1 eAlpha).alpha = u22
    ext i j
    fin_cases i <;> fin_cases j <;>
      (norm_num [mkMid4, InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm,
        Matrix.mul_apply, Fin.sum_univ_four]; try ring)
  · have hfb : fiveGradedBracket punitCubicJordanDatum
        (multipoleOperator punitCubicJordanDatum T)
        (qpCreation punitCubicJordanDatum y) =
        qpCreation punitCubicJordanDatum (T.1 y) := by
      unfold multipoleOperator injSympZero qpCreation
      rw [fiveGradedBracket_skew, fiveGradedBracket_chargePlus_zeroBlock]
      apply FiveGradedCarrier.ext <;>
        dsimp [injChargePlus] <;>
        simp only [neg_zero, zero_smul, zero_sub, neg_neg]
    rw [hfb, Phi_multipoleOperator, Phi_qpCreation, Phi_qpCreation, sympToM4R_eq_mkMid4,
      hT_alpha y, hT_beta y, mkMid4_traceless_decomp _ _ _ _ hT]
    have ht : (T.1 eAlpha).alpha = -(T.1 eBeta).beta := eq_neg_of_add_eq_zero_left hT
    rw [ht]
    simp only [comm_add_left_m4r, comm_add_right, comm_smul_left, comm_smul_right,
      comm_H0_a1Dag, comm_E12_a1Dag, comm_E21_a1Dag,
      comm_H0_a2Dag, comm_E12_a2Dag, comm_E21_a2Dag]
    module
  · have hfb : fiveGradedBracket punitCubicJordanDatum
        (multipoleOperator punitCubicJordanDatum T)
        (qpAnnihilation punitCubicJordanDatum x) =
        qpAnnihilation punitCubicJordanDatum (T.1 x) := by
      unfold multipoleOperator injSympZero qpAnnihilation
      rw [fiveGradedBracket_skew, fiveGradedBracket_chargeMinus_zeroBlock]
      apply FiveGradedCarrier.ext <;>
        dsimp [injChargeMinus] <;>
        simp only [neg_zero, zero_smul, zero_sub, neg_neg]
    rw [hfb, Phi_multipoleOperator, Phi_qpAnnihilation, Phi_qpAnnihilation, sympToM4R_eq_mkMid4,
      hT_alpha x, hT_beta x, mkMid4_traceless_decomp _ _ _ _ hT]
    have ht : (T.1 eAlpha).alpha = -(T.1 eBeta).beta := eq_neg_of_add_eq_zero_left hT
    rw [ht]
    simp only [comm_add_left_m4r, comm_sub_right_m4r, comm_smul_left, comm_smul_right,
      comm_H0_a1, comm_E12_a1, comm_E21_a1,
      comm_H0_a2, comm_E12_a2, comm_E21_a2]
    module

/-- **Degree-0 Mixed CAR Commutator Formula & Exact Identification with `Phi`**:
1. In `M4R`, `[Phi (qpAnnihilation x), Phi (qpCreation y)]` decomposes directly in terms of the
   CAR number/Pauli-blocking operators `(1 - 2 • number1)`, `(1 - 2 • number2)`, and mode-exchange
   operators `comm a1 a2Dag`, `comm a2 a1Dag`.
2. This associative CAR commutator equals `Phi (fiveGradedBracket D (qpAnnihilation x) (qpCreation y))`
   identically (zero defect under the symplectic-dual embedding `Phi`).
3. By contrast, for the untwisted mode-aligned map `x ↦ x.alpha • a1 + x.beta • a2`, the
   degree-0 CAR commutator differs from `Phi (fiveGradedBracket D (qpAnnihilation x) (qpCreation y))`
   by an explicit nonvanishing Pauli-blocking defect comparing symmetric occupation `(x.alpha y.alpha + x.beta y.beta)`
   with the skew-symmetric Freudenthal pairing `ω(x, y)`. -/
theorem degree_zero_commutator_car_decomposition_and_defect
    (x y : FreudenthalCharge PUnit.{1}) :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
        (Phi (qpAnnihilation punitCubicJordanDatum x))
        (Phi (qpCreation punitCubicJordanDatum y)) =
      (x.beta * y.alpha) • ((1 : M4R) - (2 : ℝ) • number1) -
        (x.alpha * y.beta) • ((1 : M4R) - (2 : ℝ) • number2) +
        (x.beta * y.beta) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm a1 a2Dag -
        (x.alpha * y.alpha) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm a2 a1Dag ∧
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
        (Phi (qpAnnihilation punitCubicJordanDatum x))
        (Phi (qpCreation punitCubicJordanDatum y)) =
      Phi (fiveGradedBracket punitCubicJordanDatum
        (qpAnnihilation punitCubicJordanDatum x)
        (qpCreation punitCubicJordanDatum y)) ∧
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
        (x.alpha • a1 + x.beta • a2)
        (y.alpha • a1Dag + y.beta • a2Dag) -
      Phi (fiveGradedBracket punitCubicJordanDatum
        (qpAnnihilation punitCubicJordanDatum x)
        (qpCreation punitCubicJordanDatum y)) =
      ((x.alpha * y.alpha - x.beta * y.alpha) • ((1 : M4R) - (2 : ℝ) • number1) +
        (x.beta * y.beta + x.alpha * y.beta) • ((1 : M4R) - (2 : ℝ) • number2)) +
        ((x.alpha * y.beta - x.beta * y.beta) •
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm a1 a2Dag +
         (x.beta * y.alpha + x.alpha * y.alpha) •
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm a2 a1Dag) := by
  have h1 : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
      (Phi (qpAnnihilation punitCubicJordanDatum x))
      (Phi (qpCreation punitCubicJordanDatum y)) =
      (x.beta * y.alpha) • ((1 : M4R) - (2 : ℝ) • number1) -
        (x.alpha * y.beta) • ((1 : M4R) - (2 : ℝ) • number2) +
        (x.beta * y.beta) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm a1 a2Dag -
        (x.alpha * y.alpha) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm a2 a1Dag := by
    rw [Phi_qpAnnihilation, Phi_qpCreation]
    simp only [comm_sub_left_m4r, comm_add_right, comm_smul_left, comm_smul_right,
      comm_a1_a1Dag_eq, comm_a2_a2Dag_eq]
    module
  have h2 : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
      (Phi (qpAnnihilation punitCubicJordanDatum x))
      (Phi (qpCreation punitCubicJordanDatum y)) =
      Phi (fiveGradedBracket punitCubicJordanDatum
        (qpAnnihilation punitCubicJordanDatum x)
        (qpCreation punitCubicJordanDatum y)) := by
    rw [h1, car_diag1_decomp, car_diag2_decomp, comm_a1_a2Dag_mkMid4, comm_a2_a1Dag_mkMid4]
    unfold qpAnnihilation qpCreation
    rw [fiveGradedBracket_chargeMinus_chargePlus]
    have hω : FreudenthalCharge.symplecticForm punitCubicJordanDatum x y =
        x.alpha * y.beta - x.beta * y.alpha := by
      simp [FreudenthalCharge.symplecticForm, punitCubicJordanDatum]
    have hm11 : ((mixedSymplecticBracket punitCubicJordanDatum x y :
          SymplecticTKKZero punitCubicJordanDatum).1 eBeta).beta =
        x.alpha * y.beta + y.alpha * x.beta := by
      simp only [mixedSymplecticBracket_val, symplecticRankTwo_apply,
        FreudenthalCharge.symplecticForm, punitCubicJordanDatum, eBeta,
        beta_add, beta_smul]
      ring
    have hm12 : ((mixedSymplecticBracket punitCubicJordanDatum x y :
          SymplecticTKKZero punitCubicJordanDatum).1 eAlpha).beta =
        -(2 * (x.beta * y.beta)) := by
      simp only [mixedSymplecticBracket_val, symplecticRankTwo_apply,
        FreudenthalCharge.symplecticForm, punitCubicJordanDatum, eAlpha,
        beta_add, beta_smul]
      ring
    have hm21 : ((mixedSymplecticBracket punitCubicJordanDatum x y :
          SymplecticTKKZero punitCubicJordanDatum).1 eBeta).alpha =
        2 * (x.alpha * y.alpha) := by
      simp only [mixedSymplecticBracket_val, symplecticRankTwo_apply,
        FreudenthalCharge.symplecticForm, punitCubicJordanDatum, eBeta,
        alpha_add, alpha_smul]
      ring
    have hm22 : ((mixedSymplecticBracket punitCubicJordanDatum x y :
          SymplecticTKKZero punitCubicJordanDatum).1 eAlpha).alpha =
        -(x.alpha * y.beta + y.alpha * x.beta) := by
      simp only [mixedSymplecticBracket_val, symplecticRankTwo_apply,
        FreudenthalCharge.symplecticForm, punitCubicJordanDatum, eAlpha,
        alpha_add, alpha_smul]
      ring
    change
      (x.beta * y.alpha) • (-InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
          mkMid4 1 0 0 (-1)) -
        (x.alpha * y.beta) • (-InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
          mkMid4 (-1) 0 0 1) +
        (x.beta * y.beta) • mkMid4 0 (-2) 0 0 -
        (x.alpha * y.alpha) • mkMid4 0 0 (-2) 0 =
      (0 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation +
        ((0 : FreudenthalCharge PUnit.{1}).beta • a1 -
          (0 : FreudenthalCharge PUnit.{1}).alpha • a2) +
        sympToM4R (mixedSymplecticBracket punitCubicJordanDatum x y) +
        (FreudenthalCharge.symplecticForm punitCubicJordanDatum x y) •
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
        ((0 : FreudenthalCharge PUnit.{1}).alpha • a1Dag +
          (0 : FreudenthalCharge PUnit.{1}).beta • a2Dag) +
        (0 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation
    rw [sympToM4R_eq_mkMid4, hω, hm11, hm12, hm21, hm22,
      charge_zero_alpha, charge_zero_beta]
    simp only [zero_smul, sub_zero, add_zero, zero_add]
    have hmid :
        (x.beta * y.alpha) • mkMid4 1 0 0 (-1) -
          (x.alpha * y.beta) • mkMid4 (-1) 0 0 1 +
          (x.beta * y.beta) • mkMid4 0 (-2) 0 0 -
          (x.alpha * y.alpha) • mkMid4 0 0 (-2) 0 =
        mkMid4 (x.alpha * y.beta + y.alpha * x.beta) (-(2 * (x.beta * y.beta)))
          (2 * (x.alpha * y.alpha)) (-(x.alpha * y.beta + y.alpha * x.beta)) := by
      simp only [sub_eq_add_neg, ← mkMid4_smul, mkMid4_neg, ← mkMid4_add]
      congr 1 <;> ring
    rw [smul_add, smul_add, smul_neg, smul_neg]
    calc
      -((x.beta * y.alpha) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator) +
          (x.beta * y.alpha) • mkMid4 1 0 0 (-1) -
          (-((x.alpha * y.beta) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator) +
            (x.alpha * y.beta) • mkMid4 (-1) 0 0 1) +
          (x.beta * y.beta) • mkMid4 0 (-2) 0 0 -
          (x.alpha * y.alpha) • mkMid4 0 0 (-2) 0
        = ((x.alpha * y.beta - x.beta * y.alpha) •
              InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator) +
            ((x.beta * y.alpha) • mkMid4 1 0 0 (-1) -
              (x.alpha * y.beta) • mkMid4 (-1) 0 0 1 +
              (x.beta * y.beta) • mkMid4 0 (-2) 0 0 -
              (x.alpha * y.alpha) • mkMid4 0 0 (-2) 0) := by
          module
      _ = ((x.alpha * y.beta - x.beta * y.alpha) •
              InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator) +
            mkMid4 (x.alpha * y.beta + y.alpha * x.beta) (-(2 * (x.beta * y.beta)))
              (2 * (x.alpha * y.alpha)) (-(x.alpha * y.beta + y.alpha * x.beta)) := by
          rw [hmid]
      _ = _ := by abel
  refine ⟨h1, h2, ?_⟩
  rw [← h2, h1]
  have h3 : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
      (x.alpha • a1 + x.beta • a2) (y.alpha • a1Dag + y.beta • a2Dag) =
      (x.alpha * y.alpha) • ((1 : M4R) - (2 : ℝ) • number1) +
        (x.beta * y.beta) • ((1 : M4R) - (2 : ℝ) • number2) +
        (x.alpha * y.beta) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm a1 a2Dag +
        (x.beta * y.alpha) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm a2 a1Dag := by
    simp only [comm_add_left_m4r, comm_add_right, comm_smul_left, comm_smul_right,
      comm_a1_a1Dag_eq, comm_a2_a2Dag_eq]
    module
  rw [h3]
  module

/-- **Freudenthal Mixed-Jacobi Obstruction vs. Associative CAR Jacobi Theorem**:
1. On `FiveGradedCarrier D`, the mixed Jacobiator of `(pairingCreation 1, pairingAnnihilation 1, qpCreation y)`
   equals `qpCreation (-2 • y)` (strictly nonzero whenever `y ≠ 0`), proving that `fiveGradedBracket`
   carries a genuine `(-2, +2, +1)` mixed-Jacobi obstruction.
2. In `M4R`, the image triple satisfies exact Jacobi `= 0` (`comm_jacobi`), because the CAR sign
   `[pairAnnihilation, Φ(qpCreation y)] = -Φ([pairingAnnihilation 1, qpCreation y])` cancels
   the discrepancy. -/
theorem freudenthal_mixed_jacobi_obstruction_vs_car_jacobi
    (D : CubicJordanDatum J) (y : FreudenthalCharge J)
    (yp : FreudenthalCharge PUnit.{1}) :
    (fiveGradedBracket D (pairingCreation D 1)
        (fiveGradedBracket D (pairingAnnihilation D 1) (qpCreation D y)) +
      fiveGradedBracket D (pairingAnnihilation D 1)
        (fiveGradedBracket D (qpCreation D y) (pairingCreation D 1)) +
      fiveGradedBracket D (qpCreation D y)
        (fiveGradedBracket D (pairingCreation D 1) (pairingAnnihilation D 1)) =
      qpCreation D ((-2 : ℝ) • y)) ∧
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
        (Phi (pairingAnnihilation punitCubicJordanDatum 1))
        (Phi (qpCreation punitCubicJordanDatum yp)) =
      -Phi (fiveGradedBracket punitCubicJordanDatum
        (pairingAnnihilation punitCubicJordanDatum 1)
        (qpCreation punitCubicJordanDatum yp)) ∧
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
        (Phi (pairingCreation punitCubicJordanDatum 1))
        (InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
          (Phi (pairingAnnihilation punitCubicJordanDatum 1))
          (Phi (qpCreation punitCubicJordanDatum yp))) +
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
        (Phi (pairingAnnihilation punitCubicJordanDatum 1))
        (InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
          (Phi (qpCreation punitCubicJordanDatum yp))
          (Phi (pairingCreation punitCubicJordanDatum 1))) +
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
        (Phi (qpCreation punitCubicJordanDatum yp))
        (InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
          (Phi (pairingCreation punitCubicJordanDatum 1))
          (Phi (pairingAnnihilation punitCubicJordanDatum 1))) = 0 := by
  refine ⟨?_, ?_, comm_jacobi _ _ _⟩
  · have h1 : fiveGradedBracket D (pairingAnnihilation D 1) (qpCreation D y) =
        qpAnnihilation D y := by
      unfold pairingAnnihilation qpCreation qpAnnihilation
      exact extreme_minus2_action_plus1 D y
    have h2 : fiveGradedBracket D (pairingCreation D 1) (qpAnnihilation D y) =
        qpCreation D (-y) := by
      unfold pairingCreation qpAnnihilation qpCreation
      exact extreme_plus2_action_minus1 D y
    have h3 : fiveGradedBracket D (qpCreation D y) (pairingCreation D 1) = 0 := by
      apply FiveGradedCarrier.ext <;>
        dsimp [fiveGradedBracket, qpCreation, injChargePlus, pairingCreation, genEplus] <;>
        simp only [add_zero, sub_self, neg_zero, smul_zero, zero_smul, mul_zero,
          zero_mul, symplecticForm_zero_left, symplecticForm_zero_right,
          mixedSymplecticBracket_zero_left, mixedSymplecticBracket_zero_right, lie_zero]
    have h4 : fiveGradedBracket D (pairingAnnihilation D 1) (0 : FiveGradedCarrier D) = 0 := by
      apply FiveGradedCarrier.ext <;>
        dsimp [fiveGradedBracket, pairingAnnihilation, genEminus] <;>
        simp only [add_zero, sub_self, neg_zero, smul_zero, mul_zero,
          zero_mul, symplecticForm_zero_right, mixedSymplecticBracket_zero_right, lie_zero]
    have h5 : fiveGradedBracket D (qpCreation D y)
        (fiveGradedBracket D (pairingCreation D 1) (pairingAnnihilation D 1)) =
        qpCreation D (-y) := by
      rw [pairing_commutator_eq_grading, fiveGradedBracket_skew,
        grading_action_on_qpCreation]
      apply FiveGradedCarrier.ext <;>
        dsimp [qpCreation, injChargePlus] <;>
        simp only [neg_zero]
    rw [h1, h2, h3, h4, h5]
    apply FiveGradedCarrier.ext <;>
      dsimp [qpCreation, injChargePlus] <;>
      simp only [add_zero]
    module
  · unfold pairingAnnihilation qpCreation
    rw [extreme_minus2_action_plus1,
      show genEminus punitCubicJordanDatum 1 = pairingAnnihilation punitCubicJordanDatum 1 from rfl,
      show injChargePlus punitCubicJordanDatum yp = qpCreation punitCubicJordanDatum yp from rfl,
      show injChargeMinus punitCubicJordanDatum yp = qpAnnihilation punitCubicJordanDatum yp from rfl,
      Phi_pairingAnnihilation, Phi_qpCreation, Phi_qpAnnihilation, one_smul]
    simp only [comm_add_right, comm_smul_right, pairAnnihilation_comm_a1Dag,
      pairAnnihilation_comm_a2Dag]
    module

end ConcreteBridge

end InfoGeometry.Nuclear.FiveGraded
