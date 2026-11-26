/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
import InfoGeometry.Algebra.TwoSheetDiracMassEntropy
import InfoGeometry.Algebra.NoncommutativeUnifiedDiracHiggsZornTower
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Noncommutative Dirac Sheet-Mixing & Extensive Entropy Tower ($\mathcal{D}_1$–$\mathcal{D}_3$)

Formalizes over arbitrary noncommutative $\star$-rings `[Ring A] [StarRing A]`:
1. **$\mathcal{D}_1$** (`dirac_sheet_mixing_and_chiral_asymmetry`):
   Two-sheeted chiral Dirac mass operator $\mathcal{D}_M = \bigl(\begin{smallmatrix} 0 & M^\star \\ M & 0 \end{smallmatrix}\bigr)$,
   self-adjointness, chiral anticommutation with $\Gamma_1$, vanishing supertrace,
   Klein–Gordon square, and chiral mass-squared asymmetry $\Lambda(\mathcal{D}_M^2) = \⁅M^\star, M⁆$.
2. **$\mathcal{D}_2$** (`all_scales_dirac_mass_sq_additive`):
   Inductive Clifford-graded Dirac mass tower $\mathfrak{D}_n(M) \in \mathcal{C}\ell_n(A)$,
   self-adjointness, additive Klein–Gordon scaling $\mathfrak{D}_n(M)^2 = \iota_n(n \bullet M^\star M)$,
   and extensive trace $\mathrm{Tr}_{2^n}(\mathfrak{D}_n(M)^2) = (n \cdot 2^n) \bullet M^\star M$
   for normal $M$.
3. **$\mathcal{D}_3$** (`cantorProj_compress_diracTowerOp_zero`,
   `cantorProj_compress_diracTowerOp_sq`, `entropyTowerOp_extensive_trace`):
   Cantor vacuum vanishing of $\mathfrak{D}_n(M)$, Zitterbewegung vacuum energy of
   $\mathfrak{D}_n(M)^2$, and unconditional extensive trace law for the primitive entropy
   coproduct `entropyTowerOp`.

Reuses `NoncommutativeCliffordPrimitives`, `TwoSheetDiracMassEntropy`, and
`NoncommutativeUnifiedDiracHiggsZornTower`.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.TwoSheetDiracMassEntropy
open InfoGeometry.Algebra.NoncommutativeUnifiedDiracHiggsZornTower hiding towerTrace towerTrace_add

namespace InfoGeometry.Algebra.NoncommutativeDiracSheetMixingAndEntropyTower

def lefschetzSuperTrace {A : Type*} [Ring A] (M : Matrix (Fin 2) (Fin 2) A) : A :=
  M 0 0 - M 1 1

/-!
## Archetype $\mathcal{D}_1$: Two-Sheeted Chiral Dirac Operator & Noncommutative Mass Mixing
-/

section ArchetypeD1_TwoSheetedChiralDirac

variable {A : Type*} [Ring A] [StarRing A]

/-- Chiral grading $\Gamma_1 = \mathrm{diag}(1, -1)$ separating left-handed and right-handed sheets. -/
def chiralGrading : Matrix (Fin 2) (Fin 2) A :=
  mat2 1 0 0 (-1)

/-- Two-sheeted chiral Dirac mass operator $\mathcal{D}_M = \bigl(\begin{smallmatrix} 0 & M^\star \\ M & 0 \end{smallmatrix}\bigr) \in M_2(A)$
mixing left and right sheets via an arbitrary noncommutative operator $M \in A$. -/
def diracSheetMix (M : A) : Matrix (Fin 2) (Fin 2) A :=
  mat2 0 (star M) M 0

/-- **Two-Sheeted Chiral Dirac & Mass-Mixing Theorem ($\mathcal{D}_1$)**:
For any noncommutative mass operator $M \in A$:
1. Self-adjointness: $\mathcal{D}_M^\dagger = \mathcal{D}_M$,
2. Chiral anticommutation: $\{\Gamma_1, \mathcal{D}_M\} = 0$ with $\Gamma_1^2 = 1$,
3. Vanishing supertrace: $\Lambda(\mathcal{D}_M) = 0$,
4. Noncommutative Klein–Gordon mass-squared: $\mathcal{D}_M^2 = \mathrm{diag}(M^\star M, M M^\star)$,
5. Chiral mass-squared asymmetry equals the self-commutator: $\Lambda(\mathcal{D}_M^2) = \⁅M^\star, M⁆$. -/
theorem dirac_sheet_mixing_and_chiral_asymmetry (M : A) :
    let D := diracSheetMix M
    let Γ := (chiralGrading : Matrix (Fin 2) (Fin 2) A)
    Dᴴ = D ∧
    Γ * Γ = 1 ∧
    Γ * D + D * Γ = 0 ∧
    lefschetzSuperTrace D = 0 ∧
    D * D = mat2 (star M * M) 0 0 (M * star M) ∧
    lefschetzSuperTrace (D * D) = ⁅star M, M⁆ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [diracSheetMix]
  · apply ext_fin2 <;> simp [chiralGrading]
  · apply ext_fin2 <;> simp [chiralGrading, diracSheetMix]
  · dsimp [lefschetzSuperTrace, diracSheetMix]; exact sub_zero 0
  · apply ext_fin2 <;> simp [diracSheetMix]
  · simp only [Ring.lie_def]
    dsimp [lefschetzSuperTrace, diracSheetMix]
    simp

end ArchetypeD1_TwoSheetedChiralDirac

/-!
## Archetype $\mathcal{D}_2$: All-Scales Clifford–Dirac Mass Tower & Additive Klein–Gordon Scaling
-/

section ArchetypeD2_AllScalesDiracMassTower

universe u

variable {A : Type u} [Ring A]

lemma towerScalar_comm (n : ℕ) {x y : A} (h : x * y = y * x) :
    towerScalar n x * towerScalar n y = towerScalar n y * towerScalar n x := by
  rw [← towerScalar_mul, h, towerScalar_mul]

lemma towerTrace_towerScalar : ∀ (n : ℕ) (x : A),
    towerTrace (towerScalar n x) = (2 ^ n) • x
  | 0,     x => by simp [towerTrace, towerScalar]
  | n + 1, x => by
      simp only [towerTrace, towerScalar, diagEmbed, mat2_00, mat2_11]
      rw [towerTrace_towerScalar n, pow_succ', two_mul, add_nsmul]

lemma towerScalar_star [StarRing A] : ∀ (n : ℕ) (x : A),
    star (towerScalar n x) = towerScalar n (star x)
  | 0,     _ => rfl
  | n + 1, x => by apply ext_fin2 <;> simp [towerScalar, diagEmbed, towerScalar_star n]

/-- Inductive Clifford-graded Dirac mass tower $\mathfrak{D}_n(M) \in \mathcal{C}\ell_n(A)$
built via the $\mathbb{Z}_2$-graded Leibniz coproduct $D \hat{\otimes} 1 + \Gamma \hat{\otimes} D$. -/
def diracTowerOp [StarRing A] (M : A) : ∀ (n : ℕ), ClTower A n
  | 0     => (0 : A)
  | n + 1 =>
      let D_n := diracTowerOp M n
      mat2 D_n (towerScalar n (star M)) (towerScalar n M) (-D_n)

theorem diracTowerOp_selfAdjoint [StarRing A] (M : A) : ∀ (n : ℕ),
    star (diracTowerOp M n) = diracTowerOp M n
  | 0     => star_zero A
  | n + 1 => by
      apply ext_fin2 <;> simp [diracTowerOp, diracTowerOp_selfAdjoint M n, towerScalar_star]

lemma towerScalar_comm_diracTowerOp [StarRing A] (M x : A)
    (hxM : x * M = M * x) (hxMs : x * star M = star M * x) :
    ∀ (n : ℕ), towerScalar n x * diracTowerOp M n = diracTowerOp M n * towerScalar n x
  | 0     => by simp [towerScalar, diracTowerOp]
  | n + 1 => by
      have h1 := towerScalar_comm n hxM
      have h2 := towerScalar_comm n hxMs
      have ih := towerScalar_comm_diracTowerOp M x hxM hxMs n
      apply ext_fin2 <;> simp [towerScalar, diagEmbed, diracTowerOp, h1, h2, ih]

/-- **All-Scales Additive Klein–Gordon Mass-Squared & Extensive Trace Law ($\mathcal{D}_2$)**:
For any normal mass operator $M \in A$ ($M^\star M = M M^\star$) and every tensor scale $n \in \mathbb{N}$:
1. $\mathfrak{D}_n(M)^2 = \iota_n\big(n \bullet (M^\star M)\big)$ (Pythagorean/entropy additivity across scales),
2. $\mathrm{Tr}_{2^n}(\mathfrak{D}_n(M)^2) = (n \cdot 2^n) \bullet (M^\star M)$. -/
theorem all_scales_dirac_mass_sq_additive [StarRing A]
    {M : A} (hnorm : star M * M = M * star M) (n : ℕ) :
    diracTowerOp M n * diracTowerOp M n = towerScalar n (n • (star M * M)) ∧
    towerTrace (diracTowerOp M n * diracTowerOp M n) = (n * 2 ^ n) • (star M * M) := by
  have h_sq : ∀ k : ℕ,
      diracTowerOp M k * diracTowerOp M k = towerScalar k (k • (star M * M)) := by
    intro k
    induction' k with m ih
    · simp [diracTowerOp, towerScalar]
    · have hc1 : towerScalar m (star M) * diracTowerOp M m =
          diracTowerOp M m * towerScalar m (star M) :=
        towerScalar_comm_diracTowerOp M (star M) hnorm rfl m
      have hc2 : towerScalar m M * diracTowerOp M m =
          diracTowerOp M m * towerScalar m M :=
        towerScalar_comm_diracTowerOp M M rfl hnorm.symm m
      apply ext_fin2
      · simp only [diracTowerOp, towerScalar, diagEmbed, mul2_00, mat2_00, mat2_01, mat2_10]
        rw [ih, ← towerScalar_mul, ← towerScalar_add, ← succ_nsmul]
      · simp only [diracTowerOp, towerScalar, diagEmbed, mul2_01, mat2_00, mat2_01, mat2_11]
        rw [← hc1]; noncomm_ring
      · simp only [diracTowerOp, towerScalar, diagEmbed, mul2_10, mat2_00, mat2_10, mat2_11]
        rw [hc2, neg_mul, add_neg_cancel]
      · simp only [diracTowerOp, towerScalar, diagEmbed, mul2_11, mat2_01, mat2_10, mat2_11]
        rw [← towerScalar_mul, hnorm.symm, neg_mul_neg, ih, ← towerScalar_add, ← succ_nsmul']
  refine ⟨h_sq n, ?_⟩
  rw [h_sq n, towerTrace_towerScalar, smul_smul, mul_comm (2 ^ n) n]

end ArchetypeD2_AllScalesDiracMassTower

/-!
## Archetype $\mathcal{D}_3$: Vacuum Zitterbewegung & Primitive Entropy Coproduct Extensivity
-/

section ArchetypeD3_VacuumZitterbewegungAndEntropyCoproduct

universe u

variable {A : Type u} [Ring A]

def cantorProj : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (cantorProj n) 0 0 0

lemma cantorProj_idem : ∀ (n : ℕ),
    (cantorProj n : ClTower A n) * cantorProj n = cantorProj n
  | 0     => mul_one 1
  | n + 1 => by apply ext_fin2 <;> simp [cantorProj, cantorProj_idem n]

lemma cantorProj_comm_scalar : ∀ (n : ℕ) (x : A),
    cantorProj n * towerScalar n x = towerScalar n x * cantorProj n
  | 0,     _ => by simp [cantorProj, towerScalar]
  | n + 1, x => by apply ext_fin2 <;> simp [cantorProj, towerScalar, diagEmbed, cantorProj_comm_scalar n]

/-- **Pure Sheet-Mixing Vanishes in the Unmixed Cantor Vacuum**:
$\Pi_{\mathcal{C}_n} \mathfrak{D}_n(M) \Pi_{\mathcal{C}_n} = 0$ at every scale $n \in \mathbb{N}$. -/
theorem cantorProj_compress_diracTowerOp_zero [StarRing A] (M : A) : ∀ (n : ℕ),
    cantorProj n * diracTowerOp M n * cantorProj n = 0
  | 0     => by simp [cantorProj, diracTowerOp]
  | n + 1 => by
      have ih := cantorProj_compress_diracTowerOp_zero M n
      apply ext_fin2 <;> simp [cantorProj, diracTowerOp, ih]

/-- **Vacuum Zitterbewegung Energy Law**:
While $\Pi_{\mathcal{C}_n} \mathfrak{D}_n(M) \Pi_{\mathcal{C}_n} = 0$, the squared operator
$\mathfrak{D}_n(M)^2$ returns to the unmixed vacuum with extensive energy $n \bullet (M^\star M) \Pi_{\mathcal{C}_n}$. -/
theorem cantorProj_compress_diracTowerOp_sq [StarRing A]
    {M : A} (hnorm : star M * M = M * star M) (n : ℕ) :
    cantorProj n * (diracTowerOp M n * diracTowerOp M n) * cantorProj n =
      towerScalar n (n • (star M * M)) * cantorProj n := by
  obtain ⟨h_sq, _⟩ := all_scales_dirac_mass_sq_additive hnorm n
  rw [h_sq, cantorProj_comm_scalar, mul_assoc, cantorProj_idem]

/-- Primitive / entropy tensor-tower coproduct $\mathcal{S}_n(H) \in \mathcal{C}\ell_n(A)$
lifting $H \mapsto H \otimes 1 + 1 \otimes H$ across all scales. -/
def entropyTowerOp (H : A) : ∀ (n : ℕ), ClTower A n
  | 0     => (0 : A)
  | n + 1 => mat2 (entropyTowerOp H n + towerScalar n H) 0 0 (entropyTowerOp H n)

/-- **Unconditional Extensive Entropy Trace Law ($\mathcal{D}_3$)**:
For any operator $H \in A$ (with no normality or commutativity hypotheses) and every $n \in \mathbb{N}$,
$2 \bullet \mathrm{Tr}_{2^n}(\mathcal{S}_n(H)) = (n \cdot 2^n) \bullet H$. -/
theorem entropyTowerOp_extensive_trace (H : A) : ∀ (n : ℕ),
    2 • towerTrace (entropyTowerOp H n) = (n * 2 ^ n) • H
  | 0     => by simp [entropyTowerOp, towerTrace]
  | n + 1 => by
      have ih := entropyTowerOp_extensive_trace H n
      dsimp [entropyTowerOp, towerTrace]
      rw [two_nsmul, towerTrace_add n, towerTrace_towerScalar]
      have h_arith :
          (towerTrace (entropyTowerOp H n) + 2 ^ n • H + towerTrace (entropyTowerOp H n)) +
          (towerTrace (entropyTowerOp H n) + 2 ^ n • H + towerTrace (entropyTowerOp H n)) =
          (2 • towerTrace (entropyTowerOp H n) + 2 • towerTrace (entropyTowerOp H n)) +
          (2 ^ n • H + 2 ^ n • H) := by
        simp only [two_smul]; abel
      rw [h_arith, ih]
      simp only [← add_nsmul]
      congr 1
      ring

end ArchetypeD3_VacuumZitterbewegungAndEntropyCoproduct

end InfoGeometry.Algebra.NoncommutativeDiracSheetMixingAndEntropyTower
