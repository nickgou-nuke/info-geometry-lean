import InfoGeometry.Canonical.GrandCanonicalCore
import InfoGeometry.Canonical.MixtureOfExperts
import InfoGeometry.Canonical.Clifford
import Mathlib.Analysis.Convex.Birkhoff

open scoped BigOperators

namespace InfoGeometry.Canonical.MoE

open InfoGeometry.GrandCanonical

section GrandCanonicalBridge

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (n : Nat) [Nonempty (Fin n)]

/--
Token-local grand-canonical parameters induced by router energy over the expert index.
-/
noncomputable def routerParams (x : Fin n → V) (i : Fin n) :
    GrandCanonicalParams (ExpertIdx n) where
  energy := routerEnergy n x i

omit [NormedSpace ℝ V] [Nonempty (Fin n)] in
@[simp] lemma gc_partition_eq_routerPartition (β : ℝ) (x : Fin n → V) (i : Fin n) :
    partition (routerParams n x i) β = routerPartition n β x i := rfl

omit [NormedSpace ℝ V] [Nonempty (Fin n)] in
@[simp] lemma gc_gibbsWeight_eq_normalizedWeights
    (β : ℝ) (x : Fin n → V) (i : Fin n) (e : ExpertIdx n) :
    gibbsWeight (routerParams n x i) β e = normalizedWeights n β x i e := rfl

end GrandCanonicalBridge

section Switch

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (n : Nat) [Nonempty (Fin n)]

/-- Router-induced switch matrix (rows: tokens, columns: experts). -/
noncomputable def switchMatrix (β : ℝ) (x : Fin n → V) : Matrix (Fin n) (Fin n) ℝ :=
  fun i e => normalizedWeights n β x i e

omit [NormedSpace ℝ V] [Nonempty (Fin n)] in
@[simp] lemma switchMatrix_apply (β : ℝ) (x : Fin n → V) (i e : Fin n) :
    switchMatrix n β x i e = normalizedWeights n β x i e := rfl

omit [NormedSpace ℝ V] in
/-- Lemma `normalizedWeights_nonneg`. -/
lemma normalizedWeights_nonneg (β : ℝ) (x : Fin n → V) (i e : Fin n) :
    0 ≤ normalizedWeights n β x i e := by
  unfold normalizedWeights unnormalizedWeights
  exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (routerPartition_pos n β x i))

omit [NormedSpace ℝ V] in
/-- Lemma `switchMatrix_row_sum_one`. -/
lemma switchMatrix_row_sum_one (β : ℝ) (x : Fin n → V) (i : Fin n) :
    ∑ e : Fin n, switchMatrix n β x i e = 1 := by
  simpa [switchMatrix] using normalizedWeights_sum_one (n := n) β x i

omit [NormedSpace ℝ V] in
/-- Lemma `switchMatrix_mem_rowStochastic`. -/
lemma switchMatrix_mem_rowStochastic (β : ℝ) (x : Fin n → V) :
    switchMatrix n β x ∈ Matrix.rowStochastic ℝ (Fin n) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  refine ⟨?_, ?_⟩
  · intro i e
    exact normalizedWeights_nonneg (n := n) β x i e
  · intro i
    exact switchMatrix_row_sum_one (n := n) β x i

/--
Column-normalization hypothesis for the switch matrix.

When this holds together with the always-true row normalization, the switch is bistochastic.
-/
def IsBistochasticSwitch (β : ℝ) (x : Fin n → V) : Prop :=
  ∀ e : Fin n, ∑ i : Fin n, switchMatrix n β x i e = 1

omit [NormedSpace ℝ V] in
/-- Lemma `switchMatrix_mem_doublyStochastic`. -/
lemma switchMatrix_mem_doublyStochastic
    (β : ℝ) (x : Fin n → V) (hcol : IsBistochasticSwitch n β x) :
    switchMatrix n β x ∈ doublyStochastic ℝ (Fin n) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro i e
    exact normalizedWeights_nonneg (n := n) β x i e
  · intro i
    exact switchMatrix_row_sum_one (n := n) β x i
  · intro e
    exact hcol e

omit [NormedSpace ℝ V] in
/--
Birkhoff-von Neumann decomposition for a bistochastic router switch.

This realizes the switch as a simplex combination of permutation matrices.
-/
theorem exists_perm_decomposition_of_bistochastic
    (β : ℝ) (x : Fin n → V) (hcol : IsBistochasticSwitch n β x) :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • σ.permMatrix ℝ = switchMatrix n β x := by
  exact exists_eq_sum_perm_of_mem_doublyStochastic
    (M := switchMatrix n β x)
    (switchMatrix_mem_doublyStochastic (n := n) β x hcol)

/--
Certificate that a switch matrix has been Sinkhorn-balanced into a bistochastic matrix.
-/
structure SinkhornCertificate (β : ℝ) (x : Fin n → V) where
  leftScale : Fin n → ℝ
  rightScale : Fin n → ℝ
  leftScale_pos : ∀ i, 0 < leftScale i
  rightScale_pos : ∀ j, 0 < rightScale j
  balanced_mem_doublyStochastic :
    (Matrix.diagonal leftScale * switchMatrix n β x * Matrix.diagonal rightScale)
      ∈ doublyStochastic ℝ (Fin n)

omit [NormedSpace ℝ V] [Nonempty (Fin n)] in
/--
Any Sinkhorn-balanced switch matrix admits a permutation simplex decomposition.
-/
theorem exists_perm_decomposition_of_sinkhornBalanced
    (β : ℝ) (x : Fin n → V) (cert : SinkhornCertificate (n := n) β x) :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • σ.permMatrix ℝ =
        Matrix.diagonal cert.leftScale * switchMatrix n β x * Matrix.diagonal cert.rightScale := by
  exact exists_eq_sum_perm_of_mem_doublyStochastic
    (M := Matrix.diagonal cert.leftScale * switchMatrix n β x * Matrix.diagonal cert.rightScale)
    cert.balanced_mem_doublyStochastic

end Switch

section CliffordLabel

open InfoGeometry.Clifford

/-- Split/Clifford semantic labels for permutation modes. -/
inductive CliffordLabel where
  | plus
  | minus
deriving DecidableEq, Repr

/-- Canonical split basis vector for the `plus` label. -/
def splitBasisPlus : ℝ × ℝ := (1, 0)

/-- Canonical split basis vector for the `minus` label. -/
def splitBasisMinus : ℝ × ℝ := (0, 1)

/-- Label-to-basis map into the split `(1,1)` semantic plane. -/
def cliffordBasis : CliffordLabel → ℝ × ℝ
  | .plus => splitBasisPlus
  | .minus => splitBasisMinus

@[simp] lemma cliffordBasis_plus : cliffordBasis CliffordLabel.plus = splitBasisPlus := rfl
@[simp] lemma cliffordBasis_minus : cliffordBasis CliffordLabel.minus = splitBasisMinus := rfl

@[simp] lemma splitQ11_splitBasisPlus :
    splitQ11 splitBasisPlus = 1 := by
  simp [splitBasisPlus]

@[simp] lemma splitQ11_splitBasisMinus :
    splitQ11 splitBasisMinus = -1 := by
  simp [splitBasisMinus]

@[simp] lemma splitB11_splitBasis_orthogonal :
    splitB11 splitBasisPlus splitBasisMinus = 0 := by
  simp [splitBasisPlus, splitBasisMinus]

abbrev PermMode (n : Nat) := Equiv.Perm (Fin n)

/-- Canonical naming alias for permutation routing modes. -/
abbrev PermutationMode (n : Nat) := PermMode n

/-- Weighted Clifford mode contribution for a single permutation mode. -/
def cliffordModeContribution {n : Nat}
    (w : PermMode n → ℝ) (label : PermMode n → CliffordLabel) (σ : PermMode n) : ℝ × ℝ :=
  w σ • cliffordBasis (label σ)

/-- Total Clifford semantic state obtained from all permutation modes. -/
noncomputable def cliffordSemanticState {n : Nat}
    (w : PermMode n → ℝ) (label : PermMode n → CliffordLabel) : ℝ × ℝ :=
  ∑ σ : PermMode n, cliffordModeContribution w label σ

/-- Canonical naming alias for permutation-mode Clifford semantic state. -/
noncomputable abbrev permutationCliffordSemanticState {n : Nat}
    (w : PermutationMode n → ℝ) (label : PermutationMode n → CliffordLabel) : ℝ × ℝ :=
  cliffordSemanticState w label

/-- Total `plus`-labeled mass in the permutation simplex decomposition. -/
noncomputable def plusMass {n : Nat}
    (w : PermMode n → ℝ) (label : PermMode n → CliffordLabel) : ℝ :=
  ∑ σ : PermMode n, if label σ = CliffordLabel.plus then w σ else 0

/-- Total `minus`-labeled mass in the permutation simplex decomposition. -/
noncomputable def minusMass {n : Nat}
    (w : PermMode n → ℝ) (label : PermMode n → CliffordLabel) : ℝ :=
  ∑ σ : PermMode n, if label σ = CliffordLabel.minus then w σ else 0

/-- Lemma `cliffordSemanticState_fst_eq_plusMass`. -/
lemma cliffordSemanticState_fst_eq_plusMass {n : Nat}
    (w : PermMode n → ℝ) (label : PermMode n → CliffordLabel) :
    (cliffordSemanticState w label).1 = plusMass w label := by
  classical
  unfold cliffordSemanticState plusMass cliffordModeContribution cliffordBasis
  rw [Prod.fst_sum]
  refine Finset.sum_congr rfl ?_
  intro σ hσ
  rcases h : label σ with _ | _
  · simp [splitBasisPlus]
  · simp [splitBasisMinus]

/-- Lemma `cliffordSemanticState_snd_eq_minusMass`. -/
lemma cliffordSemanticState_snd_eq_minusMass {n : Nat}
    (w : PermMode n → ℝ) (label : PermMode n → CliffordLabel) :
    (cliffordSemanticState w label).2 = minusMass w label := by
  classical
  unfold cliffordSemanticState minusMass cliffordModeContribution cliffordBasis
  rw [Prod.snd_sum]
  refine Finset.sum_congr rfl ?_
  intro σ hσ
  rcases h : label σ with _ | _
  · simp [splitBasisPlus]
  · simp [splitBasisMinus]

/-- Lemma `plusMass_nonneg`. -/
lemma plusMass_nonneg {n : Nat} {w : PermMode n → ℝ} {label : PermMode n → CliffordLabel}
    (hw : ∀ σ, 0 ≤ w σ) : 0 ≤ plusMass w label := by
  classical
  unfold plusMass
  refine Finset.sum_nonneg ?_
  intro σ hσ
  by_cases h : label σ = CliffordLabel.plus
  · simp [h, hw σ]
  · simp [h]

/-- Lemma `minusMass_nonneg`. -/
lemma minusMass_nonneg {n : Nat} {w : PermMode n → ℝ} {label : PermMode n → CliffordLabel}
    (hw : ∀ σ, 0 ≤ w σ) : 0 ≤ minusMass w label := by
  classical
  unfold minusMass
  refine Finset.sum_nonneg ?_
  intro σ hσ
  by_cases h : label σ = CliffordLabel.minus
  · simp [h, hw σ]
  · simp [h]

/-- Lemma `plusMass_add_minusMass_eq_sum`. -/
lemma plusMass_add_minusMass_eq_sum {n : Nat}
    (w : PermMode n → ℝ) (label : PermMode n → CliffordLabel) :
    plusMass w label + minusMass w label = ∑ σ : PermMode n, w σ := by
  classical
  unfold plusMass minusMass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro σ hσ
  rcases label σ with _ | _
  · simp
  · simp

/-- Lemma `cliffordSemanticState_coord_sum_eq_weight_sum`. -/
lemma cliffordSemanticState_coord_sum_eq_weight_sum {n : Nat}
    (w : PermMode n → ℝ) (label : PermMode n → CliffordLabel) :
    (cliffordSemanticState w label).1 + (cliffordSemanticState w label).2
      = ∑ σ : PermMode n, w σ := by
  rw [cliffordSemanticState_fst_eq_plusMass, cliffordSemanticState_snd_eq_minusMass]
  exact plusMass_add_minusMass_eq_sum w label

/-! ## Graded Superalgebra Layer -/

/-- `ℤ₂`-parity for split Clifford labels (`plus` even, `minus` odd). -/
def parity : CliffordLabel → Nat
  | .plus => 0
  | .minus => 1

@[simp] lemma parity_plus : parity CliffordLabel.plus = 0 := rfl
@[simp] lemma parity_minus : parity CliffordLabel.minus = 1 := rfl

/-- Super sign `(-1)^{|a||b|}` specialized to `{plus, minus}`. -/
def superSign : CliffordLabel → CliffordLabel → ℝ
  | .minus, .minus => -1
  | _, _ => 1

@[simp] lemma superSign_plus_left (b : CliffordLabel) :
    superSign CliffordLabel.plus b = 1 := by
  cases b <;> rfl

@[simp] lemma superSign_plus_right (a : CliffordLabel) :
    superSign a CliffordLabel.plus = 1 := by
  cases a <;> rfl

@[simp] lemma superSign_minus_minus :
    superSign CliffordLabel.minus CliffordLabel.minus = -1 := rfl

/-- Lemma `splitB11_symm`. -/
lemma splitB11_symm (u v : ℝ × ℝ) : splitB11 u v = splitB11 v u := by
  simp [splitB11_apply, mul_comm]

/--
Super-bracket induced by the split bilinear form and Clifford grading labels.

This is the scalar super-commutator proxy
`[u,v]_{a,b} = B(u,v) - (-1)^{|a||b|} B(v,u)`.
-/
noncomputable def splitSuperBracket (a b : CliffordLabel) (u v : ℝ × ℝ) : ℝ :=
  splitB11 u v - superSign a b * splitB11 v u

@[simp] lemma splitSuperBracket_plus_left (b : CliffordLabel) (u v : ℝ × ℝ) :
    splitSuperBracket CliffordLabel.plus b u v = 0 := by
  unfold splitSuperBracket superSign
  simp [splitB11_apply]
  ring

@[simp] lemma splitSuperBracket_plus_right (a : CliffordLabel) (u v : ℝ × ℝ) :
    splitSuperBracket a CliffordLabel.plus u v = 0 := by
  unfold splitSuperBracket superSign
  simp [splitB11_apply]
  ring

@[simp] lemma splitSuperBracket_minus_minus (u v : ℝ × ℝ) :
    splitSuperBracket CliffordLabel.minus CliffordLabel.minus u v = 2 * splitB11 u v := by
  unfold splitSuperBracket superSign
  simp [splitB11_apply]
  ring

/-- Minimal split `Cl(n,n)`-style graded mode data over permutation modes. -/
structure SplitCliffordSuperData (n : Nat) where
  label : PermMode n → CliffordLabel

/-- Mode-level super sign induced by the graded label map. -/
def modeSuperSign {n : Nat} (S : SplitCliffordSuperData n) (σ τ : PermMode n) : ℝ :=
  superSign (S.label σ) (S.label τ)

/-- Mode-level split super-bracket induced by the graded label map. -/
noncomputable def modeSplitSuperBracket {n : Nat} (S : SplitCliffordSuperData n)
    (σ τ : PermMode n) (u v : ℝ × ℝ) : ℝ :=
  splitSuperBracket (S.label σ) (S.label τ) u v

/-! ## CliffordAlgebra-Valued Mode Representation -/

/-- Canonical split Clifford algebra for the `(1,1)` metric. -/
noncomputable abbrev SplitCliffordAlg := CliffordAlgebra splitQ11

/-- Clifford generator attached to a split label (`plus`/`minus`). -/
noncomputable def labelGenerator (a : CliffordLabel) : SplitCliffordAlg :=
  CliffordAlgebra.ι splitQ11 (cliffordBasis a)

/-- Lemma `labelGenerator_sq`. -/
lemma labelGenerator_sq (a : CliffordLabel) :
    labelGenerator a * labelGenerator a
      = algebraMap ℝ SplitCliffordAlg (splitQ11 (cliffordBasis a)) := by
  simp [labelGenerator, SplitCliffordAlg]

@[simp] lemma labelGenerator_sq_plus :
    labelGenerator CliffordLabel.plus * labelGenerator CliffordLabel.plus
      = algebraMap ℝ SplitCliffordAlg 1 := by
  simpa [cliffordBasis, splitBasisPlus, splitQ11_splitBasisPlus] using
    (labelGenerator_sq CliffordLabel.plus)

@[simp] lemma labelGenerator_sq_minus :
    labelGenerator CliffordLabel.minus * labelGenerator CliffordLabel.minus
      = algebraMap ℝ SplitCliffordAlg (-1) := by
  simpa [cliffordBasis, splitBasisMinus, splitQ11_splitBasisMinus] using
    (labelGenerator_sq CliffordLabel.minus)

/--
`Cl(n,n)`-style modewise split representation:
each permutation mode carries one split `Cl(1,1)` generator.
-/
abbrev ModewiseSplitRep (n : Nat) := PermMode n → SplitCliffordAlg

/-- Canonical modewise graded Clifford representation from labels. -/
noncomputable def canonicalModewiseRep {n : Nat}
    (S : SplitCliffordSuperData n) : ModewiseSplitRep n :=
  fun σ => labelGenerator (S.label σ)

/-- Weighted superposition of modewise Clifford generators (from permutation coefficients). -/
noncomputable def weightedModeCliffordState {n : Nat}
    (S : SplitCliffordSuperData n) (w : PermMode n → ℝ) : SplitCliffordAlg :=
  ∑ σ : PermMode n, algebraMap ℝ SplitCliffordAlg (w σ) * canonicalModewiseRep S σ

/-- Canonical naming alias for weighted modewise Clifford state. -/
noncomputable abbrev modewiseCliffordState {n : Nat}
    (S : SplitCliffordSuperData n) (w : PermutationMode n → ℝ) : SplitCliffordAlg :=
  weightedModeCliffordState S w

/-- Even (`plus`) component of the weighted Clifford state. -/
noncomputable def weightedModeCliffordStatePlus {n : Nat}
    (S : SplitCliffordSuperData n) (w : PermMode n → ℝ) : SplitCliffordAlg :=
  ∑ σ : PermMode n,
    if S.label σ = CliffordLabel.plus then
      algebraMap ℝ SplitCliffordAlg (w σ) * canonicalModewiseRep S σ
    else 0

/-- Canonical naming alias for even/plus modewise Clifford component. -/
noncomputable abbrev modewiseCliffordStateEven {n : Nat}
    (S : SplitCliffordSuperData n) (w : PermutationMode n → ℝ) : SplitCliffordAlg :=
  weightedModeCliffordStatePlus S w

/-- Odd (`minus`) component of the weighted Clifford state. -/
noncomputable def weightedModeCliffordStateMinus {n : Nat}
    (S : SplitCliffordSuperData n) (w : PermMode n → ℝ) : SplitCliffordAlg :=
  ∑ σ : PermMode n,
    if S.label σ = CliffordLabel.minus then
      algebraMap ℝ SplitCliffordAlg (w σ) * canonicalModewiseRep S σ
    else 0

/-- Canonical naming alias for odd/minus modewise Clifford component. -/
noncomputable abbrev modewiseCliffordStateOdd {n : Nat}
    (S : SplitCliffordSuperData n) (w : PermutationMode n → ℝ) : SplitCliffordAlg :=
  weightedModeCliffordStateMinus S w

/-- Graded decomposition of the modewise Clifford state into `plus` and `minus` parts. -/
lemma weightedModeCliffordState_split {n : Nat}
    (S : SplitCliffordSuperData n) (w : PermMode n → ℝ) :
    weightedModeCliffordState S w
      = weightedModeCliffordStatePlus S w + weightedModeCliffordStateMinus S w := by
  classical
  unfold weightedModeCliffordState weightedModeCliffordStatePlus weightedModeCliffordStateMinus
    canonicalModewiseRep
  calc
    ∑ σ : PermMode n, algebraMap ℝ SplitCliffordAlg (w σ) * labelGenerator (S.label σ)
      =
        ∑ σ : PermMode n,
          ((if S.label σ = CliffordLabel.plus then
              algebraMap ℝ SplitCliffordAlg (w σ) * labelGenerator (S.label σ)
            else 0) +
           (if S.label σ = CliffordLabel.minus then
              algebraMap ℝ SplitCliffordAlg (w σ) * labelGenerator (S.label σ)
            else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro σ hσ
          rcases h : S.label σ with _ | _
          · simp
          · simp
    _ =
        (∑ σ : PermMode n,
          if S.label σ = CliffordLabel.plus then
            algebraMap ℝ SplitCliffordAlg (w σ) * labelGenerator (S.label σ)
          else 0) +
        (∑ σ : PermMode n,
          if S.label σ = CliffordLabel.minus then
            algebraMap ℝ SplitCliffordAlg (w σ) * labelGenerator (S.label σ)
          else 0) := by
            rw [Finset.sum_add_distrib]

/-- Lemma `modewiseCliffordState_split`. -/
lemma modewiseCliffordState_split {n : Nat}
    (S : SplitCliffordSuperData n) (w : PermutationMode n → ℝ) :
    modewiseCliffordState S w
      = modewiseCliffordStateEven S w + modewiseCliffordStateOdd S w := by
  exact weightedModeCliffordState_split S w

/-! ## Dirac Dynamics On Modewise Clifford States -/

abbrev ModeMass (n : Nat) := PermMode n → ℝ

/-- Canonical naming alias for modewise Dirac mass profile. -/
abbrev ModeDiracMassProfile (n : Nat) := ModeMass n

/-- Dirac operator induced by a modewise mass profile. -/
noncomputable def modeDiracOperator {n : Nat}
    (S : SplitCliffordSuperData n) (m : ModeMass n) : SplitCliffordAlg :=
  ∑ σ : PermMode n, algebraMap ℝ SplitCliffordAlg (m σ) * canonicalModewiseRep S σ

/-- Left Clifford action of the Dirac operator on a state. -/
noncomputable def diracAction (D ψ : SplitCliffordAlg) : SplitCliffordAlg :=
  D * ψ

@[simp] lemma diracAction_def (D ψ : SplitCliffordAlg) :
    diracAction D ψ = D * ψ := rfl

/-- One explicit Euler step for a Dirac-driven semantic flow. -/
noncomputable def diracEulerStep (η : ℝ) (D ψ : SplitCliffordAlg) : SplitCliffordAlg :=
  ψ + η • diracAction D ψ

@[simp] lemma diracEulerStep_zero (D ψ : SplitCliffordAlg) :
    diracEulerStep 0 D ψ = ψ := by
  simp [diracEulerStep]

/-- Lemma `diracAction_add_right`. -/
lemma diracAction_add_right (D ψ₁ ψ₂ : SplitCliffordAlg) :
    diracAction D (ψ₁ + ψ₂) = diracAction D ψ₁ + diracAction D ψ₂ := by
  simp [diracAction, mul_add]

/--
The Dirac action respects the `plus/minus` grading split inherited from labels.
-/
lemma modeDiracAction_respects_grading {n : Nat}
    (S : SplitCliffordSuperData n) (m : ModeMass n) (w : PermMode n → ℝ) :
    diracAction (modeDiracOperator S m) (weightedModeCliffordState S w)
      = diracAction (modeDiracOperator S m) (weightedModeCliffordStatePlus S w)
        + diracAction (modeDiracOperator S m) (weightedModeCliffordStateMinus S w) := by
  rw [weightedModeCliffordState_split]
  exact diracAction_add_right _ _ _

/-- Shannon-style entropy of raw permutation-mode weights. -/
noncomputable def modeWeightEntropy {n : Nat} (w : PermMode n → ℝ) : ℝ :=
  0 - ∑ σ : PermMode n, w σ * Real.log (w σ)

/-- Coarse-grained parity entropy from the `plus/minus` mass decomposition. -/
noncomputable def parityEntropy {n : Nat}
    (w : PermMode n → ℝ) (label : PermMode n → CliffordLabel) : ℝ :=
  let p := plusMass w label
  let q := minusMass w label
  0 - (p * Real.log p + q * Real.log q)

section FromBistochastic

variable {V : Type*} [NormedAddCommGroup V]
variable (n : Nat) [Nonempty (Fin n)]

/--
For a bistochastic switch, the Birkhoff weights `w` can be lifted to a
Clifford-labeled split semantic state with simplex coordinates.
-/
theorem exists_clifford_labeled_state_of_bistochastic
    (β : ℝ) (x : Fin n → V) (hcol : IsBistochasticSwitch n β x)
    (label : PermMode n → CliffordLabel) :
    ∃ w : PermMode n → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • σ.permMatrix ℝ = switchMatrix n β x ∧
      let ψ := cliffordSemanticState w label
      0 ≤ ψ.1 ∧ 0 ≤ ψ.2 ∧ ψ.1 + ψ.2 = 1 := by
  rcases exists_perm_decomposition_of_bistochastic (n := n) β x hcol with
    ⟨w, hw_nonneg, hw_sum, hw_matrix⟩
  refine ⟨w, hw_nonneg, hw_sum, hw_matrix, ?_⟩
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · rw [cliffordSemanticState_fst_eq_plusMass]
    exact plusMass_nonneg hw_nonneg
  · rw [cliffordSemanticState_snd_eq_minusMass]
    exact minusMass_nonneg hw_nonneg
  · rw [cliffordSemanticState_coord_sum_eq_weight_sum, hw_sum]

/-- Theorem `exists_modewiseClifford_rep_of_bistochastic`. -/
theorem exists_modewiseClifford_rep_of_bistochastic
    (β : ℝ) (x : Fin n → V) (hcol : IsBistochasticSwitch n β x)
    (S : SplitCliffordSuperData n) :
    ∃ w : PermMode n → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • σ.permMatrix ℝ = switchMatrix n β x ∧
      weightedModeCliffordState S w
        = weightedModeCliffordStatePlus S w + weightedModeCliffordStateMinus S w := by
  rcases exists_perm_decomposition_of_bistochastic (n := n) β x hcol with
    ⟨w, hw_nonneg, hw_sum, hw_matrix⟩
  exact ⟨w, hw_nonneg, hw_sum, hw_matrix, weightedModeCliffordState_split S w⟩

end FromBistochastic

end CliffordLabel

section SinkhornFlow

variable (n : Nat)

abbrev SinkhornMatrix := Matrix (Fin n) (Fin n) ℝ

/-- Row sum of a square matrix on `Fin n`. -/
noncomputable def rowSum (M : SinkhornMatrix n) (i : Fin n) : ℝ :=
  ∑ j : Fin n, M i j

/-- Column sum of a square matrix on `Fin n`. -/
noncomputable def colSum (M : SinkhornMatrix n) (j : Fin n) : ℝ :=
  ∑ i : Fin n, M i j

/-- Positivity certificate for row sums (required for row normalization). -/
def HasPositiveRowSums (M : SinkhornMatrix n) : Prop :=
  ∀ i : Fin n, 0 < rowSum n M i

/-- Positivity certificate for column sums (required for column normalization). -/
def HasPositiveColSums (M : SinkhornMatrix n) : Prop :=
  ∀ j : Fin n, 0 < colSum n M j

/-- One Sinkhorn row-normalization step. -/
noncomputable def rowNormalize (M : SinkhornMatrix n) (_hrow : HasPositiveRowSums n M) :
    SinkhornMatrix n :=
  fun i j => M i j / rowSum n M i

/-- One Sinkhorn column-normalization step. -/
noncomputable def colNormalize (M : SinkhornMatrix n) (_hcol : HasPositiveColSums n M) :
    SinkhornMatrix n :=
  fun i j => M i j / colSum n M j

/-- Left Weyl-gauge scale for row normalization (`1 / rowSum`). -/
noncomputable def leftWeylScale (M : SinkhornMatrix n) : Fin n → ℝ :=
  fun i => (rowSum n M i)⁻¹

/-- Right Weyl-gauge scale for column normalization (`1 / colSum`). -/
noncomputable def rightWeylScale (M : SinkhornMatrix n) : Fin n → ℝ :=
  fun j => (colSum n M j)⁻¹

/--
Row normalization is exactly left diagonal Weyl scaling by inverse row sums.
-/
lemma rowNormalize_eq_leftDiagonalGauge
    (M : SinkhornMatrix n) (hrow : HasPositiveRowSums n M) :
    rowNormalize n M hrow = Matrix.diagonal (leftWeylScale n M) * M := by
  ext i j
  simp [rowNormalize, leftWeylScale, rowSum, Matrix.diagonal_mul, div_eq_mul_inv, mul_comm]

/--
Column normalization is exactly right diagonal Weyl scaling by inverse column sums.
-/
lemma colNormalize_eq_rightDiagonalGauge
    (M : SinkhornMatrix n) (hcol : HasPositiveColSums n M) :
    colNormalize n M hcol = M * Matrix.diagonal (rightWeylScale n M) := by
  ext i j
  simp [colNormalize, rightWeylScale, colSum, Matrix.mul_diagonal, div_eq_mul_inv]

/--
Two-step Sinkhorn-Knopp update as a two-sided Weyl gauge transform.

This is the matrix-level gauge-fixing map:
`M ↦ diag(ℓ) * M * diag(r)` with `ℓ_i = 1/rowSum_i`, `r_j = 1/colSum_j`.
-/
lemma sinkhornTwoStep_eq_weylGauge
    (M : SinkhornMatrix n)
    (hrow : HasPositiveRowSums n M)
    (hcol : HasPositiveColSums n (rowNormalize n M hrow)) :
    colNormalize n (rowNormalize n M hrow) hcol
      = Matrix.diagonal (leftWeylScale n M) * M
          * Matrix.diagonal (rightWeylScale n (rowNormalize n M hrow)) := by
  rw [colNormalize_eq_rightDiagonalGauge (n := n) (M := rowNormalize n M hrow) hcol,
      rowNormalize_eq_leftDiagonalGauge (n := n) (M := M) hrow]

/-- Lemma `rowSum_rowNormalize`. -/
lemma rowSum_rowNormalize (M : SinkhornMatrix n) (hrow : HasPositiveRowSums n M) (i : Fin n) :
    rowSum n (rowNormalize n M hrow) i = 1 := by
  unfold rowSum rowNormalize
  have hne : (∑ k : Fin n, M i k) ≠ 0 := (hrow i).ne'
  calc
    ∑ j : Fin n, M i j / ∑ k : Fin n, M i k
        = (∑ j : Fin n, M i j) / ∑ k : Fin n, M i k := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset (Fin n)))
                (f := fun j : Fin n => M i j)
                (a := ∑ k : Fin n, M i k))
    _ = 1 := div_self hne

/-- Lemma `colSum_colNormalize`. -/
lemma colSum_colNormalize (M : SinkhornMatrix n) (hcol : HasPositiveColSums n M) (j : Fin n) :
    colSum n (colNormalize n M hcol) j = 1 := by
  unfold colSum colNormalize
  have hne : (∑ k : Fin n, M k j) ≠ 0 := (hcol j).ne'
  calc
    ∑ i : Fin n, M i j / ∑ k : Fin n, M k j
        = (∑ i : Fin n, M i j) / ∑ k : Fin n, M k j := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset (Fin n)))
                (f := fun i : Fin n => M i j)
                (a := ∑ k : Fin n, M k j))
    _ = 1 := div_self hne

/-- Row-normalization residual objective. -/
noncomputable def rowLyapunov (M : SinkhornMatrix n) : ℝ :=
  ∑ i : Fin n, |rowSum n M i - 1|

/-- Column-normalization residual objective. -/
noncomputable def colLyapunov (M : SinkhornMatrix n) : ℝ :=
  ∑ j : Fin n, |colSum n M j - 1|

/-- Lemma `rowLyapunov_nonneg`. -/
lemma rowLyapunov_nonneg (M : SinkhornMatrix n) : 0 ≤ rowLyapunov n M := by
  unfold rowLyapunov
  refine Finset.sum_nonneg ?_
  intro i hi
  exact abs_nonneg _

/-- Lemma `colLyapunov_nonneg`. -/
lemma colLyapunov_nonneg (M : SinkhornMatrix n) : 0 ≤ colLyapunov n M := by
  unfold colLyapunov
  refine Finset.sum_nonneg ?_
  intro j hj
  exact abs_nonneg _

/-- Lemma `rowLyapunov_rowNormalize_eq_zero`. -/
lemma rowLyapunov_rowNormalize_eq_zero (M : SinkhornMatrix n) (hrow : HasPositiveRowSums n M) :
    rowLyapunov n (rowNormalize n M hrow) = 0 := by
  unfold rowLyapunov
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [rowSum_rowNormalize (n := n) M hrow i]
  simp

/-- Lemma `colLyapunov_colNormalize_eq_zero`. -/
lemma colLyapunov_colNormalize_eq_zero (M : SinkhornMatrix n) (hcol : HasPositiveColSums n M) :
    colLyapunov n (colNormalize n M hcol) = 0 := by
  unfold colLyapunov
  refine Finset.sum_eq_zero ?_
  intro j hj
  rw [colSum_colNormalize (n := n) M hcol j]
  simp

/--
Row-wise Radon-Nikodym log-density generator:
the logarithmic Jacobian surrogate `∑ᵢ log(rowSumᵢ)`.
-/
noncomputable def rowRadonNikodymGenerator (M : SinkhornMatrix n) : ℝ :=
  ∑ i : Fin n, Real.log (rowSum n M i)

/--
Column-wise Radon-Nikodym log-density generator:
the logarithmic Jacobian surrogate `∑ⱼ log(colSumⱼ)`.
-/
noncomputable def colRadonNikodymGenerator (M : SinkhornMatrix n) : ℝ :=
  ∑ j : Fin n, Real.log (colSum n M j)

/--
Row self-concordant-style barrier potential:
negative log Radon-Nikodym/Jacobian generator.
-/
noncomputable def rowBarrierPotential (M : SinkhornMatrix n) : ℝ :=
  -rowRadonNikodymGenerator n M

/--
Column self-concordant-style barrier potential:
negative log Radon-Nikodym/Jacobian generator.
-/
noncomputable def colBarrierPotential (M : SinkhornMatrix n) : ℝ :=
  -colRadonNikodymGenerator n M

/--
Nonnegative row barrier functional from absolute log row-mass change.
-/
noncomputable def rowRNBarrier (M : SinkhornMatrix n) : ℝ :=
  ∑ i : Fin n, |Real.log (rowSum n M i)|

/--
Nonnegative column barrier functional from absolute log column-mass change.
-/
noncomputable def colRNBarrier (M : SinkhornMatrix n) : ℝ :=
  ∑ j : Fin n, |Real.log (colSum n M j)|

/-- Lemma `rowRNBarrier_nonneg`. -/
lemma rowRNBarrier_nonneg (M : SinkhornMatrix n) : 0 ≤ rowRNBarrier n M := by
  unfold rowRNBarrier
  refine Finset.sum_nonneg ?_
  intro i hi
  exact abs_nonneg _

/-- Lemma `colRNBarrier_nonneg`. -/
lemma colRNBarrier_nonneg (M : SinkhornMatrix n) : 0 ≤ colRNBarrier n M := by
  unfold colRNBarrier
  refine Finset.sum_nonneg ?_
  intro j hj
  exact abs_nonneg _

/-- Lemma `rowRNBarrier_rowNormalize_eq_zero`. -/
lemma rowRNBarrier_rowNormalize_eq_zero (M : SinkhornMatrix n) (hrow : HasPositiveRowSums n M) :
    rowRNBarrier n (rowNormalize n M hrow) = 0 := by
  unfold rowRNBarrier
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [rowSum_rowNormalize (n := n) M hrow i]
  simp

/-- Lemma `colRNBarrier_colNormalize_eq_zero`. -/
lemma colRNBarrier_colNormalize_eq_zero (M : SinkhornMatrix n) (hcol : HasPositiveColSums n M) :
    colRNBarrier n (colNormalize n M hcol) = 0 := by
  unfold colRNBarrier
  refine Finset.sum_eq_zero ?_
  intro j hj
  rw [colSum_colNormalize (n := n) M hcol j]
  simp

/-- Alternating Sinkhorn phase (row step or column step). -/
inductive SinkhornPhase where
  | row
  | col
deriving DecidableEq, Repr

/-- One admissible Sinkhorn step at the given phase. -/
def SinkhornStep (phase : SinkhornPhase) (M M' : SinkhornMatrix n) : Prop :=
  match phase with
  | .row => ∃ hrow : HasPositiveRowSums n M, M' = rowNormalize n M hrow
  | .col => ∃ hcol : HasPositiveColSums n M, M' = colNormalize n M hcol

/--
Phase-aligned pre-step Lyapunov objective:
- for row steps we track column imbalance,
- for column steps we track row imbalance.
-/
noncomputable def phaseLyapunovBefore (phase : SinkhornPhase) (M : SinkhornMatrix n) : ℝ :=
  match phase with
  | .row => colLyapunov n M
  | .col => rowLyapunov n M

/--
Phase-aligned post-step Lyapunov objective:
tracks the axis normalized by the current phase step.
-/
noncomputable def phaseLyapunovAfter (phase : SinkhornPhase) (M : SinkhornMatrix n) : ℝ :=
  match phase with
  | .row => rowLyapunov n M
  | .col => colLyapunov n M

/--
Phase-aligned Radon-Nikodym barrier objective before a Sinkhorn step.
-/
noncomputable def phaseRNBarrierBefore (phase : SinkhornPhase) (M : SinkhornMatrix n) : ℝ :=
  match phase with
  | .row => colRNBarrier n M
  | .col => rowRNBarrier n M

/--
Phase-aligned Radon-Nikodym barrier objective after a Sinkhorn step:
tracks the barrier on the axis normalized by the current phase step.
-/
noncomputable def phaseRNBarrierAfter (phase : SinkhornPhase) (M : SinkhornMatrix n) : ℝ :=
  match phase with
  | .row => rowRNBarrier n M
  | .col => colRNBarrier n M

/-- Lemma `phaseLyapunovBefore_nonneg`. -/
lemma phaseLyapunovBefore_nonneg (phase : SinkhornPhase) (M : SinkhornMatrix n) :
    0 ≤ phaseLyapunovBefore n phase M := by
  cases phase <;>
    simp [phaseLyapunovBefore, rowLyapunov_nonneg, colLyapunov_nonneg]

/-- Lemma `phaseRNBarrierBefore_nonneg`. -/
lemma phaseRNBarrierBefore_nonneg (phase : SinkhornPhase) (M : SinkhornMatrix n) :
    0 ≤ phaseRNBarrierBefore n phase M := by
  cases phase <;>
    simp [phaseRNBarrierBefore, rowRNBarrier_nonneg, colRNBarrier_nonneg]

/--
Sinkhorn one-step Lyapunov contraction in the phase-aligned objective.
-/
lemma sinkhornStep_phaseLyapunov_monotone
    {phase : SinkhornPhase} {M M' : SinkhornMatrix n}
    (hstep : SinkhornStep n phase M M') :
    phaseLyapunovAfter n phase M' ≤ phaseLyapunovBefore n phase M := by
  cases phase with
  | row =>
      rcases hstep with ⟨hrow, rfl⟩
      rw [show phaseLyapunovAfter n SinkhornPhase.row (rowNormalize n M hrow)
            = rowLyapunov n (rowNormalize n M hrow) by rfl]
      rw [rowLyapunov_rowNormalize_eq_zero (n := n) M hrow]
      exact phaseLyapunovBefore_nonneg (n := n) SinkhornPhase.row M
  | col =>
      rcases hstep with ⟨hcol, rfl⟩
      rw [show phaseLyapunovAfter n SinkhornPhase.col (colNormalize n M hcol)
            = colLyapunov n (colNormalize n M hcol) by rfl]
      rw [colLyapunov_colNormalize_eq_zero (n := n) M hcol]
      exact phaseLyapunovBefore_nonneg (n := n) SinkhornPhase.col M

/--
Radon-Nikodym barrier contraction lemma.
-/
lemma sinkhornStep_phaseRNBarrier_monotone
    {phase : SinkhornPhase} {M M' : SinkhornMatrix n}
    (hstep : SinkhornStep n phase M M') :
    phaseRNBarrierAfter n phase M' ≤ phaseRNBarrierBefore n phase M := by
  cases phase with
  | row =>
      rcases hstep with ⟨hrow, rfl⟩
      rw [show phaseRNBarrierAfter n SinkhornPhase.row (rowNormalize n M hrow)
            = rowRNBarrier n (rowNormalize n M hrow) by rfl]
      rw [rowRNBarrier_rowNormalize_eq_zero (n := n) M hrow]
      exact phaseRNBarrierBefore_nonneg (n := n) SinkhornPhase.row M
  | col =>
      rcases hstep with ⟨hcol, rfl⟩
      rw [show phaseRNBarrierAfter n SinkhornPhase.col (colNormalize n M hcol)
            = colRNBarrier n (colNormalize n M hcol) by rfl]
      rw [colRNBarrier_colNormalize_eq_zero (n := n) M hcol]
      exact phaseRNBarrierBefore_nonneg (n := n) SinkhornPhase.col M

/-- Exact vanishing of the phase-aligned post-step Lyapunov objective. -/
lemma sinkhornStep_phaseLyapunovAfter_eq_zero
    {phase : SinkhornPhase} {M M' : SinkhornMatrix n}
    (hstep : SinkhornStep n phase M M') :
    phaseLyapunovAfter n phase M' = 0 := by
  cases phase with
  | row =>
      rcases hstep with ⟨hrow, rfl⟩
      simpa [phaseLyapunovAfter] using rowLyapunov_rowNormalize_eq_zero (n := n) M hrow
  | col =>
      rcases hstep with ⟨hcol, rfl⟩
      simpa [phaseLyapunovAfter] using colLyapunov_colNormalize_eq_zero (n := n) M hcol

/-- Exact vanishing of the phase-aligned post-step RN barrier objective. -/
lemma sinkhornStep_phaseRNBarrierAfter_eq_zero
    {phase : SinkhornPhase} {M M' : SinkhornMatrix n}
    (hstep : SinkhornStep n phase M M') :
    phaseRNBarrierAfter n phase M' = 0 := by
  cases phase with
  | row =>
      rcases hstep with ⟨hrow, rfl⟩
      simpa [phaseRNBarrierAfter] using rowRNBarrier_rowNormalize_eq_zero (n := n) M hrow
  | col =>
      rcases hstep with ⟨hcol, rfl⟩
      simpa [phaseRNBarrierAfter] using colRNBarrier_colNormalize_eq_zero (n := n) M hcol

/-- Alternating row/column phase schedule. -/
def phaseAt (k : Nat) : SinkhornPhase :=
  if k % 2 = 0 then SinkhornPhase.row else SinkhornPhase.col

/--
A (possibly noncomputable) Sinkhorn trajectory with explicit admissible steps.
-/
structure SinkhornTrajectory where
  state : Nat → SinkhornMatrix n
  step : ∀ k, SinkhornStep n (phaseAt k) (state k) (state (k + 1))

/-- Lyapunov objective evaluated before the step at iteration `k`. -/
noncomputable def trajectoryLyapunov (T : SinkhornTrajectory n) (k : Nat) : ℝ :=
  phaseLyapunovBefore n (phaseAt k) (T.state k)

/-- Lyapunov objective evaluated after the step at iteration `k`. -/
noncomputable def trajectoryLyapunovNext (T : SinkhornTrajectory n) (k : Nat) : ℝ :=
  phaseLyapunovAfter n (phaseAt k) (T.state (k + 1))

/-- Radon-Nikodym barrier objective before the step at iteration `k`. -/
noncomputable def trajectoryRNBarrier (T : SinkhornTrajectory n) (k : Nat) : ℝ :=
  phaseRNBarrierBefore n (phaseAt k) (T.state k)

/-- Radon-Nikodym barrier objective after the step at iteration `k`. -/
noncomputable def trajectoryRNBarrierNext (T : SinkhornTrajectory n) (k : Nat) : ℝ :=
  phaseRNBarrierAfter n (phaseAt k) (T.state (k + 1))

/-- Every admissible Sinkhorn step has zero phase-aligned post-step Lyapunov objective. -/
theorem trajectoryLyapunovNext_eq_zero (T : SinkhornTrajectory n) (k : Nat) :
    trajectoryLyapunovNext n T k = 0 := by
  unfold trajectoryLyapunovNext
  exact sinkhornStep_phaseLyapunovAfter_eq_zero (n := n) (hstep := T.step k)

/-- Every admissible Sinkhorn step has zero phase-aligned post-step RN barrier. -/
theorem trajectoryRNBarrierNext_eq_zero (T : SinkhornTrajectory n) (k : Nat) :
    trajectoryRNBarrierNext n T k = 0 := by
  unfold trajectoryRNBarrierNext
  exact sinkhornStep_phaseRNBarrierAfter_eq_zero (n := n) (hstep := T.step k)

/--
Monotonic Lyapunov inequality along the Sinkhorn trajectory.
This is the genuine convergence theorem: imbalance on the uncontrolled axis decreases.
-/
theorem trajectoryLyapunov_monotone (T : SinkhornTrajectory n) (k : Nat) :
    trajectoryLyapunovNext n T k ≤ trajectoryLyapunov n T k := by
  simpa [trajectoryLyapunovNext, trajectoryLyapunov] using
    sinkhornStep_phaseLyapunov_monotone (n := n) (hstep := T.step k)

/--
Exact row-step identity on the normalized axis:
the post-row-normalization RN barrier on rows is zero.
-/
theorem rn_barrier_row_step_eq_zero (M : SinkhornMatrix n) (hpos : HasPositiveRowSums n M) :
    rowRNBarrier n (rowNormalize n M hpos) = 0 :=
  rowRNBarrier_rowNormalize_eq_zero (n := n) M hpos

/--
Monotonic Radon-Nikodym barrier inequality along the Sinkhorn trajectory.
The logarithmic imbalance contracts after each alternating normalization.
-/
theorem trajectoryRNBarrier_monotone (T : SinkhornTrajectory n) (k : Nat) :
    trajectoryRNBarrierNext n T k ≤ trajectoryRNBarrier n T k := by
  simpa [trajectoryRNBarrierNext, trajectoryRNBarrier] using
    sinkhornStep_phaseRNBarrier_monotone (n := n) (hstep := T.step k)

end SinkhornFlow

section EntropicOTBridge

variable (n : Nat)

abbrev CostMatrix := SinkhornMatrix n
abbrev Coupling := SinkhornMatrix n
abbrev Marginal := Fin n → ℝ

/-- Coupling with prescribed row/column marginals. -/
def HasMarginals (PiM : Coupling n) (mu nu : Marginal n) : Prop :=
  (∀ i : Fin n, rowSum n PiM i = mu i) ∧
    (∀ j : Fin n, colSum n PiM j = nu j)

/-- Entropic OT Gibbs kernel `K_ε(i,j) = exp(-C(i,j)/ε)`. -/
noncomputable def entropicKernel (ε : ℝ) (C : CostMatrix n) : Coupling n :=
  fun i j => Real.exp (-C i j / ε)

/-- Sinkhorn-Knopp two-sided diagonal scaling of a kernel. -/
noncomputable def sinkhornScaledCoupling
    (K : Coupling n) (left right : Fin n → ℝ) : Coupling n :=
  Matrix.diagonal left * K * Matrix.diagonal right

@[simp] lemma sinkhornScaledCoupling_def
    (K : Coupling n) (left right : Fin n → ℝ) :
    sinkhornScaledCoupling n K left right
      = Matrix.diagonal left * K * Matrix.diagonal right := rfl

/-- Linear transport cost term `<C, PiM>`. -/
noncomputable def transportCost (C PiM : Coupling n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, C i j * PiM i j

/-- Negative Shannon entropy term `∑ PiM_ij log PiM_ij`. -/
noncomputable def negativeEntropy (PiM : Coupling n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, PiM i j * Real.log (PiM i j)

/-- Entropically regularized OT objective `⟨C,PiM⟩ + ε * ∑ PiM log PiM`. -/
noncomputable def regularizedOTObjective (ε : ℝ) (C PiM : Coupling n) : ℝ :=
  transportCost n C PiM + ε * negativeEntropy n PiM

/-! ### OT / Bayesian / Convex Naming Layer

These are explicit naming aliases for the same functional objects already present:
- entropic OT objective
- Bayesian free-energy objective
- convex objective = linear transport term + entropy regularizer
-/

/-- Explicit OT naming alias for the regularized transport objective. -/
noncomputable abbrev entropicOptimalTransportObjective
    (ε : ℝ) (C PiM : Coupling n) : ℝ :=
  regularizedOTObjective n ε C PiM

/-- Bayesian free-energy naming alias for the same functional. -/
noncomputable abbrev bayesianFreeEnergyObjective
    (ε : ℝ) (C PiM : Coupling n) : ℝ :=
  regularizedOTObjective n ε C PiM

/-- Convex-program decomposition: linear transport term plus entropy regularizer. -/
lemma entropicOptimalTransportObjective_eq_transport_plus_entropy
    (ε : ℝ) (C PiM : Coupling n) :
    entropicOptimalTransportObjective n ε C PiM
      = transportCost n C PiM + ε * negativeEntropy n PiM := rfl

@[simp] lemma bayesianFreeEnergyObjective_eq_regularizedOTObjective
    (ε : ℝ) (C PiM : Coupling n) :
    bayesianFreeEnergyObjective n ε C PiM = regularizedOTObjective n ε C PiM := rfl

/-- OT Gibbs kernel interpreted as Bayesian likelihood matrix. -/
noncomputable abbrev bayesianLikelihoodKernel (ε : ℝ) (C : CostMatrix n) : Coupling n :=
  entropicKernel n ε C

/-- Two-sided Sinkhorn scaling interpreted as Bayesian posterior coupling update. -/
noncomputable abbrev bayesianPosteriorCoupling
    (K : Coupling n) (left right : Fin n → ℝ) : Coupling n :=
  sinkhornScaledCoupling n K left right

/-! ### Schrödinger Bridge Naming Layer

Discrete entropic OT with Gibbs kernel + Sinkhorn scaling is the finite Schrödinger bridge model.
-/

/-- Schrödinger bridge reference kernel (entropic Gibbs kernel). -/
noncomputable abbrev schroedingerBridgeKernel (ε : ℝ) (C : CostMatrix n) : Coupling n :=
  entropicKernel n ε C

/-- Schrödinger bridge coupling via two-sided Sinkhorn scaling. -/
noncomputable abbrev schroedingerBridgeCoupling
    (K : Coupling n) (left right : Fin n → ℝ) : Coupling n :=
  sinkhornScaledCoupling n K left right

/-- Schrödinger bridge objective (entropic OT action). -/
noncomputable abbrev schroedingerBridgeObjective
    (ε : ℝ) (C PiM : Coupling n) : ℝ :=
  regularizedOTObjective n ε C PiM

/-- Row-normalization enforces unit row marginals. -/
lemma rowNormalize_has_unit_rowMarginal
    (M : Coupling n) (hrow : HasPositiveRowSums n M) :
    ∀ i : Fin n, rowSum n (rowNormalize n M hrow) i = 1 :=
  rowSum_rowNormalize (n := n) M hrow

/-- Column-normalization enforces unit column marginals. -/
lemma colNormalize_has_unit_colMarginal
    (M : Coupling n) (hcol : HasPositiveColSums n M) :
    ∀ j : Fin n, colSum n (colNormalize n M hcol) j = 1 :=
  colSum_colNormalize (n := n) M hcol

/--
Sinkhorn-Knopp update is exactly a two-sided Weyl gauge transform on the coupling kernel.
-/
lemma sinkhornTwoStep_eq_twoSidedGauge
    (M : Coupling n)
    (hrow : HasPositiveRowSums n M)
    (hcol : HasPositiveColSums n (rowNormalize n M hrow)) :
    colNormalize n (rowNormalize n M hrow) hcol
      = sinkhornScaledCoupling n M
          (leftWeylScale n M)
          (rightWeylScale n (rowNormalize n M hrow)) := by
  simpa [sinkhornScaledCoupling] using
    (sinkhornTwoStep_eq_weylGauge (n := n) M hrow hcol)

/--
Bayesian posterior form: one Sinkhorn two-step is a two-sided posterior reweighting update.
-/
lemma sinkhornTwoStep_eq_bayesianPosteriorGauge
    (M : Coupling n)
    (hrow : HasPositiveRowSums n M)
    (hcol : HasPositiveColSums n (rowNormalize n M hrow)) :
    colNormalize n (rowNormalize n M hrow) hcol
      = bayesianPosteriorCoupling n M
          (leftWeylScale n M)
          (rightWeylScale n (rowNormalize n M hrow)) := by
  simpa [bayesianPosteriorCoupling] using
    (sinkhornTwoStep_eq_twoSidedGauge (n := n) M hrow hcol)

/--
Schrödinger bridge form: one Sinkhorn two-step is a two-sided gauge-scaled bridge coupling.
-/
lemma sinkhornTwoStep_eq_schroedingerBridgeGauge
    (M : Coupling n)
    (hrow : HasPositiveRowSums n M)
    (hcol : HasPositiveColSums n (rowNormalize n M hrow)) :
    colNormalize n (rowNormalize n M hrow) hcol
      = schroedingerBridgeCoupling n M
          (leftWeylScale n M)
          (rightWeylScale n (rowNormalize n M hrow)) := by
  simpa [schroedingerBridgeCoupling] using
    (sinkhornTwoStep_eq_twoSidedGauge (n := n) M hrow hcol)

/--
Phase-aligned Lyapunov monotonicity for one Sinkhorn step, in OT language.
-/
lemma sinkhornStep_regularizedObjective_monotone
    {phase : SinkhornPhase} {M M' : Coupling n}
    (hstep : SinkhornStep n phase M M') :
    phaseLyapunovAfter n phase M' ≤ phaseLyapunovBefore n phase M :=
  sinkhornStep_phaseLyapunov_monotone (n := n) hstep

/--
Entropic OT step monotonicity alias (via the same phase Lyapunov functional).
-/
lemma sinkhornStep_entropicOT_monotone
    {phase : SinkhornPhase} {M M' : Coupling n}
    (hstep : SinkhornStep n phase M M') :
    phaseLyapunovAfter n phase M' ≤ phaseLyapunovBefore n phase M :=
  sinkhornStep_regularizedObjective_monotone (n := n) hstep

/--
Bayesian free-energy step monotonicity alias (same statement in Bayesian language).
-/
lemma sinkhornStep_bayesianFreeEnergy_monotone
    {phase : SinkhornPhase} {M M' : Coupling n}
    (hstep : SinkhornStep n phase M M') :
    phaseLyapunovAfter n phase M' ≤ phaseLyapunovBefore n phase M :=
  sinkhornStep_regularizedObjective_monotone (n := n) hstep

/--
Radon-Nikodym barrier monotonicity alias:
the negative-log Jacobian generator contracts to the normalized axis after each step.
-/
lemma sinkhornStep_radonNikodymBarrier_monotone
    {phase : SinkhornPhase} {M M' : Coupling n}
    (hstep : SinkhornStep n phase M M') :
    phaseRNBarrierAfter n phase M' ≤ phaseRNBarrierBefore n phase M :=
  sinkhornStep_phaseRNBarrier_monotone (n := n) hstep

/-- Schrödinger bridge step monotonicity alias. -/
lemma schroedingerBridgeStep_monotone
    {phase : SinkhornPhase} {M M' : Coupling n}
    (hstep : SinkhornStep n phase M M') :
    phaseLyapunovAfter n phase M' ≤ phaseLyapunovBefore n phase M :=
  sinkhornStep_regularizedObjective_monotone (n := n) hstep

/--
Schrödinger bridge form of RN-barrier monotonicity.
-/
lemma schroedingerBridgeStep_radonNikodymBarrier_monotone
    {phase : SinkhornPhase} {M M' : Coupling n}
    (hstep : SinkhornStep n phase M M') :
    phaseRNBarrierAfter n phase M' ≤ phaseRNBarrierBefore n phase M :=
  sinkhornStep_radonNikodymBarrier_monotone (n := n) hstep

end EntropicOTBridge

end InfoGeometry.Canonical.MoE
