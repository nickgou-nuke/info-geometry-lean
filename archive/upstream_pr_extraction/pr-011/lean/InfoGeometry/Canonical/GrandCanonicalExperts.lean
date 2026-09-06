import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.Canonical.Clifford

open scoped BigOperators

namespace InfoGeometry.Canonical.MoE

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

end InfoGeometry.Canonical.MoE
