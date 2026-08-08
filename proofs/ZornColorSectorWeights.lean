import proofs.ZornColorLieRepresentation

/-!
# Color-center sector weights

This file computes the central `gl₃` generator `Σ r, Tᵣᵣ` directly on the
eight Zorn coordinates.  The result is the weight table
`(3,1,2,0; 0,-2,-1,-3)` on the positive and negative semispinors.
-/

noncomputable section

namespace ZornColorSectorWeights

open SplitOctonionBraidSU3
open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open ZornThreeChannelCAR ZornColorLieAction

/-- Central matrix-unit sum in the proved color action. -/
def colorCenter : Module.End ℂ DiracSpinor16 :=
  ∑ r : Fin 3, colorEvenOp r r

/-- Expected action of the color center on the positive Zorn block. -/
def colorCenterPlusZorn (X : Zorn) : Zorn where
  a := 3 * X.a
  u := X.u
  v := 2 • X.v
  b := 0

/-- Expected action of the color center on the negative Zorn block. -/
def colorCenterMinusZorn (X : Zorn) : Zorn where
  a := 0
  u := (-2 : ℂ) • X.u
  v := -X.v
  b := -3 * X.b

private theorem copy_add_val {q : TrialitySector} (X Y : ZornCopy q) :
    (X + Y).val = zornAdd X.val Y.val :=
  CanonicalZornCliffordRepresentation.copy_add_val X Y

private theorem copy_smul_val' {q : TrialitySector} (c : ℂ) (X : ZornCopy q) :
    (c • X).val = zornSmul c X.val :=
  CanonicalZornCliffordRepresentation.copy_smul_val c X

private theorem dirac_smul_fst_val (c : ℂ) (X : DiracSpinor16) :
    (c • X).1.val = zornSmul c X.1.val := by
  change (c • X.1).val = zornSmul c X.1.val
  exact copy_smul_val' c X.1

private theorem dirac_smul_snd_val (c : ℂ) (X : DiracSpinor16) :
    (c • X).2.val = zornSmul c X.2.val := by
  change (c • X.2).val = zornSmul c X.2.val
  exact copy_smul_val' c X.2

/-- Exact positive-block action of the central color generator. -/
theorem colorCenter_fst_exact (S : SpinorPlus8) (C : SpinorMinus8) :
    (colorCenter (S, C)).1.val = colorCenterPlusZorn S.val := by
  rw [colorCenter, Fin.sum_univ_three]
  simp only [LinearMap.add_apply, Prod.fst_add, copy_add_val]
  rw [colorEvenOp_fst_exact, colorEvenOp_fst_exact, colorEvenOp_fst_exact]
  apply zorn_ext
  · simp [colorPlusZorn, mixedPlusZorn, colorCenterPlusZorn, zornAdd,
      colorDelta, zornSmul]
    ring
  · funext i
    fin_cases i <;>
      simp [colorPlusZorn, mixedPlusZorn, colorCenterPlusZorn, zornAdd,
        colorDelta, zornSmul]
  · funext i
    fin_cases i <;>
      simp [colorPlusZorn, mixedPlusZorn, colorCenterPlusZorn, zornAdd,
        colorDelta, zornSmul]
    <;> ring
  · simp [colorPlusZorn, mixedPlusZorn, colorCenterPlusZorn, zornAdd, zornSmul]

/-- Exact negative-block action of the central color generator. -/
theorem colorCenter_snd_exact (S : SpinorPlus8) (C : SpinorMinus8) :
    (colorCenter (S, C)).2.val = colorCenterMinusZorn C.val := by
  rw [colorCenter, Fin.sum_univ_three]
  simp only [LinearMap.add_apply, Prod.snd_add, copy_add_val]
  rw [colorEvenOp_snd_exact, colorEvenOp_snd_exact, colorEvenOp_snd_exact]
  apply zorn_ext
  · simp [colorMinusZorn, mixedMinusZorn, colorCenterMinusZorn, zornAdd]
  · funext i
    fin_cases i <;>
      simp [colorMinusZorn, mixedMinusZorn, colorCenterMinusZorn, zornAdd,
        colorDelta]
    <;> ring
  · funext i
    fin_cases i <;>
      simp [colorMinusZorn, mixedMinusZorn, colorCenterMinusZorn, zornAdd,
        colorDelta]
  · simp [colorMinusZorn, mixedMinusZorn, colorCenterMinusZorn, zornAdd,
      colorDelta]
    ring

/-! Coordinate-sector embeddings. -/

def positiveA (a : ℂ) : DiracSpinor16 :=
  (⟨{ a := a, u := 0, v := 0, b := 0 }⟩, 0)

def positiveU (u : Fin 3 → ℂ) : DiracSpinor16 :=
  (⟨{ a := 0, u := u, v := 0, b := 0 }⟩, 0)

def positiveV (v : Fin 3 → ℂ) : DiracSpinor16 :=
  (⟨{ a := 0, u := 0, v := v, b := 0 }⟩, 0)

def positiveB (b : ℂ) : DiracSpinor16 :=
  (⟨{ a := 0, u := 0, v := 0, b := b }⟩, 0)

def negativeA (a : ℂ) : DiracSpinor16 :=
  (0, ⟨{ a := a, u := 0, v := 0, b := 0 }⟩)

def negativeU (u : Fin 3 → ℂ) : DiracSpinor16 :=
  (0, ⟨{ a := 0, u := u, v := 0, b := 0 }⟩)

def negativeV (v : Fin 3 → ℂ) : DiracSpinor16 :=
  (0, ⟨{ a := 0, u := 0, v := v, b := 0 }⟩)

def negativeB (b : ℂ) : DiracSpinor16 :=
  (0, ⟨{ a := 0, u := 0, v := 0, b := b }⟩)

/-- The complete eight-sector color-center weight table. -/
theorem colorCenter_positiveA (a : ℂ) :
    colorCenter (positiveA a) = (3 : ℂ) • positiveA a := by
  apply Prod.ext <;> apply ZornCopy.ext
  · rw [colorCenter_fst_exact]
    rw [dirac_smul_fst_val]
    apply zorn_ext <;>
      simp [positiveA, colorCenterPlusZorn, zornSmul] <;>
        try { funext i; simp }
  · rw [colorCenter_snd_exact]
    rw [dirac_smul_snd_val]
    apply zorn_ext <;>
      simp [positiveA, colorCenterMinusZorn, zornSmul] <;>
        try { funext i; simp }

theorem colorCenter_positiveU (u : Fin 3 → ℂ) : colorCenter (positiveU u) = positiveU u := by
  apply Prod.ext <;> apply ZornCopy.ext
  · rw [colorCenter_fst_exact]
    apply zorn_ext <;> simp [positiveU, colorCenterPlusZorn]
  · rw [colorCenter_snd_exact]
    apply zorn_ext <;> simp [positiveU, colorCenterMinusZorn]

theorem colorCenter_positiveV (v : Fin 3 → ℂ) :
    colorCenter (positiveV v) = (2 : ℂ) • positiveV v := by
  apply Prod.ext <;> apply ZornCopy.ext
  · rw [colorCenter_fst_exact]
    rw [dirac_smul_fst_val]
    apply zorn_ext <;>
      simp [positiveV, colorCenterPlusZorn, zornSmul] <;>
        try { funext i; simp }
  · rw [colorCenter_snd_exact]
    rw [dirac_smul_snd_val]
    apply zorn_ext <;>
      simp [positiveV, colorCenterMinusZorn, zornSmul] <;>
        try { funext i; simp }

theorem colorCenter_positiveB (b : ℂ) : colorCenter (positiveB b) = 0 := by
  apply Prod.ext <;> apply ZornCopy.ext
  · rw [colorCenter_fst_exact]
    apply zorn_ext <;> simp [positiveB, colorCenterPlusZorn]
  · rw [colorCenter_snd_exact]
    apply zorn_ext <;> simp [positiveB, colorCenterMinusZorn]

theorem colorCenter_negativeA (a : ℂ) : colorCenter (negativeA a) = 0 := by
  apply Prod.ext <;> apply ZornCopy.ext
  · rw [colorCenter_fst_exact]
    apply zorn_ext <;> simp [negativeA, colorCenterPlusZorn]
  · rw [colorCenter_snd_exact]
    apply zorn_ext <;> simp [negativeA, colorCenterMinusZorn]

theorem colorCenter_negativeU (u : Fin 3 → ℂ) :
    colorCenter (negativeU u) = (-2 : ℂ) • negativeU u := by
  apply Prod.ext <;> apply ZornCopy.ext
  · rw [colorCenter_fst_exact]
    rw [dirac_smul_fst_val]
    apply zorn_ext <;>
      simp [negativeU, colorCenterPlusZorn, zornSmul] <;>
        try { funext i; simp }
  · rw [colorCenter_snd_exact]
    rw [dirac_smul_snd_val]
    apply zorn_ext <;>
      simp [negativeU, colorCenterMinusZorn, zornSmul] <;>
        try { funext i; simp }

theorem colorCenter_negativeV (v : Fin 3 → ℂ) :
    colorCenter (negativeV v) = (-1 : ℂ) • negativeV v := by
  apply Prod.ext <;> apply ZornCopy.ext
  · rw [colorCenter_fst_exact]
    rw [dirac_smul_fst_val]
    apply zorn_ext <;>
      simp [negativeV, colorCenterPlusZorn, zornSmul] <;>
        try { funext i; simp }
  · rw [colorCenter_snd_exact]
    rw [dirac_smul_snd_val]
    apply zorn_ext <;>
      simp [negativeV, colorCenterMinusZorn, zornSmul] <;>
        try { funext i; simp }

theorem colorCenter_negativeB (b : ℂ) :
    colorCenter (negativeB b) = (-3 : ℂ) • negativeB b := by
  apply Prod.ext <;> apply ZornCopy.ext
  · rw [colorCenter_fst_exact]
    rw [dirac_smul_fst_val]
    apply zorn_ext <;>
      simp [negativeB, colorCenterPlusZorn, zornSmul] <;>
        try { funext i; simp }
  · rw [colorCenter_snd_exact]
    rw [dirac_smul_snd_val]
    apply zorn_ext <;>
      simp [negativeB, colorCenterMinusZorn, zornSmul] <;>
        try { funext i; simp }

end ZornColorSectorWeights

end noncomputable section
