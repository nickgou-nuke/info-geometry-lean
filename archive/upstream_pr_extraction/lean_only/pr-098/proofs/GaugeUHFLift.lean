import Mathlib
import proofs.UHFInductiveColimit
import proofs.ChiralCausalCone

/-!
# Gauge → UHF Boundary — stage-n lift

`M₂(ℂ)` acts on `DiagAlg 1 ≅ ℂ²` as an algebra representation.
The action lifts to `DiagAlg n` for all `n ≥ 1` by acting on bit 0,
and this lift commutes with `diagEmbedSucc` for `n ≥ 1`.
Colimit lift follows from `diagEmbedSucc` compatibility.

Zero sorries.
-/

namespace GaugeUHFLift
open UHFInductiveColimit
open ChiralCausalCone

def wF : BitWord 1 := fun _ => false
def wT : BitWord 1 := fun _ => true

@[simp] theorem wF_val : wF 0 = false := rfl
@[simp] theorem wT_val : wT 0 = true := rfl

theorem bitWord1_cases (w : BitWord 1) : w = wF ∨ w = wT := by
  by_cases h : w 0
  · right; ext i; fin_cases i; exact h
  · left; ext i; fin_cases i; simpa using h

def pairEmbed (p : ℂ × ℂ) : DiagAlg 1 := fun w =>
  match w 0 with | false => p.1 | true => p.2

def gaugeAct1 (A : M2C) : DiagAlg 1 → DiagAlg 1 := fun f =>
  pairEmbed (A 0 0 * f wF + A 0 1 * f wT, A 1 0 * f wF + A 1 1 * f wT)

theorem gaugeAct1_add (A : M2C) (f g : DiagAlg 1) :
    gaugeAct1 A (f + g) = gaugeAct1 A f + gaugeAct1 A g := by
  ext w; rcases bitWord1_cases w with (rfl|rfl)
  · simp [gaugeAct1, pairEmbed, wF, wT]; ring
  · simp [gaugeAct1, pairEmbed, wF, wT]; ring

theorem gaugeAct1_smul (A : M2C) (c : ℂ) (f : DiagAlg 1) :
    gaugeAct1 A (c • f) = c • gaugeAct1 A f := by
  ext w; rcases bitWord1_cases w with (rfl|rfl)
  · simp [gaugeAct1, pairEmbed, wF, wT]; ring
  · simp [gaugeAct1, pairEmbed, wF, wT]; ring

theorem gaugeAct1_mul (A B : M2C) (f : DiagAlg 1) :
    gaugeAct1 (A * B) f = gaugeAct1 A (gaugeAct1 B f) := by
  ext w; rcases bitWord1_cases w with (rfl|rfl)
  · simp [gaugeAct1, pairEmbed, wF, wT, Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [gaugeAct1, pairEmbed, wF, wT, Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem gaugeAct1_one (f : DiagAlg 1) : gaugeAct1 (1 : M2C) f = f := by
  ext w; rcases bitWord1_cases w with (rfl|rfl)
  · simp [gaugeAct1, pairEmbed, wF, wT, Matrix.one_apply]
  · simp [gaugeAct1, pairEmbed, wF, wT, Matrix.one_apply]

theorem gaugeAct1_is_representation :
    (∀ (A B : M2C) (f : DiagAlg 1), gaugeAct1 (A * B) f = gaugeAct1 A (gaugeAct1 B f)) ∧
    (∀ f : DiagAlg 1, gaugeAct1 (1 : M2C) f = f) ∧
    (∀ (A : M2C) (f g : DiagAlg 1), gaugeAct1 A (f + g) = gaugeAct1 A f + gaugeAct1 A g) ∧
    (∀ (A : M2C) (c : ℂ) (f : DiagAlg 1), gaugeAct1 A (c • f) = c • gaugeAct1 A f) :=
  ⟨gaugeAct1_mul, gaugeAct1_one, gaugeAct1_add, gaugeAct1_smul⟩

/-! ## Stage-n action (n ≥ 1) and the colimit lift -/

/-- Replace bit 0 of a `BitWord n` (n ≥ 1) with `b`, keeping other bits unchanged. -/
def setBit0 {n : ℕ} (w : BitWord (n+1)) (b : Bool) : BitWord (n+1) :=
  fun i => if i.val = 0 then b else w i

@[simp] theorem setBit0_val {n : ℕ} (w : BitWord (n+1)) (b : Bool) : setBit0 w b 0 = b := rfl

/-- If `w 0 = b`, then `setBit0 w b = w`. -/
theorem setBit0_eq_of_val {n : ℕ} (w : BitWord (n+1)) (b : Bool) (h : w 0 = b) :
    setBit0 w b = w := by
  ext i
  dsimp [setBit0]
  by_cases hi : i.val = 0
  · have : i = 0 := by
      apply Fin.ext; simpa using hi
    subst this; simp [h]
  · simp [hi]

/-- `setBit0` is idempotent with respect to overwriting: second write wins. -/
theorem setBit0_overwrite {n : ℕ} (w : BitWord (n+1)) (b c : Bool) :
    setBit0 (setBit0 w b) c = setBit0 w c := by
  ext i
  dsimp [setBit0]
  by_cases h : i.val = 0
  · simp [h]
  · simp [h]

/-- `prefixSucc` commutes with `setBit0` for `n ≥ 0`. -/
theorem prefixSucc_setBit0_comm {n : ℕ} (w : BitWord (n+2)) (b : Bool) :
    prefixSucc (n+1) (setBit0 w b) = setBit0 (prefixSucc (n+1) w) b := by
  ext i
  simp [prefixSucc, setBit0]

@[simp] theorem prefixSucc_val_zero {n : ℕ} (w : BitWord (n+2)) :
    (prefixSucc (n+1) w) 0 = w 0 := by
  simp [prefixSucc]

/-- Gauge action at stage n: A acts on bit 0 of `BitWord n`.
For n=0 the action is trivial (1-dim algebra). For n≥1 the action
is the fundamental M₂(ℂ) representation on the bit-0 subspace. -/
def gaugeActAt (n : ℕ) (A : M2C) : DiagAlg n → DiagAlg n :=
  match n with
  | 0 => id
  | n+1 => fun f w =>
    if w 0
    then A 1 0 * f (setBit0 w false) + A 1 1 * f (setBit0 w true)
    else A 0 0 * f (setBit0 w false) + A 0 1 * f (setBit0 w true)

/-- At stage 1, `gaugeActAt 1 = gaugeAct1`. -/
theorem gaugeActAt_one (A : M2C) : gaugeActAt 1 A = gaugeAct1 A := by
  ext f w
  rcases bitWord1_cases w with (rfl|rfl)
  · have hF : setBit0 wF false = wF := by
      ext i; fin_cases i; rfl
    have hT : setBit0 wF true = wT := by
      ext i; fin_cases i; rfl
    simp [gaugeActAt, gaugeAct1, pairEmbed, wF, hF, hT]
  · have hF : setBit0 wT false = wF := by
      ext i; fin_cases i; rfl
    have hT : setBit0 wT true = wT := by
      ext i; fin_cases i; rfl
    simp [gaugeActAt, gaugeAct1, pairEmbed, wT, hF, hT]

/-- `gaugeActAt` is an algebra representation: it preserves Mul, One, Add, SMul. -/
theorem gaugeActAt_is_representation (n : ℕ) (A B : M2C) :
    (∀ f : DiagAlg n, gaugeActAt n (A * B) f = gaugeActAt n A (gaugeActAt n B f)) ∧
    (∀ f : DiagAlg n, gaugeActAt n (1 : M2C) f = f) ∧
    (∀ (f g : DiagAlg n), gaugeActAt n A (f + g) = gaugeActAt n A f + gaugeActAt n A g) ∧
    (∀ (c : ℂ) (f : DiagAlg n), gaugeActAt n A (c • f) = c • gaugeActAt n A f) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact fun f => rfl
    · exact fun f => rfl
    · exact fun f g => rfl
    · exact fun c f => rfl
  | succ n _ =>
    have hMul : ∀ f : DiagAlg (n+1),
        gaugeActAt (n+1) (A * B) f = gaugeActAt (n+1) A (gaugeActAt (n+1) B f) := by
      intro f
      ext w
      dsimp [gaugeActAt]
      by_cases h : w 0
      · simp [h, setBit0_overwrite, Matrix.mul_apply, Fin.sum_univ_two]; ring
      · simp [h, setBit0_overwrite, Matrix.mul_apply, Fin.sum_univ_two]; ring
    have hOne : ∀ f : DiagAlg (n+1), gaugeActAt (n+1) (1 : M2C) f = f := by
      intro f
      ext w
      dsimp [gaugeActAt]
      by_cases h : w 0
      · have hw : setBit0 w true = w := setBit0_eq_of_val w true h
        simp [h, hw]
      · have hf : w 0 = false := Bool.eq_false_iff.mpr h
        have hw : setBit0 w false = w := setBit0_eq_of_val w false hf
        simp [hf, hw]
    have hAdd : ∀ f g : DiagAlg (n+1),
        gaugeActAt (n+1) A (f + g) = gaugeActAt (n+1) A f + gaugeActAt (n+1) A g := by
      intro f g
      ext w
      dsimp [gaugeActAt]
      by_cases h : w 0
      · simp [h]; ring
      · simp [h]; ring
    have hSMul : ∀ (c : ℂ) (f : DiagAlg (n+1)),
        gaugeActAt (n+1) A (c • f) = c • gaugeActAt (n+1) A f := by
      intro c f
      ext w
      dsimp [gaugeActAt]
      by_cases h : w 0
      · simp [h]; ring
      · simp [h]; ring
    exact ⟨hMul, hOne, hAdd, hSMul⟩

/-- The key commutation: gauge action on bit 0 commutes with `diagEmbedSucc`
which acts on the last bit. These are independent operations for n ≥ 1. -/
theorem gaugeActAt_commutes_diagEmbed_succ (n : ℕ) (A : M2C) (f : DiagAlg (n+1)) :
    gaugeActAt (n+2) A (diagEmbedSucc (n+1) f) =
    diagEmbedSucc (n+1) (gaugeActAt (n+1) A f) := by
  ext w
  dsimp [gaugeActAt, diagEmbedSucc]
  by_cases h : w 0
  · simp [h, prefixSucc_setBit0_comm]
  · simp [h, prefixSucc_setBit0_comm]

/-- Colimit lift: the gauge action is compatible with all `diagEmbedSucc` maps
for stages n ≥ 1, so it lifts to a well-defined action on the UHF colimit. -/
theorem gaugeActAt_colimit_compatible (n m : ℕ) (A : M2C) (f : DiagAlg (n+m+1)) :
    gaugeActAt (n+m+2) A (diagEmbedSucc (n+m+1) f) =
    diagEmbedSucc (n+m+1) (gaugeActAt (n+m+1) A f) :=
  gaugeActAt_commutes_diagEmbed_succ (n+m) A f

/-- The full gauge-to-UHF-boundary lift theorem:
  1. Stage-1 action is an algebra representation on DiagAlg 1.
  2. Stage-n action is an algebra representation for all n.
  3. The action commutes with UHF transition maps for n ≥ 1.
  4. The colimit is compatible. -/
theorem gauge_uhf_boundary_synthesis (A B : M2C) (f g : DiagAlg 1) :
    (gaugeAct1 (A * B) f = gaugeAct1 A (gaugeAct1 B f)) ∧
    (gaugeAct1 (1 : M2C) f = f) ∧
    (gaugeAct1 A (f + g) = gaugeAct1 A f + gaugeAct1 A g) ∧
    (∀ (c : ℂ) (h : DiagAlg 1), gaugeAct1 A (c • h) = c • gaugeAct1 A h) ∧
    (∀ n : ℕ, (∀ h : DiagAlg n, gaugeActAt n (A * B) h = gaugeActAt n A (gaugeActAt n B h)) ∧
      (∀ h : DiagAlg n, gaugeActAt n (1 : M2C) h = h) ∧
      (∀ h₁ h₂ : DiagAlg n, gaugeActAt n A (h₁ + h₂) = gaugeActAt n A h₁ + gaugeActAt n A h₂) ∧
      (∀ (c : ℂ) (h : DiagAlg n), gaugeActAt n A (c • h) = c • gaugeActAt n A h)) ∧
    (∀ n : ℕ, ∀ h : DiagAlg (n+1),
      gaugeActAt (n+2) A (diagEmbedSucc (n+1) h) =
      diagEmbedSucc (n+1) (gaugeActAt (n+1) A h)) := by
  refine ⟨gaugeAct1_mul A B f, gaugeAct1_one f, gaugeAct1_add A f g,
    gaugeAct1_smul A, ?_, ?_⟩
  · intro n; exact gaugeActAt_is_representation n A B
  · intro n; exact gaugeActAt_commutes_diagEmbed_succ n A

end GaugeUHFLift
