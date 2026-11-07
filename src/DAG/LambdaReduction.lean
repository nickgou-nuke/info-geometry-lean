import InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge
import DAG.ReductionTrace

/-!
# De Bruijn beta reduction

The reduction layer is kept separate from the static causal-net readout.  The
term carrier is the existing de Bruijn `LambdaTerm`; substitution performs the
necessary lifting under binders.
-/

namespace InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge

namespace LambdaTerm

/-- Lift free indices at and above the cutoff `c`. -/
def shiftAbove (d c : Nat) : LambdaTerm → LambdaTerm
  | .var k => if c ≤ k then .var (k + d) else .var k
  | .abs body => .abs (shiftAbove d (c + 1) body)
  | .app f a => .app (shiftAbove d c f) (shiftAbove d c a)

/-- Remove `d` binder levels at and above the cutoff when they are present. -/
def shiftDown (d c : Nat) : LambdaTerm → LambdaTerm
  | .var k => if c + d ≤ k then .var (k - d) else .var k
  | .abs body => .abs (shiftDown d (c + 1) body)
  | .app f a => .app (shiftDown d c f) (shiftDown d c a)

@[simp] theorem shiftDown_shiftAbove (d c : Nat) (t : LambdaTerm) :
    shiftDown d c (shiftAbove d c t) = t := by
  induction t generalizing c with
  | var k =>
      by_cases h : c ≤ k
      · simp [shiftAbove, shiftDown, h]
      · simp [shiftAbove, shiftDown, h]
        omega
  | abs body ih =>
      simp only [shiftAbove, shiftDown]
      rw [ih]
  | app f a ihf iha =>
      simp only [shiftAbove, shiftDown]
      rw [ihf, iha]

@[simp] theorem shiftAbove_var_of_lt {d c k : Nat} (h : k < c) :
    shiftAbove d c (.var k) = .var k := by
  simp [shiftAbove, Nat.not_le.mpr h]

@[simp] theorem shiftAbove_var_of_le {d c k : Nat} (h : c ≤ k) :
    shiftAbove d c (.var k) = .var (k + d) := by
  simp [shiftAbove, h]

@[simp] theorem shiftAbove_app (d c : Nat) (f a : LambdaTerm) :
    shiftAbove d c (.app f a) =
      .app (shiftAbove d c f) (shiftAbove d c a) := rfl

@[simp] theorem shiftAbove_abs (d c : Nat) (body : LambdaTerm) :
    shiftAbove d c (.abs body) =
      .abs (shiftAbove d (c + 1) body) := rfl

/-- The reduction layer's binder shift is the canonical lambda-term lift. -/
theorem liftAt_eq_shiftAbove (cutoff : Nat) (s : LambdaTerm) :
    LambdaTerm.liftAt cutoff s = shiftAbove 1 cutoff s := by
  induction s generalizing cutoff with
  | var k => by_cases h : cutoff ≤ k <;> simp [LambdaTerm.liftAt, shiftAbove, h]
  | abs body ih => simp only [LambdaTerm.liftAt, shiftAbove]; rw [ih]
  | app f a ihf iha => simp only [LambdaTerm.liftAt, shiftAbove]; rw [ihf, iha]

theorem lift_eq_shiftAbove (s : LambdaTerm) :
    LambdaTerm.lift s = shiftAbove 1 0 s := by
  exact liftAt_eq_shiftAbove 0 s

@[simp] theorem subst_var_eq (j : Nat) (s : LambdaTerm) :
    subst j s (.var j) = s := by
  simp [LambdaTerm.subst]

@[simp] theorem subst_var_of_lt {j k : Nat} (h : k < j) (s : LambdaTerm) :
    subst j s (.var k) = .var k := by
  simp [LambdaTerm.subst, h]

@[simp] theorem subst_var_of_gt {j k : Nat} (h : j < k) (s : LambdaTerm) :
    subst j s (.var k) = .var (k - 1) := by
  simp [LambdaTerm.subst, Nat.not_lt.mpr (Nat.le_of_lt h), Nat.ne_of_gt h]

@[simp] theorem shiftAbove_zero (c : Nat) (t : LambdaTerm) :
    shiftAbove 0 c t = t := by
  induction t generalizing c with
  | var k => by_cases h : c ≤ k <;> simp [shiftAbove, h]
  | abs body ih =>
      simp only [shiftAbove]
      rw [ih]
  | app f a ihf iha =>
      simp only [shiftAbove]
      rw [ihf, iha]

@[simp] theorem subst_app (j : Nat) (s f a : LambdaTerm) :
    subst j s (.app f a) =
      .app (subst j s f) (subst j s a) := by
  rfl

@[simp] theorem subst_abs (j : Nat) (s body : LambdaTerm) :
    subst j s (.abs body) =
      .abs (subst (j + 1) (shiftAbove 1 0 s) body) := by
  change LambdaTerm.abs (LambdaTerm.subst (j + 1) (LambdaTerm.lift s) body) = _
  rw [lift_eq_shiftAbove]

/-- One beta contraction, including its exact de Bruijn contractum. -/
inductive BetaStep : LambdaTerm → LambdaTerm → Type where
  | redex (body arg : LambdaTerm) :
      BetaStep (.app (.abs body) arg)
        (shiftDown 1 0 (subst 0 (shiftAbove 1 0 arg) body))
  | app_left {f f' a : LambdaTerm} :
      BetaStep f f' → BetaStep (.app f a) (.app f' a)
  | app_right {f a a' : LambdaTerm} :
      BetaStep a a' → BetaStep (.app f a) (.app f a')
  | abs {body body' : LambdaTerm} :
      BetaStep body body' → BetaStep (.abs body) (.abs body')

def betaStep_redex (body arg : LambdaTerm) :
    BetaStep (.app (.abs body) arg)
      (shiftDown 1 0 (subst 0 (shiftAbove 1 0 arg) body)) :=
  .redex body arg

def betaStep_app_left {f f' a : LambdaTerm}
    (h : BetaStep f f') :
    BetaStep (.app f a) (.app f' a) :=
  .app_left h

def betaStep_app_right {f a a' : LambdaTerm}
    (h : BetaStep a a') :
    BetaStep (.app f a) (.app f a') :=
  .app_right h

def betaStep_abs {body body' : LambdaTerm}
    (h : BetaStep body body') :
    BetaStep (.abs body) (.abs body') :=
  .abs h

def identityTerm : LambdaTerm := .abs (.var 0)

def betaStep_identity (arg : LambdaTerm) :
    BetaStep (.app identityTerm arg) arg := by
  simpa [identityTerm, subst, shiftDown, shiftAbove] using
    (betaStep_redex (.var 0) arg)

/-- The propositional existence of a computational beta-step. -/
def BetaStepExists (t u : LambdaTerm) : Prop :=
  Nonempty (BetaStep t u)

theorem betaStep_exists {t u : LambdaTerm} (r : BetaStep t u) :
    BetaStepExists t u :=
  ⟨r⟩

/-- Multi-step beta reduction as the reflexive-transitive logical closure. -/
def BetaStar : LambdaTerm → LambdaTerm → Prop :=
  Relation.ReflTransGen BetaStepExists

theorem betaStep_to_betaStar {t u : LambdaTerm} (r : BetaStep t u) :
    BetaStar t u :=
  Relation.ReflTransGen.single (betaStep_exists r)

theorem betaStar_refl (t : LambdaTerm) : BetaStar t t :=
  Relation.ReflTransGen.refl

theorem betaStar_trans {t u v : LambdaTerm}
    (h₁ : BetaStar t u) (h₂ : BetaStar u v) :
    BetaStar t v :=
  Relation.ReflTransGen.trans h₁ h₂

theorem betaStar_identity (arg : LambdaTerm) :
    BetaStar (.app identityTerm arg) arg :=
  betaStep_to_betaStar (betaStep_identity arg)

theorem betaStar_app_left {f f' a : LambdaTerm}
    (h : BetaStar f f') :
    BetaStar (.app f a) (.app f' a) := by
  induction h with
  | refl => exact betaStar_refl _
  | tail h r ih =>
      rcases r with ⟨r⟩
      exact betaStar_trans ih
        (betaStep_to_betaStar (betaStep_app_left r))

theorem betaStar_app_right {f a a' : LambdaTerm}
    (h : BetaStar a a') :
    BetaStar (.app f a) (.app f a') := by
  induction h with
  | refl => exact betaStar_refl _
  | tail h r ih =>
      rcases r with ⟨r⟩
      exact betaStar_trans ih
        (betaStep_to_betaStar (betaStep_app_right r))

theorem betaStar_abs {body body' : LambdaTerm}
    (h : BetaStar body body') :
    BetaStar (.abs body) (.abs body') := by
  induction h with
  | refl => exact betaStar_refl _
  | tail h r ih =>
      rcases r with ⟨r⟩
      exact betaStar_trans ih
        (betaStep_to_betaStar (betaStep_abs r))

theorem betaTrace_to_betaStar {t u : LambdaTerm} (xs : List LambdaTerm)
    (h : DAG.ReductionTrace BetaStep t xs u) :
    BetaStar t u := by
  exact DAG.ReductionTrace.to_reflTransGen h

theorem betaTrace_trans {t u v : LambdaTerm}
    {xs ys : List LambdaTerm}
    (h₁ : DAG.ReductionTrace BetaStep t xs u)
    (h₂ : DAG.ReductionTrace BetaStep u ys v) :
    Nonempty (DAG.ReductionTrace BetaStep t (xs ++ ys) v) := by
  exact ⟨DAG.ReductionTrace.trans h₁ h₂⟩

theorem betaTrace_trans_to_betaStar {t u v : LambdaTerm}
    {xs ys : List LambdaTerm}
    (h₁ : DAG.ReductionTrace BetaStep t xs u)
    (h₂ : DAG.ReductionTrace BetaStep u ys v) :
    BetaStar t v := by
  exact betaTrace_to_betaStar (xs ++ ys) (DAG.ReductionTrace.trans h₁ h₂)

end LambdaTerm

end InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge
