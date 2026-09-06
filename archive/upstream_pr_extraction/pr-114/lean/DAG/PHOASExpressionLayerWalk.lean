import DAG.PHOASExpressionLayer

/-!
# PHOAS walker unfolding lemmas

Small definitional lemmas for the budgeted PHOAS tree walker.
-/

namespace DAG.PHOASExpressionLayer

/-- If the expression is a variable, walking it returns either just itself or nothing. -/
theorem walkPHOASTree_var
    (p : ScopedPHOASExpr Nat Nat → Bool) (s : PHOASQueryState) (maxSteps : Nat) (n : Nat)
    (h_steps : maxSteps > 0)
    (h_expr : s.expr = ScopedPHOASExpr.fvar n) :
    walkPHOASTree p maxSteps s = if p s.expr then [s.expr] else [] := by
  have hne : maxSteps ≠ 0 := Nat.ne_of_gt h_steps
  rw [walkPHOASTree.eq_def p maxSteps s]
  simp [hne, h_expr]

/-- If the expression is an application, the walk unfolds into the recursive walks. -/
theorem walkPHOASTree_app
    (p : ScopedPHOASExpr Nat Nat → Bool) (s : PHOASQueryState) (maxSteps : Nat)
    (f a : ScopedPHOASExpr Nat Nat)
    (h_steps : maxSteps > 0)
    (h_expr : s.expr = ScopedPHOASExpr.app f a) :
    walkPHOASTree p maxSteps s =
      (if p s.expr then [s.expr] else [])
      ++ (walkPHOASTree p (maxSteps - 1) { s with expr := f })
      ++ (walkPHOASTree p (maxSteps / 2) { s with expr := a }) := by
  have hne : maxSteps ≠ 0 := Nat.ne_of_gt h_steps
  rw [walkPHOASTree.eq_def p maxSteps s]
  simp [hne, h_expr]

/-- If the expression is a lambda, the walk stops without extending the context. -/
theorem walkPHOASTree_lam
    (p : ScopedPHOASExpr Nat Nat → Bool) (s : PHOASQueryState) (maxSteps : Nat)
    (body : Nat → ScopedPHOASExpr Nat Nat)
    (h_steps : maxSteps > 0)
    (h_expr : s.expr = ScopedPHOASExpr.lam body) :
    walkPHOASTree p maxSteps s = if p s.expr then [s.expr] else [] := by
  have hne : maxSteps ≠ 0 := Nat.ne_of_gt h_steps
  rw [walkPHOASTree.eq_def p maxSteps s]
  simp [hne, h_expr]

end DAG.PHOASExpressionLayer
