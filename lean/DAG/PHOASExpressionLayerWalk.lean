import DAG.PHOASExpressionLayer

/-!
# PHOAS walker unfolding lemmas

Small definitional lemmas for the budgeted PHOAS tree walker.
-/

namespace DAG.PHOASExpressionLayer

/-- If the expression is a variable, walking it returns either just itself or nothing. -/
theorem walkPHOASTree_var
    (p : PHOASExpr Nat → Bool) (s : PHOASQueryState) (maxSteps : Nat) (n : Nat)
    (h_steps : maxSteps > 0)
    (h_expr : s.expr = PHOASExpr.var n) :
    walkPHOASTree p maxSteps s = if p s.expr then [s.expr] else [] := by
  have hne : maxSteps ≠ 0 := Nat.ne_of_gt h_steps
  rw [walkPHOASTree.eq_def p maxSteps s]
  simp [hne, h_expr]

/-- If the expression is an application, the walk unfolds into the recursive walks. -/
theorem walkPHOASTree_app
    (p : PHOASExpr Nat → Bool) (s : PHOASQueryState) (maxSteps : Nat)
    (f a : PHOASExpr Nat)
    (h_steps : maxSteps > 0)
    (h_expr : s.expr = PHOASExpr.app f a) :
    walkPHOASTree p maxSteps s =
      (if p s.expr then [s.expr] else [])
      ++ (walkPHOASTree p (maxSteps - 1) { s with expr := f })
      ++ (walkPHOASTree p (maxSteps / 2) { s with expr := a }) := by
  have hne : maxSteps ≠ 0 := Nat.ne_of_gt h_steps
  rw [walkPHOASTree.eq_def p maxSteps s]
  simp [hne, h_expr]

/-- If the expression is a lambda, the walk stops without extending the context. -/
theorem walkPHOASTree_lam
    (p : PHOASExpr Nat → Bool) (s : PHOASQueryState) (maxSteps : Nat)
    (body : Nat → PHOASExpr Nat)
    (h_steps : maxSteps > 0)
    (h_expr : s.expr = PHOASExpr.lam body) :
    walkPHOASTree p maxSteps s = if p s.expr then [s.expr] else [] := by
  have hne : maxSteps ≠ 0 := Nat.ne_of_gt h_steps
  rw [walkPHOASTree.eq_def p maxSteps s]
  simp [hne, h_expr]

end DAG.PHOASExpressionLayer
