import sys
content = open('lean/InfoGeometry/Analytic/LogSumExp.lean').read()

replacement_1 = """  have hlin : HasDerivAt (fun t : ℝ => t * a i) (a i) θ := by
    have h := (hasDerivAt_id' θ).mul_const (a i)
    rw [one_mul] at h
    exact h
  have hExp :
      HasDerivAt (fun t : ℝ => Real.exp (t * a i))
        (a i * Real.exp (θ * a i)) θ := by
    have h1 := (Real.hasDerivAt_exp (θ * a i)).comp θ hlin
    change HasDerivAt (fun t => Real.exp (t * a i)) _ θ at h1
    rw [mul_comm] at h1
    exact h1
  exact hExp.const_mul (w i)"""

content = content.replace("""  have hlin : HasDerivAt (fun t : ℝ => t * a i) (a i) θ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id' θ).mul_const (a i))
  have hExp :
      HasDerivAt (fun t : ℝ => Real.exp (t * a i))
        (a i * Real.exp (θ * a i)) θ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_exp (θ * a i)).comp θ hlin
  simpa [mul_assoc, mul_left_comm, mul_comm] using hExp.const_mul (w i)""", replacement_1)

replacement_2 = """        / (logSumExpPartition w a θ) ^ (2 : ℕ) := by
            have h := deriv_div (c := logSumExpMoment1 w a) (d := logSumExpPartition w a) (x := θ) hnumDiff hdenDiff hZne
            change deriv (fun t => logSumExpMoment1 w a t / logSumExpPartition w a t) θ = _ at h
            exact h"""

content = content.replace("""        / (logSumExpPartition w a θ) ^ (2 : ℕ) := by
            simpa using
              (deriv_div
                (c := logSumExpMoment1 w a)
                (d := logSumExpPartition w a)
                (x := θ) hnumDiff hdenDiff hZne)""", replacement_2)

replacement_3 = """    HasDerivAt (logSumExp w a) (logSumExpMean w a θ) θ := by
  have hpart := hasDerivAt_logSumExpPartition (w := w) (a := a) (θ := θ)
  have hlog := hpart.log (ne_of_gt (logSumExp_sum_pos w a hw θ))
  change HasDerivAt (logSumExp w a) _ θ at hlog
  exact hlog"""

content = content.replace("""    HasDerivAt (logSumExp w a) (logSumExpMean w a θ) θ := by
  have hpart := hasDerivAt_logSumExpPartition (w := w) (a := a) (θ := θ)
  have hlog := hpart.log (ne_of_gt (logSumExp_sum_pos w a hw θ))
  simpa [logSumExp, logSumExpMean] using hlog""", replacement_3)

open('lean/InfoGeometry/Analytic/LogSumExp.lean', 'w').write(content)
