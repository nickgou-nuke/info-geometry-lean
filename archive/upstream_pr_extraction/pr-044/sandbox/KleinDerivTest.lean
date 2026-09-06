import Mathlib

noncomputable section

def planeWaveFactor (k x : ℝ) : ℂ := Complex.exp (Complex.I * (k * x : ℂ))

theorem test_second_deriv_planeWaveFactor (k x : ℝ) :
    deriv (fun u : ℝ => deriv (fun v : ℝ => planeWaveFactor k v) u) x =
      -(k : ℂ) ^ 2 * planeWaveFactor k x := by
  have hinner :
      HasDerivAt (fun u : ℝ => Complex.I * (k * u : ℂ))
        (Complex.I * (k : ℂ)) x := by
    convert ((hasDerivAt_id (x : ℂ)).comp_ofReal.const_mul (k : ℂ)).const_mul
      Complex.I using 1 <;> simp [mul_assoc]
  have hfirst :
      (fun u : ℝ => deriv (fun v : ℝ => planeWaveFactor k v) u) =
        (fun u : ℝ => Complex.exp (Complex.I * (k * u : ℂ)) *
          (Complex.I * (k : ℂ))) := by
    funext u
    have hinner' :
        HasDerivAt (fun z : ℝ => Complex.I * (k * z : ℂ))
          (Complex.I * (k : ℂ)) u := by
      convert ((hasDerivAt_id (u : ℂ)).comp_ofReal.const_mul (k : ℂ)).const_mul
        Complex.I using 1 <;> simp [mul_assoc]
    have hexp := (Complex.hasDerivAt_exp (Complex.I * (k * u : ℂ))).comp u hinner'
    simpa [planeWaveFactor] using hexp.deriv
  rw [hfirst]
  have hexp := (Complex.hasDerivAt_exp (Complex.I * (k * x : ℂ))).comp x hinner
  have hprod := hexp.mul_const (Complex.I * (k : ℂ))
  have hi :
      (Complex.I * (k : ℂ)) * (Complex.I * (k : ℂ)) = -(k : ℂ) ^ 2 := by
    calc
      (Complex.I * (k : ℂ)) * (Complex.I * (k : ℂ)) =
          (Complex.I * Complex.I) * ((k : ℂ) * (k : ℂ)) := by ring
      _ = -(k : ℂ) ^ 2 := by rw [Complex.I_mul_I]; ring
  have hder := hprod.deriv
  rw [mul_assoc, hi] at hder
  simpa [planeWaveFactor, mul_comm] using hder
