import InfoGeometry.Physics.KleinBottleSpectrum

noncomputable section

open InfoGeometry.Physics.KleinBottleSpectrum

def partialX (f : KleinPoint → ℂ) (p : KleinPoint) : ℂ :=
  deriv (fun u : ℝ => f (u, p.2)) p.1

def partialY (f : KleinPoint → ℂ) (p : KleinPoint) : ℂ :=
  deriv (fun v : ℝ => f (p.1, v)) p.2

def flatLaplacian (f : KleinPoint → ℂ) (p : KleinPoint) : ℂ :=
  partialX (partialX f) p + partialY (partialY f) p

theorem flatLaplacian_product (u v : ℝ → ℂ) (x y : ℝ) :
    flatLaplacian (fun p : KleinPoint => u p.1 * v p.2) (x, y) =
      deriv (fun z : ℝ => deriv (fun w : ℝ => u w) z) x * v y +
        u x * deriv (fun z : ℝ => deriv (fun w : ℝ => v w) z) y := by
  simp [flatLaplacian, partialX, partialY, deriv_mul_const_field,
    deriv_const_mul_field]

theorem flatLaplacian_product_transverse (u v : ℝ → ℂ) (x y : ℝ) :
    flatLaplacian (fun p : KleinPoint => u p.2 * v p.1) (x, y) =
      deriv (fun z : ℝ => deriv (fun w : ℝ => v w) z) x * u y +
        v x * deriv (fun z : ℝ => deriv (fun w : ℝ => u w) z) y := by
  simp [flatLaplacian, partialX, partialY, deriv_mul_const_field,
    deriv_const_mul_field]
  ring

theorem evenMode_flatLaplacian (a b : ℝ) (n : ℤ) (m : ℕ)
    (p : KleinPoint) :
    flatLaplacian (evenMode a b n m) p =
      -(evenBranchEigenvalue a b n m : ℂ) * evenMode a b n m p := by
  rcases p with ⟨x, y⟩
  have heq : evenMode a b n m =
      (fun q : KleinPoint =>
        cosineFactor (transverseWaveNumber b m) q.2 *
          planeWaveFactor (evenLongitudinalWaveNumber a n) q.1) := by
    funext q
    exact evenMode_eq_factor_product a b n m q
  rw [heq]
  rw [flatLaplacian_product_transverse]
  rw [cosineFactor_second_deriv, planeWaveFactor_second_deriv]
  simp [evenBranchEigenvalue, cosineFactor, planeWaveFactor,
    evenLongitudinalWaveNumber, transverseWaveNumber, pow_two]
  ring

theorem oddMode_flatLaplacian (a b : ℝ) (n : ℤ) (m : ℕ)
    (p : KleinPoint) :
    flatLaplacian (oddMode a b n m) p =
      -(oddBranchEigenvalue a b n m : ℂ) * oddMode a b n m p := by
  rcases p with ⟨x, y⟩
  have heq : oddMode a b n m =
      (fun q : KleinPoint =>
        sineFactor (transverseWaveNumber b m) q.2 *
          planeWaveFactor (oddLongitudinalWaveNumber a n) q.1) := by
    funext q
    exact oddMode_eq_factor_product a b n m q
  rw [heq]
  rw [flatLaplacian_product_transverse]
  rw [sineFactor_second_deriv, planeWaveFactor_second_deriv]
  simp [oddBranchEigenvalue, sineFactor, planeWaveFactor,
    oddLongitudinalWaveNumber, transverseWaveNumber, pow_two]
  ring
