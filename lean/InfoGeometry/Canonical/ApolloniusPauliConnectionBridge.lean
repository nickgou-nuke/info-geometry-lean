 import Mathlib.Tactic
 import InfoGeometry.Canonical.PauliBraidB3
 import InfoGeometry.Canonical.ApolloniusWindingFluxBridge
 
 /-!
 # Apollonius Pauli connection and spinorial winding holonomy
 
 This file supplies the finite Pauli-algebra layer of the Apollonius operator
 connection.  It reuses the repository's concrete Pauli matrices and its proved
 logarithmic circle period.
 
 The connection values lie on the single Cartan axis `sigma3`, so their
 commutator wedge vanishes.  The unit winding period `2 pi i`, evaluated in
 the half-weight spin representation, exponentiates to `-1`; the associated
 matrix holonomy is therefore `-I_2`.
 
 This is a finite matrix and winding theorem.  It does not identify arbitrary
 punctures with Aharonov--Bohm vortices and does not derive a BdG scattering
 amplitude.
 -/
 
 noncomputable section
 
 namespace InfoGeometry.Canonical.ApolloniusPauliConnectionBridge
 
 open scoped Matrix
 open InfoGeometry.Canonical.ApolloniusWindingFluxBridge
 open InfoGeometry.Canonical.PauliBraidB3
 
 abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ
 
 /-- Matrix commutator. -/
 def commutator (A B : Mat2C) : Mat2C :=
   A * B - B * A
 
 /-- Positive circular Pauli eigenoperator. -/
 def sigmaPlus : Mat2C :=
   (1 / 2 : ℂ) • (sigma1 + Complex.I • sigma2)
 
 /-- Negative circular Pauli eigenoperator. -/
 def sigmaMinus : Mat2C :=
   (1 / 2 : ℂ) • (sigma1 - Complex.I • sigma2)
 
 /-- The positive circular operator has adjoint weight `+2` under `sigma3`. -/
 theorem sigma3_commutator_sigmaPlus :
     commutator sigma3 sigmaPlus = (2 : ℂ) • sigmaPlus := by
   ext i j <;> fin_cases i <;> fin_cases j <;>
     simp [commutator, sigmaPlus, sigma1, sigma2, sigma3,
       InfoGeometryCore.sigma1C, InfoGeometryCore.sigma2C,
       InfoGeometryCore.sigma3C, Matrix.mul_apply, Fin.sum_univ_two] <;>
     ring_nf <;> rw [Complex.I_sq] <;> ring
 
 /-- The negative circular operator has adjoint weight `-2` under `sigma3`. -/
 theorem sigma3_commutator_sigmaMinus :
     commutator sigma3 sigmaMinus = (-2 : ℂ) • sigmaMinus := by
   ext i j <;> fin_cases i <;> fin_cases j <;>
     simp [commutator, sigmaMinus, sigma1, sigma2, sigma3,
       InfoGeometryCore.sigma1C, InfoGeometryCore.sigma2C,
       InfoGeometryCore.sigma3C, Matrix.mul_apply, Fin.sum_univ_two] <;>
     ring_nf <;> rw [Complex.I_sq] <;> ring
 
 /-- Chiral light-cone/circular matrix layout for a complex four-component
 readout. -/
 def chiralPotentialMatrix
     (Aplus Aminus Aright Aleft : ℂ) : Mat2C :=
   !![Aplus, Aright; Aleft, Aminus]
 
 /-- Logarithmic boost-plus-phase generator on the Cartan Pauli axis. -/
 def logarithmicGenerator (eta theta : ℝ) : Mat2C :=
   (((eta : ℂ) + Complex.I * (theta : ℂ)) / 2) • sigma3
 
 /-- Value of the Cartan-valued logarithmic connection on a scalar one-form
 coefficient. -/
 def cartanConnectionValue (z : ℂ) : Mat2C :=
   (z / 2) • sigma3
 
 /-- All values of the Cartan connection commute.  This is the exact finite
 matrix content of the vanishing `A wedge A` term. -/
 theorem cartanConnectionValue_commutator (z w : ℂ) :
     commutator (cartanConnectionValue z) (cartanConnectionValue w) = 0 := by
   ext i j <;> fin_cases i <;> fin_cases j <;>
     simp [commutator, cartanConnectionValue, sigma3,
       InfoGeometryCore.sigma3C, Matrix.mul_apply, Fin.sum_univ_two] <;>
     ring
 
 /-- Finite curvature readout: exterior differential plus the commutator-wedge
 term. -/
 def curvatureReadout (dA : Mat2C) (z w : ℂ) : Mat2C :=
   dA + commutator (cartanConnectionValue z) (cartanConnectionValue w)
 
 /-- For the one-axis Cartan connection, curvature is exactly its exterior
 differential term. -/
 theorem curvatureReadout_eq_exteriorDifferential
     (dA : Mat2C) (z w : ℂ) :
     curvatureReadout dA z w = dA := by
   rw [curvatureReadout, cartanConnectionValue_commutator]
   simp
 
 /-- A closed one-axis Cartan connection is flat. -/
 theorem curvatureReadout_eq_zero_of_closed
     (dA : Mat2C) (hdA : dA = 0) (z w : ℂ) :
     curvatureReadout dA z w = 0 := by
   rw [curvatureReadout_eq_exteriorDifferential, hdA]
 
 /-- Half-weight scalar holonomy obtained from the proved winding flux. -/
 def spinHolonomyScalar (R : ℝ) : ℂ :=
   Complex.exp (quantizedWindingFlux R 1 / 2)
 
 /-- A unit winding gives the nontrivial spinorial sign. -/
 theorem spinHolonomyScalar_eq_neg_one
     (R : ℝ) (hR : 0 < R) :
     spinHolonomyScalar R = -1 := by
   unfold spinHolonomyScalar
   rw [quantizedWindingFlux_eq_two_pi_mul_I R hR 1]
   convert Complex.exp_pi_mul_I using 1 <;> ring
 
 /-- Matrix-valued half-weight holonomy. -/
 def spinHolonomyMatrix (R : ℝ) : Mat2C :=
   spinHolonomyScalar R • (1 : Mat2C)
 
 /-- The unit winding holonomy is `-I_2`. -/
 theorem spinHolonomyMatrix_eq_neg_identity
     (R : ℝ) (hR : 0 < R) :
     spinHolonomyMatrix R = -(1 : Mat2C) := by
   rw [spinHolonomyMatrix, spinHolonomyScalar_eq_neg_one R hR]
   ext i j <;> fin_cases i <;> fin_cases j <;> simp
 
 end InfoGeometry.Canonical.ApolloniusPauliConnectionBridge
 
