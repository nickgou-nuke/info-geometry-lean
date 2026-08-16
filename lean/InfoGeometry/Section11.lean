import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Section9
import InfoGeometry.Section10

/-!
# Section 11: Bianchi Identities

This file formalizes the finite algebraic core of the Bianchi section.

It deliberately does not claim a full manifold-level proof of the differential
Bianchi identity from a Levi-Civita connection.  Instead it proves the two
algebraic transitions used in the prose:

* a cyclic Bianchi sum is preserved by any linear spinorial readout;
* the contracted Bianchi identity is exactly the vanishing of the divergence of
  the Einstein tensor once `div Ricci = (1/2) grad scalar` is supplied.
-/

noncomputable section

namespace Section11

open Matrix

abbrev SpinMat := Matrix (Fin 2) (Fin 2) ℂ
abbrev RiemannCoeff := Fin 4 → Fin 4 → ℂ
abbrev VectorField4 := Fin 4 → ℂ

/-! ## 11.1 First Bianchi identity -/

/-- Cyclic sum of three curvature slots. -/
def cyclicSum {V : Type*} [Add V] (x y z : V) : V :=
  x + y + z

/--
Any linear readout preserves a zero cyclic Bianchi sum.

This is the abstract algebraic content behind passing from vector/Riemann
curvature to spinorial curvature through soldering forms or Pauli generators.
-/
theorem cyclic_zero_of_linear_readout
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (L : V →ₗ[ℂ] W) (x y z : V) (h : cyclicSum x y z = 0) :
    cyclicSum (L x) (L y) (L z) = 0 := by
  unfold cyclicSum at h ⊢
  calc
    L x + L y + L z = L (x + y + z) := by simp
    _ = L 0 := by rw [h]
    _ = 0 := by simp

/-- Linear map implementing `F = (1/2) sum_ab R_ab sigma_ab`. -/
def spinCurvatureFromRiemannLinear : RiemannCoeff →ₗ[ℂ] SpinMat where
  toFun := Section9.spinCurvatureFromRiemann
  map_add' R S := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Section9.spinCurvatureFromRiemann, Pi.add_apply, add_smul, Fin.sum_univ_four] <;>
      ring
  map_smul' c R := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Section9.spinCurvatureFromRiemann, Pi.smul_apply, smul_smul, Fin.sum_univ_four] <;>
      ring

/--
Spinorial first Bianchi identity from the vector/Riemann cyclic Bianchi
identity.
-/
theorem spinorial_first_bianchi_from_vector
    (RmuNu RnuRho RrhoMu : RiemannCoeff)
    (hVector : cyclicSum RmuNu RnuRho RrhoMu = 0) :
    cyclicSum
      (Section9.spinCurvatureFromRiemann RmuNu)
      (Section9.spinCurvatureFromRiemann RnuRho)
      (Section9.spinCurvatureFromRiemann RrhoMu) = 0 :=
  cyclic_zero_of_linear_readout spinCurvatureFromRiemannLinear RmuNu RnuRho RrhoMu hVector

/-! ## 11.2 Contracted Bianchi identity -/

/--
Finite readout for the divergence of the Einstein tensor:
`div G = div Ricci - (1/2) grad scalar`.
-/
def einsteinDivergence (divRicci gradScalar : VectorField4) : VectorField4 :=
  divRicci - (1 / 2 : ℂ) • gradScalar

/--
Contracted Bianchi identity in finite algebraic form.

The full geometric theorem supplies `div Ricci = (1/2) grad scalar`; once that
identity is available, the Einstein tensor divergence vanishes by algebra.
-/
theorem contracted_bianchi_of_ricci_scalar_balance
    (divRicci gradScalar : VectorField4)
    (hBalance : divRicci = (1 / 2 : ℂ) • gradScalar) :
    einsteinDivergence divRicci gradScalar = 0 := by
  ext nu
  simp [einsteinDivergence, hBalance]

end Section11
