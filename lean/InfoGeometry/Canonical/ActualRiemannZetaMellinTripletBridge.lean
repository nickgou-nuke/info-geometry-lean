import Mathlib.NumberTheory.LSeries.Dirichlet
import InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge
import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Topology.MellinDeRhamArithmeticCayleyBridge

/-!
# Actual convergent-half-plane Mellin triplet for `riemannZeta`

This module realizes the existing arithmetic Mellin triplet with Mathlib's
`riemannZeta` and von Mangoldt L-series on `1 < Re(s)`.  It does not assert
analytic continuation, a global logarithmic differential form, or a colimit
convergence theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualRiemannZetaMellinTripletBridge

open scoped LSeries.notation
open ArithmeticFunction
open InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge
open InfoGeometry.Topology.MellinDeRhamArithmeticCayleyBridge

def actualRiemannZetaMellinTriplet (s : ℂ) (hs : 1 < s.re) :
    ArithmeticMellinTriplet
      (riemannZeta s) (riemannZeta s)⁻¹
      (L ↗Λ s) (-deriv riemannZeta s) where
  zeta_inv_product := by
    exact mul_inv_cancel₀ (riemannZeta_ne_zero_of_one_lt_re hs)
  mangoldt_factorization := by
    rw [← actualRiemannZetaLogDerivative_eq_vonMangoldt_LSeries hs]
    dsimp [actualRiemannZetaLogDerivative]
    field_simp [riemannZeta_ne_zero_of_one_lt_re hs]

theorem actualRiemannZetaMellinTriplet_zeta_inv_product
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * (riemannZeta s)⁻¹ = 1 :=
  (actualRiemannZetaMellinTriplet s hs).zeta_inv_product

theorem actualRiemannZetaMellinTriplet_mangoldt_factorization
    {s : ℂ} (hs : 1 < s.re) :
    L ↗Λ s = (riemannZeta s)⁻¹ * (-deriv riemannZeta s) :=
  (actualRiemannZetaMellinTriplet s hs).mangoldt_factorization

theorem actualRiemannZetaMellinTriplet_mangoldt_reconstruction
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * L ↗Λ s = -deriv riemannZeta s :=
  mellin_mangoldt_reconstruction
    (riemannZeta s) (riemannZeta s)⁻¹ (L ↗Λ s)
    (-deriv riemannZeta s)
    (actualRiemannZetaMellinTriplet s hs)
    (riemannZeta_ne_zero_of_one_lt_re hs)

theorem actualRiemannZetaLogDerivative_mellin_factorization
    {s : ℂ} (hs : 1 < s.re) :
    actualRiemannZetaLogDerivative s =
      (riemannZeta s)⁻¹ * (-deriv riemannZeta s) := by
  rw [actualRiemannZetaLogDerivative_eq_vonMangoldt_LSeries hs]
  exact actualRiemannZetaMellinTriplet_mangoldt_factorization hs

theorem dirichletSeriesZeta_mangoldt_reconstruction
    {s : ℂ} (hs : 1 < s.re) :
    InfoGeometry.Arithmetic.RiemannZetaEquivalences.dirichletSeriesZeta s * L ↗Λ s =
      -deriv InfoGeometry.Arithmetic.RiemannZetaEquivalences.dirichletSeriesZeta s := by
  have hderiv :
      deriv InfoGeometry.Arithmetic.RiemannZetaEquivalences.dirichletSeriesZeta s =
        deriv riemannZeta s := by
    apply Filter.EventuallyEq.deriv_eq
    have hopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact InfoGeometry.Arithmetic.RiemannZetaEquivalences.dirichletSeriesZeta_eq_riemannZeta z hz
  rw [InfoGeometry.Arithmetic.RiemannZetaEquivalences.dirichletSeriesZeta_eq_riemannZeta s hs,
    hderiv]
  exact actualRiemannZetaMellinTriplet_mangoldt_reconstruction hs

theorem dirichletSeriesZeta_logDerivative_eq_vonMangoldt_LSeries
    {s : ℂ} (hs : 1 < s.re) :
    -deriv InfoGeometry.Arithmetic.RiemannZetaEquivalences.dirichletSeriesZeta s /
        InfoGeometry.Arithmetic.RiemannZetaEquivalences.dirichletSeriesZeta s =
      L ↗Λ s := by
  have hD :
      InfoGeometry.Arithmetic.RiemannZetaEquivalences.dirichletSeriesZeta s ≠ 0 := by
    rw [InfoGeometry.Arithmetic.RiemannZetaEquivalences.dirichletSeriesZeta_eq_riemannZeta
      s hs]
    exact riemannZeta_ne_zero_of_one_lt_re hs
  apply (div_eq_iff hD).2
  calc
    -deriv InfoGeometry.Arithmetic.RiemannZetaEquivalences.dirichletSeriesZeta s =
        InfoGeometry.Arithmetic.RiemannZetaEquivalences.dirichletSeriesZeta s * L ↗Λ s :=
      (dirichletSeriesZeta_mangoldt_reconstruction hs).symm
    _ = L ↗Λ s *
        InfoGeometry.Arithmetic.RiemannZetaEquivalences.dirichletSeriesZeta s :=
      mul_comm _ _

end InfoGeometry.Canonical.ActualRiemannZetaMellinTripletBridge
