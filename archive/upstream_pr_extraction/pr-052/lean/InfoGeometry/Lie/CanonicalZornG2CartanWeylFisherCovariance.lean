import InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariant

/-!
# Bilinear Fisher covariance for the concrete G₂ reflection consumers

The reflection owner already proves the quadratic Fisher covariance.  This
file exposes its polarized bilinear form without reproving the reflection,
Gibbs, or moment-map calculations.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2CartanWeylFisherCovariance

open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariant

open scoped BigOperators

variable {State : Type*} [Fintype State] [Nonempty State]

def fisherSouriauBilinear
    (W : WeylEquivariantEnsemble State)
    (beta v u : Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    v i * fisherSouriauMatrix W.datum beta i j * u j

theorem fisherSouriauBilinear_diag
    (W : WeylEquivariantEnsemble State) (beta v : Fin 2 → ℝ) :
    fisherSouriauBilinear W beta v v =
      fisherSouriauQuadratic W.datum beta v := rfl

private theorem fisherSouriauQuadratic_polarization
    (W : WeylEquivariantEnsemble State) (beta v u : Fin 2 → ℝ) :
    fisherSouriauQuadratic W.datum beta (v + u)
      - fisherSouriauQuadratic W.datum beta v
      - fisherSouriauQuadratic W.datum beta u =
      fisherSouriauBilinear W beta v u +
        fisherSouriauBilinear W beta u v := by
  unfold fisherSouriauQuadratic fisherSouriauBilinear
  simp only [Pi.add_apply]
  simp_rw [← Finset.sum_sub_distrib]
  simp_rw [add_mul, mul_add]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem fisherSouriauBilinear_symmetric
    (W : WeylEquivariantEnsemble State) (beta v u : Fin 2 → ℝ) :
    fisherSouriauBilinear W beta v u =
      fisherSouriauBilinear W beta u v := by
  unfold fisherSouriauBilinear
  calc
    (∑ i : Fin 2, ∑ j : Fin 2,
        v i * fisherSouriauMatrix W.datum beta i j * u j) =
      ∑ j : Fin 2, ∑ i : Fin 2,
        v i * fisherSouriauMatrix W.datum beta i j * u j := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin 2, ∑ i : Fin 2,
        u j * fisherSouriauMatrix W.datum beta j i * v i := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          rw [fisherSouriauMatrix_symmetric]
          ring
    _ = fisherSouriauBilinear W beta u v := by
          unfold fisherSouriauBilinear
          rw [Finset.sum_comm]

private theorem shortDualReal_add (v u : Fin 2 → ℝ) :
    canonicalShortReflectionDualReal (v + u) =
      canonicalShortReflectionDualReal v + canonicalShortReflectionDualReal u := by
  unfold canonicalShortReflectionDualReal
  ext i
  fin_cases i <;> simp <;> ring

private theorem longDualReal_add (v u : Fin 2 → ℝ) :
    canonicalLongReflectionDualReal (v + u) =
      canonicalLongReflectionDualReal v + canonicalLongReflectionDualReal u := by
  unfold canonicalLongReflectionDualReal
  ext i
  fin_cases i <;> simp <;> ring

theorem fisherSouriauBilinear_short_covariant
    (W : WeylEquivariantEnsemble State) (beta v u : Fin 2 → ℝ) :
    fisherSouriauBilinear W (canonicalShortReflectionDualReal beta) v u =
      fisherSouriauBilinear W beta
        (canonicalShortReflectionDualReal v)
        (canonicalShortReflectionDualReal u) := by
  have h := fisherSouriauQuadratic_short_covariant W beta (v + u)
  have hv := fisherSouriauQuadratic_short_covariant W beta v
  have hu := fisherSouriauQuadratic_short_covariant W beta u
  have hp := fisherSouriauQuadratic_polarization W
    (canonicalShortReflectionDualReal beta) v u
  have hp' := fisherSouriauQuadratic_polarization W beta
    (canonicalShortReflectionDualReal v)
    (canonicalShortReflectionDualReal u)
  rw [shortDualReal_add] at h
  rw [h, hv, hu] at hp
  have hs₁ := fisherSouriauBilinear_symmetric W
    (canonicalShortReflectionDualReal beta) v u
  have hs₂ := fisherSouriauBilinear_symmetric W beta
    (canonicalShortReflectionDualReal v)
    (canonicalShortReflectionDualReal u)
  linarith

theorem fisherSouriauBilinear_long_covariant
    (W : WeylEquivariantEnsemble State) (beta v u : Fin 2 → ℝ) :
    fisherSouriauBilinear W (canonicalLongReflectionDualReal beta) v u =
      fisherSouriauBilinear W beta
        (canonicalLongReflectionDualReal v)
        (canonicalLongReflectionDualReal u) := by
  have h := fisherSouriauQuadratic_long_covariant W beta (v + u)
  have hv := fisherSouriauQuadratic_long_covariant W beta v
  have hu := fisherSouriauQuadratic_long_covariant W beta u
  have hp := fisherSouriauQuadratic_polarization W
    (canonicalLongReflectionDualReal beta) v u
  have hp' := fisherSouriauQuadratic_polarization W beta
    (canonicalLongReflectionDualReal v)
    (canonicalLongReflectionDualReal u)
  rw [longDualReal_add] at h
  rw [h, hv, hu] at hp
  have hs₁ := fisherSouriauBilinear_symmetric W
    (canonicalLongReflectionDualReal beta) v u
  have hs₂ := fisherSouriauBilinear_symmetric W beta
    (canonicalLongReflectionDualReal v)
    (canonicalLongReflectionDualReal u)
  linarith

end InfoGeometry.Lie.CanonicalZornG2CartanWeylFisherCovariance
