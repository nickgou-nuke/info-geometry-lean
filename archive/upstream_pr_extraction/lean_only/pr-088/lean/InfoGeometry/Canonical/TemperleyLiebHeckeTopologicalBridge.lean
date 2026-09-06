import InfoGeometry.Canonical.HeckeBraidTopologicalBridge
import InfoGeometry.Canonical.TemperleyLiebJonesBridge

/-!
# Temperley--Lieb at `δ = 2` as the `q = 1` Hecke shadow

For a Temperley--Lieb system with loop parameter `2`, the shifted generators
`sᵢ = eᵢ - 1` are involutions and satisfy the Artin relation.  This owner
packages that finite noncommutative calculation as the generic topological
Hecke interface.  It is the Coxeter specialization, not a claim about a
nontrivial anyonic parameter.
-/

noncomputable section

namespace InfoGeometry.Canonical.TemperleyLiebHeckeTopologicalBridge

open CategoryTheory
open InfoGeometry.Canonical.HeckeBraidTopologicalBridge
open TemperleyLiebJonesBridge

variable {R : Type*} [Ring R] [Algebra ℂ R]
variable (sys : TemperleyLiebSystem (2 : ℂ) R)

private lemma self_loop_one_two_mul :
    sys.e1 * sys.e1 = 2 * sys.e1 := by
  simpa [Algebra.smul_def, map_ofNat (algebraMap ℂ R) 2] using sys.self_loop_1

private lemma self_loop_two_two_mul :
    sys.e2 * sys.e2 = 2 * sys.e2 := by
  simpa [Algebra.smul_def, map_ofNat (algebraMap ℂ R) 2] using sys.self_loop_2

private lemma shifted_artin_relation :
    (sys.e1 - 1) * (sys.e2 - 1) * (sys.e1 - 1) =
      (sys.e2 - 1) * (sys.e1 - 1) * (sys.e2 - 1) := by
  have hleft :
      (sys.e1 - 1) * (sys.e2 - 1) * (sys.e1 - 1) =
        sys.e1 - sys.e1 * sys.e2 - sys.e2 * sys.e1 + sys.e2 - 1 := by
    calc
      (sys.e1 - 1) * (sys.e2 - 1) * (sys.e1 - 1) =
          sys.e1 * sys.e2 * sys.e1 - sys.e1 * sys.e2 -
            sys.e1 * sys.e1 + sys.e1 - sys.e2 * sys.e1 +
            sys.e2 + sys.e1 - 1 := by noncomm_ring
      _ = sys.e1 - sys.e1 * sys.e2 - sys.e2 * sys.e1 + sys.e2 - 1 := by
        rw [sys.contraction_121, self_loop_one_two_mul]
        noncomm_ring
  have hright :
      (sys.e2 - 1) * (sys.e1 - 1) * (sys.e2 - 1) =
        sys.e2 - sys.e2 * sys.e1 - sys.e1 * sys.e2 + sys.e1 - 1 := by
    calc
      (sys.e2 - 1) * (sys.e1 - 1) * (sys.e2 - 1) =
          sys.e2 * sys.e1 * sys.e2 - sys.e2 * sys.e1 -
            sys.e2 * sys.e2 + sys.e2 - sys.e1 * sys.e2 +
            sys.e1 + sys.e2 - 1 := by noncomm_ring
      _ = sys.e2 - sys.e2 * sys.e1 - sys.e1 * sys.e2 + sys.e1 - 1 := by
        rw [sys.contraction_212, self_loop_two_two_mul]
        noncomm_ring
  rw [hleft, hright]
  noncomm_ring

variable [TopologicalSpace R] [ContinuousMul R]

/-- The first shifted TL generator satisfies the topological Hecke quadratic
relation. -/
theorem tl_delta_two_hecke1_leftTopCat_relation :
    leftMulTopCatHom ((sys.e1 - 1) + algebraMap ℂ R (1 : ℂ)) ≫
      leftMulTopCatHom ((sys.e1 - 1) - algebraMap ℂ R (1 : ℂ)) =
      TopCat.ofHom (ContinuousMap.const R 0) := by
  have h1 :
      ((sys.e1 - 1) - algebraMap ℂ R (1 : ℂ)) *
          ((sys.e1 - 1) + algebraMap ℂ R (1 : ℂ)⁻¹) = 0 := by
    simp only [map_one, inv_one]
    calc
      ((sys.e1 - 1) - 1) * ((sys.e1 - 1) + 1) =
          sys.e1 * sys.e1 - 2 * sys.e1 := by
            noncomm_ring
      _ = 0 := by rw [self_loop_one_two_mul]; noncomm_ring
  simpa only [inv_one] using
    hecke1_leftTopCat_relation (1 : ℂ) (sys.e1 - 1) h1

/-- The second shifted TL generator satisfies the topological Hecke
quadratic relation. -/
theorem tl_delta_two_hecke2_leftTopCat_relation :
    leftMulTopCatHom ((sys.e2 - 1) + algebraMap ℂ R (1 : ℂ)) ≫
      leftMulTopCatHom ((sys.e2 - 1) - algebraMap ℂ R (1 : ℂ)) =
      TopCat.ofHom (ContinuousMap.const R 0) := by
  have h2 :
      ((sys.e2 - 1) - algebraMap ℂ R (1 : ℂ)) *
          ((sys.e2 - 1) + algebraMap ℂ R (1 : ℂ)⁻¹) = 0 := by
    simp only [map_one, inv_one]
    calc
      ((sys.e2 - 1) - 1) * ((sys.e2 - 1) + 1) =
          sys.e2 * sys.e2 - 2 * sys.e2 := by
            noncomm_ring
      _ = 0 := by rw [self_loop_two_two_mul]; noncomm_ring
  simpa only [inv_one] using
    hecke2_leftTopCat_relation (1 : ℂ) (sys.e2 - 1) h2

/-- The shifted TL generators satisfy the Artin relation as continuous
left-multiplication maps. -/
theorem tl_delta_two_artin_leftTopCat_relation :
    leftMulTopCatHom (sys.e1 - 1) ≫
        leftMulTopCatHom (sys.e2 - 1) ≫
        leftMulTopCatHom (sys.e1 - 1) =
      leftMulTopCatHom (sys.e2 - 1) ≫
        leftMulTopCatHom (sys.e1 - 1) ≫
      leftMulTopCatHom (sys.e2 - 1) := by
  exact artin_leftTopCat_relation (sys.e1 - 1) (sys.e2 - 1)
    (shifted_artin_relation sys)

end InfoGeometry.Canonical.TemperleyLiebHeckeTopologicalBridge
