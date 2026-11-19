/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Tactic

/-!
# Root-Space Tschirnhaus and Vandermonde Plücker Data

This owner formalizes constructions on an ordered five-root vector over `ℂ`.
It keeps them separate from the source-ordered binary-quintic coefficient
representation and its Klein-orbit evaluation map. In particular, no root
extraction or `S₅`-quotient map is asserted here.

The ten oriented coordinates are indexed by increasing pairs of roots. The
linear difference bivector has the diagonal translation kernel; the cubic
Vandermonde bivector is the wedge of the centered root vector and its square.
Both are decomposable, and the latter has the stated degree-three affine
transformation law.
-/

namespace InfoGeometry.Erlangen.KleinQuinticTschirnhausPlucker

noncomputable section

/-- Increasing pairs index the ten independent Plücker coordinates of
`Λ² ℂ⁵`. -/
abbrev RootPair5 := {p : Fin 5 × Fin 5 // p.1 < p.2}

/-- The average of an ordered five-root vector, written explicitly to keep
the coefficient `1/5` visible in the Tschirnhaus projection. -/
def rootMean (x : Fin 5 → ℂ) : ℂ :=
  (x 0 + x 1 + x 2 + x 3 + x 4) / 5

/-- Centered roots, whose coordinate sum is zero. -/
def centeredRoots (x : Fin 5 → ℂ) : Fin 5 → ℂ :=
  fun i => x i - rootMean x

/-- The mean of the coordinatewise square of a root vector. -/
def squareMean (x : Fin 5 → ℂ) : ℂ :=
  ((x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2 + (x 4) ^ 2) / 5

/-- Centered quadratic root covariant. -/
def centeredRootSquares (x : Fin 5 → ℂ) : Fin 5 → ℂ :=
  fun i => (centeredRoots x i) ^ 2 - squareMean (centeredRoots x)

/-- The coordinate of the wedge `u ∧ v` at an oriented pair `(i,j)`.
Coordinates are stored only for `i < j` by `RootPair5`. -/
def wedgeCoordinate (u v : Fin 5 → ℂ) (i j : Fin 5) : ℂ :=
  u i * v j - u j * v i

/-- The ten-coordinate difference bivector `1 ∧ x`. -/
def rootDifferenceBivector (x : Fin 5 → ℂ) : RootPair5 → ℂ :=
  fun p => wedgeCoordinate (fun _ => 1) x p.1.1 p.1.2

@[simp] theorem rootDifferenceBivector_coordinate
    (x : Fin 5 → ℂ) (p : RootPair5) :
    rootDifferenceBivector x p = x p.1.2 - x p.1.1 := by
  simp [rootDifferenceBivector, wedgeCoordinate]

/-- A constant ordered root tuple lies in the kernel of the linear
root-difference bivector. -/
theorem rootDifferenceBivector_eq_zero_of_constant
    (x : Fin 5 → ℂ) (a : ℂ) (hx : ∀ i, x i = a) :
    rootDifferenceBivector x = 0 := by
  funext p
  rw [rootDifferenceBivector_coordinate, hx, hx, sub_self]
  rfl

/-- The ten-coordinate cubic Vandermonde bivector `y ∧ y²`, where `y` is
the centered root vector. -/
def tschirnhausVandermondeBivector (x : Fin 5 → ℂ) : RootPair5 → ℂ :=
  fun p => wedgeCoordinate (centeredRoots x) (centeredRootSquares x)
    p.1.1 p.1.2

/-- Under an affine change of roots, the centered roots transform by the
linear part alone. -/
theorem centeredRoots_affine (x : Fin 5 → ℂ) (μ τ : ℂ) :
    centeredRoots (fun i => μ * x i + τ) = fun i => μ * centeredRoots x i := by
  funext i
  fin_cases i <;> simp [centeredRoots, rootMean] <;> ring

/-- The Tschirnhaus projection has coordinate sum zero. -/
theorem centeredRoots_sum_zero (x : Fin 5 → ℂ) :
    centeredRoots x 0 + centeredRoots x 1 + centeredRoots x 2 +
      centeredRoots x 3 + centeredRoots x 4 = 0 := by
  simp [centeredRoots, rootMean]
  ring

/-- On centered root vectors the difference bivector has no nonzero
constant-vector kernel: if all ten independent differences vanish, the
centered vector itself is zero. -/
theorem centeredRoots_eq_zero_of_differenceBivector_eq_zero
    (x : Fin 5 → ℂ) (hx : rootDifferenceBivector x = 0) :
    centeredRoots x = 0 := by
  have hall : ∀ i : Fin 5, x i = x 0 := by
    intro i
    fin_cases i
    · rfl
    · have hcoord : x 1 - x 0 = 0 := by
        simpa [rootDifferenceBivector_coordinate] using
          congrFun hx (⟨(0, 1), by decide⟩ : RootPair5)
      exact sub_eq_zero.mp hcoord
    · have hcoord : x 2 - x 0 = 0 := by
        simpa [rootDifferenceBivector_coordinate] using
          congrFun hx (⟨(0, 2), by decide⟩ : RootPair5)
      exact sub_eq_zero.mp hcoord
    · have hcoord : x 3 - x 0 = 0 := by
        simpa [rootDifferenceBivector_coordinate] using
          congrFun hx (⟨(0, 3), by decide⟩ : RootPair5)
      exact sub_eq_zero.mp hcoord
    · have hcoord : x 4 - x 0 = 0 := by
        simpa [rootDifferenceBivector_coordinate] using
          congrFun hx (⟨(0, 4), by decide⟩ : RootPair5)
      exact sub_eq_zero.mp hcoord
  funext i
  have hs := centeredRoots_sum_zero x
  have hconst : x 0 - rootMean x = 0 := by
    have hmul : (5 : ℂ) * (x 0 - rootMean x) = 0 := by
      calc
        (5 : ℂ) * (x 0 - rootMean x) =
            centeredRoots x 0 + centeredRoots x 1 + centeredRoots x 2 +
              centeredRoots x 3 + centeredRoots x 4 := by
          simp [centeredRoots, rootMean, hall 1, hall 2, hall 3, hall 4]
          ring
        _ = 0 := hs
    exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  change x i - rootMean x = 0
  rw [hall i, hconst]

/-- On the Tschirnhaus sum-zero subspace, the root-difference bivector has
trivial kernel. This removes the diagonal base point of `1 ∧ x` before
projectivization. -/
theorem rootDifferenceBivector_eq_zero_of_sum_zero
    (x : Fin 5 → ℂ)
    (hsum : x 0 + x 1 + x 2 + x 3 + x 4 = 0)
    (hB : rootDifferenceBivector x = 0) :
    x = 0 := by
  have hcentered := centeredRoots_eq_zero_of_differenceBivector_eq_zero x hB
  have hmean : rootMean x = 0 := by
    unfold rootMean
    rw [hsum]
    norm_num
  funext i
  have hi := congrFun hcentered i
  change x i - rootMean x = 0 at hi
  simpa [hmean] using hi

/-- Proportional root-difference bivectors on the Tschirnhaus subspace come
from proportional centered root vectors. Together with homogeneity, this is
the injectivity criterion for the induced map on projective classes. -/
theorem rootDifferenceBivector_smul_injective_on_sum_zero
    (x y : Fin 5 → ℂ) (c : ℂ)
    (hx : x 0 + x 1 + x 2 + x 3 + x 4 = 0)
    (hy : y 0 + y 1 + y 2 + y 3 + y 4 = 0)
    (hB : rootDifferenceBivector x = c • rootDifferenceBivector y) :
    x = c • y := by
  have hsum :
      (x 0 - c * y 0) + (x 1 - c * y 1) + (x 2 - c * y 2) +
        (x 3 - c * y 3) + (x 4 - c * y 4) = 0 := by
    linear_combination hx - c * hy
  have hkernel : rootDifferenceBivector (x - c • y) = 0 := by
    funext p
    have hp := congrFun hB p
    simp only [rootDifferenceBivector_coordinate, Pi.smul_apply,
      smul_eq_mul] at hp
    simp only [Pi.zero_apply]
    simp only [rootDifferenceBivector_coordinate]
    change (x p.1.2 - c * y p.1.2) -
      (x p.1.1 - c * y p.1.1) = 0
    linear_combination hp
  have hzero := rootDifferenceBivector_eq_zero_of_sum_zero (x - c • y)
    (by simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hsum)
    hkernel
  have hxy : x - c • y = 0 := hzero
  exact sub_eq_zero.mp hxy

/-- The projective class of the root-difference bivector on the zero-sum
Tschirnhaus subspace. Triviality of the restricted kernel is used explicitly
to ensure that the bivector is nonzero for every nonzero representative. -/
noncomputable def projectiveRootDifferenceBivector
    (x : Fin 5 → ℂ)
    (hsum : x 0 + x 1 + x 2 + x 3 + x 4 = 0)
    (hx : x ≠ 0) : Projectivization ℂ (RootPair5 → ℂ) :=
  Projectivization.mk ℂ (rootDifferenceBivector x) (by
    intro hB
    exact hx (rootDifferenceBivector_eq_zero_of_sum_zero x hsum hB))

/-- The projective difference-bivector construction is independent of the
chosen nonzero scalar representative in the zero-sum Tschirnhaus subspace.
This establishes projective descent on that subspace, rather than merely
recording homogeneity on the full five-root space. -/
theorem projectiveRootDifferenceBivector_smul
    (x : Fin 5 → ℂ)
    (hsum : x 0 + x 1 + x 2 + x 3 + x 4 = 0)
    (hx : x ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    projectiveRootDifferenceBivector (c • x)
      (by
        simp only [Pi.smul_apply, smul_eq_mul]
        calc
          c * x 0 + c * x 1 + c * x 2 + c * x 3 + c * x 4 =
              c * (x 0 + x 1 + x 2 + x 3 + x 4) := by ring
          _ = 0 := by rw [hsum, mul_zero])
      (by
        intro hcx
        apply hx
        have hzero : c • x = 0 := hcx
        exact (smul_eq_zero.mp hzero).resolve_left hc) =
    projectiveRootDifferenceBivector x hsum hx := by
  have hB : rootDifferenceBivector (c • x) = c • rootDifferenceBivector x := by
    funext p
    simp [rootDifferenceBivector_coordinate, Pi.smul_apply, smul_eq_mul]
    ring
  have hBne : rootDifferenceBivector x ≠ 0 := by
    intro h
    exact hx (rootDifferenceBivector_eq_zero_of_sum_zero x hsum h)
  apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ hBne).2
  refine ⟨Units.mk0 c hc, ?_⟩
  exact hB.symm

/-- Equal projective root-difference bivectors on the zero-sum subspace
come from proportional root vectors. This proves injectivity of the induced
map on projective Tschirnhaus classes. -/
theorem projectiveRootDifferenceBivector_injective
    (x y : Fin 5 → ℂ)
    (hxsum : x 0 + x 1 + x 2 + x 3 + x 4 = 0)
    (hysum : y 0 + y 1 + y 2 + y 3 + y 4 = 0)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hproj : projectiveRootDifferenceBivector x hxsum hx =
      projectiveRootDifferenceBivector y hysum hy) :
    ∃ c : ℂˣ, x = (c : ℂ) • y := by
  have hBx : rootDifferenceBivector x ≠ 0 := by
    intro h
    exact hx (rootDifferenceBivector_eq_zero_of_sum_zero x hxsum h)
  have hBy : rootDifferenceBivector y ≠ 0 := by
    intro h
    exact hy (rootDifferenceBivector_eq_zero_of_sum_zero y hysum h)
  obtain ⟨c, hc⟩ :=
    (Projectivization.mk_eq_mk_iff ℂ _ _ hBx hBy).mp hproj
  refine ⟨c, ?_⟩
  apply rootDifferenceBivector_smul_injective_on_sum_zero x y c
    hxsum hysum
  simpa only [Units.smul_def] using hc.symm

/-- Centered quadratic roots have affine weight two. Translation disappears
and dilation by `μ` multiplies them by `μ²`. -/
theorem centeredRootSquares_affine (x : Fin 5 → ℂ) (μ τ : ℂ) :
    centeredRootSquares (fun i => μ * x i + τ) =
      fun i => μ ^ 2 * centeredRootSquares x i := by
  funext i
  unfold centeredRootSquares
  rw [centeredRoots_affine]
  simp [squareMean]
  ring

/-- The four-index Plücker relation for any wedge in five dimensions. This
is the decomposability identity in `Λ² ℂ⁵`, not a special property of the
root-difference subspace. -/
theorem wedge_plucker_relation (u v : Fin 5 → ℂ)
    (i j k l : Fin 5) :
    (u i * v j - u j * v i) * (u k * v l - u l * v k) -
      (u i * v k - u k * v i) * (u j * v l - u l * v j) +
      (u i * v l - u l * v i) * (u j * v k - u k * v j) = 0 := by
  ring

/-- Every four-index Plücker relation vanishes for the root-difference
bivector. -/
theorem rootDifferenceBivector_plucker (x : Fin 5 → ℂ)
    (i j k l : Fin 5) :
    (wedgeCoordinate (fun _ => 1) x i j) *
        (wedgeCoordinate (fun _ => 1) x k l) -
      (wedgeCoordinate (fun _ => 1) x i k) *
        (wedgeCoordinate (fun _ => 1) x j l) +
      (wedgeCoordinate (fun _ => 1) x i l) *
        (wedgeCoordinate (fun _ => 1) x j k) = 0 := by
  exact wedge_plucker_relation (fun _ => 1) x i j k l

/-- Every four-index Plücker relation vanishes for the cubic Vandermonde
bivector because it is the wedge of two explicit root covariants. -/
theorem tschirnhausVandermondeBivector_plucker (x : Fin 5 → ℂ)
    (i j k l : Fin 5) :
    (wedgeCoordinate (centeredRoots x) (centeredRootSquares x) i j) *
        (wedgeCoordinate (centeredRoots x) (centeredRootSquares x) k l) -
      (wedgeCoordinate (centeredRoots x) (centeredRootSquares x) i k) *
        (wedgeCoordinate (centeredRoots x) (centeredRootSquares x) j l) +
      (wedgeCoordinate (centeredRoots x) (centeredRootSquares x) i l) *
        (wedgeCoordinate (centeredRoots x) (centeredRootSquares x) j k) = 0 := by
  exact wedge_plucker_relation (centeredRoots x) (centeredRootSquares x)
    i j k l

/-- The degree-three affine covariance of the centered Vandermonde
bivector. -/
theorem tschirnhausVandermondeBivector_affine (x : Fin 5 → ℂ) (μ τ : ℂ) :
    tschirnhausVandermondeBivector (fun i => μ * x i + τ) =
      fun p => μ ^ 3 * tschirnhausVandermondeBivector x p := by
  funext p
  rw [tschirnhausVandermondeBivector, tschirnhausVandermondeBivector,
    centeredRoots_affine, centeredRootSquares_affine]
  simp only [wedgeCoordinate]
  ring

/-- The simplicial coboundary of the cubic Vandermonde coordinates factors
as the product of the three corresponding root differences. -/
theorem vandermonde_coboundary (x : Fin 5 → ℂ) (i j k : Fin 5) :
    (x i * x j ^ 2 - x j * x i ^ 2) +
      (x j * x k ^ 2 - x k * x j ^ 2) -
      (x i * x k ^ 2 - x k * x i ^ 2) =
      (x j - x i) * (x k - x j) * (x k - x i) := by
  ring

/-- The centered cubic Vandermonde bivector has the same simplicial
coboundary factorization, now expressed in the original (uncentered) root
differences. Centering subtracts a common scalar from all roots, which leaves
each difference unchanged. -/
theorem tschirnhausVandermondeBivector_coboundary
    (x : Fin 5 → ℂ) (i j k : Fin 5) :
    (wedgeCoordinate (centeredRoots x) (centeredRootSquares x) i j) +
      (wedgeCoordinate (centeredRoots x) (centeredRootSquares x) j k) -
      (wedgeCoordinate (centeredRoots x) (centeredRootSquares x) i k) =
      (x j - x i) * (x k - x j) * (x k - x i) := by
  have hcoord (a b : Fin 5) :
      wedgeCoordinate (centeredRoots x) (centeredRootSquares x) a b =
        (centeredRoots x a) * (centeredRoots x b) ^ 2 -
          (centeredRoots x b) * (centeredRoots x a) ^ 2 +
          squareMean (centeredRoots x) *
            (centeredRoots x b - centeredRoots x a) := by
    simp [wedgeCoordinate, centeredRootSquares]
    ring_nf
  rw [hcoord i j, hcoord j k, hcoord i k]
  have hraw := vandermonde_coboundary (centeredRoots x) i j k
  have hdiff (a b : Fin 5) : centeredRoots x b - centeredRoots x a = x b - x a := by
    simp [centeredRoots]
  calc
    (centeredRoots x i * (centeredRoots x j) ^ 2 -
          centeredRoots x j * (centeredRoots x i) ^ 2 +
        squareMean (centeredRoots x) * (centeredRoots x j - centeredRoots x i)) +
        (centeredRoots x j * (centeredRoots x k) ^ 2 -
          centeredRoots x k * (centeredRoots x j) ^ 2 +
        squareMean (centeredRoots x) * (centeredRoots x k - centeredRoots x j)) -
        (centeredRoots x i * (centeredRoots x k) ^ 2 -
          centeredRoots x k * (centeredRoots x i) ^ 2 +
        squareMean (centeredRoots x) * (centeredRoots x k - centeredRoots x i))
        = (centeredRoots x j - centeredRoots x i) *
          (centeredRoots x k - centeredRoots x j) *
          (centeredRoots x k - centeredRoots x i) := by
            rw [← hraw]
            ring
    _ = (x j - x i) * (x k - x j) * (x k - x i) := by
          rw [hdiff i j, hdiff j k, hdiff i k]

/-- With three pairwise distinct roots, the cubic Tschirnhaus Vandermonde
bivector is not in the image of the linear root-difference map. Every
root-difference coordinate is an exact 1-coboundary and has zero cyclic
coboundary, while this cubic bivector has a nonzero cyclic coboundary. -/
theorem tschirnhausVandermondeBivector_not_rootDifferenceBivector
    (x y : Fin 5 → ℂ) (i j k : Fin 5)
    (hij : i < j) (hjk : j < k)
    (hij_ne : x i ≠ x j) (hjk_ne : x j ≠ x k)
    (hik_ne : x i ≠ x k) :
    tschirnhausVandermondeBivector x ≠ rootDifferenceBivector y := by
  intro hEq
  let p_ij : RootPair5 := ⟨(i, j), hij⟩
  let p_jk : RootPair5 := ⟨(j, k), hjk⟩
  let p_ik : RootPair5 := ⟨(i, k), lt_trans hij hjk⟩
  have h_ij := congrFun hEq p_ij
  have h_jk := congrFun hEq p_jk
  have h_ik := congrFun hEq p_ik
  simp only [tschirnhausVandermondeBivector, rootDifferenceBivector_coordinate]
    at h_ij h_jk h_ik
  have hFlat :
      (wedgeCoordinate (centeredRoots x) (centeredRootSquares x) i j) +
        (wedgeCoordinate (centeredRoots x) (centeredRootSquares x) j k) -
        (wedgeCoordinate (centeredRoots x) (centeredRootSquares x) i k) = 0 := by
    rw [h_ij, h_jk, h_ik]
    ring
  have hCurved := tschirnhausVandermondeBivector_coboundary x i j k
  rw [hFlat] at hCurved
  have hnonzero :
      (x j - x i) * (x k - x j) * (x k - x i) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hij_ne))
        (sub_ne_zero.mpr (Ne.symm hjk_ne))
    · exact sub_ne_zero.mpr (Ne.symm hik_ne)
  exact hnonzero hCurved.symm

/-- The linear difference bivector is invariant under common root
translation and has weight one under root dilation. -/
theorem rootDifferenceBivector_affine (x : Fin 5 → ℂ) (μ τ : ℂ) :
    rootDifferenceBivector (fun i => μ * x i + τ) =
      fun p => μ * rootDifferenceBivector x p := by
  funext p
  simp [rootDifferenceBivector, wedgeCoordinate]
  ring

end

end InfoGeometry.Erlangen.KleinQuinticTschirnhausPlucker
