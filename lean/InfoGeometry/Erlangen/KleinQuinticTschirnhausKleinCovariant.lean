/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Tactic
import InfoGeometry.Projective.KleinQuadricPlucker
import InfoGeometry.Erlangen.KleinQuinticTschirnhausPlucker

/-!
# The Centered Tschirnhaus Klein Covariant of Five Ordered Roots

For an ordered affine root tuple `x : Fin 5 → ℂ`, center the tuple to
`y = x - mean(x)·1`, then center its coordinatewise square to `z`. The
decomposable bivector `y ∧ z` lives in the six-dimensional exterior square
of the four-dimensional standard representation. This is a root-space
covariant, not a map from quintic coefficient classes: it has root-dilation
weight three, is invariant under common translation, and is undefined as a
projective point on its nonzero base locus.
-/

noncomputable section

namespace InfoGeometry.Erlangen.KleinQuinticTschirnhausKleinCovariant

open InfoGeometry.Projective.KleinQuadricPlucker

/-- Arithmetic mean of a five-root tuple. -/
def rootMean (x : Fin 5 → ℂ) : ℂ := (∑ i : Fin 5, x i) / 5

/-- The monic polynomial with the ordered root tuple `x`, counted with
multiplicity. -/
def rootPolynomial (x : Fin 5 → ℂ) : Polynomial ℂ :=
  ∏ i : Fin 5, (Polynomial.X - Polynomial.C (x i))

/-- The polynomial assembled from five ordered roots is monic. -/
theorem rootPolynomial_monic (x : Fin 5 → ℂ) : (rootPolynomial x).Monic := by
  unfold rootPolynomial
  exact Polynomial.monic_prod_X_sub_C x Finset.univ

/-- The ordered-root polynomial is unchanged by reindexing the roots by any
permutation. This is the forward, symmetric Vieta direction. -/
theorem rootPolynomial_perm (x : Fin 5 → ℂ) (σ : Equiv.Perm (Fin 5)) :
    rootPolynomial (fun i => x (σ i)) = rootPolynomial x := by
  unfold rootPolynomial
  exact Fintype.prod_bijective σ σ.bijective
    (fun i => Polynomial.X - Polynomial.C (x (σ i)))
    (fun i => Polynomial.X - Polynomial.C (x i))
    (by intro i; rfl)

/-- Every listed root is a root of the polynomial assembled from the tuple. -/
theorem rootPolynomial_eval_eq_zero (x : Fin 5 → ℂ) (i : Fin 5) :
    (rootPolynomial x).eval (x i) = 0 := by
  classical
  simp only [rootPolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

/-- Uniform nonzero scaling of polynomial coefficients leaves the root locus
unchanged. This is distinct from dilating the root tuple. -/
theorem polynomial_smul_root_iff (P : Polynomial ℂ) (c : ℂ) (hc : c ≠ 0)
    (r : ℂ) :
    (c • P).eval r = 0 ↔ P.eval r = 0 := by
  rw [Polynomial.eval_smul]
  simp only [smul_eq_mul]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hc
  · intro h
    simp [h]

/-- Projection of an ordered root tuple to the zero-sum standard module. -/
def centeredRoots (x : Fin 5 → ℂ) : Fin 5 → ℂ :=
  fun i => x i - rootMean x

/-- The centered quadratic Tschirnhaus covariant. -/
def centeredRootSquares (x : Fin 5 → ℂ) : Fin 5 → ℂ :=
  centeredRoots (fun i => centeredRoots x i ^ 2)

/-- The first four coordinates identify the zero-sum standard module with
`ℂ⁴`; the fifth coordinate is forced by the zero-sum relation. -/
def standardCoordinates (y : Fin 5 → ℂ) : Vec4 ℂ :=
  ⟨y 0, y 1, y 2, y 3⟩

/-- The curved Klein bivector `y ∧ z` of the centered linear and quadratic
root covariants. -/
def rootKleinOmega (x : Fin 5 → ℂ) : Plucker6 ℂ :=
  Plucker6.pluckerLine (standardCoordinates (centeredRoots x))
    (standardCoordinates (centeredRootSquares x))

/-- The five centered roots sum to zero. -/
theorem centeredRoots_sum_zero (x : Fin 5 → ℂ) :
    ∑ i : Fin 5, centeredRoots x i = 0 := by
  unfold centeredRoots rootMean
  rw [Finset.sum_sub_distrib]
  simp
  field_simp
  ring

/-- Scaling the root tuple scales its centered part with weight one. -/
theorem centeredRoots_scale (x : Fin 5 → ℂ) (μ : ℂ) :
    centeredRoots (fun i => μ * x i) = fun i => μ * centeredRoots x i := by
  funext i
  unfold centeredRoots rootMean
  rw [← Finset.mul_sum]
  ring

/-- Translating every root does not change its centered part. -/
theorem centeredRoots_translate (x : Fin 5 → ℂ) (τ : ℂ) :
    centeredRoots (fun i => x i + τ) = centeredRoots x := by
  funext i
  unfold centeredRoots rootMean
  rw [Finset.sum_add_distrib]
  simp
  ring

/-- Centering commutes with reindexing by a root permutation. -/
theorem centeredRoots_perm (x : Fin 5 → ℂ) (σ : Equiv.Perm (Fin 5)) :
    centeredRoots (fun i => x (σ i)) = fun i => centeredRoots x (σ i) := by
  have hsum : (∑ i : Fin 5, x (σ i)) = ∑ i : Fin 5, x i :=
    Fintype.sum_bijective σ σ.bijective
      (fun i => x (σ i)) (fun i => x i) (by intro i; rfl)
  funext i
  unfold centeredRoots rootMean
  rw [hsum]

/-- Centered quadratic roots transform by the same permutation. -/
theorem centeredRootSquares_perm (x : Fin 5 → ℂ)
    (σ : Equiv.Perm (Fin 5)) :
    centeredRootSquares (fun i => x (σ i)) =
      fun i => centeredRootSquares x (σ i) := by
  unfold centeredRootSquares
  rw [centeredRoots_perm]
  simpa [centeredRootSquares] using
    centeredRoots_perm (fun i => centeredRoots x i ^ 2) σ

/-- Reconstruct the fifth coordinate of a vector in the zero-sum standard
representation from its first four coordinates. -/
private def standardLift (v : Vec4 ℂ) : Fin 5 → ℂ := fun i =>
  match i.val with
  | 0 => v.x0
  | 1 => v.x1
  | 2 => v.x2
  | 3 => v.x3
  | _ => -(v.x0 + v.x1 + v.x2 + v.x3)

/-- The coordinate action of a root permutation on the zero-sum standard
representation, written in the first-four-coordinate chart. -/
def standardPermutationAction (σ : Equiv.Perm (Fin 5)) (v : Vec4 ℂ) : Vec4 ℂ :=
  standardCoordinates (fun i => standardLift v (σ i))

/-- The reconstructed standard vector has coordinate sum zero. -/
private theorem standardLift_sum_zero (v : Vec4 ℂ) :
    ∑ i : Fin 5, standardLift v i = 0 := by
  simp [standardLift, Fin.sum_univ_succ]

/-- A zero-sum vector is recovered by lifting its first four coordinates. -/
private theorem standardLift_standardCoordinates
    (y : Fin 5 → ℂ) (hy : ∑ i : Fin 5, y i = 0) :
    standardLift (standardCoordinates y) = y := by
  have hy' : y 0 + (y 1 + (y 2 + (y 3 + y 4))) = 0 := by
    simpa [Fin.sum_univ_succ] using hy
  have hsum : y 0 + y 1 + y 2 + y 3 + y 4 = 0 := by
    linear_combination hy'
  have hlast : y 4 = -(y 0 + y 1 + y 2 + y 3) := by
    linear_combination hsum
  funext i
  fin_cases i
  · simp [standardLift, standardCoordinates]
  · simp [standardLift, standardCoordinates]
  · simp [standardLift, standardCoordinates]
  · simp [standardLift, standardCoordinates]
  · simp [standardLift, standardCoordinates, hlast]

/-- The first-four-coordinate chart intertwines root reindexing with the
induced coordinate action on the four-dimensional zero-sum standard module. -/
theorem standardCoordinates_perm
    (y : Fin 5 → ℂ) (hy : ∑ i : Fin 5, y i = 0)
    (σ : Equiv.Perm (Fin 5)) :
    standardCoordinates (fun i => y (σ i)) =
      standardPermutationAction σ (standardCoordinates y) := by
  rw [← standardLift_standardCoordinates y hy]
  rfl

/-- The induced coordinate maps compose by precomposition, with the order
recorded explicitly in `Equiv.trans`. -/
theorem standardPermutationAction_comp
    (σ τ : Equiv.Perm (Fin 5)) (v : Vec4 ℂ) :
    standardPermutationAction σ (standardPermutationAction τ v) =
      standardPermutationAction (σ.trans τ) v := by
  have hsum : ∑ i : Fin 5, standardLift v (τ i) = 0 := by
    calc
      (∑ i : Fin 5, standardLift v (τ i)) =
          ∑ i : Fin 5, standardLift v i := by
            exact Fintype.sum_bijective τ τ.bijective
              (fun i => standardLift v (τ i)) (fun i => standardLift v i)
              (by intro i; rfl)
      _ = 0 := standardLift_sum_zero v
  unfold standardPermutationAction
  rw [standardLift_standardCoordinates _ hsum]
  rfl

/-- The identity permutation acts as the identity in the first-four chart. -/
theorem standardPermutationAction_refl (v : Vec4 ℂ) :
    standardPermutationAction (Equiv.refl (Fin 5)) v = v := by
  cases v with
  | mk x0 x1 x2 x3 =>
      simp [standardPermutationAction, standardCoordinates, standardLift]

/-- The centered quadratic covariant has root-dilation weight two. -/
theorem centeredRootSquares_scale (x : Fin 5 → ℂ) (μ : ℂ) :
    centeredRootSquares (fun i => μ * x i) =
      fun i => μ ^ 2 * centeredRootSquares x i := by
  rw [centeredRootSquares, centeredRootSquares, centeredRoots_scale]
  have hsq : (fun i : Fin 5 => (μ * centeredRoots x i) ^ 2) =
      fun i => μ ^ 2 * centeredRoots x i ^ 2 := by
    funext i
    ring
  rw [hsq, centeredRoots_scale]

/-- The centered quadratic covariant is translation invariant and has weight
two under root dilation. -/
theorem centeredRootSquares_affine (x : Fin 5 → ℂ) (μ τ : ℂ) :
    centeredRootSquares (fun i => μ * x i + τ) =
      fun i => μ ^ 2 * centeredRootSquares x i := by
  unfold centeredRootSquares
  rw [centeredRoots_translate (fun i => μ * x i) τ]
  exact centeredRootSquares_scale x μ

/-- Restricting a coordinatewise scalar multiple to the chosen basis of the
zero-sum module agrees with `Vec4.scale`. -/
theorem standardCoordinates_scale (y : Fin 5 → ℂ) (μ : ℂ) :
    standardCoordinates (fun i => μ * y i) =
      Vec4.scale μ (standardCoordinates y) := by
  rfl

/-- The Tschirnhaus Klein covariant has exact affine-root weight three:
`Ω(μx + τ) = μ³ Ω(x)`. -/
theorem rootKleinOmega_affine
    (x : Fin 5 → ℂ) (μ τ : ℂ) :
    rootKleinOmega (fun i => μ * x i + τ) =
      Plucker6.scale (μ ^ 3) (rootKleinOmega x) := by
  rw [rootKleinOmega, rootKleinOmega,
    centeredRoots_translate (fun i => μ * x i) τ,
    centeredRootSquares_affine]
  rw [centeredRoots_scale, standardCoordinates_scale, standardCoordinates_scale,
    Plucker6.pluckerLine_scale_left, Plucker6.pluckerLine_scale_right]
  apply Plucker6.ext <;> simp [Plucker6.scale] <;> ring

/-- Every value of the Tschirnhaus covariant lies on Klein's quadric. -/
theorem rootKleinOmega_on_klein (x : Fin 5 → ℂ) :
    Plucker6.kleinQ (rootKleinOmega x) = 0 := by
  exact Plucker6.kleinQ_pluckerLine
    (standardCoordinates (centeredRoots x))
    (standardCoordinates (centeredRootSquares x))

/-- The six Plücker coordinates in the fixed order `01, 02, 03, 12, 13,
23`, represented as a vector so the Klein covariant can be projectivized. -/
def rootKleinOmegaCoordinates (x : Fin 5 → ℂ) : Fin 6 → ℂ :=
  let P := rootKleinOmega x
  fun i => match i.val with
    | 0 => P.p01
    | 1 => P.p02
    | 2 => P.p03
    | 3 => P.p12
    | 4 => P.p13
    | _ => P.p23

/-- A nonzero Klein bivector has a nonzero six-coordinate representative. -/
theorem rootKleinOmegaCoordinates_ne_zero (x : Fin 5 → ℂ)
    (hΩ : rootKleinOmega x ≠ ⟨0, 0, 0, 0, 0, 0⟩) :
    rootKleinOmegaCoordinates x ≠ 0 := by
  intro hcoords
  apply hΩ
  apply Plucker6.ext
  · have h := congrFun hcoords ⟨0, by decide⟩
    simpa [rootKleinOmegaCoordinates] using h
  · have h := congrFun hcoords ⟨1, by decide⟩
    simpa [rootKleinOmegaCoordinates] using h
  · have h := congrFun hcoords ⟨2, by decide⟩
    simpa [rootKleinOmegaCoordinates] using h
  · have h := congrFun hcoords ⟨3, by decide⟩
    simpa [rootKleinOmegaCoordinates] using h
  · have h := congrFun hcoords ⟨4, by decide⟩
    simpa [rootKleinOmegaCoordinates] using h
  · have h := congrFun hcoords ⟨5, by decide⟩
    simpa [rootKleinOmegaCoordinates] using h

/-- Projective Klein point of the centered root covariant. The hypothesis
excludes exactly the covariant's base locus. -/
noncomputable def projectiveRootKleinOmega (x : Fin 5 → ℂ)
    (hΩ : rootKleinOmega x ≠ ⟨0, 0, 0, 0, 0, 0⟩) :
    Projectivization ℂ (Fin 6 → ℂ) :=
  Projectivization.mk ℂ (rootKleinOmegaCoordinates x)
    (rootKleinOmegaCoordinates_ne_zero x hΩ)

/-- Root dilation preserves the projective Klein point on the nonzero locus:
the affine-root weight three is the scalar removed by projectivization. -/
theorem projectiveRootKleinOmega_scale
    (x : Fin 5 → ℂ) (μ : ℂ) (hμ : μ ≠ 0)
    (hΩ : rootKleinOmega x ≠ ⟨0, 0, 0, 0, 0, 0⟩) :
    projectiveRootKleinOmega (fun i => μ * x i)
      (by
        intro hzero
        apply hΩ
        have hAff : rootKleinOmega (fun i => μ * x i) =
            Plucker6.scale (μ ^ 3) (rootKleinOmega x) := by
          simpa using rootKleinOmega_affine x μ 0
        have hscale : Plucker6.scale (μ ^ 3) (rootKleinOmega x) =
            ⟨0, 0, 0, 0, 0, 0⟩ := by
          exact hAff.symm.trans hzero
        have hμ3 : μ ^ 3 ≠ 0 := pow_ne_zero 3 hμ
        apply Plucker6.ext
        · have h := congrArg Plucker6.p01 hscale
          exact (mul_eq_zero.mp (by simpa [Plucker6.scale] using h)).resolve_left hμ3
        · have h := congrArg Plucker6.p02 hscale
          exact (mul_eq_zero.mp (by simpa [Plucker6.scale] using h)).resolve_left hμ3
        · have h := congrArg Plucker6.p03 hscale
          exact (mul_eq_zero.mp (by simpa [Plucker6.scale] using h)).resolve_left hμ3
        · have h := congrArg Plucker6.p12 hscale
          exact (mul_eq_zero.mp (by simpa [Plucker6.scale] using h)).resolve_left hμ3
        · have h := congrArg Plucker6.p13 hscale
          exact (mul_eq_zero.mp (by simpa [Plucker6.scale] using h)).resolve_left hμ3
        · have h := congrArg Plucker6.p23 hscale
          exact (mul_eq_zero.mp (by simpa [Plucker6.scale] using h)).resolve_left hμ3)
      = projectiveRootKleinOmega x hΩ := by
  have hcoord : rootKleinOmegaCoordinates (fun i => μ * x i) =
      μ ^ 3 • rootKleinOmegaCoordinates x := by
    have hAff : rootKleinOmega (fun i => μ * x i) =
        Plucker6.scale (μ ^ 3) (rootKleinOmega x) := by
      simpa using rootKleinOmega_affine x μ 0
    unfold rootKleinOmegaCoordinates
    rw [hAff]
    funext i
    fin_cases i <;> rfl
  have hμ3 : μ ^ 3 ≠ 0 := pow_ne_zero 3 hμ
  apply (Projectivization.mk_eq_mk_iff ℂ _ _ _
    (rootKleinOmegaCoordinates_ne_zero x hΩ)).2
  refine ⟨Units.mk0 (μ ^ 3) hμ3, ?_⟩
  exact hcoord.symm

/-- The six-coordinate Tschirnhaus Klein bivector is covariant under root
permutations through the induced action on the zero-sum standard module.
This is an equivariance statement upstairs on ordered roots; it does not
descend to a fixed Plücker vector on coefficient classes. -/
theorem rootKleinOmega_perm (x : Fin 5 → ℂ) (σ : Equiv.Perm (Fin 5)) :
    rootKleinOmega (fun i => x (σ i)) =
      Plucker6.pluckerLine
        (standardPermutationAction σ (standardCoordinates (centeredRoots x)))
        (standardPermutationAction σ (standardCoordinates (centeredRootSquares x))) := by
  have hsumSq : ∑ i : Fin 5, centeredRootSquares x i = 0 := by
    simpa [centeredRootSquares] using
      centeredRoots_sum_zero (fun i => centeredRoots x i ^ 2)
  unfold rootKleinOmega
  rw [centeredRoots_perm, centeredRootSquares_perm,
    standardCoordinates_perm _ (centeredRoots_sum_zero x) σ,
    standardCoordinates_perm _ hsumSq σ]

/-- The finite set of Klein covariants obtained from all orderings of a root
tuple. This is the natural unordered-root object at the level of the raw
covariant; it is not asserted to be a classical resolvent or a map from
coefficient classes. -/
def rootKleinOmegaOrbit (x : Fin 5 → ℂ) : Set (Plucker6 ℂ) :=
  Set.range fun σ : Equiv.Perm (Fin 5) =>
    rootKleinOmega (fun i => x (σ i))

/-- Reordering the roots does not change their covariant orbit. Together with
`rootPolynomial_perm`, this gives a genuinely ordering-independent object
over the ordered-root presentation of a monic quintic. -/
theorem rootKleinOmegaOrbit_perm (x : Fin 5 → ℂ) (τ : Equiv.Perm (Fin 5)) :
    rootKleinOmegaOrbit (fun i => x (τ i)) = rootKleinOmegaOrbit x := by
  ext P
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ.trans τ, ?_⟩
    simpa [rootKleinOmegaOrbit, Equiv.trans_apply] using hσ
  · rintro ⟨σ, hσ⟩
    refine ⟨σ.trans τ.symm, ?_⟩
    simpa [rootKleinOmegaOrbit, Equiv.trans_apply] using hσ

/-- The full-permutation orbit polynomial of the `01` Plücker coordinate,
with one factor for each of the 120 permutations and multiplicities retained.
This is a canonical invariant polynomial attached to this coordinate choice;
it is not asserted to be Cayley's degree-six or Klein's degree-five classical
resolvent. -/
def rootKleinOmegaOrbitPolynomial (x : Fin 5 → ℂ) : Polynomial ℂ :=
  ∏ σ : Equiv.Perm (Fin 5),
    (Polynomial.X - Polynomial.C
      (rootKleinOmega (fun i => x (σ i))).p01)

/-- Reordering the roots leaves the full-permutation orbit polynomial
unchanged. The proof is reindexing the product by right composition with the
given permutation; no choice of an ordering is made. -/
theorem rootKleinOmegaOrbitPolynomial_perm (x : Fin 5 → ℂ)
    (τ : Equiv.Perm (Fin 5)) :
    rootKleinOmegaOrbitPolynomial (fun i => x (τ i)) =
      rootKleinOmegaOrbitPolynomial x := by
  unfold rootKleinOmegaOrbitPolynomial
  let e : Equiv.Perm (Fin 5) → Equiv.Perm (Fin 5) := fun σ => σ.trans τ
  have he : Function.Bijective e := by
    constructor
    · intro σ ρ h
      apply Equiv.ext
      intro i
      have hv := congrArg (fun π : Equiv.Perm (Fin 5) => π i) h
      exact τ.injective (by simpa [e, Equiv.trans_apply] using hv)
    · intro ρ
      refine ⟨ρ.trans τ.symm, ?_⟩
      apply Equiv.ext
      intro i
      simp [e, Equiv.trans_apply]
  exact Fintype.prod_bijective e he
    (fun σ => Polynomial.X - Polynomial.C
      ((rootKleinOmega (fun i => x (τ (σ i)))).p01))
    (fun σ => Polynomial.X - Polynomial.C
      ((rootKleinOmega (fun i => x (σ i))).p01))
    (by intro σ; rfl)

/-- Every coordinate value in the full-permutation orbit is a root of its
orbit polynomial, including values repeated by a nontrivial stabilizer. -/
theorem rootKleinOmegaOrbitPolynomial_eval_eq_zero
    (x : Fin 5 → ℂ) (σ : Equiv.Perm (Fin 5)) :
    (rootKleinOmegaOrbitPolynomial x).eval
      ((rootKleinOmega (fun i => x (σ i))).p01) = 0 := by
  classical
  unfold rootKleinOmegaOrbitPolynomial
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ σ)
  simp

/-- The full-permutation orbit polynomial is monic. The product is indexed by
all root permutations, so repeated coordinate values remain repeated factors;
this does not identify a smaller classical resolvent. -/
theorem rootKleinOmegaOrbitPolynomial_monic (x : Fin 5 → ℂ) :
    (rootKleinOmegaOrbitPolynomial x).Monic := by
  unfold rootKleinOmegaOrbitPolynomial
  exact Polynomial.monic_prod_X_sub_C _ _

/-- The full-permutation orbit polynomial has degree `5! = 120`, even when
some orbit coordinates coincide: the product is indexed by permutations,
not by distinct values. In particular, permutation invariance alone has not
constructed a degree-five quintic resolvent. -/
theorem rootKleinOmegaOrbitPolynomial_natDegree (x : Fin 5 → ℂ) :
    (rootKleinOmegaOrbitPolynomial x).natDegree = 120 := by
  unfold rootKleinOmegaOrbitPolynomial
  rw [Polynomial.natDegree_prod_of_monic]
  · norm_num [Fintype.card_perm]
  · intro σ hσ
    exact (Polynomial.monic_X_sub_C
      ((rootKleinOmega (fun i => x (σ i))).p01))

/-- A strict degree obstruction: this full `S₅`-indexed construction is not
the degree-five resolvent polynomial used for a quintic. -/
theorem rootKleinOmegaOrbitPolynomial_not_degree_five (x : Fin 5 → ℂ) :
    (rootKleinOmegaOrbitPolynomial x).natDegree ≠ 5 := by
  rw [rootKleinOmegaOrbitPolynomial_natDegree]
  norm_num

/-- Reordering a root tuple preserves both its monic root polynomial and the
full-permutation orbit polynomial. This is the exact ordering invariance
proved here; it does not identify coefficient scaling with root dilation. -/
theorem rootKleinOmegaOrbitPolynomial_same_under_root_reordering
    (x : Fin 5 → ℂ) (τ : Equiv.Perm (Fin 5)) :
    rootPolynomial (fun i => x (τ i)) = rootPolynomial x ∧
      rootKleinOmegaOrbitPolynomial (fun i => x (τ i)) =
        rootKleinOmegaOrbitPolynomial x :=
  ⟨rootPolynomial_perm x τ, rootKleinOmegaOrbitPolynomial_perm x τ⟩

/-- A fixed root tuple used to test whether the ordered-root Klein covariant
can be assigned to the polynomial independently of the ordering of its roots. -/
def permutationDescentExample : Fin 5 → ℂ := fun i => (i.val : ℂ)

/-- Exact Klein-coordinate values on a root tuple and its transposed ordering. -/
theorem permutationDescentExample_covariant_values :
    rootKleinOmega permutationDescentExample = ⟨4, 4, 0, 2, 2, 2⟩ ∧
      rootKleinOmega (fun i => permutationDescentExample (Equiv.swap 0 1 i)) =
        ⟨-4, 2, 2, 4, 0, 2⟩ := by
  constructor
  · apply Plucker6.ext <;>
      norm_num [permutationDescentExample, rootKleinOmega, rootMean,
        centeredRoots, centeredRootSquares, standardCoordinates,
        Plucker6.pluckerLine, Fin.sum_univ_succ]
  · apply Plucker6.ext <;>
      norm_num [permutationDescentExample, rootKleinOmega, rootMean,
        centeredRoots, centeredRootSquares, standardCoordinates,
        Plucker6.pluckerLine, Equiv.swap_apply_def, Fin.sum_univ_succ]

/-- The same monic quintic has different ordered root lists under a transposition,
but the six-coordinate Tschirnhaus Klein covariant changes. In particular, this
covariant is not itself a function of the unordered polynomial (even before
passing to projective Plücker coordinates). -/
theorem rootKleinOmega_not_invariant_under_root_swap :
    rootPolynomial (fun i => permutationDescentExample (Equiv.swap 0 1 i)) =
        rootPolynomial permutationDescentExample ∧
      rootKleinOmega (fun i => permutationDescentExample (Equiv.swap 0 1 i)) ≠
        rootKleinOmega permutationDescentExample := by
  rcases permutationDescentExample_covariant_values with ⟨hOrigVal, hSwapVal⟩
  constructor
  · exact rootPolynomial_perm permutationDescentExample (Equiv.swap 0 1)
  · rw [hSwapVal, hOrigVal]
    norm_num

/-- The permutation obstruction survives projectivization: these two ordered
root tuples define the same monic polynomial, but their nonzero Klein
covariants represent distinct points of projective Plücker space. -/
theorem projectiveRootKleinOmega_not_invariant_under_root_swap :
    projectiveRootKleinOmega
        (fun i => permutationDescentExample (Equiv.swap 0 1 i))
        (by
          intro h
          have h03 := congrArg Plucker6.p03 h
          have hValues := permutationDescentExample_covariant_values.2
          rw [hValues] at h03
          norm_num at h03) ≠
      projectiveRootKleinOmega permutationDescentExample
        (by
          intro h
          have h02 := congrArg Plucker6.p02 h
          have hValues := permutationDescentExample_covariant_values.1
          rw [hValues] at h02
          norm_num at h02) := by
  rcases permutationDescentExample_covariant_values with ⟨hOrigVal, hSwapVal⟩
  intro hproj
  have hΩswap : rootKleinOmega
      (fun i => permutationDescentExample (Equiv.swap 0 1 i)) ≠
        ⟨0, 0, 0, 0, 0, 0⟩ := by
    intro h
    have h03 := congrArg Plucker6.p03 h
    rw [hSwapVal] at h03
    norm_num at h03
  have hΩ : rootKleinOmega permutationDescentExample ≠
      ⟨0, 0, 0, 0, 0, 0⟩ := by
    intro h
    have h02 := congrArg Plucker6.p02 h
    rw [hOrigVal] at h02
    norm_num at h02
  have hscale := (Projectivization.mk_eq_mk_iff ℂ
      (rootKleinOmegaCoordinates
        (fun i => permutationDescentExample (Equiv.swap 0 1 i)))
      (rootKleinOmegaCoordinates permutationDescentExample)
      (rootKleinOmegaCoordinates_ne_zero _ hΩswap)
      (rootKleinOmegaCoordinates_ne_zero _ hΩ)).mp hproj
  rcases hscale with ⟨a, ha⟩
  have hcoord := congrFun ha 2
  have hOrigCoord : (rootKleinOmegaCoordinates permutationDescentExample) 2 = 0 := by
    simp [rootKleinOmegaCoordinates, hOrigVal]
  have hSwapCoord : (rootKleinOmegaCoordinates
      (fun i => permutationDescentExample (Equiv.swap 0 1 i))) 2 = 2 := by
    simp [rootKleinOmegaCoordinates, hSwapVal]
  simp only [Pi.smul_apply, hOrigCoord, hSwapCoord] at hcoord
  norm_num at hcoord

/-- The six Plücker minors of two four-vectors vanish precisely when the
vectors are linearly dependent. -/
private theorem second_eq_ratio_of_minor {a b u v : ℂ} (ha : a ≠ 0)
    (h : a * v - b * u = 0) : v = (u / a) * b := by
  have hab : a * v = b * u := sub_eq_zero.mp h
  calc
    v = (a * v) / a := by field_simp [ha]
    _ = (b * u) / a := by rw [hab]
    _ = (u / a) * b := by field_simp [ha]

theorem pluckerLine_eq_zero_iff_dependent (X Y : Vec4 ℂ) :
    Plucker6.pluckerLine X Y = ⟨0, 0, 0, 0, 0, 0⟩ ↔
      X = ⟨0, 0, 0, 0⟩ ∨ ∃ c : ℂ, Y = Vec4.scale c X := by
  rcases X with ⟨x0, x1, x2, x3⟩
  rcases Y with ⟨y0, y1, y2, y3⟩
  simp only [Plucker6.pluckerLine, Plucker6.mk.injEq]
  constructor
  · rintro ⟨h01, h02, h03, h12, h13, h23⟩
    by_cases hx0 : x0 ≠ 0
    · right
      refine ⟨y0 / x0, ?_⟩
      simp only [Vec4.mk.injEq, Vec4.scale]
      refine ⟨?_, ?_, ?_, ?_⟩
      · field_simp [hx0]
      · exact second_eq_ratio_of_minor hx0 h01
      · exact second_eq_ratio_of_minor hx0 h02
      · exact second_eq_ratio_of_minor hx0 h03
    · have hx0z : x0 = 0 := by by_contra hn; exact hx0 hn
      by_cases hx1 : x1 ≠ 0
      · have hy0 : y0 = 0 := by
          rw [hx0z] at h01
          have hprod : x1 * y0 = 0 := by simpa using h01
          exact (mul_eq_zero.mp hprod).resolve_left hx1
        right
        refine ⟨y1 / x1, ?_⟩
        simp only [Vec4.mk.injEq, Vec4.scale]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hy0, hx0z]; simp
        · field_simp [hx1]
        · exact second_eq_ratio_of_minor hx1 h12
        · exact second_eq_ratio_of_minor hx1 h13
      · have hx1z : x1 = 0 := by by_contra hn; exact hx1 hn
        by_cases hx2 : x2 ≠ 0
        · have hy0 : y0 = 0 := by
            rw [hx0z] at h02
            have hprod : x2 * y0 = 0 := by simpa using h02
            exact (mul_eq_zero.mp hprod).resolve_left hx2
          have hy1 : y1 = 0 := by
            rw [hx1z] at h12
            have hprod : x2 * y1 = 0 := by simpa using h12
            exact (mul_eq_zero.mp hprod).resolve_left hx2
          right
          refine ⟨y2 / x2, ?_⟩
          simp only [Vec4.mk.injEq, Vec4.scale]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hy0, hx0z]; simp
          · rw [hy1, hx1z]; simp
          · field_simp [hx2]
          · exact second_eq_ratio_of_minor hx2 h23
        · have hx2z : x2 = 0 := by by_contra hn; exact hx2 hn
          by_cases hx3 : x3 ≠ 0
          · have hy0 : y0 = 0 := by
              rw [hx0z] at h03
              have hprod : x3 * y0 = 0 := by simpa using h03
              exact (mul_eq_zero.mp hprod).resolve_left hx3
            have hy1 : y1 = 0 := by
              rw [hx1z] at h13
              have hprod : x3 * y1 = 0 := by simpa using h13
              exact (mul_eq_zero.mp hprod).resolve_left hx3
            have hy2 : y2 = 0 := by
              rw [hx2z] at h23
              have hprod : x3 * y2 = 0 := by simpa using h23
              exact (mul_eq_zero.mp hprod).resolve_left hx3
            right
            refine ⟨y3 / x3, ?_⟩
            simp only [Vec4.mk.injEq, Vec4.scale]
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [hy0, hx0z]; simp
            · rw [hy1, hx1z]; simp
            · rw [hy2, hx2z]; simp
            · field_simp [hx3]
          · have hx3z : x3 = 0 := by by_contra hn; exact hx3 hn
            left
            simp [hx0z, hx1z, hx2z, hx3z]
  · rintro (hX | ⟨c, hY⟩)
    · simp only [Vec4.mk.injEq] at hX
      rcases hX with ⟨rfl, rfl, rfl, rfl⟩
      simp
    · simp only [Vec4.mk.injEq, Vec4.scale] at hY
      rcases hY with ⟨h0, h1, h2, h3⟩
      rw [h0, h1, h2, h3]
      repeat' constructor <;> first | trivial | ring

/-- Increasing pairs index the ten independent coordinates of `Λ² ℂ⁵`.
This ambient carrier is distinct from the six-coordinate Klein chart on the
four-dimensional zero-sum standard module. -/
abbrev RootPair5 := {p : Fin 5 × Fin 5 // p.1 < p.2}

/-- The full five-root ambient bivector `y ∧ z`, retaining all ten
coordinates before identifying the zero-sum carrier with `ℂ⁴`. -/
def rootKleinOmega5 (x : Fin 5 → ℂ) : RootPair5 → ℂ := fun p =>
  centeredRoots x p.1.1 * centeredRootSquares x p.1.2 -
    centeredRoots x p.1.2 * centeredRootSquares x p.1.1

/-- Restrict the ambient ten-coordinate bivector to the first four root
coordinates, using the fixed Plücker order `01, 02, 03, 12, 13, 23`.
This is a coordinate projection on arbitrary ambient bivectors; its exact
compatibility with the centered Tschirnhaus covariant is stated below. -/
def rootKleinOmega5ToPlucker6 (Ω : RootPair5 → ℂ) : Plucker6 ℂ where
  p01 := Ω ⟨(0, 1), by decide⟩
  p02 := Ω ⟨(0, 2), by decide⟩
  p03 := Ω ⟨(0, 3), by decide⟩
  p12 := Ω ⟨(1, 2), by decide⟩
  p13 := Ω ⟨(1, 3), by decide⟩
  p23 := Ω ⟨(2, 3), by decide⟩

/-- The ten-coordinate ambient Tschirnhaus bivector projects exactly to the
six-coordinate `Gr(2,4)` Klein chart on the first four coordinates. This
theorem identifies the displayed covariants; it does not claim that the
projection is injective on arbitrary ten-coordinate bivectors. -/
theorem rootKleinOmega5ToPlucker6_eq_rootKleinOmega (x : Fin 5 → ℂ) :
    rootKleinOmega5ToPlucker6 (rootKleinOmega5 x) = rootKleinOmega x := by
  apply Plucker6.ext <;>
    simp [rootKleinOmega5ToPlucker6, rootKleinOmega5, rootKleinOmega,
      standardCoordinates, Plucker6.pluckerLine]

/-- The projected ambient covariant lies on the Klein quadric. This transfers
the existing decomposability theorem across the explicit ten-to-six
coordinate identification. -/
theorem rootKleinOmega5ToPlucker6_on_klein (x : Fin 5 → ℂ) :
    Plucker6.kleinQ (rootKleinOmega5ToPlucker6 (rootKleinOmega5 x)) = 0 := by
  rw [rootKleinOmega5ToPlucker6_eq_rootKleinOmega]
  exact rootKleinOmega_on_klein x

/-- The full ten-coordinate covariant agrees with the independent
`KleinQuinticTschirnhausPlucker` implementation of the same centered wedge.
This is an equality of root-space covariants, not a descent to coefficient
space. -/
theorem rootKleinOmega5_eq_tschirnhausVandermondeBivector
    (x : Fin 5 → ℂ) :
    rootKleinOmega5 x =
      InfoGeometry.Erlangen.KleinQuinticTschirnhausPlucker.tschirnhausVandermondeBivector x := by
  funext p
  have hcenter : ∀ y : Fin 5 → ℂ,
      centeredRoots y =
        InfoGeometry.Erlangen.KleinQuinticTschirnhausPlucker.centeredRoots y := by
    intro y
    funext i
    fin_cases i <;>
      simp [centeredRoots, rootMean,
        InfoGeometry.Erlangen.KleinQuinticTschirnhausPlucker.centeredRoots,
        InfoGeometry.Erlangen.KleinQuinticTschirnhausPlucker.rootMean,
        Fin.sum_univ_five]
  have hsquare : centeredRootSquares x =
      InfoGeometry.Erlangen.KleinQuinticTschirnhausPlucker.centeredRootSquares x := by
    funext i
    simp only [centeredRootSquares,
      InfoGeometry.Erlangen.KleinQuinticTschirnhausPlucker.centeredRootSquares]
    rw [hcenter x]
    have houter := hcenter
      (fun j => InfoGeometry.Erlangen.KleinQuinticTschirnhausPlucker.centeredRoots x j ^ 2)
    exact congrFun houter i
  rcases p with ⟨⟨i, j⟩, hij⟩
  simp [rootKleinOmega5,
    InfoGeometry.Erlangen.KleinQuinticTschirnhausPlucker.tschirnhausVandermondeBivector,
    InfoGeometry.Erlangen.KleinQuinticTschirnhausPlucker.wedgeCoordinate,
    hcenter, hsquare]

/-- Oriented ambient Plücker coordinate, defined for any ordered pair of
indices so permutation covariance does not require sorting the pair. -/
def rootKleinOmega5Ordered (x : Fin 5 → ℂ) (i j : Fin 5) : ℂ :=
  centeredRoots x i * centeredRootSquares x j -
    centeredRoots x j * centeredRootSquares x i

/-- The ambient ordered-root bivector is `S₅`-equivariant: reindexing roots
reindexes both Plücker indices. This is covariance upstairs, not descent to
a fixed coefficient-space bivector. -/
theorem rootKleinOmega5Ordered_perm (x : Fin 5 → ℂ)
    (σ : Equiv.Perm (Fin 5)) (i j : Fin 5) :
    rootKleinOmega5Ordered (fun k => x (σ k)) i j =
      rootKleinOmega5Ordered x (σ i) (σ j) := by
  simp [rootKleinOmega5Ordered, centeredRoots_perm, centeredRootSquares_perm]

/-- The centered ambient bivector contracts to zero against the all-ones
vector. Equivalently, for each fixed first index, the sum of its oriented
Plücker coordinates vanishes. This places `y ∧ z` in the exterior square of
the zero-sum four-dimensional standard subspace, even when it is represented
with all ten ambient `Λ² ℂ⁵` coordinates. -/
theorem rootKleinOmega5Ordered_contract_ones_zero (x : Fin 5 → ℂ) (i : Fin 5) :
    ∑ j : Fin 5, rootKleinOmega5Ordered x i j = 0 := by
  have hz : ∑ j : Fin 5, centeredRootSquares x j = 0 := by
    simpa [centeredRootSquares] using
      centeredRoots_sum_zero (fun j => centeredRoots x j ^ 2)
  unfold rootKleinOmega5Ordered
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    hz, centeredRoots_sum_zero x]
  ring

/-- Every four-index Plücker relation vanishes for the ambient
five-dimensional bivector. -/
theorem rootKleinOmega5_plucker (x : Fin 5 → ℂ) (i j k l : Fin 5) :
    (centeredRoots x i * centeredRootSquares x j -
        centeredRoots x j * centeredRootSquares x i) *
        (centeredRoots x k * centeredRootSquares x l -
          centeredRoots x l * centeredRootSquares x k) -
      (centeredRoots x i * centeredRootSquares x k -
        centeredRoots x k * centeredRootSquares x i) *
        (centeredRoots x j * centeredRootSquares x l -
          centeredRoots x l * centeredRootSquares x j) +
      (centeredRoots x i * centeredRootSquares x l -
        centeredRoots x l * centeredRootSquares x i) *
        (centeredRoots x j * centeredRootSquares x k -
          centeredRoots x k * centeredRootSquares x j) = 0 := by
  ring

/-- The ambient ten-coordinate bivector has root-dilation weight three and
is invariant under common translation. -/
theorem rootKleinOmega5_affine (x : Fin 5 → ℂ) (μ τ : ℂ) :
    rootKleinOmega5 (fun i => μ * x i + τ) =
      fun p => μ ^ 3 * rootKleinOmega5 x p := by
  funext p
  simp only [rootKleinOmega5, centeredRoots_translate (fun i => μ * x i) τ,
    centeredRoots_scale, centeredRootSquares_affine]
  ring

/-- The simplicial coboundary of the cubic ambient Plücker coordinates is
the product of the three centered-root differences. -/
theorem rootKleinOmega5_coboundary (x : Fin 5 → ℂ) (i j k : Fin 5) :
    (centeredRoots x i * centeredRootSquares x j -
        centeredRoots x j * centeredRootSquares x i) +
      (centeredRoots x j * centeredRootSquares x k -
        centeredRoots x k * centeredRootSquares x j) -
      (centeredRoots x i * centeredRootSquares x k -
        centeredRoots x k * centeredRootSquares x i) =
      (centeredRoots x j - centeredRoots x i) *
        (centeredRoots x k - centeredRoots x j) *
        (centeredRoots x k - centeredRoots x i) := by
  unfold centeredRootSquares centeredRoots
  ring

/-- The root-space base locus of the covariant: the centered quadratic vector
is proportional to the centered linear vector (including the zero-vector
case). This is the rank-drop condition for the two rows defining `Ω`. -/
def rootKleinDegenerate (x : Fin 5 → ℂ) : Prop :=
  standardCoordinates (centeredRoots x) = ⟨0, 0, 0, 0⟩ ∨
    ∃ c : ℂ,
      standardCoordinates (centeredRootSquares x) =
        Vec4.scale c (standardCoordinates (centeredRoots x))

/-- The rank-drop condition is contained in the projective base locus of `Ω`.
The converse (classifying all affine root tuples in that base locus) is a
separate finite-root argument. -/
theorem rootKleinOmega_eq_zero_of_degenerate (x : Fin 5 → ℂ)
    (h : rootKleinDegenerate x) : rootKleinOmega x =
      ⟨0, 0, 0, 0, 0, 0⟩ := by
  rcases h with hX | ⟨c, hY⟩
  · unfold rootKleinOmega
    rw [hX]
    rcases standardCoordinates (centeredRootSquares x) with ⟨y0, y1, y2, y3⟩
    simp [Plucker6.pluckerLine]
  · unfold rootKleinOmega
    rw [hY]
    rcases standardCoordinates (centeredRoots x) with ⟨x0, x1, x2, x3⟩
    simp only [Plucker6.pluckerLine, Vec4.scale]
    apply Plucker6.ext <;> ring

/-- Every completely confluent root tuple lies in the base locus. Thus the
root covariant does not define a projective Plücker point on all root tuples. -/
theorem rootKleinOmega_constant_roots (r : ℂ) :
    rootKleinOmega (fun _ : Fin 5 => r) = ⟨0, 0, 0, 0, 0, 0⟩ := by
  apply rootKleinOmega_eq_zero_of_degenerate
  left
  change (⟨centeredRoots (fun _ : Fin 5 => r) 0,
    centeredRoots (fun _ : Fin 5 => r) 1,
    centeredRoots (fun _ : Fin 5 => r) 2,
    centeredRoots (fun _ : Fin 5 => r) 3⟩ : Vec4 ℂ) = ⟨0, 0, 0, 0⟩
  simp only [Vec4.mk.injEq]
  repeat' constructor <;> simp [centeredRoots, rootMean]

/-- If the centered roots take at most two values, their centered squares
lie in the span of the centered roots, so the Klein covariant vanishes. -/
theorem rootKleinDegenerate_of_two_centered_values
    (x : Fin 5 → ℂ) (a b : ℂ)
    (hvalues : ∀ i, centeredRoots x i = a ∨ centeredRoots x i = b) :
    rootKleinDegenerate x := by
  let y := centeredRoots x
  have hySum : ∑ i : Fin 5, y i = 0 := by
    dsimp [y]
    exact centeredRoots_sum_zero x
  have hquadratic (i : Fin 5) : y i ^ 2 = (a + b) * y i - a * b := by
    rcases hvalues i with hi | hi
    · have hi' : y i = a := hi
      rw [hi']
      ring
    · have hi' : y i = b := hi
      rw [hi']
      ring
  have hsumSquares : ∑ i : Fin 5, y i ^ 2 = -5 * a * b := by
    calc
      (∑ i : Fin 5, y i ^ 2) = ∑ i : Fin 5, ((a + b) * y i - a * b) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hquadratic i
      _ = (a + b) * (∑ i : Fin 5, y i) - 5 * a * b := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp
        ring
      _ = -5 * a * b := by rw [hySum]; ring
  have hmeanSquares : rootMean (fun i : Fin 5 => y i ^ 2) = -a * b := by
    unfold rootMean
    rw [hsumSquares]
    ring
  have hcov (i : Fin 5) : centeredRootSquares x i = (a + b) * y i := by
    change y i ^ 2 - rootMean (fun j : Fin 5 => y j ^ 2) = (a + b) * y i
    rw [hmeanSquares, hquadratic i]
    ring
  right
  refine ⟨a + b, ?_⟩
  change (⟨centeredRootSquares x 0, centeredRootSquares x 1,
    centeredRootSquares x 2, centeredRootSquares x 3⟩ : Vec4 ℂ) =
    Vec4.scale (a + b) ⟨centeredRoots x 0, centeredRoots x 1,
      centeredRoots x 2, centeredRoots x 3⟩
  simp only [Vec4.mk.injEq, Vec4.scale]
  repeat' constructor
  all_goals exact hcov _

/-- If two values of a scalar satisfy the same quadratic relation
`t² - c*t = d` and are distinct, their sum is `c`. -/
private theorem quadratic_relation_sum_of_ne
    {u v c d : ℂ} (hu : u ^ 2 - c * u = d) (hv : v ^ 2 - c * v = d)
    (huv : u ≠ v) : u + v = c := by
  have hfac : (u - v) * (u + v - c) = 0 := by
    calc
      (u - v) * (u + v - c) = (u ^ 2 - c * u) - (v ^ 2 - c * v) := by ring
      _ = 0 := by rw [hu, hv]; ring
  rcases mul_eq_zero.mp hfac with h | h
  · exact False.elim (huv (sub_eq_zero.mp h))
  · exact sub_eq_zero.mp h

/-- Exact root-space base-locus criterion: the six first-four-coordinate
Plücker chart vanishes iff the centered roots take at most two values.
This classification concerns ordered roots and is not a coefficient-to-root
map. -/
theorem rootKleinOmega_eq_zero_iff_two_centered_values
    (x : Fin 5 → ℂ) :
    rootKleinOmega x = ⟨0, 0, 0, 0, 0, 0⟩ ↔
      ∃ a b : ℂ, ∀ i, centeredRoots x i = a ∨ centeredRoots x i = b := by
  constructor
  · intro hΩ
    let y := centeredRoots x
    let z := centeredRootSquares x
    have hdep := (pluckerLine_eq_zero_iff_dependent
      (standardCoordinates y) (standardCoordinates z)).mp (by
        simpa [rootKleinOmega, y, z] using hΩ)
    have hySum : ∑ i : Fin 5, y i = 0 := by
      dsimp [y]
      exact centeredRoots_sum_zero x
    have hzSum : ∑ i : Fin 5, z i = 0 := by
      dsimp [z, centeredRootSquares]
      exact centeredRoots_sum_zero (fun i => centeredRoots x i ^ 2)
    have hprop : ∃ c : ℂ, ∀ i, z i = c * y i := by
      rcases hdep with hX | ⟨c, hY⟩
      · have hy0 : ∀ i, y i = 0 := by
          have h0 : y 0 = 0 := by
            simpa [standardCoordinates] using congrArg Vec4.x0 hX
          have h1 : y 1 = 0 := by
            simpa [standardCoordinates] using congrArg Vec4.x1 hX
          have h2 : y 2 = 0 := by
            simpa [standardCoordinates] using congrArg Vec4.x2 hX
          have h3 : y 3 = 0 := by
            simpa [standardCoordinates] using congrArg Vec4.x3 hX
          have hs : y 0 + (y 1 + (y 2 + (y 3 + y 4))) = 0 := by
            simpa [Fin.sum_univ_succ] using hySum
          have h4 : y 4 = 0 := by rw [h0, h1, h2, h3] at hs; simpa using hs
          intro i
          fin_cases i <;> assumption
        have hz0 : ∀ i, z i = 0 := by
          intro i
          change centeredRoots (fun j => y j ^ 2) i = 0
          simp [centeredRoots, rootMean, y, hy0]
        refine ⟨0, ?_⟩
        intro i
        rw [hz0 i, hy0 i]
        simp
      · have hcoords : z 0 = c * y 0 ∧ z 1 = c * y 1 ∧
            z 2 = c * y 2 ∧ z 3 = c * y 3 := by
          simpa [standardCoordinates, Vec4.scale, y, z] using hY
        have hz5 : z 4 = c * y 4 := by
          have hyExpanded : y 0 + (y 1 + (y 2 + (y 3 + y 4))) = 0 := by
            simpa [Fin.sum_univ_succ] using hySum
          have hzExpanded : z 0 + (z 1 + (z 2 + (z 3 + z 4))) = 0 := by
            simpa [Fin.sum_univ_succ] using hzSum
          have hyFirst : y 0 + y 1 + y 2 + y 3 = -y 4 := by
            linear_combination hyExpanded
          have hzFirst : z 0 + z 1 + z 2 + z 3 = -z 4 := by
            linear_combination hzExpanded
          calc
            z 4 = -(z 0 + z 1 + z 2 + z 3) := by rw [hzFirst]; ring
            _ = -(c * y 0 + c * y 1 + c * y 2 + c * y 3) := by
              rw [hcoords.1, hcoords.2.1, hcoords.2.2.1, hcoords.2.2.2]
            _ = c * y 4 := by
              calc
                -(c * y 0 + c * y 1 + c * y 2 + c * y 3)
                    = -(c * (y 0 + y 1 + y 2 + y 3)) := by ring
                _ = -(c * (-y 4)) := by rw [hyFirst]
                _ = c * y 4 := by ring
        refine ⟨c, ?_⟩
        intro i
        fin_cases i
        · exact hcoords.1
        · exact hcoords.2.1
        · exact hcoords.2.2.1
        · exact hcoords.2.2.2
        · exact hz5
    rcases hprop with ⟨c, hc⟩
    have hquad (i : Fin 5) : y i ^ 2 - c * y i = rootMean (fun j => y j ^ 2) := by
      have hi := hc i
      change y i ^ 2 - rootMean (fun j => y j ^ 2) = c * y i at hi
      linear_combination hi
    by_cases hall : ∀ i, y i = y 0
    · exact ⟨y 0, y 0, fun i => Or.inl (hall i)⟩
    · push Not at hall
      rcases hall with ⟨k, hk⟩
      refine ⟨y 0, y k, ?_⟩
      intro i
      by_cases hi0 : y i = y 0
      · exact Or.inl hi0
      · by_cases hik : y i = y k
        · exact Or.inr hik
        · have h0k := quadratic_relation_sum_of_ne (hquad 0) (hquad k) (Ne.symm hk)
          have h0i := quadratic_relation_sum_of_ne (hquad 0) (hquad i) (Ne.symm hi0)
          have : y k = y i := by
            apply add_left_cancel
            calc
              y 0 + y k = c := h0k
              _ = y 0 + y i := h0i.symm
          exact False.elim (hik this.symm)
  · rintro ⟨a, b, hab⟩
    exact rootKleinOmega_eq_zero_of_degenerate x
      (rootKleinDegenerate_of_two_centered_values x a b hab)

/-- The projective base locus is unchanged by centering: the Klein covariant
vanishes exactly when the original ordered roots take at most two values.
For five roots this is contained in the repeated-root locus, by pigeonhole,
but is strictly smaller: a triple root with two other distinct values is
outside this base locus, as shown below. -/
theorem rootKleinOmega_eq_zero_iff_two_root_values
    (x : Fin 5 → ℂ) :
    rootKleinOmega x = ⟨0, 0, 0, 0, 0, 0⟩ ↔
      ∃ a b : ℂ, ∀ i, x i = a ∨ x i = b := by
  rw [rootKleinOmega_eq_zero_iff_two_centered_values]
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a + rootMean x, b + rootMean x, ?_⟩
    intro i
    rcases hab i with hi | hi
    · left
      have h := hi
      simp only [centeredRoots] at h
      linear_combination h
    · right
      have h := hi
      simp only [centeredRoots] at h
      linear_combination h
  · rintro ⟨a, b, hab⟩
    refine ⟨a - rootMean x, b - rootMean x, ?_⟩
    intro i
    rcases hab i with hi | hi
    · left
      simp [centeredRoots, hi]
    · right
      simp [centeredRoots, hi]

/-- The exact covariant base locus is contained in the finite root-tuple
multiplicity locus: among five roots taking at most two values, at least one
value occurs at least three times. This records only the root multiplicity
condition; it does not assert a binary-form GIT equivalence. -/
def hasRootMultiplicityAtLeastThree (x : Fin 5 → ℂ) : Prop :=
  ∃ a : ℂ, 3 ≤ (Finset.univ.filter fun i : Fin 5 => x i = a).card

theorem rootKleinOmega_zero_implies_root_multiplicity_at_least_three
    (x : Fin 5 → ℂ) (hΩ : rootKleinOmega x = ⟨0, 0, 0, 0, 0, 0⟩) :
    hasRootMultiplicityAtLeastThree x := by
  obtain ⟨a, b, hab⟩ := (rootKleinOmega_eq_zero_iff_two_root_values x).mp hΩ
  by_cases hab' : a = b
  · subst b
    refine ⟨a, ?_⟩
    have hfilter : (Finset.univ.filter fun i : Fin 5 => x i = a) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hab i with hi | hi
      · simp [hi]
      · simp [hi]
    rw [hfilter]
    simp
  · let A : Finset (Fin 5) := Finset.univ.filter fun i => x i = a
    let B : Finset (Fin 5) := Finset.univ.filter fun i => x i = b
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      have hia := (Finset.mem_filter.mp hiA).2
      have hib := (Finset.mem_filter.mp hiB).2
      exact hab' (hia.symm.trans hib)
    have hunion : A ∪ B = Finset.univ := by
      ext i
      simp only [Finset.mem_union, A, B, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hab i with hi | hi
      · simp [hi]
      · simp [hi]
    have hsum : 5 = A.card + B.card := by
      have h := Finset.card_union_of_disjoint hdisj
      rw [hunion] at h
      simpa using h
    by_contra hnone
    have hA : A.card < 3 := by
      dsimp [A]
      exact Nat.lt_of_not_ge (by
        intro hA
        exact hnone ⟨a, hA⟩)
    have hB : B.card < 3 := by
      dsimp [B]
      exact Nat.lt_of_not_ge (by
        intro hB
        exact hnone ⟨b, hB⟩)
    omega

/-- A concrete ordered quintic root tuple with a triple root and three
distinct values. -/
def tripleRootThreeValueExample : Fin 5 → ℂ :=
  fun i => if i.val < 3 then 0 else if i.val = 3 then 1 else 2

/-- The example has a root of multiplicity at least three. -/
theorem tripleRootThreeValueExample_triple_root :
    tripleRootThreeValueExample 0 = 0 ∧
    tripleRootThreeValueExample 1 = 0 ∧
    tripleRootThreeValueExample 2 = 0 := by
  norm_num [tripleRootThreeValueExample]

/-- The counterexample has a root value occurring at least three times. -/
theorem tripleRootThreeValueExample_multiplicity_at_least_three :
    hasRootMultiplicityAtLeastThree tripleRootThreeValueExample := by
  refine ⟨0, ?_⟩
  have hsubset : ({0, 1, 2} : Finset (Fin 5)) ⊆
      Finset.univ.filter (fun i : Fin 5 => tripleRootThreeValueExample i = 0) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;>
      simp [tripleRootThreeValueExample]
  have hcard : ({0, 1, 2} : Finset (Fin 5)).card = 3 := by norm_num
  rw [← hcard]
  exact Finset.card_le_card hsubset

/-- This tuple's Tschirnhaus Klein covariant is nonzero despite having a root
value of multiplicity at least three. Thus root multiplicity at least three
does not characterize this covariant's zero locus. -/
theorem tripleRootThreeValueExample_rootKleinOmega_ne_zero :
    rootKleinOmega tripleRootThreeValueExample ≠ ⟨0, 0, 0, 0, 0, 0⟩ := by
  intro hΩ
  obtain ⟨a, b, hab⟩ :=
    (rootKleinOmega_eq_zero_iff_two_root_values
      tripleRootThreeValueExample).mp hΩ
  have h0 := hab 0
  have h3 := hab 3
  have h4 := hab 4
  norm_num [tripleRootThreeValueExample] at h0 h3 h4
  rcases h0 with h0 | h0
  · rcases h3 with h3 | h3
    · exact (by norm_num : (0 : ℂ) ≠ 1) (h0.trans h3.symm)
    · rcases h4 with h4 | h4
      · exact (by norm_num : (0 : ℂ) ≠ 2) (h0.trans h4.symm)
      · exact (by norm_num : (1 : ℂ) ≠ 2) (h3.trans h4.symm)
  · rcases h3 with h3 | h3
    · rcases h4 with h4 | h4
      · exact (by norm_num : (1 : ℂ) ≠ 2) (h3.trans h4.symm)
      · exact (by norm_num : (0 : ℂ) ≠ 2) (h0.trans h4.symm)
    · exact (by norm_num : (0 : ℂ) ≠ 1) (h0.trans h3.symm)

end InfoGeometry.Erlangen.KleinQuinticTschirnhausKleinCovariant
