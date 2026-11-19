/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent
import InfoGeometry.Erlangen.KleinQuinticTschirnhausKleinCovariant
import InfoGeometry.Projective.KleinQuadricPlucker
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Binary Quintic Resolvent Roots as Grassmann–Plücker Data

For a source-ordered binary quintic, the existing Klein-orbit evaluation gives
five signed coordinates. Squaring them gives the five roots used by the
existing degree-five evaluation resolvent. This file sends any four selected
resolvent roots to the row-plane chart `(1, r_i)` in `Gr(2,4)` and reads its
six minors as the existing Klein `Plucker6` carrier. The induced Plucker
point lies on the Klein quadric, and the order-ten coefficient action
transports the chart by the owner's successor permutation.

The Klein equation holds even in the degenerate zero-bivector case. A
projective Grassmannian point is obtained when the selected roots are not all
equal (the theorem below gives a simple sufficient condition). No positivity
or Cantor-cylinder conclusion is claimed for these generally complex
coordinates.
-/

noncomputable section

namespace InfoGeometry.Erlangen.KleinQuinticGrassmannPluckerBridge

open InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent
open InfoGeometry.Erlangen.KleinQuinticTschirnhausKleinCovariant
open InfoGeometry.Erlangen.KleinIcosahedralQuinticModularJ
open InfoGeometry.Projective.KleinQuadricPlucker

/-- On the owner-defined binary forms, the Brioschi parameter is reciprocal
to the shifted icosahedral ratio `-H^3/F^5 + 1728`. This identifies the
parameter used by the quintic resolvent with Klein's algebraic invariant
coordinate wherever both denominators are nonzero. It does not identify that
coordinate with the analytic modular `jInvariant` on the upper half-plane. -/
theorem brioschiParameter_mul_shiftedKleinRatio_eq_one
    {z₁ z₂ : ℂ}
    (hF : kleinIcosahedralVertexF z₁ z₂ ≠ 0)
    (hT : kleinIcosahedralEdgeT z₁ z₂ ≠ 0) :
    brioschiParameter z₁ z₂ *
      (kleinBinaryFormRatio z₁ z₂ + 1728) = 1 := by
  rw [brioschiParameter, kleinBinaryFormRatio_add_1728 hF]
  field_simp [hF, hT]

/-- A chosen four-element subconfiguration of the five squared
source-quintic orbit evaluations. -/
def resolventSubconfiguration (v : BinaryQuinticCoefficientSpace)
    (z : ℂ × ℂ) (pick : Fin 4 → Fin 5) : Fin 4 → ℂ :=
  fun i => binaryQuinticResolventTuple v z (pick i)

/-- The `2 × 4` row chart whose rows are `(1,1,1,1)` and the selected four
resolvent roots. -/
def resolventGrassmannChart (v : BinaryQuinticCoefficientSpace)
    (z : ℂ × ℂ) (pick : Fin 4 → Fin 5) : Matrix (Fin 2) (Fin 4) ℂ :=
  fun i j => if i = 0 then 1 else resolventSubconfiguration v z pick j

/-- The two row vectors of the selected `Gr(2,4)` chart. -/
def resolventGrassmannRows (v : BinaryQuinticCoefficientSpace)
    (z : ℂ × ℂ) (pick : Fin 4 → Fin 5) : Vec4 ℂ × Vec4 ℂ :=
  (⟨1, 1, 1, 1⟩,
   ⟨resolventSubconfiguration v z pick 0,
    resolventSubconfiguration v z pick 1,
    resolventSubconfiguration v z pick 2,
    resolventSubconfiguration v z pick 3⟩)

/-- The Plucker readout of the selected Grassmannian row chart. -/
def binaryQuinticResolventPlucker6 (v : BinaryQuinticCoefficientSpace)
    (z : ℂ × ℂ) (pick : Fin 4 → Fin 5) : Plucker6 ℂ :=
  Plucker6.pluckerLine (resolventGrassmannRows v z pick).1
    (resolventGrassmannRows v z pick).2

/-- The Plücker readout depends only on the signed orbit evaluation of the
source coefficient vector. This is the kernel-invariance needed to descend
the nonlinear, squared-coordinate construction to the representation
quotient. -/
theorem binaryQuinticResolventPlucker6_eq_of_orbitEvaluation_eq
    (v w : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ)
    (pick : Fin 4 → Fin 5)
    (heval : binaryQuinticOrbitEvaluation z v = binaryQuinticOrbitEvaluation z w) :
    binaryQuinticResolventPlucker6 v z pick =
      binaryQuinticResolventPlucker6 w z pick := by
  have hcoord : ∀ k : Fin 5,
      binaryQuinticSignedOrbit v z k = binaryQuinticSignedOrbit w z k := by
    intro k
    exact congrFun heval k
  apply Plucker6.ext <;>
    simp [binaryQuinticResolventPlucker6, resolventGrassmannRows,
      resolventSubconfiguration, binaryQuinticResolventTuple,
      Plucker6.pluckerLine, hcoord]

/-- Under uniform coefficient scaling by `c`, the signed orbit evaluations
scale by `c`, their squares by `c ^ 2`, and the selected Plücker bivector by
`c ^ 2`. These orbit evaluations are not the roots of the input quintic.
This identity alone gives no projective map at points where the bivector
vanishes. -/
theorem binaryQuinticResolventPlucker6_smul
    (c : ℂ) (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ)
    (pick : Fin 4 → Fin 5) :
    binaryQuinticResolventPlucker6 (c • v) z pick =
      Plucker6.scale (c ^ 2) (binaryQuinticResolventPlucker6 v z pick) := by
  have hcoord (k : Fin 5) :
      binaryQuinticSignedOrbit (c • v) z k =
        c * binaryQuinticSignedOrbit v z k := by
    change (binaryQuinticOrbitEvaluation z (c • v)) k =
      c * (binaryQuinticOrbitEvaluation z v) k
    rw [map_smul]
    simp
  apply Plucker6.ext <;>
    simp [binaryQuinticResolventPlucker6, resolventGrassmannRows,
      resolventSubconfiguration, binaryQuinticResolventTuple,
      Plucker6.pluckerLine, Plucker6.scale, hcoord] <;>
    ring

/-- Coordinates of a `Plucker6` vector in its fixed order `01, 02, 03, 12,
13, 23`, for use in the genuine projectivization of a six-dimensional
vector space. -/
def plucker6CoordinateVector (P : Plucker6 ℂ) : Fin 6 → ℂ
  | ⟨0, _⟩ => P.p01
  | ⟨1, _⟩ => P.p02
  | ⟨2, _⟩ => P.p03
  | ⟨3, _⟩ => P.p12
  | ⟨4, _⟩ => P.p13
  | ⟨_, _h⟩ => P.p23

@[simp] theorem plucker6CoordinateVector_scale (c : ℂ) (P : Plucker6 ℂ) :
    plucker6CoordinateVector (Plucker6.scale c P) =
      c • plucker6CoordinateVector P := by
  funext i
  fin_cases i <;> rfl

/-- Projective Plücker readout, defined only when the Plücker vector is
nonzero. The explicit hypothesis records the base-locus exclusion. -/
def projectivePlucker6 (P : Plucker6 ℂ)
    (hP : plucker6CoordinateVector P ≠ 0) :
    Projectivization ℂ (Fin 6 → ℂ) :=
  Projectivization.mk ℂ (plucker6CoordinateVector P) hP

/-- Uniform scaling of the source coefficient vector induces the expected
projective invariance on the domain where the selected Plücker vector is
nonzero. This is a partial projective descent on the stated nonzero locus,
not a total map on projective coefficient space. -/
theorem binaryQuinticResolventProjectivePlucker6_smul
    (c : ℂ) (hc : c ≠ 0) (v : BinaryQuinticCoefficientSpace)
    (z : ℂ × ℂ) (pick : Fin 4 → Fin 5)
    (hP : plucker6CoordinateVector
      (binaryQuinticResolventPlucker6 v z pick) ≠ 0) :
    projectivePlucker6
        (binaryQuinticResolventPlucker6 (c • v) z pick)
        (by
          intro hzero
          apply hP
          funext i
          have hi := congrFun hzero i
          rw [binaryQuinticResolventPlucker6_smul,
            plucker6CoordinateVector_scale, Pi.smul_apply, smul_eq_mul] at hi
          exact (mul_eq_zero.mp hi).resolve_left (pow_ne_zero 2 hc)) =
      projectivePlucker6 (binaryQuinticResolventPlucker6 v z pick) hP := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hvec : plucker6CoordinateVector
      (binaryQuinticResolventPlucker6 (c • v) z pick) =
        c ^ 2 • plucker6CoordinateVector
          (binaryQuinticResolventPlucker6 v z pick) := by
    rw [binaryQuinticResolventPlucker6_smul,
      plucker6CoordinateVector_scale]
  apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ hP).2
  refine ⟨Units.mk0 (c ^ 2) hc2, ?_⟩
  simpa using hvec.symm

/-- The selected four-root Plücker construction on the quotient of the
source-ordered binary-quintic representation by the kernel of its signed
orbit evaluation. This quotient map exists even when the affine-chart
equivalence to the full five-coordinate orbit space is unavailable. -/
noncomputable def binaryQuinticOrbitQuotientPlucker6 (z : ℂ × ℂ)
    (pick : Fin 4 → Fin 5) :
    (BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker (binaryQuinticOrbitEvaluation z)) → Plucker6 ℂ :=
  Quotient.lift (fun v => binaryQuinticResolventPlucker6 v z pick) (by
    intro v w hvw
    have hmem : v - w ∈ LinearMap.ker (binaryQuinticOrbitEvaluation z) :=
      (LinearMap.ker (binaryQuinticOrbitEvaluation z)).quotientRel_def.mp hvw
    have hzero : binaryQuinticOrbitEvaluation z (v - w) = 0 :=
      LinearMap.mem_ker.mp hmem
    have heval : binaryQuinticOrbitEvaluation z v =
        binaryQuinticOrbitEvaluation z w := by
      rw [map_sub] at hzero
      exact sub_eq_zero.mp hzero
    exact binaryQuinticResolventPlucker6_eq_of_orbitEvaluation_eq
      v w z pick heval)

/-- On a representative class, the quotient-level Plücker map returns the
same six-vector as the source coefficient construction. -/
@[simp] theorem binaryQuinticOrbitQuotientPlucker6_mk
    (z : ℂ × ℂ) (pick : Fin 4 → Fin 5)
    (v : BinaryQuinticCoefficientSpace) :
    binaryQuinticOrbitQuotientPlucker6 z pick (Submodule.Quotient.mk v) =
      binaryQuinticResolventPlucker6 v z pick := rfl

/-- The quotient-level Plücker map is homogeneous of degree two under
scaling in the signed-orbit representation quotient. This is the quotient
carrier version of coefficient scaling, independent of the chosen
representative. -/
theorem binaryQuinticOrbitQuotientPlucker6_smul
    (c : ℂ) (z : ℂ × ℂ) (pick : Fin 4 → Fin 5)
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker (binaryQuinticOrbitEvaluation z)) :
    binaryQuinticOrbitQuotientPlucker6 z pick (c • q) =
      Plucker6.scale (c ^ 2) (binaryQuinticOrbitQuotientPlucker6 z pick q) := by
  refine Submodule.Quotient.induction_on _ q ?_
  intro v
  rw [← Submodule.Quotient.mk_smul,
    binaryQuinticOrbitQuotientPlucker6_mk,
    binaryQuinticOrbitQuotientPlucker6_mk,
    binaryQuinticResolventPlucker6_smul]

/-- Projective Plücker readout of the signed-orbit representation quotient,
defined on the open locus where its six coordinates are nonzero as a vector.
The guard is explicit because the affine Plücker cone has a genuine base
locus. -/
noncomputable def binaryQuinticOrbitQuotientProjectivePlucker6
    (z : ℂ × ℂ) (pick : Fin 4 → Fin 5)
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker (binaryQuinticOrbitEvaluation z))
    (hq : plucker6CoordinateVector
      (binaryQuinticOrbitQuotientPlucker6 z pick q) ≠ 0) :
    Projectivization ℂ (Fin 6 → ℂ) :=
  projectivePlucker6 (binaryQuinticOrbitQuotientPlucker6 z pick q) hq

/-- Nonzero scalar rescaling of a quotient class leaves its projective
Plücker readout unchanged wherever the readout is defined. The degree-two
homogeneity supplies the projective scalar; the theorem makes no extension
through the base locus. -/
theorem binaryQuinticOrbitQuotientProjectivePlucker6_smul
    (c : ℂ) (hc : c ≠ 0) (z : ℂ × ℂ) (pick : Fin 4 → Fin 5)
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker (binaryQuinticOrbitEvaluation z))
    (hq : plucker6CoordinateVector
      (binaryQuinticOrbitQuotientPlucker6 z pick q) ≠ 0) :
    binaryQuinticOrbitQuotientProjectivePlucker6 z pick (c • q)
        (by
          intro hzero
          apply hq
          funext i
          have hi := congrFun hzero i
          rw [binaryQuinticOrbitQuotientPlucker6_smul,
            plucker6CoordinateVector_scale, Pi.smul_apply, smul_eq_mul] at hi
          exact (mul_eq_zero.mp hi).resolve_left (pow_ne_zero 2 hc)) =
      binaryQuinticOrbitQuotientProjectivePlucker6 z pick q hq := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hvec : plucker6CoordinateVector
      (binaryQuinticOrbitQuotientPlucker6 z pick (c • q)) =
        c ^ 2 • plucker6CoordinateVector
          (binaryQuinticOrbitQuotientPlucker6 z pick q) := by
    rw [binaryQuinticOrbitQuotientPlucker6_smul,
      plucker6CoordinateVector_scale]
  apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ hq).2
  refine ⟨Units.mk0 (c ^ 2) hc2, ?_⟩
  simpa using hvec.symm

/-- Every point in the quotient-level Plücker image satisfies Klein's
quadric equation. This is the Grassmann–Plücker relation after quotienting
the original binary-quintic coefficient representation by invisible orbit
directions. -/
theorem binaryQuinticOrbitQuotientPlucker6_on_klein
    (z : ℂ × ℂ) (pick : Fin 4 → Fin 5)
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker (binaryQuinticOrbitEvaluation z)) :
    Plucker6.kleinQ (binaryQuinticOrbitQuotientPlucker6 z pick q) = 0 := by
  refine Submodule.Quotient.induction_on _ q ?_
  intro v
  rw [binaryQuinticOrbitQuotientPlucker6_mk]
  exact Plucker6.kleinQ_pluckerLine (resolventGrassmannRows v z pick).1
    (resolventGrassmannRows v z pick).2

/-- The descended Plücker map is even: the central sign on the odd-degree
quintic representation disappears after forming the squared resolvent
coordinates. -/
theorem binaryQuinticOrbitQuotientPlucker6_neg
    (z : ℂ × ℂ) (pick : Fin 4 → Fin 5)
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker (binaryQuinticOrbitEvaluation z)) :
    binaryQuinticOrbitQuotientPlucker6 z pick (-q) =
      binaryQuinticOrbitQuotientPlucker6 z pick q := by
  refine Submodule.Quotient.induction_on _ q ?_
  intro v
  rw [← Submodule.Quotient.mk_neg,
    binaryQuinticOrbitQuotientPlucker6_mk,
    binaryQuinticOrbitQuotientPlucker6_mk]
  apply Plucker6.ext <;>
    simp [binaryQuinticResolventPlucker6, resolventGrassmannRows,
      resolventSubconfiguration, binaryQuinticResolventTuple,
      binaryQuinticSignedOrbit, binaryQuinticEval, Plucker6.pluckerLine]

/-- The four affine coordinates in the Grassmann chart are precisely the
squares of the coordinates of the source-quintic class in the signed-orbit
quotient. This is the coefficient-representation input to the Plücker map;
the chart is not defined from an unrelated five-tuple. -/
theorem binaryQuinticResolventPlucker6_eq_quotient_coordinates
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ)
    (pick : Fin 4 → Fin 5)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (hnodes : Function.Injective
      (fun k : Fin 5 => (kleinOrderFiveIterate k.val z).2 /
        (kleinOrderFiveIterate k.val z).1)) :
    binaryQuinticResolventPlucker6 v z pick =
      Plucker6.pluckerLine
        (⟨1, 1, 1, 1⟩ : Vec4 ℂ)
        (⟨(((binaryQuinticOrbitQuotientEquiv z hfirst hnodes
              (Submodule.Quotient.mk v) : BrioschiRootCoordinateSpace)
              (pick 0)) ^ 2),
          (((binaryQuinticOrbitQuotientEquiv z hfirst hnodes
              (Submodule.Quotient.mk v) : BrioschiRootCoordinateSpace)
              (pick 1)) ^ 2),
          (((binaryQuinticOrbitQuotientEquiv z hfirst hnodes
              (Submodule.Quotient.mk v) : BrioschiRootCoordinateSpace)
              (pick 2)) ^ 2),
          (((binaryQuinticOrbitQuotientEquiv z hfirst hnodes
              (Submodule.Quotient.mk v) : BrioschiRootCoordinateSpace)
              (pick 3)) ^ 2)⟩ : Vec4 ℂ) := by
  have hqcoord (k : Fin 5) :
      (binaryQuinticOrbitQuotientEquiv z hfirst hnodes
        (Submodule.Quotient.mk v) : BrioschiRootCoordinateSpace) k =
        binaryQuinticSignedOrbit v z k := by
    have hq := binaryQuinticOrbitQuotientEquiv_apply_mk z hfirst hnodes v
    exact congrFun hq k
  apply Plucker6.ext <;>
    simp [binaryQuinticResolventPlucker6, resolventGrassmannRows,
      resolventSubconfiguration, binaryQuinticResolventTuple,
      Plucker6.pluckerLine, hqcoord]

/-- The row-pair realization is exactly the decomposable bivector represented
by the selected resolvent chart. -/
theorem resolventGrassmannChart_pluckerLine
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ)
    (pick : Fin 4 → Fin 5) :
    binaryQuinticResolventPlucker6 v z pick =
      Plucker6.pluckerLine (resolventGrassmannRows v z pick).1
        (resolventGrassmannRows v z pick).2 := rfl

/-- Every four-root Grassmann chart cut from a binary-quintic evaluation
resolvent gives a point on the Klein quadric. This is the concrete
representation-to-Grassmann-to-Plucker-to-Klein map. -/
theorem binaryQuinticResolventPlucker6_on_klein
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ)
    (pick : Fin 4 → Fin 5) :
    Plucker6.kleinQ (binaryQuinticResolventPlucker6 v z pick) = 0 := by
  exact Plucker6.kleinQ_pluckerLine (resolventGrassmannRows v z pick).1
    (resolventGrassmannRows v z pick).2

/-- The source order-ten generator acts on the selected Grassmann chart by
reindexing its four selected orbit slots by the established Klein successor.
This retains the owner's order convention instead of identifying unlike
representations by dimension. -/
theorem binaryQuinticResolventPlucker6_generator_covariance
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ)
    (pick : Fin 4 → Fin 5) :
    binaryQuinticResolventPlucker6 (binaryQuinticGenerator v) z pick =
      binaryQuinticResolventPlucker6 v z
        (fun i => kleinResolventCycleSucc (pick i)) := by
  apply Plucker6.ext <;>
    simp [binaryQuinticResolventPlucker6, resolventGrassmannRows,
      resolventSubconfiguration, binaryQuinticResolventTuple_equivariant,
    Plucker6.pluckerLine]

/-- The induced order-ten action on the signed-orbit quotient intertwines
with reindexing the four selected squared-resolvent roots in the descended
Grassmann–Plücker map. -/
theorem binaryQuinticOrbitQuotientPlucker6_generator_covariance
    (z : ℂ × ℂ) (pick : Fin 4 → Fin 5)
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker (binaryQuinticOrbitEvaluation z)) :
    binaryQuinticOrbitQuotientPlucker6 z pick
        (binaryQuinticOrbitQuotientGenerator z q) =
      binaryQuinticOrbitQuotientPlucker6 z
        (fun i => kleinResolventCycleSucc (pick i)) q := by
  refine Submodule.Quotient.induction_on _ q ?_
  intro v
  simp only [binaryQuinticOrbitQuotientGenerator_apply_mk,
    binaryQuinticOrbitQuotientPlucker6_mk]
  exact binaryQuinticResolventPlucker6_generator_covariance v z pick

/-- The Klein relation can also be read directly from the Grassmann chart's
six `2 × 2` minors: they are the differences `r_j-r_i`. -/
theorem binaryQuinticResolventPlucker6_coordinates
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ)
    (pick : Fin 4 → Fin 5) :
    let r := resolventSubconfiguration v z pick
    let P := binaryQuinticResolventPlucker6 v z pick
    P.p01 = r 1 - r 0 ∧ P.p02 = r 2 - r 0 ∧
    P.p03 = r 3 - r 0 ∧ P.p12 = r 2 - r 1 ∧
    P.p13 = r 3 - r 1 ∧ P.p23 = r 3 - r 2 := by
  simp [binaryQuinticResolventPlucker6, resolventGrassmannRows,
    resolventSubconfiguration, Plucker6.pluckerLine]

/-- If two selected resolvent roots differ, the decomposable bivector is
nonzero. Thus the corresponding row chart has rank two and determines an
actual projective point of `Gr(2,4)`, rather than only a point of the affine
Plucker cone. -/
theorem binaryQuinticResolventPlucker6_p01_ne_zero_of_first_two_ne
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ)
    (pick : Fin 4 → Fin 5)
    (hneq : resolventSubconfiguration v z pick 0 ≠
      resolventSubconfiguration v z pick 1) :
    (binaryQuinticResolventPlucker6 v z pick).p01 ≠ 0 := by
  have hcoords := binaryQuinticResolventPlucker6_coordinates v z pick
  simpa [binaryQuinticResolventPlucker6, resolventGrassmannRows,
    resolventSubconfiguration, Plucker6.pluckerLine] using
      (show resolventSubconfiguration v z pick 1 -
        resolventSubconfiguration v z pick 0 ≠ 0 from
        sub_ne_zero.mpr (Ne.symm hneq))

/-- Exact base-locus criterion for the selected affine Grassmann chart:
its Plücker bivector vanishes exactly when all four selected squared
resolvent coordinates coincide. Thus projectivization is
defined precisely off this locus; a single unequal pair is sufficient and
necessary. This characterizes the guard used by
`binaryQuinticResolventProjectivePlucker6_smul`. -/
theorem binaryQuinticResolventPlucker6_eq_zero_iff_selected_values_equal
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ)
    (pick : Fin 4 → Fin 5) :
    binaryQuinticResolventPlucker6 v z pick = ⟨0, 0, 0, 0, 0, 0⟩ ↔
      ∀ i : Fin 4, resolventSubconfiguration v z pick i =
        resolventSubconfiguration v z pick 0 := by
  constructor
  · intro h i
    fin_cases i
    · rfl
    · have hcoord := congrArg (fun P : Plucker6 ℂ => P.p01) h
      have hdiff : resolventSubconfiguration v z pick 1 -
          resolventSubconfiguration v z pick 0 = 0 := by
        simpa [binaryQuinticResolventPlucker6,
          resolventGrassmannRows, resolventSubconfiguration,
          Plucker6.pluckerLine] using hcoord
      exact sub_eq_zero.mp hdiff
    · have hcoord := congrArg (fun P : Plucker6 ℂ => P.p02) h
      have hdiff : resolventSubconfiguration v z pick 2 -
          resolventSubconfiguration v z pick 0 = 0 := by
        simpa [binaryQuinticResolventPlucker6,
          resolventGrassmannRows, resolventSubconfiguration,
          Plucker6.pluckerLine] using hcoord
      exact sub_eq_zero.mp hdiff
    · have hcoord := congrArg (fun P : Plucker6 ℂ => P.p03) h
      have hdiff : resolventSubconfiguration v z pick 3 -
          resolventSubconfiguration v z pick 0 = 0 := by
        simpa [binaryQuinticResolventPlucker6,
          resolventGrassmannRows, resolventSubconfiguration,
          Plucker6.pluckerLine] using hcoord
      exact sub_eq_zero.mp hdiff
  · intro h
    have h1 := h (1 : Fin 4)
    have h2 := h (2 : Fin 4)
    have h3 := h (3 : Fin 4)
    change binaryQuinticResolventTuple v z (pick 1) =
      binaryQuinticResolventTuple v z (pick 0) at h1
    change binaryQuinticResolventTuple v z (pick 2) =
      binaryQuinticResolventTuple v z (pick 0) at h2
    change binaryQuinticResolventTuple v z (pick 3) =
      binaryQuinticResolventTuple v z (pick 0) at h3
    apply Plucker6.ext <;>
      simp [binaryQuinticResolventPlucker6, resolventGrassmannRows,
        resolventSubconfiguration, Plucker6.pluckerLine, h1, h2, h3]

/-- The centered Tschirnhaus bivector of the five squared signed-orbit
evaluations. This keeps the full ten-coordinate `Λ² ℂ⁵` carrier, rather than
identifying it with the six-coordinate chart made from four selected roots. -/
def binaryQuinticResolventOmega5 (v : BinaryQuinticCoefficientSpace)
    (z : ℂ × ℂ) : RootPair5 → ℂ :=
  rootKleinOmega5 (binaryQuinticResolventTuple v z)

/-- On the generic affine evaluation chart, one can choose a source
binary-quintic coefficient vector whose ordered squared evaluation tuple is
Klein's indexed Brioschi root tuple. The induced degree-five polynomial is
then the displayed Brioschi resolvent, and the full ten-coordinate
Tschirnhaus covariant agrees with the one formed from those Brioschi roots.
The coefficient vector remains a noncanonical square-root/interpolation
choice; this theorem does not assert a canonical inverse or equivariant
selection. -/
theorem exists_binaryQuinticResolventTuple_eq_kleinBrioschiRootTuple
    (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (hnodes : Function.Injective
      (fun k : Fin 5 => (kleinOrderFiveIterate k.val z).2 /
        (kleinOrderFiveIterate k.val z).1))
    (hT : kleinIcosahedralEdgeT z.1 z.2 ≠ 0)
    (hinj : Function.Injective (kleinBrioschiRootTuple z)) :
    ∃ v : BinaryQuinticCoefficientSpace,
      binaryQuinticResolventTuple v z = kleinBrioschiRootTuple z ∧
      binaryQuinticEvaluationResolvent v z =
        brioschiResolvent (brioschiParameter z.1 z.2) ∧
      binaryQuinticResolventOmega5 v z =
        rootKleinOmega5 (kleinBrioschiRootTuple z) := by
  classical
  have hroot (k : Fin 5) :
      ∃ q : ℂ, q ^ 2 = kleinBrioschiRootTuple z k :=
    IsAlgClosed.exists_pow_nat_eq (kleinBrioschiRootTuple z k) (by norm_num)
  choose q hq using hroot
  obtain ⟨v, hv⟩ := binaryQuinticOrbitEvaluation_surjective_of_affine_chart
    z hfirst hnodes q
  have htuple : binaryQuinticResolventTuple v z = kleinBrioschiRootTuple z := by
    funext k
    change binaryQuinticSignedOrbit v z k ^ 2 = kleinBrioschiRootTuple z k
    have hk := congrFun hv k
    change binaryQuinticSignedOrbit v z k = q k at hk
    rw [hk, hq k]
  have horbit : binaryQuinticEvaluationResolvent v z =
      kleinBrioschiOrbitPolynomial z := by
    rw [binaryQuinticEvaluationResolvent, kleinBrioschiOrbitPolynomial, htuple]
  refine ⟨v, htuple, horbit.trans
    (kleinBrioschiOrbitPolynomial_eq_resolvent_of_injective z hT hinj), ?_⟩
  unfold binaryQuinticResolventOmega5
  rw [htuple]

/-- The resolvent-induced Tschirnhaus bivector is decomposable, so every
four-index Plücker relation holds. -/
theorem binaryQuinticResolventOmega5_plucker
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ)
    (i j k l : Fin 5) :
    (rootKleinOmega5Ordered (binaryQuinticResolventTuple v z) i j) *
        (rootKleinOmega5Ordered (binaryQuinticResolventTuple v z) k l) -
      (rootKleinOmega5Ordered (binaryQuinticResolventTuple v z) i k) *
        (rootKleinOmega5Ordered (binaryQuinticResolventTuple v z) j l) +
      (rootKleinOmega5Ordered (binaryQuinticResolventTuple v z) i l) *
        (rootKleinOmega5Ordered (binaryQuinticResolventTuple v z) j k) = 0 := by
  exact rootKleinOmega5_plucker (binaryQuinticResolventTuple v z) i j k l

/-- The simplicial coboundary of the coefficient-derived cubic bivector is
the product of differences of its five squared signed-orbit coordinates.
Thus this identity is on the resolvent tuple obtained from the coefficient
representation, rather than on an unrelated ordered-root variable. -/
theorem binaryQuinticResolventOmega5_coboundary
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ)
    (i j k : Fin 5) :
    rootKleinOmega5Ordered (binaryQuinticResolventTuple v z) i j +
        rootKleinOmega5Ordered (binaryQuinticResolventTuple v z) j k -
        rootKleinOmega5Ordered (binaryQuinticResolventTuple v z) i k =
      (binaryQuinticResolventTuple v z j - binaryQuinticResolventTuple v z i) *
        (binaryQuinticResolventTuple v z k - binaryQuinticResolventTuple v z j) *
        (binaryQuinticResolventTuple v z k - binaryQuinticResolventTuple v z i) := by
  unfold rootKleinOmega5Ordered
  rw [rootKleinOmega5_coboundary]
  have hcenter (a b : Fin 5) :
      centeredRoots (binaryQuinticResolventTuple v z) a -
          centeredRoots (binaryQuinticResolventTuple v z) b =
        binaryQuinticResolventTuple v z a - binaryQuinticResolventTuple v z b := by
    unfold centeredRoots
    ring
  rw [hcenter, hcenter, hcenter]

/-- Under the source order-ten generator, the five squared orbit evaluations
cycle, and the ambient bivector transforms by the induced permutation of its
two Plücker indices. This is the actual nonlinear equivariance map between
the binary-quintic representation, its resolvent tuple, and `Λ² ℂ⁵`. -/
private def kleinResolventCyclePerm : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective kleinResolventCycleSucc (by
    constructor
    · intro a b hab
      apply Fin.ext
      have hval := congrArg Fin.val hab
      simp [kleinResolventCycleSucc] at hval
      omega
    · intro b
      refine ⟨⟨(b.val + 4) % 5, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
      apply Fin.ext
      simp [kleinResolventCycleSucc]
      omega)

theorem binaryQuinticResolventOmega5_generator_covariance
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) (i j : Fin 5) :
    rootKleinOmega5Ordered
        (binaryQuinticResolventTuple (binaryQuinticGenerator v) z) i j =
      rootKleinOmega5Ordered (binaryQuinticResolventTuple v z)
        (kleinResolventCycleSucc i) (kleinResolventCycleSucc j) := by
  rw [binaryQuinticResolventTuple_equivariant]
  exact rootKleinOmega5Ordered_perm
    (binaryQuinticResolventTuple v z) kleinResolventCyclePerm i j

/-- Uniform scaling of the coefficient vector scales signed orbit values by
`c`, squared resolvent roots by `c²`, and the degree-three Tschirnhaus
covariant of those squared roots by `c⁶`. This is coefficient scaling, not
root dilation. -/
theorem binaryQuinticResolventOmega5_smul
    (c : ℂ) (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) :
    binaryQuinticResolventOmega5 (c • v) z =
      fun p => c ^ 6 * binaryQuinticResolventOmega5 v z p := by
  have htuple : binaryQuinticResolventTuple (c • v) z =
      fun k => c ^ 2 * binaryQuinticResolventTuple v z k := by
    funext k
    have hsigned : binaryQuinticSignedOrbit (c • v) z k =
        c * binaryQuinticSignedOrbit v z k := by
      change (binaryQuinticOrbitEvaluation z (c • v)) k =
        c * (binaryQuinticOrbitEvaluation z v) k
      rw [map_smul]
      simp
    change binaryQuinticSignedOrbit (c • v) z k ^ 2 =
      c ^ 2 * binaryQuinticSignedOrbit v z k ^ 2
    rw [hsigned]
    ring
  calc
    binaryQuinticResolventOmega5 (c • v) z =
        rootKleinOmega5 (fun k => c ^ 2 * binaryQuinticResolventTuple v z k) := by
          unfold binaryQuinticResolventOmega5
          exact congrArg rootKleinOmega5 htuple
    _ = fun p => (c ^ 2) ^ 3 * binaryQuinticResolventOmega5 v z p := by
          unfold binaryQuinticResolventOmega5
          simpa only [add_zero] using
            (rootKleinOmega5_affine (binaryQuinticResolventTuple v z) (c ^ 2) 0)
    _ = fun p => c ^ 6 * binaryQuinticResolventOmega5 v z p := by
          funext p
          congr 1
          ring

/-- The degree-five evaluation resolvent obeys the expected weighted
root-dilation identity: scaling the source coefficient vector by `c`, then
scaling the polynomial argument by `c²`, scales the value by `c¹⁰`. This
records the actual polynomial-level consequence of signed evaluation (weight
one), squaring (weight two), and taking a product of five linear factors. -/
theorem binaryQuinticEvaluationResolvent_scale_eval
    (c x : ℂ) (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) :
    Polynomial.eval (c ^ 2 * x) (binaryQuinticEvaluationResolvent (c • v) z) =
      c ^ 10 * Polynomial.eval x (binaryQuinticEvaluationResolvent v z) := by
  have htuple : binaryQuinticResolventTuple (c • v) z =
      fun k => c ^ 2 * binaryQuinticResolventTuple v z k := by
    funext k
    change binaryQuinticSignedOrbit (c • v) z k ^ 2 =
      c ^ 2 * binaryQuinticSignedOrbit v z k ^ 2
    rw [show binaryQuinticSignedOrbit (c • v) z k =
      c * binaryQuinticSignedOrbit v z k by
        change (binaryQuinticOrbitEvaluation z (c • v)) k =
          c * (binaryQuinticOrbitEvaluation z v) k
        rw [map_smul]
        simp]
    ring
  simp only [binaryQuinticEvaluationResolvent, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [htuple]
  calc
    (∏ k : Fin 5, (c ^ 2 * x - c ^ 2 * binaryQuinticResolventTuple v z k)) =
        ∏ k : Fin 5, c ^ 2 * (x - binaryQuinticResolventTuple v z k) := by
          apply Finset.prod_congr rfl
          intro k hk
          ring
    _ = (∏ _k : Fin 5, c ^ 2) *
        ∏ k : Fin 5, (x - binaryQuinticResolventTuple v z k) := by
          rw [Finset.prod_mul_distrib]
    _ = c ^ 10 *
        ∏ k : Fin 5, (x - binaryQuinticResolventTuple v z k) := by
          have hconst : (∏ _k : Fin 5, c ^ 2) = c ^ 10 := by
            simp [Finset.prod_const, Fintype.card_fin]
            ring
          rw [hconst]

/-- Polynomial form of the weighted scaling law. If `R_v` denotes the monic
evaluation resolvent, scaling the source by `c` scales its roots by `c²`;
consequently `R_(c•v)(c² X) = c¹⁰ R_v(X)`. This identity also holds at
`c = 0`. -/
theorem binaryQuinticEvaluationResolvent_weighted_polynomial_identity
    (c : ℂ) (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) :
    (binaryQuinticEvaluationResolvent (c • v) z).comp
        (Polynomial.C (c ^ 2) * Polynomial.X) =
      Polynomial.C (c ^ 10) * binaryQuinticEvaluationResolvent v z := by
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  rw [binaryQuinticEvaluationResolvent_scale_eval]

/-- The two Grassmann outputs have different coefficient-scaling weights:
the four-selected-root chart is quadratic, while the centered five-root
Tschirnhaus covariant is sextic after composing its cubic root-degree map with
the quadratic signed-orbit resolvent. The theorem keeps their distinct
carriers explicit. -/
theorem binaryQuinticGrassmannOutputs_scaling
    (c : ℂ) (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ)
    (pick : Fin 4 → Fin 5) :
    binaryQuinticResolventPlucker6 (c • v) z pick =
        Plucker6.scale (c ^ 2) (binaryQuinticResolventPlucker6 v z pick) ∧
      binaryQuinticResolventOmega5 (c • v) z =
        fun p => c ^ 6 * binaryQuinticResolventOmega5 v z p := by
  exact ⟨binaryQuinticResolventPlucker6_smul c v z pick,
    binaryQuinticResolventOmega5_smul c v z⟩

/-- A concrete witness that the ordered-root covariant does not descend as a
fixed coordinate assignment to the unordered polynomial: swapping two roots
preserves the monic root polynomial but changes the `01` coordinate of the
ambient bivector. The general theorem is permutation covariance; this witness
shows why covariance is not invariance and why a quotient or additional
ordering data is required. -/
theorem rootPermutation_preserves_polynomial_but_changes_omega_coordinate :
    rootPolynomial (fun i : Fin 5 => (i.val : ℂ)) =
        rootPolynomial (fun i : Fin 5 => ((Equiv.swap (0 : Fin 5) 1) i).val) ∧
      rootKleinOmega5Ordered (fun i : Fin 5 => (i.val : ℂ)) 0 1 ≠
        rootKleinOmega5Ordered
          (fun i : Fin 5 => ((Equiv.swap (0 : Fin 5) 1) i).val) 0 1 := by
  constructor
  · exact (rootPolynomial_perm (fun i : Fin 5 => (i.val : ℂ))
      (Equiv.swap (0 : Fin 5) 1)).symm
  · norm_num [rootKleinOmega5Ordered, centeredRoots, centeredRootSquares,
      rootMean, Equiv.swap_apply_def, Fin.sum_univ_succ]

end InfoGeometry.Erlangen.KleinQuinticGrassmannPluckerBridge
