/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Erlangen.GrassmannPluckerKleinCrossPillarBridges
import InfoGeometry.Canonical.GrassmannPfaffianDarbouxAlgebra
import InfoGeometry.Canonical.GrassmannPfaffianSyzygyAndNormalForms
import InfoGeometry.Canonical.OperatorErlangenGaloisConnection
import InfoGeometry.Algebra.KinematicCliffordAlgebra
import InfoGeometry.Geometry.PhaseErlanger
import InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis
import InfoGeometry.Lie.SplitG2RealFormCapstone
import InfoGeometry.Lie.G2RollingBall
import InfoGeometry.Algebra.AlternativeRing
import InfoGeometry.Algebra.ZornAlternativeLaws
import InfoGeometry.Algebra.SplitOctonionZornAlgebra
import InfoGeometry.Exceptional.SplitOctonionZorn
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Lie, Klein, Pfaff–Darboux, Cartan `(2,3,5)`/$G_{2(2)}$, & Zorn Primary Sources (`S2-05`..`S2-10`)

This module formalizes primary-source mathematical archetypes across `S2-05`..`S2-10` while
preserving `ORIGINAL_REQUEST.md § R3.2` and `§ R3.4` (`BUCKET 1/2` algebraic/geometric theorems;
smooth PDE integration remains in `O-EXT` (`BUCKET 3 analytic PDE boundary`)):

1. **`S2-05` (Lie 1872)**: Line-sphere `(3,3) ↔ (3,2)` hyperplane cut and Sylvester signature
   identification (`kleinQuadricForm ℝ` ↔ `(lieQuadricBilin 2).toQuadraticMap` ↔ `lieBilinForm`),
   degenerate special-complex hyperplane edge case, and zero-radius point-sphere dilation.
2. **`S2-06` (Klein 1872 / 1893)**: Antitone Erlanger `(M, G)` invariant-predicate and readout
   lattice (`H ≤ K → Inv(K) ⊆ Inv(H)`), Galois connection & adjoining, strict `SO(Q)`
   expansion in `CliffordAlgebra Q`, `{1, -1}` non-faithful normal stabilizer on `evenOdd Q 0`,
   and chiral stabilizer invariance.
3. **`S2-07` (Klein 1871, 1873)**: `(n + 1)`-dimensional Cayley–Klein quadratic-signature
   trichotomy (`κ > 0` elliptic `(n+1, 0, 0)`, `κ < 0` hyperbolic `(1, n, 0)`, `κ = 0` parabolic
   `(1, 0, n)`), parabolic Euclidean chord limit, and coordinate-free Klein–Beltrami chord bound
   with null-cone infinite-distance boundary.
4. **`S2-08` (Pfaff 1814–15 & Darboux 1882)**: Faithfulness-free `LieActionLane` /
   `DerivationOperatorForm` algebraic Pfaffian class invariants (`ω ∧ (dω)^r`), even/odd class
   disjointness, Lie-closed characteristic subspace `ker ω ∩ ker dω`, and `contactCEOneForm 2`
   class-5 certification (with smooth local PDE Frobenius/Darboux integration kept in `O-EXT`).
5. **`S2-09` (É. Cartan 1910, 1914)**: 5-variable `(2,3,5)` Pfaffian derived flag `3 → 2 → 0`
   (distribution growth `2 → 3 → 5`), integrable `(2,2,2)` and Engel `(2,3,4)` edge cases,
   `cartan235Symbol1 < cartan235Symbol2 < cartan235Symbol3 ≤ g2Submodule` inside `g2LieSubalgebra`,
   split `g_{2(2)}` real-form witness (`g2H1 * g2Zpos2 - g2Zpos2 * g2H1 = 2 • g2Zpos2` + `ℝ¹⁶`
   `kreinMetric88`-skew invariance), `3 : 1` rolling ball, `SL(2)` binary-quartic invariance/syzygy
   (`quarticInvI`, `quarticInvJ`, `cayley_binary_quartic_syzygy`) with flat vs. non-flat
   separation, and `split_g2_derivation_exponential_is_real_automorphism`.
6. **`S2-10` (Zorn 1930–1933)**: Explicit isomorphism `SplitOctonion ≃ₗ[ℝ] ZornVectorMatrix ℝ`,
   alternative and Moufang laws, Teichmüller identity, multiplicative split `(4,4)` norm,
   zero-divisor witnesses across all three repo Zorn models, 3-element non-associativity
   witnesses, and Zorn (1930) Peirce relations.
-/

noncomputable section

namespace InfoGeometry.Erlangen.LieKleinPfaffCartanPrimary

open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.PluckerMatrixAction
open InfoGeometry.Projective.GrassmannAusdehnungslehreRegressiveShadow
open InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms
open InfoGeometry.Canonical.GrassmannPfaffianDarbouxAlgebra
open InfoGeometry.Canonical.MajoranaPfaffian4
open InfoGeometry.Canonical.GrassmannPfaffianSyzygyAndNormalForms
open InfoGeometry.Canonical.OperatorErlangenFixedPoints
open InfoGeometry.Erlangen.InvariantGeometry
open InfoGeometry.Erlangen.ErlangenProgramGroupHierarchyAndPrincipal
open InfoGeometry.Erlangen.ErlangenProgramMobiusLieAndContact
open InfoGeometry.Erlangen.ErlangenProgramCurvatureBinaryAndMasterAtlas
open InfoGeometry.Erlangen.GrassmannPluckerKleinCrossPillarBridges
open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.Clifford.CoordinateLessCliffordInvariance
open InfoGeometry.Geometry
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis
open InfoGeometry.Lie.SplitG2RealFormCapstone
open InfoGeometry.Lie.G2RollingBall
open InfoGeometry.Algebra
open InfoGeometry.Algebra.SplitOctonionZorn
open scoped Matrix

/-! ## Section 1: Lie (1872) — Line-Sphere `(3,3) ↔ (3,2)` Hyperplane & Signature Relation (`S2-05`) -/

section LieLineSphere1872

/-- **Lie (`S2-05` §§1–18; `R3.2`)**:
explicit diagonalizing isometry from `kleinQuadricForm ℝ` on `Fin 6 → ℝ` to the split
`(3, 3)` weighted sum of squares `![1, 1, 1, -1, -1, -1]`. -/
def kleinWeightedSumEquiv :
    (kleinQuadricForm ℝ).IsometryEquiv
      (QuadraticMap.weightedSumSquares ℝ (![1, 1, 1, -1, -1, -1] : Fin 6 → ℝ)) where
  toFun x :=
    ![(x 0 + x 5) / 2, (x 2 + x 3) / 2, (x 4 - x 1) / 2,
      (x 0 - x 5) / 2, (x 2 - x 3) / 2, (x 4 + x 1) / 2]
  invFun u :=
    ![u 0 + u 3, u 5 - u 2, u 1 + u 4, u 1 - u 4, u 5 + u 2, u 0 - u 3]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring
  left_inv x := by
    ext i
    fin_cases i <;> simp <;> ring
  right_inv u := by
    ext i
    fin_cases i <;> simp
  map_app' x := by
    change QuadraticMap.weightedSumSquares ℝ (![1, 1, 1, -1, -1, -1] : Fin 6 → ℝ) _ =
      kleinQuadricForm ℝ x
    rw [QuadraticMap.weightedSumSquares_apply]
    simp only [Fin.sum_univ_six, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, kleinQuadricForm, QuadraticMap.coe_mk, Plucker6.kleinQ,
      coordinates, Equiv.coe_fn_symm_mk]
    ring

/-- **Lie (`S2-05` §§1–18; `R3.2`)**:
Sylvester inertia signature of the Klein quadric `kleinQuadricForm ℝ` is `(3, 3)`. -/
theorem kleinQuadricForm_signature :
    sigPos (kleinQuadricForm ℝ) = 3 ∧ sigNeg (kleinQuadricForm ℝ) = 3 := by
  let w : Fin 6 → ℝ := ![1, 1, 1, -1, -1, -1]
  have heq : (kleinQuadricForm ℝ).Equivalent (QuadraticMap.weightedSumSquares ℝ w) :=
    ⟨kleinWeightedSumEquiv⟩
  have hpos : ({i : Fin 6 | (0 : ℝ) < w i} : Set (Fin 6)) = {0, 1, 2} := by
    ext i
    fin_cases i <;> simp [w]
  have hneg : ({i : Fin 6 | w i < 0} : Set (Fin 6)) = {3, 4, 5} := by
    ext i
    fin_cases i <;> simp [w]
  have hcpos : ({0, 1, 2} : Set (Fin 6)).ncard = 3 := by
    have hfin : ({0, 1, 2} : Set (Fin 6)) = (({0, 1, 2} : Finset (Fin 6)) : Set (Fin 6)) := by simp
    rw [hfin, Set.ncard_coe_finset]
    decide
  have hcneg : ({3, 4, 5} : Set (Fin 6)).ncard = 3 := by
    have hfin : ({3, 4, 5} : Set (Fin 6)) = (({3, 4, 5} : Finset (Fin 6)) : Set (Fin 6)) := by simp
    rw [hfin, Set.ncard_coe_finset]
    decide
  refine ⟨?_, ?_⟩
  · rw [heq.sigPos_eq, QuadraticForm.sigPos_weightedSumSquares, hpos, hcpos]
  · rw [heq.sigNeg_eq, QuadraticForm.sigNeg_weightedSumSquares, hneg, hcneg]

/-- **Lie (`S2-05` §§1–18; `R3.2`)**:
nondegenerate linear complex pole `C = ⟨1, 0, 0, 0, 0, -1⟩` (`C.kleinQ = -1`) whose polar
hyperplane in `ℝ⁶` cuts out Lie's 5D sphere quadric of signature `(3, 2)`. -/
def lieComplexPole : Plucker6 ℝ :=
  ⟨1, 0, 0, 0, 0, -1⟩

/-- **Lie (`S2-05` §§1–18; `R3.2`)**:
polar hyperplane `lieComplexPole.polar P = 0` (`x 0 = x 5`) inside `Fin 6 → ℝ`. -/
def lieComplexHyperplane : Submodule ℝ (Fin 6 → ℝ) :=
  LinearMap.ker ((LinearMap.proj 0 : (Fin 6 → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj 5)

/-- **Lie (`S2-05` §§1–18; `R3.2`)**:
characterization of `lieComplexHyperplane` as the exact polar hyperplane of `lieComplexPole`. -/
theorem mem_lieComplexHyperplane_iff_polar (x : Fin 6 → ℝ) :
    x ∈ lieComplexHyperplane ↔ Plucker6.polar lieComplexPole (coordinates.symm x) = 0 := by
  rw [lieComplexHyperplane, LinearMap.mem_ker]
  change x 0 - x 5 = 0 ↔ _
  simp only [lieComplexPole, Plucker6.polar_formula, coordinates, Equiv.coe_fn_symm_mk]
  constructor <;> intro h <;> linarith

/-- **Lie (`S2-05` §§1–18; `R3.2`)**:
linear inclusion of Lie's 5D oriented circle space `Fin 5 → ℝ` into the Klein ambient `Fin 6 → ℝ`. -/
def lie5ToKleinHyperplaneIncl : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun u := ![u 0, u 4 - u 2, u 1 + u 3, u 1 - u 3, u 2 + u 4, u 0]
  map_add' u v := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c u := by
    ext i
    fin_cases i <;> simp <;> ring

/-- **Lie (`S2-05` §§1–18; `R3.2`)**:
`lie5ToKleinHyperplaneIncl` lands inside `lieComplexHyperplane`. -/
theorem lie5ToKleinHyperplaneIncl_mem (u : Fin 5 → ℝ) :
    lie5ToKleinHyperplaneIncl u ∈ lieComplexHyperplane := by
  rw [lieComplexHyperplane, LinearMap.mem_ker]
  change lie5ToKleinHyperplaneIncl u 0 - lie5ToKleinHyperplaneIncl u 5 = 0
  simp [lie5ToKleinHyperplaneIncl]

/-- **Lie (`S2-05` §§1–18; `R3.2`)**:
linear equivalence between Lie's 5D sphere space and the polar hyperplane `lieComplexHyperplane`. -/
def lie5ToKleinHyperplaneEquiv : (Fin 5 → ℝ) ≃ₗ[ℝ] lieComplexHyperplane where
  toFun u := ⟨lie5ToKleinHyperplaneIncl u, lie5ToKleinHyperplaneIncl_mem u⟩
  invFun x :=
    ![x.1 0, (x.1 2 + x.1 3) / 2, (x.1 4 - x.1 1) / 2,
      (x.1 2 - x.1 3) / 2, (x.1 4 + x.1 1) / 2]
  map_add' u v := by
    apply Subtype.ext
    exact lie5ToKleinHyperplaneIncl.map_add u v
  map_smul' c u := by
    apply Subtype.ext
    exact lie5ToKleinHyperplaneIncl.map_smul c u
  left_inv u := by
    ext i
    fin_cases i <;> simp [lie5ToKleinHyperplaneIncl] <;> ring
  right_inv x := by
    apply Subtype.ext
    have hx : x.1 0 - x.1 5 = 0 := by
      have hmem := x.2
      dsimp only [lieComplexHyperplane] at hmem
      rw [LinearMap.mem_ker] at hmem
      exact hmem
    have hx05 : x.1 5 = x.1 0 := (sub_eq_zero.mp hx).symm
    ext i
    fin_cases i <;> simp [lie5ToKleinHyperplaneIncl, hx05] <;> ring

/-- **Lie (`S2-05` §§1–18; `R3.2`)**:
explicit quadratic isometry identifying `(lieQuadricBilin 2).toQuadraticMap` with the restriction
of `kleinQuadricForm ℝ` to the polar hyperplane `lieComplexHyperplane`. -/
def lieQuadric2ToKleinHyperplaneIsometry :
    (lieQuadricBilin 2).toQuadraticMap.IsometryEquiv
      ((kleinQuadricForm ℝ).restrict lieComplexHyperplane) where
  toLinearEquiv := lie5ToKleinHyperplaneEquiv
  map_app' u := by
    change kleinQuadricForm ℝ (lie5ToKleinHyperplaneIncl u) = lieQuadricBilin 2 u u
    simp only [kleinQuadricForm, QuadraticMap.coe_mk, Plucker6.kleinQ, coordinates,
      Equiv.coe_fn_symm_mk, lie5ToKleinHyperplaneIncl, LinearMap.coe_mk, AddHom.coe_mk]
    change ![u 0, u 4 - u 2, u 1 + u 3, u 1 - u 3, u 2 + u 4, u 0] 0 *
          ![u 0, u 4 - u 2, u 1 + u 3, u 1 - u 3, u 2 + u 4, u 0] 5 -
        ![u 0, u 4 - u 2, u 1 + u 3, u 1 - u 3, u 2 + u 4, u 0] 1 *
          ![u 0, u 4 - u 2, u 1 + u 3, u 1 - u 3, u 2 + u 4, u 0] 4 +
      ![u 0, u 4 - u 2, u 1 + u 3, u 1 - u 3, u 2 + u 4, u 0] 2 *
        ![u 0, u 4 - u 2, u 1 + u 3, u 1 - u 3, u 2 + u 4, u 0] 3 =
      (∑ i : Fin 2, u (Fin.castAdd 3 i) * u (Fin.castAdd 3 i)) +
        u ⟨2, by omega⟩ * u ⟨2, by omega⟩ -
        u ⟨3, by omega⟩ * u ⟨3, by omega⟩ -
        u ⟨4, by omega⟩ * u ⟨4, by omega⟩
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    change u 0 * u 0 - (u 4 - u 2) * (u 2 + u 4) + (u 1 + u 3) * (u 1 - u 3) =
      u 0 * u 0 + u 1 * u 1 + u 2 * u 2 - u 3 * u 3 - u 4 * u 4
    ring

/-- **Lie (`S2-05` §§1–18; `R3.2`)**:
line-sphere signature and hyperplane-cut correspondence:
1. Klein's ambient 6D line quadric has signature `(3, 3)`.
2. Cutting by the nondegenerate polar hyperplane `lieComplexHyperplane` drops the signature to `(3, 2)`.
3. Both `(lieQuadricBilin 2).toQuadraticMap` and `lieBilinForm.toQuadraticMap` share signature `(3, 2)`. -/
theorem lie_line_sphere_hyperplane_signature_relation :
    (sigPos (kleinQuadricForm ℝ) = 3 ∧ sigNeg (kleinQuadricForm ℝ) = 3) ∧
    (sigPos ((kleinQuadricForm ℝ).restrict lieComplexHyperplane) = 3 ∧
      sigNeg ((kleinQuadricForm ℝ).restrict lieComplexHyperplane) = 2) ∧
    (sigPos (lieQuadricBilin 2).toQuadraticMap = 3 ∧
      sigNeg (lieQuadricBilin 2).toQuadraticMap = 2) ∧
    (sigPos lieBilinForm.toQuadraticMap = 3 ∧ sigNeg lieBilinForm.toQuadraticMap = 2) := by
  have h2 : (lieQuadricBilin 2).toQuadraticMap.Equivalent
      ((kleinQuadricForm ℝ).restrict lieComplexHyperplane) :=
    ⟨lieQuadric2ToKleinHyperplaneIsometry⟩
  have hlie : lieBilinForm.toQuadraticMap.Equivalent (lieQuadricBilin 2).toQuadraticMap :=
    ⟨lieBilin_isometryEquiv_lieQuadric2⟩
  refine ⟨kleinQuadricForm_signature, ?_, lieQuadricBilin_signature_dim2, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [← h2.sigPos_eq]; exact lieQuadricBilin_signature_dim2.1
    · rw [← h2.sigNeg_eq]; exact lieQuadricBilin_signature_dim2.2
  · refine ⟨?_, ?_⟩
    · rw [hlie.sigPos_eq]; exact lieQuadricBilin_signature_dim2.1
    · rw [hlie.sigNeg_eq]; exact lieQuadricBilin_signature_dim2.2

/-- **Lie (`S2-05` §§1–18; `R3.2`)**:
edge cases of the line-sphere correspondence:
1. Cutting `kleinQuadricForm ℝ` by the polar hyperplane of a special complex `⟨1, 0, 0, 0, 0, 0⟩`
   (`kleinQ = 0`) yields a degenerate quadratic form with nontrivial radical (`≠ ⊥`).
2. Lie radius dilation `lieRadiusDilMatrix t` maps zero-radius point-spheres `(a, b, 0)` to
   oriented circles `(a, b, t)`. -/
theorem lie_special_complex_degenerate_hyperplane (a b t : ℝ) :
    let Cdeg : Plucker6 ℝ := ⟨1, 0, 0, 0, 0, 0⟩
    let Hdeg : Submodule ℝ (Fin 6 → ℝ) := LinearMap.ker (LinearMap.proj 5)
    Cdeg.kleinQ = 0 ∧
      ((kleinQuadricForm ℝ).restrict Hdeg).radical ≠ ⊥ ∧
      (lieRadiusDilMatrix t).mulVec (lieCircleVec a b 0) = lieCircleVec a b t := by
  intro Cdeg Hdeg
  have hq : Cdeg.kleinQ = 0 := by simp [Cdeg, Plucker6.kleinQ]
  have hrad : ((kleinQuadricForm ℝ).restrict Hdeg).radical ≠ ⊥ := by
    let e0 : Hdeg := ⟨![1, 0, 0, 0, 0, 0], by simp [Hdeg]⟩
    have he0_ne : e0 ≠ 0 := by
      intro h0
      have hval := congrArg (fun z : Hdeg => z.1 0) h0
      norm_num [e0] at hval
    have he0_rad : e0 ∈ ((kleinQuadricForm ℝ).restrict Hdeg).radical := by
      rw [QuadraticMap.mem_radical_iff']
      refine ⟨?_, fun y => ?_⟩
      · change kleinQuadricForm ℝ e0.1 = 0
        simp [kleinQuadricForm, Plucker6.kleinQ, coordinates, e0]
      · have hy5 : y.1 5 = 0 := y.2
        change kleinQuadricForm ℝ (e0.1 + y.1) = kleinQuadricForm ℝ y.1
        simp only [kleinQuadricForm, QuadraticMap.coe_mk, Plucker6.kleinQ, coordinates,
          Equiv.coe_fn_symm_mk, Pi.add_apply, hy5, e0, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val]
        ring
    intro hbot
    rw [hbot] at he0_rad
    exact he0_ne ((Submodule.mem_bot ℝ).mp he0_rad)
  exact ⟨hq, hrad, by simpa using lieRadiusDilMatrix_mulVec_circleVec t a b 0⟩

end LieLineSphere1872

/-! ## Section 2: Klein (1872 / 1893) — Erlanger `(M, G)` Lattice & Non-Faithful Stabilizers (`S2-06`) -/

section KleinErlanger1872

/-- **Klein (`S2-06` §§1–5; `R3.2`)**:
set of `H`-invariant predicates on `M` for a subgroup `H ≤ G`. -/
def invariantPredicateSet (G M : Type*) [Group G] [MulAction G M] (H : Subgroup G) :
    Set (M → Prop) :=
  {P | IsGeometricInvariant H M P}

/-- **Klein (`S2-06` §§1–5; `R3.2`)**:
set of `H`-invariant readouts `M → β` for a subgroup `H ≤ G`. -/
def invariantReadoutSet (G M β : Type*) [Group G] [MulAction G M] (H : Subgroup G) :
    Set (M → β) :=
  {f | IsInvariantReadout H M f}

/-- **Klein (`S2-06` §§1–5; `R3.2`)**:
antitone Erlanger subgroup-invariant lattice law for predicates: passing to a smaller subgroup
`H ≤ K` enlarges the invariant predicate set (`Inv(K) ⊆ Inv(H)`). -/
theorem invariantPredicateSet_antitone (G M : Type*) [Group G] [MulAction G M]
    {H K : Subgroup G} (hHK : H ≤ K) :
    invariantPredicateSet G M K ⊆ invariantPredicateSet G M H := by
  intro P hP
  exact isGeometricInvariant_mono_subgroup hHK hP

/-- **Klein (`S2-06` §§1–5; `R3.2`)**:
antitone Erlanger subgroup-invariant lattice law for readouts `M → β`. -/
theorem invariantReadoutSet_antitone (G M β : Type*) [Group G] [MulAction G M]
    {H K : Subgroup G} (hHK : H ≤ K) :
    invariantReadoutSet G M β K ⊆ invariantReadoutSet G M β H := by
  intro f hf h m
  exact hf ⟨(h : G), hHK h.property⟩ m

/-- **Klein (`S2-06` §§1–5; `R3.2`)**:
Erlanger Galois connection between subgroups and operator fixed-point sets paired with Klein's
§2 adjoining equivalence. -/
theorem erlangen_galois_and_adjoining {G A : Type*} [Group G] [Semiring A] [MulSemiringAction G A]
    (H : Subgroup G) (S : Set A) :
    (H ≤ fixingSubgroup (G := G) (A := A) S ↔ S ⊆ fixedPointSet (G := G) (A := A) H) ∧
      ∀ (C M : Type*) [MulAction G C] [MulAction G M] (c₀ : C),
        Nonempty (JointOrbitInvariant G C M c₀ ≃ StabilizerInvariant G C M c₀) := by
  refine ⟨subgroup_le_fixingSubgroup_iff, ?_⟩
  intro C M _ _ c₀
  exact ⟨klein_adjoining_equiv G C M c₀⟩

/-- **Klein (`S2-06` §§1–5; `R3.2`)**:
strict subgroup-invariant expansion inside `CliffordAlgebra Q`: for any finite-dimensional
quadratic space `(Fin n → ℝ, Q)` with `1 ≤ n`, restricting from `O(Q)` to `SO(Q)` preserves
every `O(Q)`-invariant and strictly adds the top-grade volume blade, which is `SO(Q)`-invariant
yet fails `O(Q)`-invariance. -/
theorem clifford_so_strictly_enlarges_invariant_subalgebra {n : ℕ} (hn : 1 ≤ n)
    (Q : QuadraticForm ℝ (Fin n → ℝ)) :
    (∀ x : CliffordAlgebra Q, IsInvariant (cliffordSymmetryAction Q) x →
      ∀ f ∈ specialIsometrySubgroup Q, CliffordAlgebra.equivOfIsometry f x = x) ∧
    ∃ ω : CliffordAlgebra Q,
      (∀ f ∈ specialIsometrySubgroup Q, CliffordAlgebra.equivOfIsometry f ω = ω) ∧
      ¬ IsInvariant (cliffordSymmetryAction Q) ω := by
  refine ⟨fun x hx f _ => hx f, ?_⟩
  let b := Pi.basisFun ℝ (Fin n)
  let e := CliffordAlgebra.equivExterior Q
  let volExt : ExteriorAlgebra ℝ (Fin n → ℝ) := ExteriorAlgebra.ιMulti ℝ n b
  let ω : CliffordAlgebra Q := e.symm volExt
  have hvol_mem : volExt ∈ ⋀[ℝ]^n (Fin n → ℝ) := ExteriorAlgebra.ιMulti_range ℝ n ⟨b, rfl⟩
  have hω_grade : ω ∈ cliffordGradeSubmodule Q (Module.finrank ℝ (Fin n → ℝ)) := by
    rw [Module.finrank_fin_fun, mem_cliffordGradeSubmodule_iff]
    dsimp only [cliffordGradeProj]
    change (CliffordAlgebra.equivExterior Q).symm
        (exteriorGradeProj ℝ (Fin n → ℝ) n (CliffordAlgebra.equivExterior Q (e.symm volExt))) =
      e.symm volExt
    rw [e.apply_symm_apply, exteriorGradeProj_of_mem hvol_mem]
  have hω_so : ∀ f ∈ specialIsometrySubgroup Q, CliffordAlgebra.equivOfIsometry f ω = ω := by
    rw [isInvariant_specialIsometry_iff Q ω]
    exact Submodule.mem_sup_right hω_grade
  have hω_not_scalar : ¬ ∃ c : ℝ, ω = algebraMap ℝ (CliffordAlgebra Q) c := by
    rintro ⟨c, hc⟩
    have hc_ext : volExt = algebraMap ℝ (ExteriorAlgebra ℝ (Fin n → ℝ)) c := by
      have h1 := congrArg e hc
      rw [e.apply_symm_apply, equivExterior_algebraMap] at h1
      exact h1
    have hvol_basis : volExt = b.ExteriorAlgebra Finset.univ := by
      change ExteriorAlgebra.ιMulti ℝ n b = b.ExteriorAlgebra Finset.univ
      rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_fin n)]
      let g := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (Finset.card_fin n))
      have hord : ∀ i : Fin n, g i = i := fun i => by
        have hle : i ≤ g i := g.strictMono.id_le i
        have hsub : Finset.image g (Finset.Ici i) ≤ Finset.Ici (g i) := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨k, hk, rfl⟩
          exact Finset.mem_Ici.mpr (g.monotone (Finset.mem_Ici.mp hk))
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_image_of_injective _ g.injective, Fin.card_Ici, Fin.card_Ici] at hcard
        exact Fin.ext (by omega)
      have hfun : (fun i : Fin n => b (g i)) = b := by funext i; rw [hord i]
      change ExteriorAlgebra.ιMulti ℝ n b = ExteriorAlgebra.ιMulti ℝ n (fun i => b (g i))
      rw [hfun]
    have h1_basis : (1 : ExteriorAlgebra ℝ (Fin n → ℝ)) = b.ExteriorAlgebra ∅ := by
      rw [ExteriorAlgebra.basis_apply_ofCard b Finset.card_empty]
      change (1 : ExteriorAlgebra ℝ (Fin n → ℝ)) = ExteriorAlgebra.ιMulti ℝ 0 _
      rw [ExteriorAlgebra.ιMulti_zero_apply]
    have hne_empty : (∅ : Finset (Fin n)) ≠ Finset.univ := by
      intro hem
      have hcard := congrArg Finset.card hem
      rw [Finset.card_empty, Finset.card_univ, Fintype.card_fin] at hcard
      linarith [hn, hcard]
    have hcoord := congrArg (b.ExteriorAlgebra.coord Finset.univ) hc_ext
    rw [hvol_basis, b.ExteriorAlgebra.coord_apply, b.ExteriorAlgebra.repr_self,
      Finsupp.single_eq_same, Algebra.algebraMap_eq_smul_one, h1_basis, map_smul,
      smul_eq_mul, b.ExteriorAlgebra.coord_apply, b.ExteriorAlgebra.repr_self] at hcoord
    simp [hne_empty] at hcoord
  refine ⟨ω, hω_so, ?_⟩
  rw [isInvariant_cliffordSymmetryAction_iff_mem_range Q ω]
  exact hω_not_scalar

/-- **Klein (`S2-06` §§1–5; `R3.2`)**:
two-element central inversion normal subgroup `{1, negIsometryEquiv Q}` inside `O(Q)`. -/
def negIsometryNormalSubgroup {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) : Subgroup (Q.IsometryEquiv Q) where
  carrier := {1, negIsometryEquiv Q}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    have hneg2 : negIsometryEquiv Q * negIsometryEquiv Q = 1 := by
      apply DFunLike.ext
      intro m
      change -(-m) = m
      exact neg_neg m
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · simp
    · simp
    · simp
    · rw [hneg2]; simp
  inv_mem' {a} ha := by
    have hneg2 : negIsometryEquiv Q * negIsometryEquiv Q = 1 := by
      apply DFunLike.ext
      intro m
      change -(-m) = m
      exact neg_neg m
    rcases ha with rfl | rfl
    · simp
    · right
      exact inv_eq_of_mul_eq_one_right hneg2

/-- **Klein (`S2-06` §§1–5; `R3.2`)**:
non-faithful normal stabilizer witness: `{1, -id}` is normal in `O(Q)`, acts trivially on the
entire even Clifford subalgebra `evenOdd Q 0`, yet `negIsometryEquiv Q ≠ 1` whenever `M` is
nontrivial (with `[Invertible (2 : R)]`). -/
theorem negIsometryNormalSubgroup_normal_and_fixes_even {R M : Type*} [CommRing R]
    [Invertible (2 : R)] [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) :
    (negIsometryNormalSubgroup Q).Normal ∧
      (∀ g ∈ negIsometryNormalSubgroup Q, ∀ x ∈ CliffordAlgebra.evenOdd Q 0,
        CliffordAlgebra.equivOfIsometry g x = x) ∧
      (Nontrivial M → negIsometryEquiv Q ≠ 1) := by
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · intro g hg k
    rcases hg with rfl | rfl
    · simp
    · right
      apply DFunLike.ext
      intro m
      change k (-(k⁻¹ m)) = -m
      rw [map_neg]
      have hk : k (k⁻¹ m) = m := by
        change (k * k⁻¹) m = m
        rw [mul_inv_cancel]
        rfl
      rw [hk]
  · intro g hg x hx
    rcases hg with rfl | rfl
    · change CliffordAlgebra.equivOfIsometry (QuadraticMap.IsometryEquiv.refl Q) x = x
      simp
    · exact (equivOfIsometry_neg_fixed_iff_mem_even Q x).mpr hx
  · intro hM h1
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    have hneg : negIsometryEquiv Q m = (1 : Q.IsometryEquiv Q) m :=
      congrArg (fun f : Q.IsometryEquiv Q => f m) h1
    change -m = m at hneg
    have h2m : (2 : R) • m = 0 := by
      rw [two_smul]
      calc m + m = -m + m := congrArg (· + m) hneg.symm
      _ = 0 := neg_add_cancel m
    have hm0 : m = 0 := by
      have h := congrArg (fun z : M => (⅟(2 : R)) • z) h2m
      simpa [smul_smul, invOf_mul_self, one_smul] using h
    exact hm hm0

/-- **Klein (`S2-06` §§1–5; `R3.2`)**:
any chiral-preserving phase map intertwines `leftProjector` and `rightProjector` identically,
showing enlargement of invariant endomorphisms under chiral subgroup restriction. -/
theorem phaseErlanger_chiralStabilizer_invariance {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {K : PhaseErlanger.EndR H} (χ : PhaseErlanger.ChiralAxis K)
    (F : H →L[ℝ] H) (hF : PhaseErlanger.ChiralPreserving χ χ F) :
    F.comp χ.leftProjector = χ.leftProjector.comp F ∧
      F.comp χ.rightProjector = χ.rightProjector.comp F := by
  refine ⟨?_, ?_⟩
  · ext x
    simp only [ContinuousLinearMap.comp_apply, PhaseErlanger.ChiralAxis.leftProjector,
      smul_apply, add_apply, ContinuousLinearMap.id_apply, map_smul, map_add]
    have hchi : F (χ.chi x) = χ.chi (F x) := hF.map_chi x
    rw [hchi]
  · ext x
    simp only [ContinuousLinearMap.comp_apply, PhaseErlanger.ChiralAxis.rightProjector,
      smul_apply, sub_apply, ContinuousLinearMap.id_apply, map_smul, map_sub]
    have hchi : F (χ.chi x) = χ.chi (F x) := hF.map_chi x
    rw [hchi]

end KleinErlanger1872

/-! ## Section 3: Klein (1871, 1873) — Cayley–Klein `(n+1)`-dim Quadratic Signature (`S2-07`) -/

section CayleyKlein1871

/-- **Klein (`S2-07` Vol. 4 §§1–16; Vol. 6 §§1–10; `R3.2`)**:
weight vector `![κ, ..., κ, 1]` on `Fin (n + 1)` governing the projective fundamental quadric
across elliptic (`κ > 0`), hyperbolic (`κ < 0`), and parabolic/Euclidean (`κ = 0`) regimes. -/
def cayleyKleinWeights (n : ℕ) (κ : ℝ) : Fin (n + 1) → ℝ :=
  fun i => if i.val < n then κ else 1

/-- **Klein (`S2-07` Vol. 4 §§1–16; `R3.2`)**:
Cayley–Klein projective fundamental quadratic form `κ ∑_{i < n} x_i² + x_n²` on `Fin (n + 1) → ℝ`. -/
def cayleyKleinProjQuadForm (n : ℕ) (κ : ℝ) : QuadraticForm ℝ (Fin (n + 1) → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (cayleyKleinWeights n κ)

/-- **Klein (`S2-07` Vol. 4 §§1–16; `R3.2`)**:
Cayley–Klein projective fundamental symmetric bilinear form associated to `cayleyKleinProjQuadForm`. -/
def cayleyKleinProjBilin (n : ℕ) (κ : ℝ) : LinearMap.BilinForm ℝ (Fin (n + 1) → ℝ) :=
  (cayleyKleinProjQuadForm n κ).associated

/-- **Klein (`S2-07` Vol. 4 §§1–16; `R3.2`)**:
coordinate evaluation of `cayleyKleinProjQuadForm n κ` as `κ ∑ x_i² + x_n²`. -/
theorem cayleyKleinProjQuadForm_apply (n : ℕ) (κ : ℝ) (x : Fin (n + 1) → ℝ) :
    cayleyKleinProjQuadForm n κ x = (∑ i : Fin n, κ * (x i.castSucc) ^ 2) + (x (Fin.last n)) ^ 2 := by
  rw [cayleyKleinProjQuadForm, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_castSucc]
  simp only [cayleyKleinWeights, Fin.val_castSucc, Fin.is_lt, ↓reduceIte, smul_eq_mul,
    Fin.val_last, lt_self_iff_false, one_mul]
  refine congrArg₂ (· + ·) ?_ (by ring)
  refine Finset.sum_congr rfl fun i _ => by ring

/-- **Klein (`S2-07` Vol. 4 §§1–16; `R3.2`)**:
coordinate evaluation of the polar bilinear form `cayleyKleinProjBilin n κ`. -/
theorem cayleyKleinProjBilin_apply (n : ℕ) (κ : ℝ) (x y : Fin (n + 1) → ℝ) :
    cayleyKleinProjBilin n κ x y =
      (∑ i : Fin n, κ * x i.castSucc * y i.castSucc) + x (Fin.last n) * y (Fin.last n) := by
  dsimp [cayleyKleinProjBilin, cayleyKleinProjQuadForm]
  rw [QuadraticMap.associated_apply]
  simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, Pi.add_apply,
    Fin.sum_univ_castSucc, cayleyKleinWeights, Fin.val_castSucc, Fin.is_lt, ↓reduceIte,
    Fin.val_last, lt_self_iff_false, one_mul]
  rw [invOf_smul_eq_iff, two_smul]
  have hsum : (∑ i : Fin n, κ * ((x i.castSucc + y i.castSucc) * (x i.castSucc + y i.castSucc)) -
      ∑ i : Fin n, κ * (x i.castSucc * x i.castSucc) -
      ∑ i : Fin n, κ * (y i.castSucc * y i.castSucc)) =
      2 * ∑ i : Fin n, κ * x i.castSucc * y i.castSucc := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  linarith [hsum]

/-- **Klein (`S2-07` Vol. 4 §§1–16; `R3.2`)**:
symmetry of the Cayley–Klein projective fundamental bilinear form `cayleyKleinProjBilin`. -/
theorem cayleyKleinProjBilin_symm (n : ℕ) (κ : ℝ) (x y : Fin (n + 1) → ℝ) :
    cayleyKleinProjBilin n κ x y = cayleyKleinProjBilin n κ y x := by
  rw [cayleyKleinProjBilin_apply, cayleyKleinProjBilin_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => by ring
  · ring

/-- **Klein (`S2-07` Vol. 4 §§1–16; Vol. 6 §§1–10; `R3.2`)**:
complete `(n + 1)`-dimensional Cayley–Klein Sylvester signature trichotomy:
1. Elliptic (`κ > 0`): `(sigPos, sigNeg, radical) = (n + 1, 0, 0)`.
2. Hyperbolic (`κ < 0`): `(sigPos, sigNeg, radical) = (1, n, 0)`.
3. Parabolic / Euclidean (`κ = 0`): `(sigPos, sigNeg, radical) = (1, 0, n)`. -/
theorem cayleyKleinProjQuadForm_signature_trichotomy (n : ℕ) (κ : ℝ) :
    (0 < κ → sigPos (cayleyKleinProjQuadForm n κ) = n + 1 ∧
      sigNeg (cayleyKleinProjQuadForm n κ) = 0 ∧
      Module.finrank ℝ (cayleyKleinProjQuadForm n κ).radical = 0) ∧
    (κ < 0 → sigPos (cayleyKleinProjQuadForm n κ) = 1 ∧
      sigNeg (cayleyKleinProjQuadForm n κ) = n ∧
      Module.finrank ℝ (cayleyKleinProjQuadForm n κ).radical = 0) ∧
    (κ = 0 → sigPos (cayleyKleinProjQuadForm n κ) = 1 ∧
      sigNeg (cayleyKleinProjQuadForm n κ) = 0 ∧
      Module.finrank ℝ (cayleyKleinProjQuadForm n κ).radical = n) := by
  classical
  have hcast : ∀ p : Fin (n + 1) → Prop,
      ({i : Fin (n + 1) | p i} : Set (Fin (n + 1))).ncard =
        (Finset.univ.filter p).card := by
    intro p
    have hset : ({i : Fin (n + 1) | p i} : Set (Fin (n + 1))) =
        ((Finset.univ.filter p : Finset (Fin (n + 1))) : Set (Fin (n + 1))) := by
      ext i; simp
    rw [hset, Set.ncard_coe_finset]
  have hcard_lt : (Finset.univ.filter fun i : Fin (n + 1) => i.val < n).card = n := by
    have hbi : Finset.univ.filter (fun i : Fin (n + 1) => i.val < n) =
        Finset.univ.image Fin.castSucc := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hi
        exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
      · rintro ⟨j, rfl⟩
        exact j.isLt
    rw [hbi, Finset.card_image_of_injective _ (Fin.castSucc_injective (n := n)),
      Finset.card_univ, Fintype.card_fin]
  have hcard_last : (Finset.univ.filter fun i : Fin (n + 1) => ¬ i.val < n).card = 1 := by
    have hbi : Finset.univ.filter (fun i : Fin (n + 1) => ¬ i.val < n) = {Fin.last n} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff,
        Fin.val_last]
      omega
    rw [hbi, Finset.card_singleton]
  refine ⟨?_, ?_, ?_⟩
  · intro hκ
    have hsp : {i : Fin (n + 1) | (0 : ℝ) < cayleyKleinWeights n κ i} = Set.univ := by
      ext i
      simp only [Set.mem_ofPred_eq, cayleyKleinWeights, Set.mem_univ, iff_true]
      split_ifs <;> linarith
    have hsn : {i : Fin (n + 1) | cayleyKleinWeights n κ i < 0} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, cayleyKleinWeights, Set.mem_empty_iff_false, iff_false, not_lt]
      split_ifs <;> linarith
    have hrad : {i : Fin (n + 1) | cayleyKleinWeights n κ i = 0} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, cayleyKleinWeights, Set.mem_empty_iff_false, iff_false]
      split_ifs <;> linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [cayleyKleinProjQuadForm, QuadraticForm.sigPos_weightedSumSquares, hsp, Set.ncard_univ,
        Nat.card_fin]
    · rw [cayleyKleinProjQuadForm, QuadraticForm.sigNeg_weightedSumSquares, hsn, Set.ncard_empty]
    · rw [cayleyKleinProjQuadForm, QuadraticForm.radical_weightedSumSquares, hrad, Pi.dim_spanSubset,
        Set.ncard_empty]
  · intro hκ
    have hsp : {i : Fin (n + 1) | (0 : ℝ) < cayleyKleinWeights n κ i} =
        {i : Fin (n + 1) | ¬ i.val < n} := by
      ext i
      simp only [Set.mem_ofPred_eq, cayleyKleinWeights]
      split_ifs with hi
      · constructor <;> intro h <;> linarith
      · constructor <;> intro _ <;> [exact hi; norm_num]
    have hsn : {i : Fin (n + 1) | cayleyKleinWeights n κ i < 0} =
        {i : Fin (n + 1) | i.val < n} := by
      ext i
      simp only [Set.mem_ofPred_eq, cayleyKleinWeights]
      split_ifs with hi
      · exact ⟨fun _ => hi, fun _ => hκ⟩
      · exact ⟨fun h => absurd h (by norm_num), fun h => absurd h hi⟩
    have hrad : {i : Fin (n + 1) | cayleyKleinWeights n κ i = 0} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, cayleyKleinWeights, Set.mem_empty_iff_false, iff_false]
      split_ifs <;> linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [cayleyKleinProjQuadForm, QuadraticForm.sigPos_weightedSumSquares, hsp, hcast]
      convert hcard_last
    · rw [cayleyKleinProjQuadForm, QuadraticForm.sigNeg_weightedSumSquares, hsn, hcast]
      convert hcard_lt
    · rw [cayleyKleinProjQuadForm, QuadraticForm.radical_weightedSumSquares, hrad, Pi.dim_spanSubset,
        Set.ncard_empty]
  · intro hκ
    subst hκ
    have hsp : {i : Fin (n + 1) | (0 : ℝ) < cayleyKleinWeights n 0 i} =
        {i : Fin (n + 1) | ¬ i.val < n} := by
      ext i
      simp only [Set.mem_ofPred_eq, cayleyKleinWeights]
      split_ifs with hi
      · exact ⟨fun h => absurd h (by norm_num), fun h => absurd hi h⟩
      · exact ⟨fun _ => hi, fun _ => by norm_num⟩
    have hsn : {i : Fin (n + 1) | cayleyKleinWeights n 0 i < 0} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, cayleyKleinWeights, Set.mem_empty_iff_false, iff_false, not_lt]
      split_ifs <;> norm_num
    have hrad : {i : Fin (n + 1) | cayleyKleinWeights n 0 i = 0} =
        {i : Fin (n + 1) | i.val < n} := by
      ext i
      simp only [Set.mem_ofPred_eq, cayleyKleinWeights]
      split_ifs with hi
      · exact ⟨fun _ => hi, fun _ => rfl⟩
      · exact ⟨fun h => absurd h (by norm_num), fun h => absurd h hi⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [cayleyKleinProjQuadForm, QuadraticForm.sigPos_weightedSumSquares, hsp, hcast]
      convert hcard_last
    · rw [cayleyKleinProjQuadForm, QuadraticForm.sigNeg_weightedSumSquares, hsn, Set.ncard_empty]
    · rw [cayleyKleinProjQuadForm, QuadraticForm.radical_weightedSumSquares, hrad, Pi.dim_spanSubset,
        hcast]
      convert hcard_lt

/-- **Klein (`S2-07` Vol. 4 §§1–16; `R3.2`)**:
affine chart lift `x ↦ (x, 1) ∈ ℝ^{n+1}` for Euclidean limit comparison. -/
def cayleyKleinAffineLift {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc x 1

/-- **Klein (`S2-07` Vol. 4 §§1–16; Vol. 6 §§1–10; `R3.2`)**:
exact expansion of the Cayley–Klein chord on affine lifts `(x, 1)` and `(y, 1)` showing the
leading `κ · ‖x - y‖²` Euclidean term plus `O(κ²)` Lagrange correction. -/
theorem cayleyKleinChord_affineLift_expansion (n : ℕ) (κ : ℝ) (x y : Fin n → ℝ) :
    cayleyKleinChord (cayleyKleinProjBilin n κ)
        (cayleyKleinAffineLift x) (cayleyKleinAffineLift y) =
      κ * (∑ i : Fin n, (x i - y i) ^ 2) +
        κ ^ 2 * ((∑ i : Fin n, x i ^ 2) * (∑ i : Fin n, y i ^ 2) -
          (∑ i : Fin n, x i * y i) ^ 2) := by
  have hbilin : ∀ u v : Fin n → ℝ,
      cayleyKleinProjBilin n κ (cayleyKleinAffineLift u) (cayleyKleinAffineLift v) =
        κ * (∑ i : Fin n, u i * v i) + 1 := fun u v => by
    rw [cayleyKleinProjBilin_apply]
    simp only [cayleyKleinAffineLift, Fin.snoc_castSucc, Fin.snoc_last, mul_one]
    rw [Finset.mul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => by ring) rfl
  dsimp [cayleyKleinChord]
  change cayleyKleinProjBilin n κ (cayleyKleinAffineLift x) (cayleyKleinAffineLift x) *
      cayleyKleinProjBilin n κ (cayleyKleinAffineLift y) (cayleyKleinAffineLift y) -
      (cayleyKleinProjBilin n κ (cayleyKleinAffineLift x) (cayleyKleinAffineLift y)) ^ 2 = _
  have hsq : ∑ i : Fin n, (x i - y i) ^ 2 =
      (∑ i : Fin n, x i ^ 2) - 2 * (∑ i : Fin n, x i * y i) + (∑ i : Fin n, y i ^ 2) := by
    have hpt : ∀ i : Fin n, (x i - y i) ^ 2 = x i ^ 2 - 2 * (x i * y i) + y i ^ 2 := fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.mul_sum]
  have hsqx : (∑ i : Fin n, x i * x i) = ∑ i : Fin n, x i ^ 2 :=
    Finset.sum_congr rfl fun i _ => (sq (x i)).symm
  have hsqy : (∑ i : Fin n, y i * y i) = ∑ i : Fin n, y i ^ 2 :=
    Finset.sum_congr rfl fun i _ => (sq (y i)).symm
  rw [hbilin x x, hbilin y y, hbilin x y, hsqx, hsqy, hsq]
  ring

/-- **Klein (`S2-07` Vol. 4 §§1–16; Vol. 6 §§1–10; `R3.2`)**:
parabolic Euclidean limit: dividing the nonzero-curvature Cayley–Klein chord by `κ` isolates
`‖x - y‖² + κ · Δ(x, y)` (converging to `‖x - y‖²` at `κ = 0`), while `κ = 0` collapses the
unscaled chord to `0`. -/
theorem cayleyKleinChord_parabolic_euclidean_limit (n : ℕ) (x y : Fin n → ℝ) :
    (∀ κ : ℝ, κ ≠ 0 →
      κ⁻¹ * cayleyKleinChord (cayleyKleinProjBilin n κ)
          (cayleyKleinAffineLift x) (cayleyKleinAffineLift y) =
        (∑ i : Fin n, (x i - y i) ^ 2) +
          κ * ((∑ i : Fin n, x i ^ 2) * (∑ i : Fin n, y i ^ 2) -
            (∑ i : Fin n, x i * y i) ^ 2)) ∧
      cayleyKleinChord (cayleyKleinProjBilin n 0)
        (cayleyKleinAffineLift x) (cayleyKleinAffineLift y) = 0 := by
  refine ⟨?_, ?_⟩
  · intro κ hκ
    rw [cayleyKleinChord_affineLift_expansion]
    field_simp [hκ]
  · rw [cayleyKleinChord_affineLift_expansion]
    ring

/-- **Klein (`S2-07` Vol. 4 §§1–16; Vol. 6 §§1–10; `R3.2`)**:
hyperbolic Klein–Beltrami cross-ratio discriminant bound and null-cone infinite-distance
boundary: when `κ < 0`, for any two interior timelike points `Q(x) > 0, Q(y) > 0`,
`0 ≤ (B x y)² - Q(x) Q(y)` (giving positive real cross-ratio logarithm), while any null-cone
point `Q(p) = 0` yields `cayleyKleinChord B p y = -(B p y)² ≤ 0`. -/
theorem cayleyKlein_hyperbolic_crossRatio_distance (n : ℕ) {κ : ℝ} (hκ : κ < 0)
    (x y p : Fin (n + 1) → ℝ)
    (hx : 0 < cayleyKleinProjQuadForm n κ x) (hy : 0 < cayleyKleinProjQuadForm n κ y) :
    (0 < cayleyKleinProjQuadForm n κ x * cayleyKleinProjQuadForm n κ y ∧
      cayleyKleinProjQuadForm n κ x * cayleyKleinProjQuadForm n κ y ≤
        (cayleyKleinProjBilin n κ x y) ^ 2) ∧
    (cayleyKleinProjQuadForm n κ p = 0 →
      cayleyKleinChord (cayleyKleinProjBilin n κ) p y =
        -(cayleyKleinProjBilin n κ p y) ^ 2 ∧
        cayleyKleinChord (cayleyKleinProjBilin n κ) p y ≤ 0) := by
  let Q := cayleyKleinProjQuadForm n κ
  let B := cayleyKleinProjBilin n κ
  have hBself : ∀ a : Fin (n + 1) → ℝ, B a a = Q a := fun a => by
    dsimp [B, Q]
    rw [cayleyKleinProjBilin_apply, cayleyKleinProjQuadForm_apply]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => by ring) (by ring)
  have hBxx : B x x = Q x := hBself x
  have hByy : B y y = Q y := hBself y
  have hBpp : B p p = Q p := hBself p
  let u : Fin (n + 1) → ℝ := Q x • y - B x y • x
  have hQ_pol : ∀ a b : Fin (n + 1) → ℝ, Q (a + b) = Q a + Q b + 2 * B a b := fun a b => by
    dsimp [Q, B]
    simp only [cayleyKleinProjQuadForm_apply, cayleyKleinProjBilin_apply, Pi.add_apply]
    have hsum : ∑ i : Fin n, κ * (a i.castSucc + b i.castSucc) ^ 2 =
        (∑ i : Fin n, κ * a i.castSucc ^ 2) + (∑ i : Fin n, κ * b i.castSucc ^ 2) +
          2 * ∑ i : Fin n, κ * a i.castSucc * b i.castSucc := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hsum]
    ring
  have hQ_sub : ∀ a b : Fin (n + 1) → ℝ, Q (a - b) = Q a + Q b - 2 * B a b := by
    intro a b
    rw [sub_eq_add_neg, hQ_pol, QuadraticMap.map_neg, map_neg]
    ring
  have hB_xu : B x u = 0 := by
    dsimp [u]
    rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hBxx]
    ring
  have hQu_eq : Q u = Q x * (Q x * Q y - (B x y) ^ 2) := by
    dsimp [u]
    have hByx : B y x = B x y := cayleyKleinProjBilin_symm n κ y x
    simp only [hQ_sub, QuadraticMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply,
      smul_eq_mul, hByx]
    ring
  have hQu_nonpos : Q u ≤ 0 := by
    by_contra hQu_pos
    push Not at hQu_pos
    let W : Submodule ℝ (Fin (n + 1) → ℝ) := Submodule.span ℝ {x, u}
    have hli : LinearIndependent ℝ ![x, u] := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have h0 : B x (c 0 • x + c 1 • u) = 0 := by
        have hsum0 : c 0 • x + c 1 • u = 0 := by
          simpa [Fin.sum_univ_two] using hc
        rw [hsum0, map_zero]
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hBxx, hB_xu, mul_zero,
        add_zero] at h0
      have hc0 : c 0 = 0 := (mul_eq_zero.mp h0).resolve_right hx.ne'
      have h1 : c 1 • u = 0 := by
        have hsum0 : c 0 • x + c 1 • u = 0 := by simpa [Fin.sum_univ_two] using hc
        simpa [hc0] using hsum0
      have hu_ne : u ≠ 0 := by
        intro hu0
        rw [hu0, map_zero] at hQu_pos
        linarith
      have hc1 : c 1 = 0 := (smul_eq_zero.mp h1).resolve_right hu_ne
      intro i
      fin_cases i <;> assumption
    have hW_pos : (Q.restrict W).PosDef := by
      intro ⟨w, hw⟩ hw_ne
      change 0 < Q w
      have hw' : w ∈ Submodule.span ℝ {x, u} := hw
      rw [Submodule.mem_span_pair] at hw'
      obtain ⟨α, β, rfl⟩ := hw'
      have hne_pair : α ≠ 0 ∨ β ≠ 0 := by
        by_contra h0
        push Not at h0
        apply hw_ne
        apply Subtype.ext
        simp [h0.1, h0.2]
      simp only [hQ_pol, QuadraticMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply,
        smul_eq_mul, hB_xu, mul_zero, add_zero]
      rcases hne_pair with hα | hβ
      · exact add_pos_of_pos_of_nonneg (mul_pos (mul_self_pos.mpr hα) hx)
          (mul_nonneg (mul_self_nonneg β) hQu_pos.le)
      · exact add_pos_of_nonneg_of_pos (mul_nonneg (mul_self_nonneg α) hx.le)
          (mul_pos (mul_self_pos.mpr hβ) hQu_pos)
    have hW_dim : Module.finrank ℝ W = 2 := by
      have hrange : Set.range ![x, u] = {x, u} := by
        ext z; simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨i, rfl⟩; fin_cases i <;> simp
        · rintro (rfl | rfl)
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
      change Module.finrank ℝ (Submodule.span ℝ {x, u}) = 2
      rw [← hrange, finrank_span_eq_card hli, Fintype.card_fin]
    have hle := le_sigPos_of_posDef Q hW_pos
    have hsig1 := (cayleyKleinProjQuadForm_signature_trichotomy n κ).2.1 hκ |>.1
    change sigPos Q = 1 at hsig1
    rw [hW_dim] at hle
    change 2 ≤ sigPos Q at hle
    omega
  have hdisc : Q x * Q y ≤ (B x y) ^ 2 := by
    nlinarith [hQu_eq, hQu_nonpos, hx]
  refine ⟨⟨mul_pos hx hy, hdisc⟩, ?_⟩
  intro hp
  have hchord : cayleyKleinChord B p y = -(B p y) ^ 2 := by
    dsimp [cayleyKleinChord]
    change B p p * B y y - B p y ^ 2 = -(B p y) ^ 2
    rw [hBpp, hp, zero_mul, zero_sub]
  refine ⟨hchord, ?_⟩
  rw [hchord]
  exact neg_nonpos.mpr (sq_nonneg _)

end CayleyKlein1871

/-! ## Section 4: Pfaff (1814–15) & Darboux (1882) — Algebraic Pfaffian Class & Characteristic (`S2-08`) -/

section PfaffDarboux1882

/-- **Pfaff & Darboux (`S2-08` Pt I §§I–VII, Pt II §§IX–XI; `R3.4`)**:
exterior power `(dω)^r` (`2r`-form) on any faithfulness-free `LieActionLane R A` over an
associative `R`-algebra `A`. -/
def actionTwoFormPow {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (η : ActionOperatorForm K 2) : ∀ r : ℕ, ActionOperatorForm K (2 * r)
  | 0 => reindexForm (by omega : 0 = 2 * 0) (AlternatingMap.constLinearEquivOfIsEmpty (1 : A))
  | r + 1 =>
    reindexForm (by omega : 2 + 2 * r = 2 * (r + 1)) (actionWedge K η (actionTwoFormPow K η r))

/-- **Pfaff & Darboux (`S2-08` Pt I–II; `R3.4`)**:
exterior power `(dω)^r` on `DerivationOperatorForm K`. -/
abbrev ceTwoFormPow {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) (η : DerivationOperatorForm K 2) (r : ℕ) :
    DerivationOperatorForm K (2 * r) :=
  actionTwoFormPow K.toLieActionLane η r

/-- **Pfaff & Darboux (`S2-08` Pt II §§IX–XI; `R3.4`)**:
Darboux odd invariant form `ω ∧ (dω)^r` of degree `1 + 2 * r` on `LieActionLane R A`. -/
def pfaffWedgePow {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (ω : ActionOperatorForm K 1) (r : ℕ) :
    ActionOperatorForm K (1 + 2 * r) :=
  actionWedge K ω (actionTwoFormPow K (actionExteriorDerivative K 1 ω) r)

/-- **Pfaff & Darboux (`S2-08` Pt II §§IX–XI; `R3.4`)**:
Darboux odd invariant form `ω ∧ (dω)^r` on `DerivationOperatorForm K`. -/
abbrev cePfaffWedgePow {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) (ω : DerivationOperatorForm K 1) (r : ℕ) :
    DerivationOperatorForm K (1 + 2 * r) :=
  pfaffWedgePow K.toLieActionLane ω r

/-- **Pfaff & Darboux (`S2-08` Pt II §§IX–XI; `R3.4`)**:
if `dη = 0` (e.g. `η = dω`), then `d(η^r) = 0` for every `r : ℕ`. -/
theorem actionExteriorDerivative_twoFormPow_eq_zero {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] (K : LieActionLane R A) (hK : IsLeibnizAction K)
    {η : ActionOperatorForm K 2} (hη : actionExteriorDerivative K 2 η = 0) (r : ℕ) :
    actionExteriorDerivative K (2 * r) (actionTwoFormPow K η r) = 0 := by
  induction r with
  | zero =>
    have h0 : actionTwoFormPow K η 0 =
        reindexForm (by omega : 0 = 2 * 0) (AlternatingMap.constLinearEquivOfIsEmpty (1 : A)) :=
      rfl
    rw [h0, actionExteriorDerivative_reindexForm]
    have h0d : actionExteriorDerivative K 0 (AlternatingMap.constLinearEquivOfIsEmpty (1 : A)) = 0 := by
      ext v
      rw [actionExteriorDerivative_zero_apply]
      change K.operatorAction (v 0) (1 : A) = 0
      have h1 := hK (v 0) (1 : A) (1 : A)
      simp only [mul_one, one_mul] at h1
      exact add_eq_left.mp h1.symm
    rw [h0d, reindexForm_zero]
  | succ r ih =>
    dsimp [actionTwoFormPow]
    rw [actionExteriorDerivative_reindexForm, actionExteriorDerivative_actionWedge K hK,
      hη, ih, actionWedge_zero_val_left, actionWedge_zero_val_right, reindexForm_zero]
    simp only [reindexForm_zero, smul_zero, add_zero]

/-- **Pfaff & Darboux (`S2-08` Pt II §§IX–XI; `R3.4`)**:
exterior derivative identity `d(ω ∧ (dω)^r) = (dω)^(r+1)` in `BUCKET 1` over any associative
`R`-algebra `A`. -/
theorem actionExteriorDerivative_pfaffWedgePow {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (hK : IsLeibnizAction K) (ω : ActionOperatorForm K 1) (r : ℕ) :
    actionExteriorDerivative K (1 + 2 * r) (pfaffWedgePow K ω r) =
      reindexForm (by omega : 2 * (r + 1) = (1 + 2 * r) + 1)
        (actionTwoFormPow K (actionExteriorDerivative K 1 ω) (r + 1)) := by
  dsimp [pfaffWedgePow]
  rw [actionExteriorDerivative_actionWedge K hK]
  have hd2 : actionExteriorDerivative K 2 (actionExteriorDerivative K 1 ω) = 0 :=
    actionExteriorDerivative_succ_comp K 1 ω
  rw [actionExteriorDerivative_twoFormPow_eq_zero K hK hd2 r, actionWedge_zero_val_right,
    reindexForm_zero, smul_zero, add_zero]
  dsimp [actionTwoFormPow]
  rw [reindexForm_trans]

/-- **Pfaff & Darboux (`S2-08` Pt II §§IX–XI; `R3.4`)**:
vanishing of `ω ∧ (dω)^r` implies vanishing of `(dω)^(r+1)`. -/
theorem pfaffWedgePow_eq_zero_imp_dPow_succ_eq_zero {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] (K : LieActionLane R A) (hK : IsLeibnizAction K) (ω : ActionOperatorForm K 1)
    {r : ℕ} (h : pfaffWedgePow K ω r = 0) :
    actionTwoFormPow K (actionExteriorDerivative K 1 ω) (r + 1) = 0 := by
  have hd := congrArg (actionExteriorDerivative K (1 + 2 * r)) h
  rw [map_zero, actionExteriorDerivative_pfaffWedgePow K hK ω r] at hd
  have hd' := congrArg (reindexForm (by omega : (1 + 2 * r) + 1 = 2 * (r + 1))) hd
  rwa [reindexForm_trans, reindexForm_rfl, reindexForm_zero] at hd'

/-- **Pfaff & Darboux (`S2-08` Pt II §§IX–XI; `R3.4`)**:
monotone vanishing of the Pfaffian chain: if `ω ∧ (dω)^r = 0` and `r ≤ m`, then
`ω ∧ (dω)^m = 0` and `(dω)^(m+1) = 0`. -/
theorem pfaffWedgePow_monotone_vanishing {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (hK : IsLeibnizAction K) (ω : ActionOperatorForm K 1)
    {r m : ℕ} (hrm : r ≤ m) (h : pfaffWedgePow K ω r = 0) :
    pfaffWedgePow K ω m = 0 ∧
      actionTwoFormPow K (actionExteriorDerivative K 1 ω) (m + 1) = 0 := by
  have hchain : ∀ k : ℕ,
      pfaffWedgePow K ω (r + k) = 0 ∧
        actionTwoFormPow K (actionExteriorDerivative K 1 ω) (r + k + 1) = 0 := by
    intro k
    induction k with
    | zero =>
      rw [add_zero]
      exact ⟨h, pfaffWedgePow_eq_zero_imp_dPow_succ_eq_zero K hK ω h⟩
    | succ k ih =>
      have hsucc : pfaffWedgePow K ω (r + (k + 1)) = 0 := by
        dsimp [pfaffWedgePow, actionTwoFormPow]
        have hpow_zero : actionTwoFormPow K (actionExteriorDerivative K 1 ω) (r + k + 1) = 0 := ih.2
        change actionWedge K ω (reindexForm _ (actionWedge K (actionExteriorDerivative K 1 ω)
          (actionTwoFormPow K (actionExteriorDerivative K 1 ω) (r + k)))) = 0
        have hre : reindexForm (by omega : 2 + 2 * (r + k) = 2 * (r + (k + 1)))
            (actionWedge K (actionExteriorDerivative K 1 ω)
              (actionTwoFormPow K (actionExteriorDerivative K 1 ω) (r + k))) = 0 := by
          simpa [actionTwoFormPow] using hpow_zero
        rw [hre, actionWedge_zero_val_right]
      exact ⟨hsucc, pfaffWedgePow_eq_zero_imp_dPow_succ_eq_zero K hK ω hsucc⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hrm
  exact hchain k

/-- **Pfaff & Darboux (`S2-08` Pt II §§IX–XI; `R3.4`)**:
algebraic even Pfaffian class `2r` (`r = 0` when `ω = 0`; `r ≥ 1` when `(dω)^r ≠ 0`,
`ω ∧ (dω)^r = 0`, and `ω ∧ (dω)^s ≠ 0` for all `s < r`). -/
def HasPfaffClassEven {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (ω : ActionOperatorForm K 1) (r : ℕ) : Prop :=
  (1 ≤ r → actionTwoFormPow K (actionExteriorDerivative K 1 ω) r ≠ 0) ∧
    pfaffWedgePow K ω r = 0 ∧
    (∀ s < r, pfaffWedgePow K ω s ≠ 0)

/-- **Pfaff & Darboux (`S2-08` Pt II §§IX–XI; `R3.4`)**:
algebraic odd Pfaffian class `2r + 1`: `ω ∧ (dω)^r ≠ 0` and `(dω)^(r+1) = 0`. -/
def HasPfaffClassOdd {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (ω : ActionOperatorForm K 1) (r : ℕ) : Prop :=
  pfaffWedgePow K ω r ≠ 0 ∧
    actionTwoFormPow K (actionExteriorDerivative K 1 ω) (r + 1) = 0

/-- **Pfaff & Darboux (`S2-08` Pt II §§IX–XI; `R3.4`)**:
even and odd algebraic Pfaffian classes are strictly disjoint (`BUCKET 1`). -/
theorem pfaff_even_odd_class_disjoint {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (hK : IsLeibnizAction K) (ω : ActionOperatorForm K 1)
    (r₁ r₂ : ℕ) (he : HasPfaffClassEven K ω r₁) (ho : HasPfaffClassOdd K ω r₂) : False := by
  rcases he with ⟨hr1_ne, hr1_zero, hr1_min⟩
  rcases ho with ⟨hr2_ne, hr2_succ⟩
  by_cases hle : r₁ ≤ r₂
  · exact hr2_ne (pfaffWedgePow_monotone_vanishing K hK ω hle hr1_zero).1
  · have hlt : r₂ < r₁ := Nat.lt_of_not_ge hle
    have hr1_ge : 1 ≤ r₁ := by omega
    have hr2_le : r₂ + 1 ≤ r₁ := hlt
    have hpow_zero : actionTwoFormPow K (actionExteriorDerivative K 1 ω) r₁ = 0 := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hr2_le
      have hrec : ∀ t : ℕ,
          actionTwoFormPow K (actionExteriorDerivative K 1 ω) (r₂ + 1 + t) = 0 := by
        intro t
        induction t with
        | zero => simpa using hr2_succ
        | succ t iht =>
          dsimp [actionTwoFormPow]
          rw [iht, actionWedge_zero_val_right, reindexForm_zero]
      subst hk
      exact hrec k
    exact hr1_ne hr1_ge hpow_zero

/-- **Pfaff & Darboux (`S2-08` Pt I §II; `R3.4`)**:
kernel `ker ω = {x | ω ![x] = 0}` of a 1-form on a faithfulness-free `LieActionLane`. -/
def pfaffKernel {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (K : LieActionLane R A) (ω : ActionOperatorForm K 1) : Submodule R K.L where
  carrier := {x | ω ![x] = 0}
  zero_mem' := by
    have h0 : (![(0 : K.L)] : Fin 1 → K.L) = 0 := by ext i; fin_cases i; simp
    rw [Set.mem_ofPred_eq, h0]
    exact ω.map_zero
  add_mem' {x y} hx hy := by
    change ω ![x + y] = 0
    have hadd : (![x + y] : Fin 1 → K.L) = Function.update ![x] 0 (x + y) := by
      ext i; fin_cases i; simp
    have hx' : ω ![x] = 0 := hx
    have hy' : ω ![y] = 0 := hy
    have hsum := ω.map_update_add ![x] 0 x y
    have hu1 : Function.update ![x] 0 x = ![x] := by ext i; fin_cases i; simp
    have hu2 : Function.update ![x] 0 y = ![y] := by ext i; fin_cases i; simp
    rw [← hadd, hu1, hu2] at hsum
    rw [hsum, hx', hy', add_zero]
  smul_mem' r {x} hx := by
    change ω ![r • x] = 0
    have hsm : (![r • x] : Fin 1 → K.L) = Function.update ![x] 0 (r • x) := by
      ext i; fin_cases i; simp
    have hu : Function.update ![x] 0 x = ![x] := by ext i; fin_cases i; simp
    have hmap := ω.map_update_smul ![x] 0 r x
    rw [← hsm, hu] at hmap
    rw [hmap, hx, smul_zero]

/-- **Pfaff & Darboux (`S2-08` Pt I §II; `R3.4`)**:
kernel `ker dω = {x | ∀ y, dω ![x, y] = 0}` of the exterior differential of `ω`. -/
def dPfaffKernel {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (K : LieActionLane R A) (ω : ActionOperatorForm K 1) : Submodule R K.L where
  carrier := {x | ∀ y : K.L, actionExteriorDerivative K 1 ω ![x, y] = 0}
  zero_mem' := fun y => by
    have h0 : (![(0 : K.L), y] : Fin 2 → K.L) = Function.update ![y, y] 0 0 := by
      ext i; fin_cases i <;> simp
    change actionExteriorDerivative K 1 ω ![0, y] = 0
    rw [h0]
    exact (actionExteriorDerivative K 1 ω).map_update_zero ![y, y] 0
  add_mem' {x₁ x₂} hx₁ hx₂ y := by
    have h12 : (![x₁ + x₂, y] : Fin 2 → K.L) = Function.update ![x₁, y] 0 (x₁ + x₂) := by
      ext i; fin_cases i <;> simp
    have hu1 : Function.update ![x₁, y] 0 x₁ = ![x₁, y] := by
      ext i; fin_cases i <;> simp
    have hu2 : Function.update ![x₁, y] 0 x₂ = ![x₂, y] := by
      ext i; fin_cases i <;> simp
    have hsum := (actionExteriorDerivative K 1 ω).map_update_add ![x₁, y] 0 x₁ x₂
    rw [← h12, hu1, hu2] at hsum
    change actionExteriorDerivative K 1 ω ![x₁ + x₂, y] = 0
    rw [hsum, hx₁ y, hx₂ y, add_zero]
  smul_mem' r {x} hx y := by
    have hsm : (![r • x, y] : Fin 2 → K.L) = Function.update ![x, y] 0 (r • x) := by
      ext i; fin_cases i <;> simp
    have hu : Function.update ![x, y] 0 x = ![x, y] := by
      ext i; fin_cases i <;> simp
    have hmap := (actionExteriorDerivative K 1 ω).map_update_smul ![x, y] 0 r x
    rw [← hsm, hu] at hmap
    change actionExteriorDerivative K 1 ω ![r • x, y] = 0
    rw [hmap, hx y, smul_zero]

/-- **Pfaff & Darboux (`S2-08` Pt I §II eq. (10); `R3.4`)**:
characteristic subspace `ker ω ∩ ker dω` on any faithfulness-free `LieActionLane`.
(Smooth local Frobenius/Darboux chart integration belongs to `O-EXT` (`BUCKET 3 analytic PDE boundary`).) -/
def pfaffCharacteristicSubspace {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (K : LieActionLane R A) (ω : ActionOperatorForm K 1) : Submodule R K.L :=
  pfaffKernel K ω ⊓ dPfaffKernel K ω

/-- **Pfaff & Darboux (`S2-08` Pt I §II; `R3.4`)**:
Cartan magic identity on `pfaffCharacteristicSubspace`: any `x ∈ ker ω ∩ ker dω` has zero
Lie derivative `lieDeriv K x ω = 0`. -/
theorem lieDeriv_eq_zero_of_mem_characteristic {R A : Type*} [CommRing R] [AddCommGroup A]
    [Module R A] (K : LieActionLane R A) (ω : ActionOperatorForm K 1)
    {x : K.L} (hx : x ∈ pfaffCharacteristicSubspace K ω) :
    lieDeriv K x ω = 0 := by
  have hx1 : ω ![x] = 0 := hx.1
  have hx2 : ∀ y : K.L, actionExteriorDerivative K 1 ω ![x, y] = 0 := hx.2
  ext v
  have hcur := actionExteriorDerivative_succ_curryLeft K 0 ω x
  have hlie := congrArg (fun f : ActionOperatorForm K 1 => f v) hcur
  have hv : (![v 0] : Fin 1 → K.L) = v := by ext i; fin_cases i; rfl
  have hxv : Matrix.vecCons x v = ![x, v 0] := by
    ext i; fin_cases i <;> simp [hv]
  have hd1 : (actionExteriorDerivative K 1 ω).curryLeft x v = 0 := by
    rw [AlternatingMap.curryLeft_apply_apply, hxv]
    exact hx2 (v 0)
  have hd0 : actionExteriorDerivative K 0 (ω.curryLeft x) v = 0 := by
    rw [actionExteriorDerivative_zero_apply]
    have hcurx : ω.curryLeft x Fin.elim0 = ω ![x] := by
      have hvec : Matrix.vecCons x Fin.elim0 = ![x] := by ext i; fin_cases i; rfl
      rw [AlternatingMap.curryLeft_apply_apply, hvec]
    rw [hcurx, hx1, map_zero]
  change (actionExteriorDerivative K 1 ω).curryLeft x v = 0 at hd1
  rw [AlternatingMap.sub_apply] at hlie
  rw [hd1, hd0, sub_zero] at hlie
  rw [AlternatingMap.zero_apply]
  exact hlie.symm

/-- **Pfaff & Darboux (`S2-08` Pt I §II; `R3.4`)**:
unconditional `BUCKET 1` Lie closure of the Darboux characteristic subspace
`pfaffCharacteristicSubspace K ω` (`[ker ω ∩ ker dω, ker ω ∩ ker dω] ⊆ ker ω ∩ ker dω`)
on any faithfulness-free `LieActionLane`. -/
def pfaffCharacteristicLieSubalgebra {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (K : LieActionLane R A) (ω : ActionOperatorForm K 1) : LieSubalgebra R K.L :=
  letI := K.lieRing
  letI := K.lieAlgebra
  { pfaffCharacteristicSubspace K ω with
    lie_mem' := fun {x y} hx hy => by
      have hx1 : ω ![x] = 0 := hx.1
      have hy1 : ω ![y] = 0 := hy.1
      have hx2 : ∀ z, actionExteriorDerivative K 1 ω ![x, z] = 0 := hx.2
      have hy2 : ∀ z, actionExteriorDerivative K 1 ω ![y, z] = 0 := hy.2
      have hxy_d : actionExteriorDerivative K 1 ω ![x, y] =
          K.operatorAction x (ω ![y]) - K.operatorAction y (ω ![x]) - ω ![⁅x, y⁆] := by
        have h0 := congrArg (fun f : ActionOperatorForm K 1 => f ![y])
          (actionExteriorDerivative_succ_curryLeft K 0 ω x)
        have hxy_vec : Matrix.vecCons x ![y] = ![x, y] := by ext i; fin_cases i <;> rfl
        rw [AlternatingMap.curryLeft_apply_apply, hxy_vec] at h0
        rw [h0, AlternatingMap.sub_apply, lieDeriv_apply, actionExteriorDerivative_zero_apply]
        have hcurx : ω.curryLeft x Fin.elim0 = ω ![x] := by
          have hvec : Matrix.vecCons x Fin.elim0 = ![x] := by ext i; fin_cases i; rfl
          rw [AlternatingMap.curryLeft_apply_apply, hvec]
        have hupd : Function.update ![y] (0 : Fin 1) ⁅x, ![y] 0⁆ = ![⁅x, y⁆] := by
          ext i; fin_cases i; simp
        rw [hcurx, Fin.sum_univ_one, hupd]
        change K.operatorAction x (ω ![y]) - ω ![⁅x, y⁆] - K.operatorAction y (ω ![x]) = _
        abel
      have hker_br : ω ![⁅x, y⁆] = 0 := by
        have h0 := hx2 y
        rw [hxy_d, hx1, hy1, map_zero, map_zero, sub_self, zero_sub, neg_eq_zero] at h0
        exact h0
      have hd_zero : ∀ z, actionExteriorDerivative K 1 ω ![⁅x, y⁆, z] = 0 := by
        intro z
        have hlie_x : lieDeriv K x ω = 0 := lieDeriv_eq_zero_of_mem_characteristic K ω hx
        have hlie_y : lieDeriv K y ω = 0 := lieDeriv_eq_zero_of_mem_characteristic K ω hy
        have hlie_br : lieDeriv K ⁅x, y⁆ ω = 0 := by
          rw [lieDeriv_lie]
          simp [hlie_x, hlie_y]
        have hcur_br := congrArg (fun f : ActionOperatorForm K 1 => f ![z])
          (actionExteriorDerivative_succ_curryLeft K 0 ω ⁅x, y⁆)
        have hbrz : Matrix.vecCons ⁅x, y⁆ ![z] = ![⁅x, y⁆, z] := by ext i; fin_cases i <;> rfl
        rw [AlternatingMap.curryLeft_apply_apply, hbrz, hlie_br, AlternatingMap.sub_apply,
          AlternatingMap.zero_apply, zero_sub] at hcur_br
        have h0_br : actionExteriorDerivative K 0 (ω.curryLeft ⁅x, y⁆) ![z] = 0 := by
          rw [actionExteriorDerivative_zero_apply]
          have hcur0 : ω.curryLeft ⁅x, y⁆ Fin.elim0 = ω ![⁅x, y⁆] := by
            have hvec : Matrix.vecCons ⁅x, y⁆ Fin.elim0 = ![⁅x, y⁆] := by ext i; fin_cases i; rfl
            rw [AlternatingMap.curryLeft_apply_apply, hvec]
          rw [hcur0, hker_br, map_zero]
        rw [h0_br, neg_zero] at hcur_br
        exact hcur_br
      exact ⟨hker_br, hd_zero⟩ }

private theorem actionWedge_one_four_apply {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (α : ActionOperatorForm K 1) (β : ActionOperatorForm K 4)
    (x a b c d : K.L) :
    actionWedge K α β ![x, a, b, c, d] =
      α ![x] * β ![a, b, c, d] -
        actionWedge K α (β.curryLeft x) ![a, b, c, d] := by
  have hvec : ![x, a, b, c, d] = Matrix.vecCons x ![a, b, c, d] := by
    ext i; fin_cases i <;> rfl
  rw [hvec, ← AlternatingMap.curryLeft_apply_apply, actionWedge_succ_succ_curryLeft]
  simp only [AlternatingMap.add_apply, reindexForm_apply, actionWedge_zero_left,
    AlternatingMap.smul_apply, LinearMap.compAlternatingMap_apply, LinearMap.mul_apply']
  have hx0 : Matrix.vecCons x Fin.elim0 = ![x] := by ext i; fin_cases i; rfl
  have hcast : (![a, b, c, d] ∘ ⇑(finCongr (by omega : 0 + 4 = 4))) = ![a, b, c, d] := by
    ext i; fin_cases i <;> rfl
  have hcast2 : (![a, b, c, d] ∘ ⇑(finCongr (by omega : 1 + 3 = 4))) = ![a, b, c, d] := by
    ext i; fin_cases i <;> rfl
  rw [AlternatingMap.curryLeft_apply_apply, hx0, hcast, hcast2, pow_one, neg_one_smul,
    ← sub_eq_add_neg]

private theorem actionWedge_one_two_apply {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (α : ActionOperatorForm K 1) (β : ActionOperatorForm K 2)
    (x y z : K.L) :
    actionWedge K α β ![x, y, z] =
      α ![x] * β ![y, z] - α ![y] * β ![x, z] + α ![z] * β ![x, y] := by
  have hxyz : ![x, y, z] = Matrix.vecCons x ![y, z] := by ext i; fin_cases i <;> rfl
  rw [hxyz, ← AlternatingMap.curryLeft_apply_apply, actionWedge_succ_succ_curryLeft]
  simp only [AlternatingMap.add_apply, reindexForm_apply, actionWedge_zero_left,
    AlternatingMap.smul_apply, LinearMap.compAlternatingMap_apply, LinearMap.mul_apply']
  have hx0 : Matrix.vecCons x Fin.elim0 = ![x] := by ext i; fin_cases i; rfl
  have hcast1 : (![y, z] ∘ ⇑(finCongr (by omega : 0 + 2 = 2))) = ![y, z] := by
    ext i; fin_cases i <;> rfl
  have hcast2 : (![y, z] ∘ ⇑(finCongr (by omega : 1 + 1 = 2))) = ![y, z] := by
    ext i; fin_cases i <;> rfl
  rw [AlternatingMap.curryLeft_apply_apply, hx0, hcast1, hcast2, pow_one, neg_one_smul]
  have h1 : actionWedge K α (β.curryLeft x) ![y, z] =
      α ![y] * β ![x, z] - α ![z] * β ![x, y] := by
    rw [actionWedge_one_one_apply]
    have hxy : Matrix.vecCons x ![y] = ![x, y] := by ext i; fin_cases i <;> rfl
    have hxz : Matrix.vecCons x ![z] = ![x, z] := by ext i; fin_cases i <;> rfl
    rw [AlternatingMap.curryLeft_apply_apply, AlternatingMap.curryLeft_apply_apply, hxz, hxy]
  rw [h1]
  abel

private theorem contact2_d_sq_eval :
    let K := (smoothJetDerivationLane 2).toLieActionLane
    let ω : ActionOperatorForm K 1 := contactCEOneForm 2
    let dω : ActionOperatorForm K 2 := actionExteriorDerivative K 1 ω
    let e0 : K.L := (![1, 0], (0, ![0, 0]))
    let e1 : K.L := (![0, 1], (0, ![0, 0]))
    let e3 : K.L := (![0, 0], (0, ![1, 0]))
    let e4 : K.L := (![0, 0], (0, ![0, 1]))
    ((actionTwoFormPow K dω 2 ![e0, e3, e1, e4]).1 0) = 2 := by
  intro K ω dω e0 e1 e3 e4
  have hd_val : ∀ u v : K.L, ∀ w,
      (dω ![u, v]).1 w = (u.1 0 * v.2.2 0 - v.1 0 * u.2.2 0) +
        (u.1 1 * v.2.2 1 - v.1 1 * u.2.2 1) := fun u v w => by
    have h := contactCEOneForm_d_apply 2 w u v
    change ((ceExteriorDerivative (smoothJetDerivationLane 2) 1 (contactCEOneForm 2)) ![u, v]).1 w = _
    rw [h, Fin.sum_univ_two]
  have hpow1_eq : actionTwoFormPow K dω 1 = dω := by
    apply AlternatingMap.ext
    intro v
    change (reindexForm (by omega : 2 + 2 * 0 = 2 * 1)
      (actionWedge K dω (reindexForm (by omega : 0 = 2 * 0)
        (AlternatingMap.constLinearEquivOfIsEmpty (1 : SmoothJetFun 2))))) v = dω v
    rw [reindexForm_apply, actionWedge_reindexForm_right, reindexForm_apply, actionWedge_zero_right]
    simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.constLinearEquivOfIsEmpty_apply,
      AlternatingMap.constOfIsEmpty_apply, LinearMap.flip_apply, LinearMap.mul_apply',
      Function.const_apply, mul_one]
    have hv : ((v ∘ finCongr (by omega : 2 + 0 = 2)) ∘ finCongr (by omega : 2 + 0 = 2)) = v := by
      ext i; fin_cases i <;> rfl
    rw [hv]
  change ((reindexForm (by omega : 2 + 2 * 1 = 2 * 2)
    (actionWedge K dω (actionTwoFormPow K dω 1))) ![e0, e3, e1, e4]).1 0 = 2
  rw [hpow1_eq, reindexForm_apply]
  have harg : (![e0, e3, e1, e4] ∘ finCongr (by omega : 2 + 2 = 4)) =
      Matrix.vecCons e0 ![e3, e1, e4] := by
    ext i; fin_cases i <;> rfl
  rw [harg, ← AlternatingMap.curryLeft_apply_apply, actionWedge_succ_succ_curryLeft]
  have hcomm : actionWedge K dω (dω.curryLeft e0) =
      reindexForm (by omega : 1 + 2 = 2 + 1) (actionWedge K (dω.curryLeft e0) dω) := by
    have hc := ceWedge_comm_of_commRing (smoothJetDerivationLane 2) dω (dω.curryLeft e0)
    change actionWedge K dω (dω.curryLeft e0) = ((-1 : ℝ) ^ (2 * 1)) •
      reindexForm (Nat.add_comm 1 2) (actionWedge K (dω.curryLeft e0) dω) at hc
    have h21 : ((-1 : ℝ) ^ (2 * 1)) = 1 := by norm_num
    rw [hc, h21, one_smul]
  have h12 : actionWedge K (dω.curryLeft e0) dω ![e3, e1, e4] =
      (dω.curryLeft e0) ![e3] * dω ![e1, e4] -
        (dω.curryLeft e0) ![e1] * dω ![e3, e4] +
        (dω.curryLeft e0) ![e4] * dω ![e3, e1] :=
    actionWedge_one_two_apply K (dω.curryLeft e0) dω e3 e1 e4
  have hce0 : ∀ y : K.L, ((dω.curryLeft e0 ![y]).1 0) = y.2.2 0 := fun y => by
    have hcons : Matrix.vecCons e0 ![y] = ![e0, y] := by ext i; fin_cases i <;> rfl
    rw [AlternatingMap.curryLeft_apply_apply, hcons, hd_val]
    simp [e0]
  have hterm : ((actionWedge K (dω.curryLeft e0) dω ![e3, e1, e4]).1 0) = 1 := by
    rw [h12]
    simp only [Subalgebra.coe_add, Subalgebra.coe_sub, Subalgebra.coe_mul, Pi.add_apply,
      Pi.sub_apply, Pi.mul_apply, hce0]
    rw [hd_val e1 e4 0, hd_val e3 e4 0, hd_val e3 e1 0]
    dsimp only [e1, e3, e4]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hpow2 : ((-1 : ℝ) ^ (1 + 1)) = 1 := by norm_num
  have ha1 : (![e3, e1, e4] ∘ finCongr (by omega : 1 + 2 = 2 + 1)) = ![e3, e1, e4] := by
    ext i; fin_cases i <;> rfl
  rw [AlternatingMap.add_apply, AlternatingMap.smul_apply, hpow2, one_smul, hcomm,
    reindexForm_apply, ha1]
  change ((actionWedge K (dω.curryLeft e0) dω ![e3, e1, e4]).1 0) +
    ((actionWedge K (dω.curryLeft e0) dω ![e3, e1, e4]).1 0) = 2
  rw [hterm]
  norm_num

private theorem alternatingMap_fin6_eq_zero_of_finrank_five {A : Type*} [AddCommGroup A]
    [Module ℝ A] (f : AlternatingMap ℝ (ContactJetSpace 2 ℝ) A (Fin 6)) : f = 0 := by
  apply AlternatingMap.ext
  intro v
  have hfin5 : Module.finrank ℝ (ContactJetSpace 2 ℝ) = 5 := by
    simp [ContactJetSpace, Module.finrank_prod]
  have hdep : ¬ LinearIndependent ℝ v := by
    intro hli
    have hle := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, hfin5] at hle
    omega
  exact f.map_linearDependent v hdep

/-- **Pfaff & Darboux (`S2-08` Pt II §§IX–XI; `R3.4`)**:
standard contact 1-form `contactCEOneForm 2` on `smoothJetDerivationLane 2` (5 variables)
has algebraic odd Pfaffian class `5` (`HasPfaffClassOdd ... 2`, `ω ∧ (dω)² ≠ 0`, `(dω)³ = 0`)
and trivial characteristic subspace `⊥`. -/
theorem contactCEOneForm_odd_class_n2 :
    HasPfaffClassOdd (smoothJetDerivationLane 2).toLieActionLane (contactCEOneForm 2) 2 ∧
      pfaffCharacteristicSubspace (smoothJetDerivationLane 2).toLieActionLane
        (contactCEOneForm 2) = ⊥ := by
  let K := (smoothJetDerivationLane 2).toLieActionLane
  let ω : ActionOperatorForm K 1 := contactCEOneForm 2
  let dω : ActionOperatorForm K 2 := actionExteriorDerivative K 1 ω
  let e0 : K.L := (![1, 0], (0, ![0, 0]))
  let e1 : K.L := (![0, 1], (0, ![0, 0]))
  let e2 : K.L := (![0, 0], (1, ![0, 0]))
  let e3 : K.L := (![0, 0], (0, ![1, 0]))
  let e4 : K.L := (![0, 0], (0, ![0, 1]))
  have hω_at0 : ∀ u : K.L, (ω ![u]).1 0 = u.2.1 := fun u => by
    change InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm 2 0 u =
      u.2.1
    simp [InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm]
  have hd_val : ∀ u v : K.L, ∀ w,
      (dω ![u, v]).1 w = (u.1 0 * v.2.2 0 - v.1 0 * u.2.2 0) +
        (u.1 1 * v.2.2 1 - v.1 1 * u.2.2 1) := fun u v w => by
    have h := contactCEOneForm_d_apply 2 w u v
    change ((ceExteriorDerivative (smoothJetDerivationLane 2) 1 (contactCEOneForm 2)) ![u, v]).1 w = _
    rw [h, Fin.sum_univ_two]
  have hd_e2 : dω.curryLeft e2 = 0 := by
    apply AlternatingMap.ext
    intro v
    apply Subtype.ext
    funext w
    have hv : ![v 0] = v := by ext i; fin_cases i; rfl
    have hcons : Matrix.vecCons e2 v = ![e2, v 0] := by ext i; fin_cases i <;> simp [hv]
    rw [AlternatingMap.curryLeft_apply_apply, hcons, AlternatingMap.zero_apply]
    change (dω ![e2, v 0]).1 w = 0
    rw [hd_val]
    simp [e2]
  have hpow1_eq : actionTwoFormPow K dω 1 = dω := by
    apply AlternatingMap.ext
    intro v
    change (reindexForm (by omega : 2 + 2 * 0 = 2 * 1)
      (actionWedge K dω (reindexForm (by omega : 0 = 2 * 0)
        (AlternatingMap.constLinearEquivOfIsEmpty (1 : SmoothJetFun 2))))) v = dω v
    rw [reindexForm_apply, actionWedge_reindexForm_right, reindexForm_apply, actionWedge_zero_right]
    simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.constLinearEquivOfIsEmpty_apply,
      AlternatingMap.constOfIsEmpty_apply, LinearMap.flip_apply, LinearMap.mul_apply',
      Function.const_apply, mul_one]
    have hv : ((v ∘ finCongr (by omega : 2 + 0 = 2)) ∘ finCongr (by omega : 2 + 0 = 2)) = v := by
      ext i; fin_cases i <;> rfl
    rw [hv]
  have hpow2_cur_e2 : (actionTwoFormPow K dω 2).curryLeft e2 = 0 := by
    change (reindexForm (by omega : 2 + 2 * 1 = 2 * 2)
      (actionWedge K dω (actionTwoFormPow K dω 1))).curryLeft e2 = 0
    rw [hpow1_eq, reindexForm_curryLeft, actionWedge_succ_succ_curryLeft, hd_e2,
      actionWedge_zero_val_left, reindexForm_zero, zero_add]
    have h2 : (-1 : ℝ) ^ (1 + 1) = 1 := by norm_num
    rw [h2, one_smul, actionWedge_zero_val_right, reindexForm_zero]
  have hdω2_eval : ((actionTwoFormPow K dω 2 ![e0, e3, e1, e4]).1 0) = 2 :=
    contact2_d_sq_eval
  have h5_ne : pfaffWedgePow K ω 2 ≠ 0 := by
    intro h0
    have hev := congrArg (fun f : ActionOperatorForm K 5 => (f ![e2, e0, e3, e1, e4]).1 0) h0
    simp only [AlternatingMap.zero_apply, Subalgebra.coe_zero, Pi.zero_apply] at hev
    let dω2 : ActionOperatorForm K 4 :=
      reindexForm (by omega : 2 * 2 = 4) (actionTwoFormPow K dω 2)
    have hcur2 : dω2.curryLeft e2 = 0 := by
      dsimp only [dω2]
      rw [reindexForm_curryLeft, hpow2_cur_e2, reindexForm_zero]
    have hdω2_val : (dω2 ![e0, e3, e1, e4]).1 0 = 2 := by
      dsimp only [dω2]
      rw [reindexForm_apply]
      have harg4 : (![e0, e3, e1, e4] ∘ finCongr (by omega : 2 * 2 = 4)) = ![e0, e3, e1, e4] := by
        ext i; fin_cases i <;> rfl
      rw [harg4, hdω2_eval]
    have hp : pfaffWedgePow K ω 2 ![e2, e0, e3, e1, e4] =
        actionWedge K ω dω2 ![e2, e0, e3, e1, e4] := by
      dsimp only [pfaffWedgePow, dω2]
      rw [actionWedge_reindexForm_right, reindexForm_apply]
      congr 1
    have hval : (pfaffWedgePow K ω 2 ![e2, e0, e3, e1, e4]).1 0 = 2 := by
      rw [hp, actionWedge_one_four_apply, hcur2, actionWedge_zero_val_right,
        AlternatingMap.zero_apply, sub_zero, Subalgebra.coe_mul, Pi.mul_apply, hω_at0 e2,
        hdω2_val]
      dsimp only [e2]
      norm_num
    rw [hval] at hev
    norm_num at hev
  have h6_zero : actionTwoFormPow K dω 3 = 0 :=
    alternatingMap_fin6_eq_zero_of_finrank_five (actionTwoFormPow K dω 3)
  have hchar : pfaffCharacteristicSubspace K ω = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx1 : ω ![x] = 0 := hx.1
    have hx2 : ∀ y : K.L, dω ![x, y] = 0 := hx.2
    have hx_z : x.2.1 = 0 := by
      have h0 := congrArg (fun f : SmoothJetFun 2 => f.1 0) hx1
      change (ω ![x]).1 0 = 0 at h0
      rw [hω_at0] at h0
      exact h0
    have hx_x0 : x.1 0 = 0 := by
      have h0 := congrArg (fun f : SmoothJetFun 2 => f.1 0) (hx2 e3)
      change (dω ![x, e3]).1 0 = 0 at h0
      rw [hd_val] at h0
      dsimp only [e3] at h0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, mul_one, zero_mul,
        sub_zero, add_zero] at h0
      exact h0
    have hx_x1 : x.1 1 = 0 := by
      have h0 := congrArg (fun f : SmoothJetFun 2 => f.1 0) (hx2 e4)
      change (dω ![x, e4]).1 0 = 0 at h0
      rw [hd_val] at h0
      dsimp only [e4] at h0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, mul_one, zero_mul,
        sub_zero, zero_add] at h0
      exact h0
    have hx_p0 : x.2.2 0 = 0 := by
      have h0 := congrArg (fun f : SmoothJetFun 2 => f.1 0) (hx2 e0)
      change (dω ![x, e0]).1 0 = 0 at h0
      rw [hd_val] at h0
      dsimp only [e0] at h0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_mul, one_mul,
        sub_zero, zero_sub, add_zero, neg_eq_zero] at h0
      exact h0
    have hx_p1 : x.2.2 1 = 0 := by
      have h0 := congrArg (fun f : SmoothJetFun 2 => f.1 0) (hx2 e1)
      change (dω ![x, e1]).1 0 = 0 at h0
      rw [hd_val] at h0
      dsimp only [e1] at h0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_mul, one_mul,
        sub_zero, zero_sub, zero_add, neg_eq_zero] at h0
      exact h0
    rw [Submodule.mem_bot]
    apply Prod.ext
    · ext i; fin_cases i
      · exact hx_x0
      · exact hx_x1
    · apply Prod.ext
      · exact hx_z
      · ext i; fin_cases i
        · exact hx_p0
        · exact hx_p1
  exact ⟨⟨h5_ne, h6_zero⟩, hchar⟩

private theorem actionWedge_reindexForm_right {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) {p q q' : ℕ} (h : q = q') (α : ActionOperatorForm K p)
    (β : ActionOperatorForm K q) :
    actionWedge K α (reindexForm h β) =
      reindexForm (congrArg (p + ·) h) (actionWedge K α β) := by
  subst h; rfl

/-- **Pfaff & Darboux (`S2-08` Pt II §§IX–XI; `R3.4`)**:
degenerate 1-form `dz` on `smoothJetDerivationLane 1` has algebraic odd Pfaffian class `1`
(`HasPfaffClassOdd ... 0`) and nontrivial 2-dimensional characteristic subspace
`pfaffCharacteristicSubspace` (spanned by `∂_x, ∂_p`), paired with Cayley's bordered
Pfaffian cofactor vector `borderedCharacteristicVec` (`GrassmannPfaffianDarbouxAlgebra`).
(Smooth local Frobenius/Darboux PDE integration remains in `O-EXT` (`BUCKET 3 analytic PDE boundary`).) -/
theorem degenerateOneForm_nontrivial_characteristic
    (x₁ x₂ x₃ x₄ a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄ : ℝ) :
    let K := (smoothJetDerivationLane 1).toLieActionLane
    let dz : ActionOperatorForm K 1 :=
      AlternatingMap.ofSubsingleton ℝ (ContactJetSpace 1 ℝ) (SmoothJetFun 1) (0 : Fin 1)
        { toFun := fun dw => ⟨fun _ => dw.2.1, contDiff_const (n := (⊤ : ℕ∞))⟩
          map_add' := fun u v => by apply Subtype.ext; funext _; rfl
          map_smul' := fun c u => by apply Subtype.ext; funext _; rfl }
    HasPfaffClassOdd K dz 0 ∧
      pfaffCharacteristicSubspace K dz ≠ ⊥ ∧
      (pfaffian4 a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄ = 0 →
        (skewMatrix4 a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄).mulVec
          (borderedCharacteristicVec x₁ x₂ x₃ x₄ a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄) = 0 ∧
          dotProduct ![x₁, x₂, x₃, x₄]
            (borderedCharacteristicVec x₁ x₂ x₃ x₄ a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄) = 0) := by
  intro K dz
  have hddz : actionExteriorDerivative K 1 dz = 0 := by
    apply AlternatingMap.ext
    intro u
    apply Subtype.ext
    funext w
    have hu : u = ![u 0, u 1] := by ext i; fin_cases i <;> rfl
    rw [hu]
    have h01 : ![u 0, u 1] = Matrix.vecCons (u 0) ![u 1] := by ext i; fin_cases i <;> rfl
    rw [h01, ← AlternatingMap.curryLeft_apply_apply, actionExteriorDerivative_succ_curryLeft]
    simp only [AlternatingMap.sub_apply, lieDeriv_apply, actionExteriorDerivative_zero_apply]
    have hbr : ∀ a b : K.L, (⁅a, b⁆ : K.L) = 0 := fun _ _ => rfl
    have hzero : (∑ i : Fin 1, dz (Function.update ![u 1] i ⁅u 0, ![u 1] i⁆)) = 0 := by
      rw [Fin.sum_univ_one, hbr]
      have hu0 : Function.update ![u 1] (0 : Fin 1) (0 : K.L) = ![0] := by
        ext i; fin_cases i; simp
      rw [hu0]
      apply Subtype.ext; funext _
      rfl
    have hcur : dz.curryLeft (u 0) Fin.elim0 = dz ![u 0] := by
      have hvec : Matrix.vecCons (u 0) Fin.elim0 = ![u 0] := by ext i; fin_cases i; rfl
      rw [AlternatingMap.curryLeft_apply_apply, hvec]
    have hact : ∀ a b : K.L, K.operatorAction a (dz ![b]) = 0 := fun a b => by
      apply Subtype.ext; funext v
      let b' : ContactJetSpace 1 ℝ := b
      let a' : ContactJetSpace 1 ℝ := a
      let v' : ContactJetSpace 1 ℝ := v
      change fderiv ℝ (Function.const (ContactJetSpace 1 ℝ) b'.2.1) v' a' = 0
      rw [fderiv_const]
      rfl
    rw [hzero, sub_zero, hcur, hact (u 0) (u 1), hact (![u 1] 0) (u 0), sub_self]
    rfl
  have hpow0_ne : pfaffWedgePow K dz 0 ≠ 0 := by
    intro h0
    let e_z : K.L := (![0], (1, ![0]))
    have hev := congrArg (fun f : ActionOperatorForm K 1 => (f ![e_z]).1 0) h0
    have hval : (pfaffWedgePow K dz 0 ![e_z]).1 0 = 1 := by
      dsimp [pfaffWedgePow, actionTwoFormPow]
      rw [actionWedge_reindexForm_right, reindexForm_apply, actionWedge_zero_right]
      change ((dz ![e_z] * (1 : SmoothJetFun 1)) : SmoothJetFun 1).1 0 = 1
      rw [mul_one]
      rfl
    rw [hval] at hev
    norm_num at hev
  have hpow1_zero : actionTwoFormPow K (actionExteriorDerivative K 1 dz) 1 = 0 := by
    dsimp [actionTwoFormPow]
    rw [hddz, actionWedge_zero_val_left, reindexForm_zero]
  have hchar_ne : pfaffCharacteristicSubspace K dz ≠ ⊥ := by
    let e_x : K.L := (![1], (0, ![0]))
    have hmem : e_x ∈ pfaffCharacteristicSubspace K dz := by
      refine ⟨?_, ?_⟩
      · apply Subtype.ext; funext _; rfl
      · intro y
        rw [hddz, AlternatingMap.zero_apply]
    intro hbot
    rw [hbot, Submodule.mem_bot] at hmem
    have h1 := congrArg (fun p : ContactJetSpace 1 ℝ => p.1 0) hmem
    change (1 : ℝ) = 0 at h1
    norm_num at h1
  refine ⟨⟨hpow0_ne, hpow1_zero⟩, hchar_ne, fun hpf => ?_⟩
  have hc := cayley_bordered_pfaffian5_identity x₁ x₂ x₃ x₄ a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄
  exact ⟨hc.2.2 hpf, hc.1⟩

end PfaffDarboux1882

/-! ## Section 5: É. Cartan (1910, 1914) — `(2,3,5)` Pfaffian Flag & Split `g_{2(2)}` (`S2-09`) -/

section Cartan235AndSplitG2

/-- **Cartan (`S2-09` 1910 §§VI.–XI.; `R3.2`)**:
coframe 1-forms `ω₀, ..., ω₄` on `ℝ⁵` modeled as `ExteriorAlgebra.ι ℝ (Pi.basisFun ℝ (Fin 5) i)`. -/
def cartan235Coframe (i : Fin 5) : ExteriorAlgebra ℝ (Fin 5 → ℝ) :=
  ExteriorAlgebra.ι ℝ (Pi.basisFun ℝ (Fin 5) i)

/-- **Cartan (`S2-09` 1910 §§VI.–XI.; `R3.2`)**:
structure 2-forms `dω₀ = ω₂ ∧ ω₃`, `dω₁ = ω₂ ∧ ω₄`, `dω₂ = -ω₃ ∧ ω₄`, `dω₃ = dω₄ = 0` of
Cartan's flat `(2,3,5)` Pfaffian system. -/
def cartan235Diff : Fin 5 → ExteriorAlgebra ℝ (Fin 5 → ℝ)
  | 0 => cartan235Coframe 2 * cartan235Coframe 3
  | 1 => cartan235Coframe 2 * cartan235Coframe 4
  | 2 => -(cartan235Coframe 3 * cartan235Coframe 4)
  | 3 => 0
  | 4 => 0

/-- **Cartan (`S2-09` 1910 §§VI.–XI.; `R3.2`)**:
linear differential map `c ↦ ∑ j : Fin 3, c j • dω_j` on the initial rank-3 Pfaffian system
`I⁽⁰⁾ = span {ω₀, ω₁, ω₂}`. -/
def cartan235ExtD : (Fin 3 → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Fin 5 → ℝ) where
  toFun c := ∑ j : Fin 3, c j • cartan235Diff (Fin.castLE (by omega : 3 ≤ 5) j)
  map_add' c₁ c₂ := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r c := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_smul, Finset.smul_sum]

/-- **Cartan (`S2-09` 1910 §§VI.–XI.; `R3.2`)**:
first derived-system Frobenius test `θ ↦ ω₀ ∧ ω₁ ∧ ω₂ ∧ dθ`. -/
def cartan235DerivedTest1 : (Fin 3 → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Fin 5 → ℝ) where
  toFun c := cartan235Coframe 0 * cartan235Coframe 1 * cartan235Coframe 2 * cartan235ExtD c
  map_add' c₁ c₂ := by simp only [map_add, mul_add]
  map_smul' r c := by
    simp only [map_smul]
    exact mul_smul_comm r (cartan235Coframe 0 * cartan235Coframe 1 * cartan235Coframe 2)
      (cartan235ExtD c)

/-- **Cartan (`S2-09` 1910 §§VI.–XI.; `R3.2`)**:
second derived-system Frobenius test `θ ↦ ω₀ ∧ ω₁ ∧ dθ` on `I⁽¹⁾ = span {ω₀, ω₁}`. -/
def cartan235DerivedTest2 : (Fin 2 → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Fin 5 → ℝ) where
  toFun c := cartan235Coframe 0 * cartan235Coframe 1 *
    (c 0 • cartan235Diff 0 + c 1 • cartan235Diff 1)
  map_add' c₁ c₂ := by
    simp only [Pi.add_apply, add_smul]
    rw [show (c₁ 0 • cartan235Diff 0 + c₂ 0 • cartan235Diff 0) +
        (c₁ 1 • cartan235Diff 1 + c₂ 1 • cartan235Diff 1) =
        (c₁ 0 • cartan235Diff 0 + c₁ 1 • cartan235Diff 1) +
        (c₂ 0 • cartan235Diff 0 + c₂ 1 • cartan235Diff 1) by abel, mul_add]
  map_smul' r c := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [show (r * c 0) • cartan235Diff 0 + (r * c 1) • cartan235Diff 1 =
        r • (c 0 • cartan235Diff 0 + c 1 • cartan235Diff 1) by module, mul_smul_comm]

private theorem cartan235_coframe_sq (i : Fin 5) :
    cartan235Coframe i * cartan235Coframe i = 0 :=
  ExteriorAlgebra.ι_sq_zero _

private theorem cartan235_coframe_swap (i j : Fin 5) :
    cartan235Coframe j * cartan235Coframe i = -(cartan235Coframe i * cartan235Coframe j) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

private theorem cartan235_vol5_eq_volume :
    cartan235Coframe 0 * cartan235Coframe 1 * cartan235Coframe 2 *
        cartan235Coframe 3 * cartan235Coframe 4 =
      InfoGeometry.Projective.ExteriorRegressive.volume (Pi.basisFun ℝ (Fin 5)) := by
  let b := Pi.basisFun ℝ (Fin 5)
  have hι : cartan235Coframe 0 * cartan235Coframe 1 * cartan235Coframe 2 *
      cartan235Coframe 3 * cartan235Coframe 4 = ExteriorAlgebra.ιMulti ℝ 5 b := by
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    simp only [cartan235Coframe, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, mul_assoc]
    rfl
  rw [hι]
  change ExteriorAlgebra.ιMulti ℝ 5 b = b.ExteriorAlgebra Finset.univ
  rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_fin 5)]
  let g := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (Finset.card_fin 5))
  have hord : ∀ i : Fin 5, g i = i := fun i => by
    have hle : i ≤ g i := g.strictMono.id_le i
    have hsub : Finset.image g (Finset.Ici i) ≤ Finset.Ici (g i) := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨k, hk, rfl⟩
      exact Finset.mem_Ici.mpr (g.monotone (Finset.mem_Ici.mp hk))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ g.injective, Fin.card_Ici, Fin.card_Ici] at hcard
    exact Fin.ext (by omega)
  have hfun : (fun i : Fin 5 => b (g i)) = b := by funext i; rw [hord i]
  change ExteriorAlgebra.ιMulti ℝ 5 b = ExteriorAlgebra.ιMulti ℝ 5 (fun i => b (g i))
  rw [hfun]

/-- **Cartan (`S2-09` 1910 §§VI.–XI.; `R3.2`)**:
exact Pfaffian derived flag ranks `3 → 2 → 0` (dual distribution growth `(2, 3, 5)`) for
Cartan's 5-variable Pfaffian system in `ExteriorAlgebra ℝ (Fin 5 → ℝ)`. -/
theorem cartan235_pfaff_derived_flag_ranks :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (fun j : Fin 3 =>
        cartan235Coframe (Fin.castLE (by omega : 3 ≤ 5) j)))) = 3 ∧
      LinearMap.ker cartan235DerivedTest1 = Submodule.span ℝ {![(1 : ℝ), 0, 0], ![0, 1, 0]} ∧
      Module.finrank ℝ (LinearMap.ker cartan235DerivedTest1) = 2 ∧
      LinearMap.ker cartan235DerivedTest2 = ⊥ ∧
      Module.finrank ℝ (LinearMap.ker cartan235DerivedTest2) = 0 := by
  let b := Pi.basisFun ℝ (Fin 5)
  have hli3 : LinearIndependent ℝ (fun j : Fin 3 =>
      cartan235Coframe (Fin.castLE (by omega : 3 ≤ 5) j)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    let j5 : Fin 5 := Fin.castLE (by omega : 3 ≤ 5) j
    have hmap := congrArg (b.ExteriorAlgebra.coord ({j5} : Finset (Fin 5))) hc
    have hcoord_eq : ∀ k : Fin 3,
        b.ExteriorAlgebra.coord ({j5} : Finset (Fin 5))
          (cartan235Coframe (Fin.castLE (by omega : 3 ≤ 5) k)) = if k = j then 1 else 0 :=
      fun k => by
        let k5 : Fin 5 := Fin.castLE (by omega : 3 ≤ 5) k
        have hk : cartan235Coframe k5 = b.ExteriorAlgebra ({k5} : Finset (Fin 5)) := by
          rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_singleton k5)]
          let g := Set.powersetCard.ofFinEmbEquiv.symm
            (Set.powersetCard.ofCard (Finset.card_singleton k5))
          have hg0 : g 0 = k5 := by
            have hm := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
              (Set.powersetCard.ofCard (Finset.card_singleton k5)) (g 0)).1 ⟨0, rfl⟩
            exact Finset.mem_singleton.mp hm
          change ExteriorAlgebra.ι ℝ (b k5) = ExteriorAlgebra.ιMulti ℝ 1 (fun i => b (g i))
          rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one, hg0]
        rw [hk, b.ExteriorAlgebra.coord_apply, b.ExteriorAlgebra.repr_self, Finsupp.single_apply]
        have heq_iff : ({k5} : Finset (Fin 5)) = {j5} ↔ k = j := by
          rw [Finset.singleton_inj, Fin.ext_iff, Fin.ext_iff]
          rfl
        rw [if_congr heq_iff rfl rfl]
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hmap
    have hsum : (∑ k : Fin 3,
        c k * b.ExteriorAlgebra.coord {j5}
          (cartan235Coframe (Fin.castLE (by omega : 3 ≤ 5) k))) = c j := by
      rw [Finset.sum_eq_single j]
      · simp [hcoord_eq j]
      · intro k _ hkj; simp [hcoord_eq k, hkj]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [hsum] at hmap
    exact hmap
  have hfin0 : Module.finrank ℝ
      (Submodule.span ℝ (Set.range (fun j : Fin 3 =>
        cartan235Coframe (Fin.castLE (by omega : 3 ≤ 5) j)))) = 3 := by
    rw [finrank_span_eq_card hli3, Fintype.card_fin]
  have htest1_eq : ∀ c : Fin 3 → ℝ,
      cartan235DerivedTest1 c = (-c 2) • InfoGeometry.Projective.ExteriorRegressive.volume b :=
    fun c => by
      change cartan235Coframe 0 * cartan235Coframe 1 * cartan235Coframe 2 *
          (∑ j : Fin 3, c j • cartan235Diff (Fin.castLE (by omega : 3 ≤ 5) j)) = _
      rw [Fin.sum_univ_three]
      have hle0 : Fin.castLE (by omega : 3 ≤ 5) 0 = 0 := rfl
      have hle1 : Fin.castLE (by omega : 3 ≤ 5) 1 = 1 := rfl
      have hle2 : Fin.castLE (by omega : 3 ≤ 5) 2 = 2 := rfl
      rw [hle0, hle1, hle2]
      simp only [cartan235Diff, mul_add, mul_smul_comm, mul_neg]
      have h00 : cartan235Coframe 0 * cartan235Coframe 1 * cartan235Coframe 2 *
          (cartan235Coframe 2 * cartan235Coframe 3) = 0 := by
        rw [← mul_assoc (cartan235Coframe 0 * cartan235Coframe 1 * cartan235Coframe 2),
          mul_assoc (cartan235Coframe 0 * cartan235Coframe 1) (cartan235Coframe 2),
          cartan235_coframe_sq, mul_zero, zero_mul]
      have h01 : cartan235Coframe 0 * cartan235Coframe 1 * cartan235Coframe 2 *
          (cartan235Coframe 2 * cartan235Coframe 4) = 0 := by
        rw [← mul_assoc (cartan235Coframe 0 * cartan235Coframe 1 * cartan235Coframe 2),
          mul_assoc (cartan235Coframe 0 * cartan235Coframe 1) (cartan235Coframe 2),
          cartan235_coframe_sq, mul_zero, zero_mul]
      have h02 : cartan235Coframe 0 * cartan235Coframe 1 * cartan235Coframe 2 *
          (cartan235Coframe 3 * cartan235Coframe 4) =
          InfoGeometry.Projective.ExteriorRegressive.volume b := by
        rw [← mul_assoc, cartan235_vol5_eq_volume]
      rw [h00, h01, h02, smul_zero, smul_zero, zero_add, zero_add, smul_neg, neg_smul]
  have hker1 : LinearMap.ker cartan235DerivedTest1 =
      Submodule.span ℝ {![(1 : ℝ), 0, 0], ![0, 1, 0]} := by
    ext c
    rw [LinearMap.mem_ker, htest1_eq c, smul_eq_zero]
    have hvol_ne : InfoGeometry.Projective.ExteriorRegressive.volume b ≠ 0 :=
      InfoGeometry.Projective.ExteriorRegressive.volume_ne_zero b
    simp only [hvol_ne, or_false, neg_eq_zero]
    rw [Submodule.mem_span_pair]
    constructor
    · intro hc2
      refine ⟨c 0, c 1, ?_⟩
      ext i; fin_cases i <;> simp [hc2]
    · rintro ⟨a, b', rfl⟩
      simp
  have hli2 : LinearIndependent ℝ ![![(1 : ℝ), 0, 0], ![0, 1, 0]] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp only [Fin.sum_univ_two, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, mul_one, mul_zero,
      add_zero, zero_add] at h0 h1
    fin_cases i
    · exact h0
    · exact h1
  have hfin1 : Module.finrank ℝ (LinearMap.ker cartan235DerivedTest1) = 2 := by
    rw [hker1]
    have hrange : Set.range ![![(1 : ℝ), 0, 0], ![0, 1, 0]] = {![(1 : ℝ), 0, 0], ![0, 1, 0]} := by
      ext z; simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩; fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [← hrange, finrank_span_eq_card hli2, Fintype.card_fin]
  have hker2 : LinearMap.ker cartan235DerivedTest2 = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker] at hc
    have hc_eq : cartan235DerivedTest2 c =
        c 0 • (cartan235Coframe 0 * cartan235Coframe 1 * cartan235Coframe 2 * cartan235Coframe 3) +
        c 1 • (cartan235Coframe 0 * cartan235Coframe 1 * cartan235Coframe 2 * cartan235Coframe 4) := by
      change cartan235Coframe 0 * cartan235Coframe 1 *
          (c 0 • cartan235Diff 0 + c 1 • cartan235Diff 1) = _
      dsimp only [cartan235Diff]
      simp only [mul_add, mul_smul_comm, mul_assoc]
    have h4 : cartan235DerivedTest2 c * cartan235Coframe 4 =
        c 0 • InfoGeometry.Projective.ExteriorRegressive.volume b := by
      rw [hc_eq, add_mul, smul_mul_assoc, smul_mul_assoc, cartan235_vol5_eq_volume,
        mul_assoc (cartan235Coframe 0 * cartan235Coframe 1 * cartan235Coframe 2),
        cartan235_coframe_sq, mul_zero, smul_zero, add_zero]
    have h3 : cartan235DerivedTest2 c * cartan235Coframe 3 =
        (-c 1) • InfoGeometry.Projective.ExteriorRegressive.volume b := by
      rw [hc_eq, add_mul, smul_mul_assoc, smul_mul_assoc]
      have h33 : cartan235Coframe 0 * cartan235Coframe 1 * cartan235Coframe 2 *
          cartan235Coframe 3 * cartan235Coframe 3 = 0 := by
        rw [mul_assoc, cartan235_coframe_sq, mul_zero]
      have h43 : cartan235Coframe 0 * cartan235Coframe 1 * cartan235Coframe 2 *
          cartan235Coframe 4 * cartan235Coframe 3 =
          -InfoGeometry.Projective.ExteriorRegressive.volume b := by
        rw [mul_assoc (cartan235Coframe 0 * cartan235Coframe 1 * cartan235Coframe 2),
          cartan235_coframe_swap 3 4, mul_neg, ← mul_assoc, cartan235_vol5_eq_volume]
      rw [h33, h43, smul_zero, zero_add, smul_neg, neg_smul]
    rw [hc, zero_mul] at h4 h3
    have hvol_ne : InfoGeometry.Projective.ExteriorRegressive.volume b ≠ 0 :=
      InfoGeometry.Projective.ExteriorRegressive.volume_ne_zero b
    have hc0 : c 0 = 0 := (smul_eq_zero.mp h4.symm).resolve_right hvol_ne
    have hc1 : c 1 = 0 := neg_eq_zero.mp ((smul_eq_zero.mp h3.symm).resolve_right hvol_ne)
    rw [Submodule.mem_bot]
    ext i; fin_cases i <;> assumption
  have hfin2 : Module.finrank ℝ (LinearMap.ker cartan235DerivedTest2) = 0 := by
    rw [hker2, finrank_bot]
  exact ⟨hfin0, hker1, hfin1, hker2, hfin2⟩

/-- **Cartan (`S2-09` 1910 §§VI.–XI.; `R3.2`)**:
edge-case separation between generic `(2,3,5)` Pfaffian growth and degenerate integrable
`(2,2,2)` (vanishing structure differentials) or Engel `(2,3,4)` (`dω₁ = 0`) models. -/
theorem cartan235_integrable_and_engel_rank_drop_edge_cases :
    let integrableTest : (Fin 3 → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Fin 5 → ℝ) := 0
    let engelTest2 : (Fin 2 → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Fin 5 → ℝ) :=
      { toFun := fun c => cartan235Coframe 0 * cartan235Coframe 1 * (c 0 • cartan235Diff 0)
        map_add' := fun c₁ c₂ => by simp [add_smul, mul_add]
        map_smul' := fun r c => by simp [smul_smul] }
    Module.finrank ℝ (LinearMap.ker integrableTest) = 3 ∧
      LinearMap.ker engelTest2 = Submodule.span ℝ {![(0 : ℝ), 1]} ∧
      Module.finrank ℝ (LinearMap.ker engelTest2) = 1 := by
  intro integrableTest engelTest2
  have hker0 : Module.finrank ℝ (LinearMap.ker integrableTest) = 3 := by
    rw [LinearMap.ker_zero, finrank_top, Module.finrank_fin_fun]
  have hkerE : LinearMap.ker engelTest2 = Submodule.span ℝ {![(0 : ℝ), 1]} := by
    ext c
    rw [LinearMap.mem_ker]
    have hev : engelTest2 c * cartan235Coframe 4 =
        c 0 • InfoGeometry.Projective.ExteriorRegressive.volume (Pi.basisFun ℝ (Fin 5)) := by
      change (cartan235Coframe 0 * cartan235Coframe 1 * (c 0 • cartan235Diff 0)) *
          cartan235Coframe 4 = _
      dsimp only [cartan235Diff]
      rw [mul_smul_comm, smul_mul_assoc,
        ← mul_assoc (cartan235Coframe 0 * cartan235Coframe 1) (cartan235Coframe 2) (cartan235Coframe 3),
        cartan235_vol5_eq_volume]
    constructor
    · intro hc
      rw [hc, zero_mul] at hev
      have hc0 : c 0 = 0 :=
        (smul_eq_zero.mp hev.symm).resolve_right
          (InfoGeometry.Projective.ExteriorRegressive.volume_ne_zero _)
      rw [Submodule.mem_span_singleton]
      refine ⟨c 1, ?_⟩
      ext i; fin_cases i <;> simp [hc0]
    · intro hc
      rw [Submodule.mem_span_singleton] at hc
      obtain ⟨r, rfl⟩ := hc
      dsimp [engelTest2]
      simp
  have hli1 : LinearIndependent ℝ ![(![(0 : ℝ), 1] : Fin 2 → ℝ)] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    fin_cases i
    have h1 := congrFun hc 1
    simpa [Fin.sum_univ_one] using h1
  have hfinE : Module.finrank ℝ (LinearMap.ker engelTest2) = 1 := by
    rw [hkerE]
    have hrange : Set.range ![(![(0 : ℝ), 1] : Fin 2 → ℝ)] = {![(0 : ℝ), 1]} := by
      ext z; simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩; fin_cases i; rfl
      · rintro rfl; exact ⟨0, rfl⟩
    rw [← hrange, finrank_span_eq_card hli1, Fintype.card_fin]
  exact ⟨hker0, hkerE, hfinE⟩

/-- **Cartan (`S2-09` 1910; `R3.2`)**:
compatibility between `cartan235Diff 2 = -(ω₃ ∧ ω₄)` and `GrassmannPfaffianDarbouxAlgebra`
(class-3 algebraic Darboux vanishing on `ω₂` plus 2-variable Pfaffian jet vanishing). -/
theorem cartan235_grassmann_pfaff_compatibility (u : Fin 2 → ℝ) (β α : Fin 2 → Fin 5 → ℝ) :
    cartan235Coframe 2 * cartan235Diff 2 ≠ 0 ∧
      cartan235Coframe 2 * (cartan235Diff 2) ^ 2 = 0 ∧
      (cartan235Diff 2) ^ 3 = 0 ∧
      pfaffJetOneForm u α * (pfaffJetTwoForm β α) ^ 2 = 0 := by
  have h34 : cartan235Diff 2 = -(cartan235Coframe 3 * cartan235Coframe 4) := rfl
  have hsq_diff : (cartan235Diff 2) ^ 2 = 0 := by
    rw [h34, sq, neg_mul_neg, mul_assoc,
      ← mul_assoc (cartan235Coframe 4) (cartan235Coframe 3) (cartan235Coframe 4),
      cartan235_coframe_swap 3 4, neg_mul, mul_neg,
      mul_assoc (cartan235Coframe 3) (cartan235Coframe 4) (cartan235Coframe 4),
      cartan235_coframe_sq, mul_zero, mul_zero, neg_zero]
  have hne : cartan235Coframe 2 * cartan235Diff 2 ≠ 0 := by
    intro h0
    have hmul := congrArg (fun x => cartan235Coframe 0 * cartan235Coframe 1 * x) h0
    rw [mul_zero, h34, mul_neg, mul_neg, ← mul_assoc, ← mul_assoc,
      cartan235_vol5_eq_volume, neg_eq_zero] at hmul
    exact InfoGeometry.Projective.ExteriorRegressive.volume_ne_zero (Pi.basisFun ℝ (Fin 5)) hmul
  have hpow2 : cartan235Coframe 2 * (cartan235Diff 2) ^ 2 = 0 := by
    rw [hsq_diff, mul_zero]
  have hpow3 : (cartan235Diff 2) ^ 3 = 0 := by
    have hd2 : cartan235Diff 2 ∈ ⋀[ℝ]^2 (Fin 5 → ℝ) := by
      have heq : cartan235Diff 2 =
          -(ExteriorAlgebra.ιMulti ℝ 2 ![Pi.basisFun ℝ (Fin 5) 3, Pi.basisFun ℝ (Fin 5) 4]) := by
        rw [h34, ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
          ExteriorAlgebra.ιMulti_zero_apply, mul_one]
        rfl
      rw [heq]
      exact Submodule.neg_mem _ (ExteriorAlgebra.ιMulti_range ℝ 2 ⟨_, rfl⟩)
    exact grassmann_no518_exterior_division
      ((Pi.basisFun ℝ (Fin 5)).ne_zero 2) hd2 2 hpow2
  exact ⟨hne, hpow2, hpow3, grassmann_no511_pfaff_exterior_vanishing u β α⟩

/-- **Cartan (`S2-09` 1910/1914; `R3.2`)**:
degree-1 Tanaka symbol subspace `m₁ = span {g2X4, g2F0}` inside `g2Submodule`. -/
def cartan235Symbol1 : Submodule ℝ (Matrix Krein16Idx Krein16Idx ℝ) :=
  Submodule.span ℝ {g2X4, g2F0}

/-- **Cartan (`S2-09` 1910/1914; `R3.2`)**:
degree-2 Tanaka symbol subspace `m₁ ⊕ m₂ = span {g2X4, g2F0, g2X3}` inside `g2Submodule`. -/
def cartan235Symbol2 : Submodule ℝ (Matrix Krein16Idx Krein16Idx ℝ) :=
  Submodule.span ℝ {g2X4, g2F0, g2X3}

/-- **Cartan (`S2-09` 1910/1914; `R3.2`)**:
full positive nilpotent 5-dimensional Tanaka symbol `m₁ ⊕ m₂ ⊕ m₃ = span {g2X4, g2F0, g2X3, g2Zpos2, g2X2}`. -/
def cartan235Symbol3 : Submodule ℝ (Matrix Krein16Idx Krein16Idx ℝ) :=
  Submodule.span ℝ {g2X4, g2F0, g2X3, g2Zpos2, g2X2}

private theorem g2_basis_bracket_unique_weight (i j k0 : Fin 14)
    (huniq : ∀ k : Fin 14, g2Grade k = g2Grade i + g2Grade j →
      g2AlphaWeight k = g2AlphaWeight i + g2AlphaWeight j → k = k0) :
    ∃ r : ℝ, g2Basis i * g2Basis j - g2Basis j * g2Basis i = r • g2Basis k0 := by
  obtain ⟨c, hc_eq, hc_supp⟩ := g2_basis_bracket_support i j
  refine ⟨c k0, ?_⟩
  rw [hc_eq]
  refine Finset.sum_eq_single k0 (fun k _ hk0 => ?_) (fun hk => absurd (Finset.mem_univ k0) hk)
  by_cases hck : c k = 0
  · rw [hck, zero_smul]
  · obtain ⟨hg, ha⟩ := hc_supp k hck
    have hg' : g2Grade k = g2Grade i + g2Grade j := by exact_mod_cast hg
    have ha' : g2AlphaWeight k = g2AlphaWeight i + g2AlphaWeight j := by exact_mod_cast ha
    exact absurd (huniq k hg' ha') hk0

private theorem g2_basis_bracket_vanish_of_no_weight (i j : Fin 14)
    (hnone : ∀ k : Fin 14, g2Grade k = g2Grade i + g2Grade j →
      g2AlphaWeight k ≠ g2AlphaWeight i + g2AlphaWeight j) :
    g2Basis i * g2Basis j - g2Basis j * g2Basis i = 0 := by
  obtain ⟨c, hc_eq, hc_supp⟩ := g2_basis_bracket_support i j
  rw [hc_eq]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hck : c k = 0
  · rw [hck, zero_smul]
  · obtain ⟨hg, ha⟩ := hc_supp k hck
    have hg' : g2Grade k = g2Grade i + g2Grade j := by exact_mod_cast hg
    have ha' : g2AlphaWeight k = g2AlphaWeight i + g2AlphaWeight j := by exact_mod_cast ha
    exact absurd ha' (hnone k hg')

/-- **Cartan (`S2-09` 1910/1914; `R3.2`)**:
explicit Tanaka brackets inside `g2Submodule` generating `(2, 3, 5)` growth, together with
the explicit matrix non-commutativity witness `g2X4 * g2F0 ≠ g2F0 * g2X4` (`T16`). -/
theorem cartan235_tanaka_brackets :
    g2X4 * g2F0 - g2F0 * g2X4 = (2 : ℝ) • g2X3 ∧
      g2X3 * g2X4 - g2X4 * g2X3 = (3 : ℝ) • g2Zpos2 ∧
      g2X3 * g2F0 - g2F0 * g2X3 = (3 : ℝ) • g2X2 ∧
      g2X4 * g2F0 ≠ g2F0 * g2X4 := by
  have h34 : g2X3 * g2X4 - g2X4 * g2X3 = (3 : ℝ) • g2Zpos2 :=
    g2_grade1_contact_and_serre_syzygies.2.1
  have h46 : g2X4 * g2F0 - g2F0 * g2X4 = (2 : ℝ) • g2X3 := by
    obtain ⟨r, hr⟩ := g2_basis_bracket_unique_weight 4 6 3 (by decide)
    change g2X4 * g2F0 - g2F0 * g2X4 = r • g2X3 at hr
    have heval := congrArg (fun M : Matrix Krein16Idx Krein16Idx ℝ => M (g2Pivot 3).1 (g2Pivot 3).2) hr
    have hlhs : (g2X4 * g2F0 - g2F0 * g2X4) (g2Pivot 3).1 (g2Pivot 3).2 = -2 := by
      simp only [Matrix.sub_apply, Matrix.mul_apply,
        g2X4, g2F0, u1Op, u2Op, d1Op, d2Op, d3Op, et0Op, g2Pivot, tensor4,
        cl11Up, cl11Down, cl11Neg, cl11Grad,
        Matrix.one_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fintype.sum_prod_type, Fin.sum_univ_two]
      norm_num
    have hrhs : g2X3 (g2Pivot 3).1 (g2Pivot 3).2 = -1 := by
      dsimp only [g2X3, u1Op, u2Op, d3Op, et0Op, g2Pivot]
      simp only [Matrix.add_apply, Matrix.mul_apply, tensor4,
        cl11Up, cl11Down, cl11Neg, cl11Grad,
        Matrix.one_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fintype.sum_prod_type, Fin.sum_univ_two]
      norm_num
    simp only [Matrix.smul_apply, smul_eq_mul, hlhs, hrhs] at heval
    have hr2 : r = 2 := by linarith
    rwa [hr2] at hr
  have h36 : g2X3 * g2F0 - g2F0 * g2X3 = (3 : ℝ) • g2X2 := by
    obtain ⟨r, hr⟩ := g2_basis_bracket_unique_weight 3 6 2 (by decide)
    change g2X3 * g2F0 - g2F0 * g2X3 = r • g2X2 at hr
    have heval := congrArg (fun M : Matrix Krein16Idx Krein16Idx ℝ => M (g2Pivot 2).1 (g2Pivot 2).2) hr
    have hlhs : (g2X3 * g2F0 - g2F0 * g2X3) (g2Pivot 2).1 (g2Pivot 2).2 = -3 := by
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
        g2X3, g2F0, u1Op, u2Op, d1Op, d3Op, et0Op, g2Pivot, tensor4,
        cl11Up, cl11Down, cl11Neg, cl11Grad,
        Matrix.one_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fintype.sum_prod_type, Fin.sum_univ_two]
      norm_num
    have hrhs : g2X2 (g2Pivot 2).1 (g2Pivot 2).2 = -1 := by
      dsimp only [g2X2, u2Op, d3Op, g2Pivot]
      simp only [Matrix.mul_apply, tensor4,
        cl11Up, cl11Down, cl11Grad,
        Matrix.one_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fintype.sum_prod_type, Fin.sum_univ_two]
      norm_num
    simp only [Matrix.smul_apply, smul_eq_mul, hlhs, hrhs] at heval
    have hr3 : r = 3 := by linarith
    rwa [hr3] at hr
  have hnc : g2X4 * g2F0 ≠ g2F0 * g2X4 := by
    intro heq
    have h0 : (2 : ℝ) • g2Basis 3 = 0 := by
      change (2 : ℝ) • g2X3 = 0
      rw [← h46, heq, sub_self]
    have h3 : g2Basis 3 = 0 := (smul_eq_zero.mp h0).resolve_left (by norm_num)
    exact g2Basis_linearIndependent.ne_zero 3 h3
  exact ⟨h46, h34, h36, hnc⟩

/-- **Cartan (`S2-09` 1910/1914; `R3.2`)**:
strict `(2, 3, 5)` Tanaka symbol filtration `cartan235Symbol1 < cartan235Symbol2 < cartan235Symbol3 ≤ g2Submodule`
with exact bracket generation `[m₁, m₁] ⊆ m₂` and `[m, m] ⊆ m`. -/
theorem cartan235_tanaka_symbol_growth_2_3_5 :
    Module.finrank ℝ cartan235Symbol1 = 2 ∧
      Module.finrank ℝ cartan235Symbol2 = 3 ∧
      Module.finrank ℝ cartan235Symbol3 = 5 ∧
      cartan235Symbol1 < cartan235Symbol2 ∧
      cartan235Symbol2 < cartan235Symbol3 ∧
      cartan235Symbol3 ≤ g2Submodule ∧
      (∀ A ∈ cartan235Symbol1, ∀ B ∈ cartan235Symbol1, A * B - B * A ∈ cartan235Symbol2) ∧
      (∀ A ∈ cartan235Symbol3, ∀ B ∈ cartan235Symbol3, A * B - B * A ∈ cartan235Symbol3) := by
  have hdim1 : Module.finrank ℝ cartan235Symbol1 = 2 := by
    let idx : Fin 2 → Fin 14 := ![4, 6]
    have hinj : Function.Injective idx := by
      intro i j h; fin_cases i <;> fin_cases j <;> simp [idx] at h ⊢
    have hli := g2Basis_linearIndependent.comp idx hinj
    have hrange : Set.range (g2Basis ∘ idx) = {g2X4, g2F0} := by
      ext z; simp only [Set.mem_range, Function.comp_apply, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩; fin_cases i <;> simp [idx, g2Basis]
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    have hsp : cartan235Symbol1 = Submodule.span ℝ (Set.range (g2Basis ∘ idx)) := by
      rw [hrange]; rfl
    rw [hsp, finrank_span_eq_card hli, Fintype.card_fin]
  have hdim2 : Module.finrank ℝ cartan235Symbol2 = 3 := by
    let idx : Fin 3 → Fin 14 := ![4, 6, 3]
    have hinj : Function.Injective idx := by
      intro i j h; fin_cases i <;> fin_cases j <;> simp [idx] at h ⊢
    have hli := g2Basis_linearIndependent.comp idx hinj
    have hrange : Set.range (g2Basis ∘ idx) = {g2X4, g2F0, g2X3} := by
      ext z; simp only [Set.mem_range, Function.comp_apply, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩; fin_cases i <;> simp [idx, g2Basis]
      · rintro (rfl | rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
    have hsp : cartan235Symbol2 = Submodule.span ℝ (Set.range (g2Basis ∘ idx)) := by
      rw [hrange]; rfl
    rw [hsp, finrank_span_eq_card hli, Fintype.card_fin]
  have hdim3 : Module.finrank ℝ cartan235Symbol3 = 5 := by
    let idx : Fin 5 → Fin 14 := ![4, 6, 3, 0, 2]
    have hinj : Function.Injective idx := by
      intro i j h; fin_cases i <;> fin_cases j <;> simp [idx] at h ⊢
    have hli := g2Basis_linearIndependent.comp idx hinj
    have hrange : Set.range (g2Basis ∘ idx) = {g2X4, g2F0, g2X3, g2Zpos2, g2X2} := by
      ext z; simp only [Set.mem_range, Function.comp_apply, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩; fin_cases i <;> simp [idx, g2Basis]
      · rintro (rfl | rfl | rfl | rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨3, rfl⟩
        · exact ⟨4, rfl⟩
    have hsp : cartan235Symbol3 = Submodule.span ℝ (Set.range (g2Basis ∘ idx)) := by
      rw [hrange]; rfl
    rw [hsp, finrank_span_eq_card hli, Fintype.card_fin]
  have h1_le_2 : cartan235Symbol1 ≤ cartan235Symbol2 := by
    apply Submodule.span_mono
    intro x hx
    rcases hx with rfl | rfl <;> simp
  have h2_le_3 : cartan235Symbol2 ≤ cartan235Symbol3 := by
    apply Submodule.span_mono
    intro x hx
    rcases hx with rfl | rfl | rfl <;> simp
  have h1_lt_2 : cartan235Symbol1 < cartan235Symbol2 := by
    refine lt_of_le_of_ne h1_le_2 fun heq => ?_
    have hd := congrArg (fun S : Submodule ℝ (Matrix Krein16Idx Krein16Idx ℝ) =>
      Module.finrank ℝ S) heq
    rw [hdim1, hdim2] at hd
    omega
  have h2_lt_3 : cartan235Symbol2 < cartan235Symbol3 := by
    refine lt_of_le_of_ne h2_le_3 fun heq => ?_
    have hd := congrArg (fun S : Submodule ℝ (Matrix Krein16Idx Krein16Idx ℝ) =>
      Module.finrank ℝ S) heq
    rw [hdim2, hdim3] at hd
    omega
  have h3_le_g2 : cartan235Symbol3 ≤ g2Submodule := by
    rw [cartan235Symbol3, Submodule.span_le]
    rintro _ (rfl | rfl | rfl | rfl | rfl)
    · exact Submodule.subset_span ⟨4, rfl⟩
    · exact Submodule.subset_span ⟨6, rfl⟩
    · exact Submodule.subset_span ⟨3, rfl⟩
    · exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.subset_span ⟨2, rfl⟩
  have hcomm_bilin : ∀ (S T : Submodule ℝ (Matrix Krein16Idx Krein16Idx ℝ))
      (genS : Set (Matrix Krein16Idx Krein16Idx ℝ)),
      S = Submodule.span ℝ genS →
      (∀ A ∈ genS, ∀ B ∈ genS, A * B - B * A ∈ T) →
      ∀ A ∈ S, ∀ B ∈ S, A * B - B * A ∈ T := by
    intro S T genS hS hgen A hA B hB
    rw [hS] at hA hB
    induction hA using Submodule.span_induction with
    | mem x hx =>
      induction hB using Submodule.span_induction with
      | mem y hy => exact hgen x hx y hy
      | zero => simp
      | add y z _ _ ihy ihz =>
        rw [mul_add, add_mul, show x * y + x * z - (y * x + z * x) =
          (x * y - y * x) + (x * z - z * x) by abel]
        exact T.add_mem ihy ihz
      | smul r y _ ihy =>
        rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
        exact T.smul_mem r ihy
    | zero => simp
    | add x z _ _ ihx ihz =>
      rw [add_mul, mul_add, show x * B + z * B - (B * x + B * z) =
        (x * B - B * x) + (z * B - B * z) by abel]
      exact T.add_mem ihx ihz
    | smul r x _ ihx =>
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
      exact T.smul_mem r ihx
  have h11_2 : ∀ A ∈ cartan235Symbol1, ∀ B ∈ cartan235Symbol1, A * B - B * A ∈ cartan235Symbol2 := by
    refine hcomm_bilin cartan235Symbol1 cartan235Symbol2 {g2X4, g2F0} rfl ?_
    intro A hA B hB
    have hX3 : g2X3 ∈ cartan235Symbol2 := Submodule.subset_span (by simp)
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · simp
    · rw [cartan235_tanaka_brackets.1]
      exact cartan235Symbol2.smul_mem 2 hX3
    · rw [show g2F0 * g2X4 - g2X4 * g2F0 = -(g2X4 * g2F0 - g2F0 * g2X4) by abel,
        cartan235_tanaka_brackets.1]
      exact cartan235Symbol2.neg_mem (cartan235Symbol2.smul_mem 2 hX3)
    · simp
  have h33_3 : ∀ A ∈ cartan235Symbol3, ∀ B ∈ cartan235Symbol3, A * B - B * A ∈ cartan235Symbol3 := by
    refine hcomm_bilin cartan235Symbol3 cartan235Symbol3 {g2X4, g2F0, g2X3, g2Zpos2, g2X2} rfl ?_
    have hX3 : g2X3 ∈ cartan235Symbol3 := Submodule.subset_span (by simp)
    have hZ2 : g2Zpos2 ∈ cartan235Symbol3 := Submodule.subset_span (by simp)
    have hX2 : g2X2 ∈ cartan235Symbol3 := Submodule.subset_span (by simp)
    have hvan : ∀ i j : Fin 14, (∀ k : Fin 14, g2Grade k = g2Grade i + g2Grade j →
        g2AlphaWeight k ≠ g2AlphaWeight i + g2AlphaWeight j) →
        g2Basis i * g2Basis j - g2Basis j * g2Basis i ∈ cartan235Symbol3 := fun i j h => by
      rw [g2_basis_bracket_vanish_of_no_weight i j h]
      exact cartan235Symbol3.zero_mem
    have h4 : g2X4 = g2Basis 4 := rfl
    have h6 : g2F0 = g2Basis 6 := rfl
    have h3 : g2X3 = g2Basis 3 := rfl
    have h0 : g2Zpos2 = g2Basis 0 := rfl
    have h2 : g2X2 = g2Basis 2 := rfl
    intro A hA B hB
    rcases hA with rfl | rfl | rfl | rfl | rfl <;>
      rcases hB with rfl | rfl | rfl | rfl | rfl
    · rw [sub_self]; exact cartan235Symbol3.zero_mem
    · rw [cartan235_tanaka_brackets.1]; exact cartan235Symbol3.smul_mem 2 hX3
    · rw [show g2X4 * g2X3 - g2X3 * g2X4 = -(g2X3 * g2X4 - g2X4 * g2X3) by abel,
        cartan235_tanaka_brackets.2.1]
      exact cartan235Symbol3.neg_mem (cartan235Symbol3.smul_mem 3 hZ2)
    · rw [h4, h0]; exact hvan 4 0 (by decide)
    · rw [h4, h2]; exact hvan 4 2 (by decide)
    · rw [show g2F0 * g2X4 - g2X4 * g2F0 = -(g2X4 * g2F0 - g2F0 * g2X4) by abel,
        cartan235_tanaka_brackets.1]
      exact cartan235Symbol3.neg_mem (cartan235Symbol3.smul_mem 2 hX3)
    · rw [sub_self]; exact cartan235Symbol3.zero_mem
    · rw [show g2F0 * g2X3 - g2X3 * g2F0 = -(g2X3 * g2F0 - g2F0 * g2X3) by abel,
        cartan235_tanaka_brackets.2.2.1]
      exact cartan235Symbol3.neg_mem (cartan235Symbol3.smul_mem 3 hX2)
    · rw [h6, h0]; exact hvan 6 0 (by decide)
    · rw [h6, h2]; exact hvan 6 2 (by decide)
    · rw [cartan235_tanaka_brackets.2.1]; exact cartan235Symbol3.smul_mem 3 hZ2
    · rw [cartan235_tanaka_brackets.2.2.1]; exact cartan235Symbol3.smul_mem 3 hX2
    · rw [sub_self]; exact cartan235Symbol3.zero_mem
    · rw [h3, h0]; exact hvan 3 0 (by decide)
    · rw [h3, h2]; exact hvan 3 2 (by decide)
    · rw [h0, h4]; exact hvan 0 4 (by decide)
    · rw [h0, h6]; exact hvan 0 6 (by decide)
    · rw [h0, h3]; exact hvan 0 3 (by decide)
    · rw [sub_self]; exact cartan235Symbol3.zero_mem
    · rw [h0, h2]; exact hvan 0 2 (by decide)
    · rw [h2, h4]; exact hvan 2 4 (by decide)
    · rw [h2, h6]; exact hvan 2 6 (by decide)
    · rw [h2, h3]; exact hvan 2 3 (by decide)
    · rw [h2, h0]; exact hvan 2 0 (by decide)
    · rw [sub_self]; exact cartan235Symbol3.zero_mem
  exact ⟨hdim1, hdim2, hdim3, h1_lt_2, h2_lt_3, h3_le_g2, h11_2, h33_3⟩

/-- **Cartan (`S2-09` 1910 §§VI.–XI.; `R3.2`)**:
`SL(2)` generator (`S`-inversion `aᵢ ↦ (-1)^i a_{4-i}` and `T_t`-shear `(u, v) ↦ (u + t v, v)`)
and general `GL(2)` / `SL(2)` covariance of the binary-quartic form
`ErlangenProgramCurvatureBinaryAndMasterAtlas.binQuartic` and its fundamental invariants
`quarticInvI` (weight 4) and `quarticInvJ` (weight 6), over any `[CommRing R]`. -/
theorem binary_quartic_sl2_covariance {R : Type*} [CommRing R]
    (a₀ a₁ a₂ a₃ a₄ u v t α β γ δ : R) :
    (ErlangenProgramCurvatureBinaryAndMasterAtlas.binQuartic a₄ (-a₃) a₂ (-a₁) a₀ u v =
        ErlangenProgramCurvatureBinaryAndMasterAtlas.binQuartic a₀ a₁ a₂ a₃ a₄ (-v) u ∧
      ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI a₄ (-a₃) a₂ (-a₁) a₀ =
        ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI a₀ a₁ a₂ a₃ a₄ ∧
      ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ a₄ (-a₃) a₂ (-a₁) a₀ =
        ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ a₀ a₁ a₂ a₃ a₄) ∧
    (let t₁ := a₀ * t + a₁
     let t₂ := a₀ * t ^ 2 + 2 * a₁ * t + a₂
     let t₃ := a₀ * t ^ 3 + 3 * a₁ * t ^ 2 + 3 * a₂ * t + a₃
     let t₄ := a₀ * t ^ 4 + 4 * a₁ * t ^ 3 + 6 * a₂ * t ^ 2 + 4 * a₃ * t + a₄
     ErlangenProgramCurvatureBinaryAndMasterAtlas.binQuartic a₀ t₁ t₂ t₃ t₄ u v =
         ErlangenProgramCurvatureBinaryAndMasterAtlas.binQuartic a₀ a₁ a₂ a₃ a₄ (u + t * v) v ∧
       ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI a₀ t₁ t₂ t₃ t₄ =
         ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI a₀ a₁ a₂ a₃ a₄ ∧
       ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ a₀ t₁ t₂ t₃ t₄ =
         ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ a₀ a₁ a₂ a₃ a₄) ∧
    (let c₀ := a₀ * α ^ 4 + 4 * a₁ * α ^ 3 * γ + 6 * a₂ * α ^ 2 * γ ^ 2 +
       4 * a₃ * α * γ ^ 3 + a₄ * γ ^ 4
     let c₁ := a₀ * α ^ 3 * β + a₁ * α ^ 3 * δ + 3 * a₁ * α ^ 2 * β * γ +
       3 * a₂ * α ^ 2 * γ * δ + 3 * a₂ * α * β * γ ^ 2 + 3 * a₃ * α * γ ^ 2 * δ +
       a₃ * β * γ ^ 3 + a₄ * γ ^ 3 * δ
     let c₂ := a₀ * α ^ 2 * β ^ 2 + 2 * a₁ * α ^ 2 * β * δ + 2 * a₁ * α * β ^ 2 * γ +
       a₂ * α ^ 2 * δ ^ 2 + 4 * a₂ * α * β * γ * δ + a₂ * β ^ 2 * γ ^ 2 +
       2 * a₃ * α * γ * δ ^ 2 + 2 * a₃ * β * γ ^ 2 * δ + a₄ * γ ^ 2 * δ ^ 2
     let c₃ := a₀ * α * β ^ 3 + 3 * a₁ * α * β ^ 2 * δ + a₁ * β ^ 3 * γ +
       3 * a₂ * α * β * δ ^ 2 + 3 * a₂ * β ^ 2 * γ * δ + a₃ * α * δ ^ 3 +
       3 * a₃ * β * γ * δ ^ 2 + a₄ * γ * δ ^ 3
     let c₄ := a₀ * β ^ 4 + 4 * a₁ * β ^ 3 * δ + 6 * a₂ * β ^ 2 * δ ^ 2 +
       4 * a₃ * β * δ ^ 3 + a₄ * δ ^ 4
     ErlangenProgramCurvatureBinaryAndMasterAtlas.binQuartic c₀ c₁ c₂ c₃ c₄ u v =
         ErlangenProgramCurvatureBinaryAndMasterAtlas.binQuartic a₀ a₁ a₂ a₃ a₄
           (α * u + β * v) (γ * u + δ * v) ∧
       ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI c₀ c₁ c₂ c₃ c₄ =
         (α * δ - β * γ) ^ 4 *
           ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI a₀ a₁ a₂ a₃ a₄ ∧
       ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ c₀ c₁ c₂ c₃ c₄ =
         (α * δ - β * γ) ^ 6 *
           ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ a₀ a₁ a₂ a₃ a₄) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · dsimp [ErlangenProgramCurvatureBinaryAndMasterAtlas.binQuartic]; ring
  · dsimp [ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI]; ring
  · dsimp [ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ]; ring
  · dsimp [ErlangenProgramCurvatureBinaryAndMasterAtlas.binQuartic]; ring
  · dsimp [ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI]; ring
  · dsimp [ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ]; ring
  · dsimp [ErlangenProgramCurvatureBinaryAndMasterAtlas.binQuartic]; ring
  · dsimp [ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI]; ring
  · dsimp [ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ]; ring

/-- **Cartan (`S2-09` 1910 §§VI.–XI., 1914 §VI.; `R3.2`)**:
split `g_{2(2)}` real-form, rolling-ball `3 : 1` ratio, and binary-quartic invariant synthesis:
1. 14D Lie algebra (`g2LieSubalgebra`, `canonicalZornDerivations`).
2. Split real-form witness: nonzero positive real adjoint root-eigenvalue
   `g2H1 * g2Zpos2 - g2Zpos2 * g2H1 = 2 • g2Zpos2` (`g2Zpos2 ≠ 0`) together with `ℝ¹⁶`
   `kreinMetric88`-skew invariance (`g2Submodule_mem_stabilizer`), separating split `g_{2(2)}`
   from compact `g₂`.
3. Genuine `SL(2)` binary-quartic invariant theory: invariance of
   `ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI` and `quarticInvJ` under `S`-inversion
   (`aᵢ ↦ (-1)^i a_{4-i}`), `T_t`-shear, and general `SL(2, ℝ)` substitution (`α * δ - β * γ = 1`),
   Cayley's binary-quartic syzygy (`cayley_binary_quartic_syzygy`), and flat `(0, 0, 0, 0, 0)` vs.
   non-flat `(1, 0, μ, 0, 1)` invariant separation.
4. Rolling-ball `turnsAroundFixedSphere R r = 4 ↔ R = 3 * r` (`G2RollingBall`) and real derivation
   exponential flow (`split_g2_derivation_exponential_is_real_automorphism`). -/
theorem cartan1910_1914_split_g2_and_rolling_ball_synthesis (R r : ℝ) (hr : r ≠ 0) :
    (Module.finrank ℝ g2LieSubalgebra = 14 ∧
      Module.finrank ℝ InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations = 14) ∧
    (g2H1 * g2Zpos2 - g2Zpos2 * g2H1 = (2 : ℝ) • g2Zpos2 ∧ g2Zpos2 ≠ 0 ∧
      ∀ X ∈ g2Submodule, Xᵀ * kreinMetric88 + kreinMetric88 * X = 0) ∧
    ((∀ a₀ a₁ a₂ a₃ a₄ t : ℝ,
        ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI a₄ (-a₃) a₂ (-a₁) a₀ =
          ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI a₀ a₁ a₂ a₃ a₄ ∧
        ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ a₄ (-a₃) a₂ (-a₁) a₀ =
          ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ a₀ a₁ a₂ a₃ a₄ ∧
        ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI a₀ (a₀ * t + a₁)
            (a₀ * t ^ 2 + 2 * a₁ * t + a₂)
            (a₀ * t ^ 3 + 3 * a₁ * t ^ 2 + 3 * a₂ * t + a₃)
            (a₀ * t ^ 4 + 4 * a₁ * t ^ 3 + 6 * a₂ * t ^ 2 + 4 * a₃ * t + a₄) =
          ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI a₀ a₁ a₂ a₃ a₄ ∧
        ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ a₀ (a₀ * t + a₁)
            (a₀ * t ^ 2 + 2 * a₁ * t + a₂)
            (a₀ * t ^ 3 + 3 * a₁ * t ^ 2 + 3 * a₂ * t + a₃)
            (a₀ * t ^ 4 + 4 * a₁ * t ^ 3 + 6 * a₂ * t ^ 2 + 4 * a₃ * t + a₄) =
          ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ a₀ a₁ a₂ a₃ a₄) ∧
      (∀ a₀ a₁ a₂ a₃ a₄ α β γ δ : ℝ, α * δ - β * γ = 1 →
        let c₀ := a₀ * α ^ 4 + 4 * a₁ * α ^ 3 * γ + 6 * a₂ * α ^ 2 * γ ^ 2 +
          4 * a₃ * α * γ ^ 3 + a₄ * γ ^ 4
        let c₁ := a₀ * α ^ 3 * β + a₁ * α ^ 3 * δ + 3 * a₁ * α ^ 2 * β * γ +
          3 * a₂ * α ^ 2 * γ * δ + 3 * a₂ * α * β * γ ^ 2 + 3 * a₃ * α * γ ^ 2 * δ +
          a₃ * β * γ ^ 3 + a₄ * γ ^ 3 * δ
        let c₂ := a₀ * α ^ 2 * β ^ 2 + 2 * a₁ * α ^ 2 * β * δ + 2 * a₁ * α * β ^ 2 * γ +
          a₂ * α ^ 2 * δ ^ 2 + 4 * a₂ * α * β * γ * δ + a₂ * β ^ 2 * γ ^ 2 +
          2 * a₃ * α * γ * δ ^ 2 + 2 * a₃ * β * γ ^ 2 * δ + a₄ * γ ^ 2 * δ ^ 2
        let c₃ := a₀ * α * β ^ 3 + 3 * a₁ * α * β ^ 2 * δ + a₁ * β ^ 3 * γ +
          3 * a₂ * α * β * δ ^ 2 + 3 * a₂ * β ^ 2 * γ * δ + a₃ * α * δ ^ 3 +
          3 * a₃ * β * γ * δ ^ 2 + a₄ * γ * δ ^ 3
        let c₄ := a₀ * β ^ 4 + 4 * a₁ * β ^ 3 * δ + 6 * a₂ * β ^ 2 * δ ^ 2 +
          4 * a₃ * β * δ ^ 3 + a₄ * δ ^ 4
        ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI c₀ c₁ c₂ c₃ c₄ =
            ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI a₀ a₁ a₂ a₃ a₄ ∧
          ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ c₀ c₁ c₂ c₃ c₄ =
            ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ a₀ a₁ a₂ a₃ a₄) ∧
      (∀ a₀ a₁ a₂ a₃ a₄ u v : ℝ,
        ErlangenProgramCurvatureBinaryAndMasterAtlas.binQuarticSexticCovariant
            a₀ a₁ a₂ a₃ a₄ u v ^ 2 +
          4 * ErlangenProgramCurvatureBinaryAndMasterAtlas.binQuarticHessian
            a₀ a₁ a₂ a₃ a₄ u v ^ 3 -
          ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI a₀ a₁ a₂ a₃ a₄ *
            ErlangenProgramCurvatureBinaryAndMasterAtlas.binQuarticHessian a₀ a₁ a₂ a₃ a₄ u v *
            ErlangenProgramCurvatureBinaryAndMasterAtlas.binQuartic a₀ a₁ a₂ a₃ a₄ u v ^ 2 +
          ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ a₀ a₁ a₂ a₃ a₄ *
            ErlangenProgramCurvatureBinaryAndMasterAtlas.binQuartic a₀ a₁ a₂ a₃ a₄ u v ^ 3 = 0) ∧
      ((ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI (0 : ℝ) 0 0 0 0 = 0 ∧
          ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ (0 : ℝ) 0 0 0 0 = 0) ∧
        (∀ μ : ℝ,
          ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI (1 : ℝ) 0 μ 0 1 = 1 + 3 * μ ^ 2 ∧
          ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI (1 : ℝ) 0 μ 0 1 ≠ 0))) ∧
    (turnsAroundFixedSphere R r = 4 ↔ R = 3 * r) ∧
    (∀ (D : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations) (t : ℝ),
      ∃ F : InfoGeometry.Canonical.RealSplitOctonionAut,
        (F : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) =
          InfoGeometry.Lie.CanonicalZornDerivationExponential.zornFlowLinearEquiv D.1 t) := by
  refine ⟨⟨finrank_g2LieSubalgebra, parameter_model_is_fourteen_dimensional⟩,
    ⟨?_, g2Zpos2_ne_zero, fun X hX => (g2Submodule_mem_stabilizer hX).1⟩,
    ⟨?_, ?_, ErlangenProgramCurvatureBinaryAndMasterAtlas.cayley_binary_quartic_syzygy,
      ⟨⟨?_, ?_⟩, ?_⟩⟩,
    four_turns_iff_radius_three_times hr,
    split_g2_derivation_exponential_is_real_automorphism⟩
  · have h := g2_five_grading_and_cartan.2.1 0
    simpa [g2Basis, g2Grade] using h
  · intro a₀ a₁ a₂ a₃ a₄ t
    have hcov := binary_quartic_sl2_covariance a₀ a₁ a₂ a₃ a₄ 0 0 t 1 0 0 1
    exact ⟨hcov.1.2.1, hcov.1.2.2, hcov.2.1.2.1, hcov.2.1.2.2⟩
  · intro a₀ a₁ a₂ a₃ a₄ α β γ δ hdet
    have hcov := binary_quartic_sl2_covariance a₀ a₁ a₂ a₃ a₄ 0 0 0 α β γ δ
    refine ⟨?_, ?_⟩
    · rw [hcov.2.2.2.1, hdet, one_pow, one_mul]
    · rw [hcov.2.2.2.2, hdet, one_pow, one_mul]
  · dsimp [ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI]; ring
  · dsimp [ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvJ]; ring
  · intro μ
    have hval : ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI (1 : ℝ) 0 μ 0 1 =
        1 + 3 * μ ^ 2 := by
      dsimp [ErlangenProgramCurvatureBinaryAndMasterAtlas.quarticInvI]; ring
    refine ⟨hval, ?_⟩
    rw [hval]
    nlinarith [sq_nonneg μ]

end Cartan235AndSplitG2

/-! ## Section 6: Zorn (1930–1933) — Alternative/Moufang Laws & Split-Octonions (`S2-10`) -/

section ZornAlternativeAndSplitOctonions

/-- **Zorn (`S2-10` 1930, 1933; `R3.2`, `R3.4`)**:
canonical linear equivalence identifying `SplitOctonionZorn.SplitOctonion` with
`ZornVectorMatrix ℝ`. -/
def splitOctonionToZornVectorEquiv : SplitOctonion ≃ₗ[ℝ] ZornVectorMatrix ℝ where
  toFun X := ⟨X.a, ![X.u.x, X.u.y, X.u.z], ![X.v.x, X.v.y, X.v.z], X.d⟩
  invFun X := ⟨X.a, ⟨X.v 0, X.v 1, X.v 2⟩, ⟨X.w 0, X.w 1, X.w 2⟩, X.b⟩
  map_add' X Y := by
    apply ZornVectorMatrix.ext <;> try rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  map_smul' c X := by
    apply ZornVectorMatrix.ext <;> try rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  left_inv X := by
    cases X; rename_i a u v d; cases u; cases v; rfl
  right_inv X := by
    cases X
    apply ZornVectorMatrix.ext <;> try rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl

/-- **Zorn (`S2-10` 1930, 1933; `R3.2`, `R3.4`)**:
`splitOctonionToZornVectorEquiv` preserves multiplication, unit `1`, conjugation, and the
split `(4, 4)` norm (`ZornVectorMatrix.norm = SplitOctonion.zornDet`). -/
theorem splitOctonionToZornVectorEquiv_preserves_structure (X Y : SplitOctonion) :
    splitOctonionToZornVectorEquiv (X * Y) =
      ZornVectorMatrix.mul (splitOctonionToZornVectorEquiv X)
        (splitOctonionToZornVectorEquiv Y) ∧
    splitOctonionToZornVectorEquiv 1 = ZornVectorMatrix.one ∧
    splitOctonionToZornVectorEquiv (SplitOctonion.conj X) =
      ZornVectorMatrix.conj (splitOctonionToZornVectorEquiv X) ∧
    ZornVectorMatrix.norm (splitOctonionToZornVectorEquiv X) = SplitOctonion.zornDet X := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ZornVectorMatrix.ext
    · simp [splitOctonionToZornVectorEquiv, ZornVectorMatrix.mul, ZornVec3.dot,
        Fin.sum_univ_three]
      change X.a * Y.a + (X.u.x * Y.v.x + X.u.y * Y.v.y + X.u.z * Y.v.z) =
        X.a * Y.a + (X.u.x * Y.v.x + X.u.y * Y.v.y + X.u.z * Y.v.z)
      rfl
    · funext i
      fin_cases i <;>
        simp [splitOctonionToZornVectorEquiv, ZornVectorMatrix.mul, ZornVec3.cross] <;>
        rfl
    · funext i
      fin_cases i <;>
        simp [splitOctonionToZornVectorEquiv, ZornVectorMatrix.mul, ZornVec3.cross] <;>
        rfl
    · simp [splitOctonionToZornVectorEquiv, ZornVectorMatrix.mul, ZornVec3.dot,
        Fin.sum_univ_three]
      change X.d * Y.d + (X.v.x * Y.u.x + X.v.y * Y.u.y + X.v.z * Y.u.z) =
        X.v.x * Y.u.x + X.v.y * Y.u.y + X.v.z * Y.u.z + X.d * Y.d
      ring
  · apply ZornVectorMatrix.ext <;> try rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  · apply ZornVectorMatrix.ext <;> try rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  · simp [splitOctonionToZornVectorEquiv, ZornVectorMatrix.norm, ZornVec3.dot,
      Fin.sum_univ_three, SplitOctonion.zornDet, Vector3.dot]

/-- **Zorn (`S2-10` 1930, 1933; `R3.2`, `R3.4`)**:
Teichmüller identity, left/right alternative & flexible laws, and left/right/middle Moufang
identities on `ZornVectorMatrix R` over any `[CommRing R]`. -/
theorem zorn_1930_1933_alternative_and_moufang_laws {R : Type*} [CommRing R]
    (w X Y Z : ZornVectorMatrix R) :
    (associator (w * X) Y Z - associator w (X * Y) Z + associator w X (Y * Z) =
        w * associator X Y Z + associator w X Y * Z) ∧
      ((X * X) * Y = X * (X * Y) ∧ (Y * X) * X = Y * (X * X) ∧ (X * Y) * X = X * (Y * X)) ∧
      ((X * Y) * (Z * X) = X * ((Y * Z) * X) ∧
        Z * (X * (Z * Y)) = ((Z * X) * Z) * Y ∧
        ((Y * X) * Z) * X = Y * (X * (Z * X))) := by
  refine ⟨teichmueller_identity w X Y Z,
    ⟨sub_eq_zero.mp (ZornVectorMatrix.associator_left_alternative X Y),
      sub_eq_zero.mp (ZornVectorMatrix.associator_right_alternative Y X), ?_⟩,
    ⟨ZornVectorMatrix.middle_moufang X Y Z,
      ZornVectorMatrix.left_moufang X Y Z,
      ZornVectorMatrix.right_moufang X Y Z⟩⟩
  exact sub_eq_zero.mp (ZornVectorMatrix.associator_flexible X Y)

/-- **Zorn (`S2-10` 1930, 1933; `R3.2`, `R3.4`)**:
left/right alternative and middle Moufang laws transported directly onto `SplitOctonion`. -/
theorem splitOctonion_alternative_and_moufang (X Y Z : SplitOctonion) :
    (X * X) * Y = X * (X * Y) ∧
      (Y * X) * X = Y * (X * X) ∧
      (X * Y) * (Z * X) = X * ((Y * Z) * X) := by
  have hmul := fun A B => (splitOctonionToZornVectorEquiv_preserves_structure A B).1
  refine ⟨?_, ?_, ?_⟩
  · apply splitOctonionToZornVectorEquiv.injective
    rw [hmul, hmul, hmul, hmul]
    exact sub_eq_zero.mp (ZornVectorMatrix.associator_left_alternative _ _)
  · apply splitOctonionToZornVectorEquiv.injective
    rw [hmul, hmul, hmul, hmul]
    exact sub_eq_zero.mp (ZornVectorMatrix.associator_right_alternative _ _)
  · apply splitOctonionToZornVectorEquiv.injective
    rw [hmul, hmul, hmul, hmul, hmul, hmul]
    exact ZornVectorMatrix.middle_moufang _ _ _

/-- **Zorn (`S2-10` 1933; `R3.2`)**:
standard upper off-diagonal basis unit `u₀ ∈ SplitOctonion`. -/
def splitOctonionU0 : SplitOctonion :=
  ⟨0, ⟨1, 0, 0⟩, Vector3.zero, 0⟩

/-- **Zorn (`S2-10` 1933; `R3.2`)**:
standard upper off-diagonal basis unit `u₁ ∈ SplitOctonion`. -/
def splitOctonionU1 : SplitOctonion :=
  ⟨0, ⟨0, 1, 0⟩, Vector3.zero, 0⟩

/-- **Zorn (`S2-10` 1933; `R3.2`)**:
standard upper off-diagonal basis unit `u₂ ∈ SplitOctonion`. -/
def splitOctonionU2 : SplitOctonion :=
  ⟨0, ⟨0, 0, 1⟩, Vector3.zero, 0⟩

/-- **Zorn (`S2-10` 1933; `R3.2`)**:
explicit 3-element non-associativity witness on `SplitOctonion`:
`(u₀ * u₁) * u₂ ≠ u₀ * (u₁ * u₂)` (matching `(0 : ℝ) ≠ 1` in the `d` entry). -/
theorem splitOctonion_nonassociative_witness :
    (splitOctonionU0 * splitOctonionU1) * splitOctonionU2 ≠
      splitOctonionU0 * (splitOctonionU1 * splitOctonionU2) := by
  intro h
  have hd : ((splitOctonionU0 * splitOctonionU1) * splitOctonionU2).d =
      (splitOctonionU0 * (splitOctonionU1 * splitOctonionU2)).d :=
    congrArg SplitOctonion.d h
  change ((splitOctonionU0.mul splitOctonionU1).mul splitOctonionU2).d =
      (splitOctonionU0.mul (splitOctonionU1.mul splitOctonionU2)).d at hd
  dsimp [SplitOctonion.mul, splitOctonionU0, splitOctonionU1, splitOctonionU2,
    Vector3.zero, Vector3.add, Vector3.sub, Vector3.smul, Vector3.dot, Vector3.cross] at hd
  norm_num at hd

/-- **Zorn (`S2-10` 1930, 1933; `R3.2`, `R3.4`)**:
master split-octonion synthesis uniting:
1. Multiplicative split `(4, 4)` norm on `SplitOctonion` and `ofBasis8`.
2. Two-sided adjugate inverse `X * conj X = zornDet X • 1 = conj X * X`.
3. Zero-divisor witnesses across `SplitOctonion`, `ZornVectorMatrix ℝ`, and `Exceptional.ZornMatrix`.
4. 3-element non-associativity witnesses on both `SplitOctonion` and `ZornVectorMatrix ℝ`.
5. Zorn (1930) Viereridentität, Peirce Zweierregeln, Lagrange identity, and `zornStanDerivation`. -/
theorem zorn_split_octonion_master_laws (X Y : SplitOctonion)
    (x0 x1 x2 x3 x4 x5 x6 x7 : ℝ)
    (A B C D : ZornVectorMatrix ℝ) :
    (SplitOctonion.zornDet (X * Y) = SplitOctonion.zornDet X * SplitOctonion.zornDet Y ∧
      SplitOctonion.zornDet (SplitOctonion.ofBasis8 x0 x1 x2 x3 x4 x5 x6 x7) =
        x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 - x4 ^ 2 - x5 ^ 2 - x6 ^ 2 - x7 ^ 2) ∧
    (X * SplitOctonion.conj X = SplitOctonion.zornDet X • (1 : SplitOctonion) ∧
      SplitOctonion.conj X * X = SplitOctonion.zornDet X • (1 : SplitOctonion)) ∧
    ((SplitOctonion.idempotentE1 ≠ 0 ∧ SplitOctonion.idempotentE2 ≠ 0 ∧
        SplitOctonion.idempotentE1 * SplitOctonion.idempotentE2 = 0) ∧
      ZornVectorMatrix.mul (ZornVectorMatrix.E11 : ZornVectorMatrix ℝ) ZornVectorMatrix.E22 =
        ZornVectorMatrix.zero ∧
      (InfoGeometry.Exceptional.witnessA * InfoGeometry.Exceptional.witnessB = 0 ∧
        InfoGeometry.Exceptional.witnessA ≠ 0 ∧ InfoGeometry.Exceptional.witnessB ≠ 0)) ∧
    ((splitOctonionU0 * splitOctonionU1) * splitOctonionU2 ≠
        splitOctonionU0 * (splitOctonionU1 * splitOctonionU2) ∧
      ZornVectorMatrix.mul (ZornVectorMatrix.mul (ZornVectorMatrix.U 0 : ZornVectorMatrix ℝ)
        (ZornVectorMatrix.U 1)) (ZornVectorMatrix.U 2) ≠
        ZornVectorMatrix.mul (ZornVectorMatrix.U 0)
          (ZornVectorMatrix.mul (ZornVectorMatrix.U 1) (ZornVectorMatrix.U 2))) ∧
    ((associator (A * B) C D - associator A (B * C) D + associator A B (C * D) =
        A * associator B C D + associator A B C * D) ∧
      (ZornVectorMatrix.zornPeirce12 A * ZornVectorMatrix.zornPeirce12 B +
          ZornVectorMatrix.zornPeirce12 B * ZornVectorMatrix.zornPeirce12 A = 0 ∧
        ZornVectorMatrix.zornPeirce12 A * ZornVectorMatrix.zornPeirce12 A = 0) ∧
      (zornStanDerivation A B) C =
        (A * B - B * A) * C - C * (A * B - B * A) - 3 • ZornVectorMatrix.associator A B C) := by
  refine ⟨⟨SplitOctonion.zornDet_mul X Y, SplitOctonion.zornDet_ofBasis8 x0 x1 x2 x3 x4 x5 x6 x7⟩,
    ⟨SplitOctonion.mul_conj_eq_det_smul_one X, SplitOctonion.conj_mul_eq_det_smul_one X⟩,
    ⟨SplitOctonion.zero_divisor_witness, ZornVectorMatrix.E11_mul_E22,
      InfoGeometry.Exceptional.split_octonions_have_zero_divisors⟩,
    ⟨splitOctonion_nonassociative_witness, ZornVectorMatrix.nonassociative_witness⟩,
    ⟨teichmueller_identity A B C D, ?_, ?_⟩⟩
  · have hz := ZornVectorMatrix.zorn_1930_peirce_zweierregeln_and_scalar_pullthrough A B C
    exact ⟨hz.2.1, hz.2.2.1⟩
  · exact zornStanDerivation_apply_normal_form A B C

end ZornAlternativeAndSplitOctonions

/-! ## Section 7: Master Pillar Synthesis (`S2-05`..`S2-10`) -/

section Synthesis

/-- **Master Pillar Synthesis (`S2-05`..`S2-10`, `R3.2`, `R3.4`)**:
unifies Lie's `(3,3) ↔ (3,2)` line-sphere signature relation, Klein's antitone Erlanger lattice
(plus strict `SO(Q)` top-blade expansion) and Cayley–Klein `(n+1)`-dim signature trichotomy,
Darboux–Pfaff algebraic class & Lie-closed characteristic subspace (`BUCKET 1`), Cartan's
`(2,3,5)` Pfaffian & split `g_{2(2)}` Tanaka filtration (`g2X4 * g2F0 ≠ g2F0 * g2X4`), and Zorn's
alternative/Moufang split-octonion laws. -/
theorem lie_klein_pfaff_cartan_zorn_synthesis :
    (sigPos (kleinQuadricForm ℝ) = 3 ∧ sigNeg (kleinQuadricForm ℝ) = 3 ∧
      sigPos ((kleinQuadricForm ℝ).restrict lieComplexHyperplane) = 3 ∧
      sigNeg ((kleinQuadricForm ℝ).restrict lieComplexHyperplane) = 2) ∧
    ((∀ (G M : Type) [Group G] [MulAction G M] {H K : Subgroup G},
        H ≤ K → invariantPredicateSet G M K ⊆ invariantPredicateSet G M H) ∧
      (∀ {n : ℕ}, 1 ≤ n → ∀ Q : QuadraticForm ℝ (Fin n → ℝ),
        (∀ x : CliffordAlgebra Q, IsInvariant (cliffordSymmetryAction Q) x →
          ∀ f ∈ specialIsometrySubgroup Q, CliffordAlgebra.equivOfIsometry f x = x) ∧
        ∃ ω : CliffordAlgebra Q,
          (∀ f ∈ specialIsometrySubgroup Q, CliffordAlgebra.equivOfIsometry f ω = ω) ∧
          ¬ IsInvariant (cliffordSymmetryAction Q) ω)) ∧
    (∀ (n : ℕ) (κ : ℝ),
      (0 < κ → sigPos (cayleyKleinProjQuadForm n κ) = n + 1) ∧
      (κ < 0 → sigPos (cayleyKleinProjQuadForm n κ) = 1 ∧
        sigNeg (cayleyKleinProjQuadForm n κ) = n) ∧
      (κ = 0 → sigPos (cayleyKleinProjQuadForm n κ) = 1 ∧
        Module.finrank ℝ (cayleyKleinProjQuadForm n κ).radical = n)) ∧
    ((HasPfaffClassOdd (smoothJetDerivationLane 2).toLieActionLane (contactCEOneForm 2) 2 ∧
        pfaffCharacteristicSubspace (smoothJetDerivationLane 2).toLieActionLane
          (contactCEOneForm 2) = ⊥) ∧
      (∀ (R A : Type) [CommRing R] [AddCommGroup A] [Module R A]
          (K : LieActionLane R A) (ω : ActionOperatorForm K 1) (x y : K.L),
        x ∈ pfaffCharacteristicSubspace K ω →
        y ∈ pfaffCharacteristicSubspace K ω →
        letI := K.lieRing
        ⁅x, y⁆ ∈ pfaffCharacteristicSubspace K ω)) ∧
    (Module.finrank ℝ (LinearMap.ker cartan235DerivedTest1) = 2 ∧
      Module.finrank ℝ (LinearMap.ker cartan235DerivedTest2) = 0 ∧
      Module.finrank ℝ cartan235Symbol1 = 2 ∧
      Module.finrank ℝ cartan235Symbol2 = 3 ∧
      Module.finrank ℝ cartan235Symbol3 = 5 ∧
      g2X4 * g2F0 ≠ g2F0 * g2X4) ∧
    ((∀ X Y Z : SplitOctonion,
        (X * X) * Y = X * (X * Y) ∧
        (Y * X) * X = Y * (X * X) ∧
        (X * Y) * (Z * X) = X * ((Y * Z) * X)) ∧
      (splitOctonionU0 * splitOctonionU1) * splitOctonionU2 ≠
        splitOctonionU0 * (splitOctonionU1 * splitOctonionU2) ∧
      SplitOctonion.idempotentE1 * SplitOctonion.idempotentE2 = 0) := by
  refine ⟨⟨lie_line_sphere_hyperplane_signature_relation.1.1,
      lie_line_sphere_hyperplane_signature_relation.1.2,
      lie_line_sphere_hyperplane_signature_relation.2.1.1,
      lie_line_sphere_hyperplane_signature_relation.2.1.2⟩,
    ⟨fun _ _ _ _ _ _ hHK => invariantPredicateSet_antitone _ _ hHK,
      fun hn Q => clifford_so_strictly_enlarges_invariant_subalgebra hn Q⟩,
    fun n κ => ⟨fun h => (cayleyKleinProjQuadForm_signature_trichotomy n κ).1 h |>.1,
      fun h => ⟨(cayleyKleinProjQuadForm_signature_trichotomy n κ).2.1 h |>.1,
        (cayleyKleinProjQuadForm_signature_trichotomy n κ).2.1 h |>.2.1⟩,
      fun h => ⟨(cayleyKleinProjQuadForm_signature_trichotomy n κ).2.2 h |>.1,
        (cayleyKleinProjQuadForm_signature_trichotomy n κ).2.2 h |>.2.2⟩⟩,
    ⟨contactCEOneForm_odd_class_n2,
      fun _ _ _ _ _ K ω x y hx hy => (pfaffCharacteristicLieSubalgebra K ω).lie_mem hx hy⟩,
    ⟨cartan235_pfaff_derived_flag_ranks.2.2.1,
      cartan235_pfaff_derived_flag_ranks.2.2.2.2,
      cartan235_tanaka_symbol_growth_2_3_5.1,
      cartan235_tanaka_symbol_growth_2_3_5.2.1,
      cartan235_tanaka_symbol_growth_2_3_5.2.2.1,
      cartan235_tanaka_brackets.2.2.2⟩,
    ⟨splitOctonion_alternative_and_moufang,
      splitOctonion_nonassociative_witness, SplitOctonion.zero_divisor_witness.2.2⟩⟩

end Synthesis

end InfoGeometry.Erlangen.LieKleinPfaffCartanPrimary
