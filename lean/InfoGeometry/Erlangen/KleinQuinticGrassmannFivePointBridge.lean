/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Erlangen.KleinQuinticGrassmannPluckerBridge

/-!
# The Full Five-Root Grassmann–Plücker Configuration of a Quintic Resolvent

## i. Overview

The four-root bridge gives a Klein-quadric point after selecting four roots.
Here all five squared orbit roots are retained at once. The all-ones row and
the five-root row give a decomposable 2-vector in `Λ² ℂ⁵`; when two roots
differ, it is nonzero and therefore defines a point of `Gr(2,5)`. Its ten
oriented 2-by-2 minors form an antisymmetric matrix satisfying every
four-index Plücker relation. Restricting to any four indices recovers the
existing `Plucker6` chart and hence a point on the Klein quadric.

## ii. Key results

- `quinticGrassmannFiveRootMinor_smul`: degree-2 homogeneity of every
  `Gr(2,5)` Plücker minor under coefficient scaling.
- `quinticGrassmannFiveRootVector` and
  `quinticGrassmannFiveRootProjective_smul`: full ten-coordinate bivector
  in `Λ² ℂ⁵` and guarded projective invariance off the zero-bivector base
  locus (`hnonconst`).
- `quinticGrassmannFiveRootRestriction_eq_existing` and
  `quinticGrassmannFiveRootRestriction_on_klein`: four-column restriction to
  `Plucker6` and Klein-quadric membership.

## iii. Table of contents

- Five-root `Gr(2,5)` chart, minors, scaling, and guarded projectivization.
- Antisymmetry, diagonal vanishing, and four-index Plücker relations.
- Four-column restrictions to `Plucker6` and generator covariance.

## iv. References

- `InfoGeometry.Erlangen.KleinQuinticGrassmannPluckerBridge`
- `InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent`
- `InfoGeometry.Erlangen.KleinQuinticTschirnhausKleinCovariant`
-/

noncomputable section

namespace InfoGeometry.Erlangen.KleinQuinticGrassmannFivePointBridge

open InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent
open InfoGeometry.Erlangen.KleinQuinticGrassmannPluckerBridge
open InfoGeometry.Projective.KleinQuadricPlucker

/-- The full five-root row chart in `Gr(2,5)`: its rows are the all-ones
vector and the five squared Klein-orbit evaluations. -/
def quinticGrassmannFiveRootChart (v : BinaryQuinticCoefficientSpace)
    (z : ℂ × ℂ) : Matrix (Fin 2) (Fin 5) ℂ :=
  fun i j => if i = 0 then 1 else binaryQuinticResolventTuple v z j

/-- The oriented Plücker minor for the pair `(i,j)` of columns of the full
five-root chart. The ten entries with `i < j` are the independent
`Gr(2,5)` Plücker coordinates; the reversed entries are their negatives. -/
def quinticGrassmannFiveRootMinor (v : BinaryQuinticCoefficientSpace)
    (z : ℂ × ℂ) (i j : Fin 5) : ℂ :=
  binaryQuinticResolventTuple v z j - binaryQuinticResolventTuple v z i

/-- The ten Plücker coordinates are literally the 2-by-2 minors of the
five-column chart, with no change of root or coordinate convention. -/
theorem quinticGrassmannFiveRootMinor_eq_chart_minor
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) (i j : Fin 5) :
    quinticGrassmannFiveRootChart v z 0 i *
        quinticGrassmannFiveRootChart v z 1 j -
      quinticGrassmannFiveRootChart v z 0 j *
        quinticGrassmannFiveRootChart v z 1 i =
      quinticGrassmannFiveRootMinor v z i j := by
  simp [quinticGrassmannFiveRootChart, quinticGrassmannFiveRootMinor]

/-- Distinct roots give a nonzero minor, so the two rows of the five-root
chart are linearly independent and the decomposable 2-vector is nonzero. -/
theorem quinticGrassmannFiveRootMinor_ne_zero
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) (i j : Fin 5)
    (hij : binaryQuinticResolventTuple v z i ≠
      binaryQuinticResolventTuple v z j) :
    quinticGrassmannFiveRootMinor v z i j ≠ 0 := by
  simp only [quinticGrassmannFiveRootMinor]
  exact sub_ne_zero.mpr (Ne.symm hij)

/-- If two resolvent roots differ, the two rows of the five-column chart are
linearly independent: no scalar combination vanishes in every coordinate
unless both coefficients vanish. -/
theorem quinticGrassmannFiveRootChart_rows_independent
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) (i j : Fin 5)
    (hij : binaryQuinticResolventTuple v z i ≠
      binaryQuinticResolventTuple v z j) (a b : ℂ)
    (hzero : ∀ k : Fin 5,
      a * quinticGrassmannFiveRootChart v z 0 k +
        b * quinticGrassmannFiveRootChart v z 1 k = 0) :
    a = 0 ∧ b = 0 := by
  have hi := hzero i
  have hj := hzero j
  have hb_mul : b * (binaryQuinticResolventTuple v z i -
      binaryQuinticResolventTuple v z j) = 0 := by
    calc
      b * (binaryQuinticResolventTuple v z i -
          binaryQuinticResolventTuple v z j) =
        (a * quinticGrassmannFiveRootChart v z 0 i +
            b * quinticGrassmannFiveRootChart v z 1 i) -
          (a * quinticGrassmannFiveRootChart v z 0 j +
            b * quinticGrassmannFiveRootChart v z 1 j) := by
              simp [quinticGrassmannFiveRootChart]
              ring
      _ = 0 := by rw [hi, hj]; ring
  have hroot : binaryQuinticResolventTuple v z i -
      binaryQuinticResolventTuple v z j ≠ 0 := sub_ne_zero.mpr hij
  have hb : b = 0 := (mul_eq_zero.mp hb_mul).resolve_right hroot
  refine ⟨?_, hb⟩
  have hi' := hzero i
  simpa [quinticGrassmannFiveRootChart, hb] using hi'

/-- The five-root Plücker matrix is antisymmetric. -/
theorem quinticGrassmannFiveRootMinor_skew
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) (i j : Fin 5) :
    quinticGrassmannFiveRootMinor v z j i =
      -quinticGrassmannFiveRootMinor v z i j := by
  simp [quinticGrassmannFiveRootMinor]

/-- The diagonal Plücker minors vanish. -/
theorem quinticGrassmannFiveRootMinor_diag
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) (i : Fin 5) :
    quinticGrassmannFiveRootMinor v z i i = 0 := by
  simp [quinticGrassmannFiveRootMinor]

/-- All five four-index Plücker equations hold for the complete
`Gr(2,5)` configuration. This is the decomposability relation for the
2-vector formed by wedging the two rows of the five-column chart. -/
theorem quinticGrassmannFiveRootMinor_plucker_relation
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ)
    (i j k l : Fin 5) :
    quinticGrassmannFiveRootMinor v z i j *
        quinticGrassmannFiveRootMinor v z k l -
      quinticGrassmannFiveRootMinor v z i k *
        quinticGrassmannFiveRootMinor v z j l +
      quinticGrassmannFiveRootMinor v z i l *
        quinticGrassmannFiveRootMinor v z j k = 0 := by
  simp only [quinticGrassmannFiveRootMinor]
  ring

/-- Restrict the full five-root configuration to four selected columns,
retaining the standard `01,02,03,12,13,23` Klein coordinate order. -/
def quinticGrassmannFiveRootRestriction (v : BinaryQuinticCoefficientSpace)
    (z : ℂ × ℂ) (pick : Fin 4 → Fin 5) : Plucker6 ℂ where
  p01 := quinticGrassmannFiveRootMinor v z (pick 0) (pick 1)
  p02 := quinticGrassmannFiveRootMinor v z (pick 0) (pick 2)
  p03 := quinticGrassmannFiveRootMinor v z (pick 0) (pick 3)
  p12 := quinticGrassmannFiveRootMinor v z (pick 1) (pick 2)
  p13 := quinticGrassmannFiveRootMinor v z (pick 1) (pick 3)
  p23 := quinticGrassmannFiveRootMinor v z (pick 2) (pick 3)

/-- Every four-column restriction of the full `Gr(2,5)` Plücker data is
exactly the existing four-root quintic `Plucker6` construction. -/
theorem quinticGrassmannFiveRootRestriction_eq_existing
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ)
    (pick : Fin 4 → Fin 5) :
    quinticGrassmannFiveRootRestriction v z pick =
      binaryQuinticResolventPlucker6 v z pick := by
  apply Plucker6.ext <;>
    simp [quinticGrassmannFiveRootRestriction, quinticGrassmannFiveRootMinor,
      binaryQuinticResolventPlucker6, resolventGrassmannRows,
      resolventSubconfiguration, Plucker6.pluckerLine]

/-- Consequently, each four-root restriction of the full configuration lies
on Klein's quadric. The ten coordinates are not five unrelated Klein points:
they are restrictions of one `Gr(2,5)` decomposable 2-vector. -/
theorem quinticGrassmannFiveRootRestriction_on_klein
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ)
    (pick : Fin 4 → Fin 5) :
    Plucker6.kleinQ (quinticGrassmannFiveRootRestriction v z pick) = 0 := by
  rw [quinticGrassmannFiveRootRestriction_eq_existing]
  exact binaryQuinticResolventPlucker6_on_klein v z pick

/-- The full five-root Plücker configuration is covariant under the
source-ordered order-ten generator: its central minus sign has disappeared
after squaring, and the remaining action is the owner's cyclic reindexing. -/
theorem quinticGrassmannFiveRootMinor_generator_covariant
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) (i j : Fin 5) :
    quinticGrassmannFiveRootMinor (binaryQuinticGenerator v) z i j =
      quinticGrassmannFiveRootMinor v z
        (kleinResolventCycleSucc i) (kleinResolventCycleSucc j) := by
  simp [quinticGrassmannFiveRootMinor, binaryQuinticResolventTuple_equivariant]

/-- Uniform scaling of the binary-quintic coefficient vector scales every
five-root `Gr(2,5)` Plücker minor by `c ^ 2`. -/
lemma quinticGrassmannFiveRootMinor_smul
    (c : ℂ) (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) (i j : Fin 5) :
    quinticGrassmannFiveRootMinor (c • v) z i j =
      c ^ 2 * quinticGrassmannFiveRootMinor v z i j := by
  unfold quinticGrassmannFiveRootMinor
  rw [binaryQuinticResolventTuple_smul]
  dsimp only
  rw [← mul_sub]

/-- Full ten-coordinate `Gr(2,5)` Plücker bivector of the five squared
resolvent roots, indexed by strictly increasing pairs `RootPair5` in
`Λ² ℂ⁵`. -/
noncomputable def quinticGrassmannFiveRootVector
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) :
    InfoGeometry.Erlangen.KleinQuinticTschirnhausKleinCovariant.RootPair5 →
      ℂ :=
  fun p => quinticGrassmannFiveRootMinor v z p.1.1 p.1.2

/-- Nonzero scalar rescaling of the binary-quintic coefficient vector leaves
the projective `Gr(2,5)` five-root bivector unchanged off the zero-bivector
base locus. The explicit `hnonconst` guard excludes the base locus where all
five squared orbit evaluations coincide. -/
lemma quinticGrassmannFiveRootProjective_smul
    (c : ℂ) (hc : c ≠ 0) (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ)
    (hnonconst : quinticGrassmannFiveRootVector v z ≠ 0) :
    Projectivization.mk ℂ (quinticGrassmannFiveRootVector (c • v) z)
        (by
          intro hzero
          apply hnonconst
          funext p
          have hp := congrFun hzero p
          dsimp [quinticGrassmannFiveRootVector] at hp ⊢
          rw [quinticGrassmannFiveRootMinor_smul] at hp
          exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero 2 hc)) =
      Projectivization.mk ℂ (quinticGrassmannFiveRootVector v z) hnonconst := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hvec : quinticGrassmannFiveRootVector (c • v) z =
      c ^ 2 • quinticGrassmannFiveRootVector v z := by
    funext p
    dsimp [quinticGrassmannFiveRootVector]
    rw [quinticGrassmannFiveRootMinor_smul]
  apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ hnonconst).2
  refine ⟨Units.mk0 (c ^ 2) hc2, ?_⟩
  rw [Units.smul_def, Units.val_mk0]
  exact hvec.symm

end InfoGeometry.Erlangen.KleinQuinticGrassmannFivePointBridge
