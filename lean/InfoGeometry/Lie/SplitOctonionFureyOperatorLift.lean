/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading
import InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
import InfoGeometry.Lie.SplitOctonionCircularZ3Grading
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplicationOperatorAlgebra
import InfoGeometry.Canonical.SplitOctonionAutomorphismOperatorBridge
import InfoGeometry.Lie.SplitOctonionCliffordAction
import InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation
import InfoGeometry.Lie.SplitOctonionStructurableKantor
import InfoGeometry.Lie.SplitOctonionEllStabilizer
import InfoGeometry.Lie.CanonicalZornG2CASReplay
import InfoGeometry.Algebra.ZornLeftCAR
import InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis
import Mathlib.Tactic

/-!
# Split-octonion multiplication operators and their associator obstruction

This is the operator-algebra readout of the split-octonion multiplication
used in the Furey-style multiplication-algebra construction.  The carrier
remains the native nonassociative real Zorn algebra.  Its left and right
regular multiplications live in the associative endomorphism algebra, where
their mixed commutator evaluates to the negative octonion associator.

Causal order, following the repository owners:

1. the Günaydin–Gürsey split-octonion Zorn carrier and quark basis, owned by
   `Canonical.GunaydinGurseyQuarkBasisBridge` and `Canonical.ZornWeylOperatorFockBridge`;
2. the finite split-`G₂` derivation generators, whose bracket constants have
   an exact CAS replay and an explicit alignment to the native root basis;
3. left and right regular multiplication on that already-defined carrier;
4. the derivation action of the split-`G₂` generators on both regular
   representations;
5. the left-composition and mixed-commutator defects as evaluations of the
   split-octonion associator, including a concrete nonzero root-sector
   obstruction in the zero-weight circular grade;
6. the Furey-style imaginary-space Clifford action inside the left
   multiplication algebra.

Thus the split-octonion algebra and its CAS-checked symmetry generators are
the input to the Furey-style operator construction, not consequences of it.

The division-octonion nested embeddings in Furey's paper are not asserted for
the split form.  In particular, this file does not turn the nonassociative
split-octonion carrier into an associative subalgebra of its endomorphisms.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionFureyOperatorLift

open InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading
open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
open InfoGeometry.Lie.SplitOctonionCircularZ3Grading
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.OperatorAlgebra.SplitOctonionLoxodromic
open InfoGeometry.OperatorAlgebra.SplitOctonionMultiplicationOperatorAlgebra
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
open InfoGeometry.Lie.SplitOctonionAxialPeirceTrifactor
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ

/-- Conjugation acts on endomorphisms by conjugating both the input and
output. Since split-octonion conjugation is an involution, this is the
operator-algebra counterpart of transporting regular multiplication across
the conjugation anti-automorphism. -/
def conjugateEnd (T : EndCZ) : EndCZ :=
  InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear.comp
    (T.comp
      InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear)

@[simp] theorem canonicalConjLinear_involutive (x : CZ) :
    InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
      (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear x) = x := by
  change InfoGeometry.Lie.SplitOctonionImaginaryAction.canonicalConj
      (InfoGeometry.Lie.SplitOctonionImaginaryAction.canonicalConj x) = x
  exact InfoGeometry.Lie.SplitOctonionStructurableKantor.canonicalConj_involutive x

theorem conjugateEnd_add (S T : EndCZ) :
    conjugateEnd (S + T) = conjugateEnd S + conjugateEnd T := by
  apply LinearMap.ext
  intro x
  change InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
      (S (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear x) +
        T (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear x)) =
    InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
        (S (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear x)) +
      InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
        (T (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear x))
  rw [map_add]

theorem conjugateEnd_smul (r : ℝ) (T : EndCZ) :
    conjugateEnd (r • T) = r • conjugateEnd T := by
  apply LinearMap.ext
  intro x
  change InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
      (r • T (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear x)) =
    r • InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
      (T (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear x))
  rw [map_smul]

theorem conjugateEnd_one : conjugateEnd (1 : EndCZ) = 1 := by
  apply LinearMap.ext
  intro x
  exact canonicalConjLinear_involutive x

/-- Conjugation of operators is an involution, making the left/right
regular exchange a reversible transport. -/
theorem conjugateEnd_involutive (T : EndCZ) :
    conjugateEnd (conjugateEnd T) = T := by
  apply LinearMap.ext
  intro x
  change InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
      (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
        (T (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
          (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear x)))) = T x
  rw [canonicalConjLinear_involutive x, canonicalConjLinear_involutive (T x)]

theorem conjugateEnd_mul (S T : EndCZ) :
    conjugateEnd (S * T) = conjugateEnd S * conjugateEnd T := by
  apply LinearMap.ext
  intro x
  change InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
      (S (T (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear x))) =
    InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
      (S (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
        (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
          (T (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear x)))))
  rw [canonicalConjLinear_involutive]

/-- Canonical conjugation exchanges left and right regular multiplication:
`C ∘ L_a ∘ C = R_{C(a)}`. This identity uses anti-multiplicativity and
involutivity of conjugation, not associativity of the split-octonion product. -/
theorem conjugateEnd_leftRegular (a : CZ) :
    conjugateEnd (leftRegular a) =
      rightRegular
        (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear a) := by
  apply LinearMap.ext
  intro x
  change InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
      (leftRegular a
        (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear x)) =
    rightRegular
      (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear a) x
  change InfoGeometry.Lie.SplitOctonionImaginaryAction.canonicalConj
      (a * InfoGeometry.Lie.SplitOctonionImaginaryAction.canonicalConj x) =
    x * InfoGeometry.Lie.SplitOctonionImaginaryAction.canonicalConj a
  rw [InfoGeometry.Lie.SplitOctonionStructurableKantor.canonicalConj_mul,
    InfoGeometry.Lie.SplitOctonionStructurableKantor.canonicalConj_involutive]

/-- The reverse conjugation transport exchanges right and left regular
multiplication. -/
theorem conjugateEnd_rightRegular (a : CZ) :
    conjugateEnd (rightRegular a) =
      leftRegular
        (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear a) := by
  apply LinearMap.ext
  intro x
  change InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
      (rightRegular a
        (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear x)) =
    leftRegular
      (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear a) x
  change InfoGeometry.Lie.SplitOctonionImaginaryAction.canonicalConj
      (InfoGeometry.Lie.SplitOctonionImaginaryAction.canonicalConj x * a) =
    InfoGeometry.Lie.SplitOctonionImaginaryAction.canonicalConj a * x
  rw [InfoGeometry.Lie.SplitOctonionStructurableKantor.canonicalConj_mul,
    InfoGeometry.Lie.SplitOctonionStructurableKantor.canonicalConj_involutive]

/-- The Lie and operator-algebra owners use the same native split-Zorn
carrier: their left regular operators agree pointwise. -/
theorem leftRegular_eq_zMulLinear (x : CZ) :
    leftRegular x = zMulLinear x := by
  apply LinearMap.ext
  intro y
  rfl

/-- The Lie-side left regular operators belong to the existing associative
subalgebra generated by all split-Zorn left multiplications. -/
theorem leftRegular_mem_multiplicationAlgebra (x : CZ) :
    leftRegular x ∈ leftMultiplicationAlgebra := by
  rw [leftRegular_eq_zMulLinear]
  exact leftMultiplication_mem x

/-- The native Clifford representation on split octonions has image inside
the associative algebra generated by split-octonion left multiplication.
The generator step uses the explicit carrier identification
`imaginaryLeftMul X = leftRegular X.1`; the extension to every Clifford
element follows from the universal generating property of the Clifford
algebra. This is an image-containment statement, not injectivity: the
separate kernel theorem records that the representation is not faithful. -/
theorem splitCliffordRepresentation_mem_leftMultiplicationAlgebra
    (c : CliffordAlgebra leftCliffordQuadratic) :
    splitOctonionLeftCliffordRepresentation c ∈ leftMultiplicationAlgebra := by
  have hc : c ∈ Algebra.adjoin ℝ
      (Set.range (CliffordAlgebra.ι leftCliffordQuadratic)) := by
    rw [CliffordAlgebra.adjoin_range_ι]
    trivial
  refine Algebra.adjoin_induction
    (p := fun c _ => splitOctonionLeftCliffordRepresentation c ∈
      leftMultiplicationAlgebra) ?_ ?_ ?_ ?_ hc
  · intro x hx
    rcases hx with ⟨X, rfl⟩
    rw [splitOctonionLeftCliffordRepresentation_ι]
    have hmul : imaginaryLeftMul X = leftRegular X.1 := by
      apply LinearMap.ext
      intro z
      rfl
    rw [hmul]
    exact leftRegular_mem_multiplicationAlgebra X.1
  · intro r
    simp
  · intro x y hxy hyx hx hy
    rw [map_add]
    exact leftMultiplicationAlgebra.add_mem hx hy
  · intro x y hxy hyx hx hy
    rw [map_mul]
    exact leftMultiplicationAlgebra.mul_mem hx hy

/-- The scalar/imaginary splitting of the split-Zorn carrier, using half its
intrinsic trace as scalar coordinate. -/
def splitScalarPart (x : CZ) : ℝ := realZornTrace x / 2

def splitImaginaryPart (x : CZ) : Imaginary :=
  ⟨x - splitScalarPart x • (1 : CZ), by
    change realZornTrace (x - splitScalarPart x • (1 : CZ)) = 0
    rcases x with ⟨a, b, u, v⟩
    simp [splitScalarPart, realZornTrace]
    ring⟩

/-- Every split-Zorn element is the sum of its scalar trace part and its
trace-zero (imaginary) part. -/
theorem splitZorn_scalar_imaginary_decomposition (x : CZ) :
    x = splitScalarPart x • (1 : CZ) + (splitImaginaryPart x).1 := by
  rcases x with ⟨a, b, u, v⟩
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [splitScalarPart, splitImaginaryPart, realZornTrace]
  · simp [splitScalarPart, splitImaginaryPart, realZornTrace]
  · ext i
    simp [splitScalarPart, splitImaginaryPart, realZornTrace]
  · ext i
    simp [splitScalarPart, splitImaginaryPart, realZornTrace]

/-- Every left regular operator is represented by the split Clifford action.
This is the key split-form generation statement: scalar multiplication and
the seven-dimensional imaginary Clifford generators together recover left
multiplication by an arbitrary Zorn element. -/
theorem leftRegular_mem_splitCliffordImage (x : CZ) :
    ∃ c : CliffordAlgebra leftCliffordQuadratic,
      splitOctonionLeftCliffordRepresentation c = leftRegular x := by
  let t := splitScalarPart x
  let u := splitImaginaryPart x
  refine ⟨algebraMap ℝ (CliffordAlgebra leftCliffordQuadratic) t +
    CliffordAlgebra.ι leftCliffordQuadratic u, ?_⟩
  rw [map_add, splitOctonionLeftCliffordRepresentation.commutes,
    splitOctonionLeftCliffordRepresentation_ι]
  have hmul : imaginaryLeftMul u = leftRegular u.1 := by
    apply LinearMap.ext
    intro z
    rfl
  rw [hmul]
  have hx : x = t • (1 : CZ) + u.1 := by
    simpa [t, u] using splitZorn_scalar_imaginary_decomposition x
  apply LinearMap.ext
  intro z
  change t • z + u.1 * z = x * z
  rw [hx]
  rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul]
  change t • z + u.1 * z =
    t • InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul 1 z + u.1 * z
  rw [InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.one_zMul]

/-- The split Clifford representation is onto the full left multiplication
operator algebra. Together with `splitCliffordRepresentation_mem_leftMultiplicationAlgebra`,
this identifies that algebra with the image of the Clifford action, without
claiming the Clifford representation itself is injective. -/
theorem leftMultiplicationAlgebra_mem_splitCliffordImage
    {T : EndCZ} (hT : T ∈ leftMultiplicationAlgebra) :
    ∃ c : CliffordAlgebra leftCliffordQuadratic,
      splitOctonionLeftCliffordRepresentation c = T := by
  have hgen : T ∈ Algebra.adjoin ℝ (Set.range zMulLinear) := hT
  refine Algebra.adjoin_induction
    (p := fun T _ => ∃ c : CliffordAlgebra leftCliffordQuadratic,
      splitOctonionLeftCliffordRepresentation c = T) ?_ ?_ ?_ ?_ hgen
  · intro T hT
    rcases hT with ⟨x, rfl⟩
    rw [← leftRegular_eq_zMulLinear]
    exact leftRegular_mem_splitCliffordImage x
  · intro r
    exact ⟨algebraMap ℝ (CliffordAlgebra leftCliffordQuadratic) r, by simp⟩
  · intro S T hS hT hS' hT'
    rcases hS' with ⟨c, rfl⟩
    rcases hT' with ⟨d, rfl⟩
    exact ⟨c + d, by simp⟩
  · intro S T hS hT hS' hT'
    rcases hS' with ⟨c, rfl⟩
    rcases hT' with ⟨d, rfl⟩
    exact ⟨c * d, by simp⟩

/-- Exact carrier identification: an endomorphism belongs to the generated
left multiplication algebra precisely when it is represented by an element
of the split Clifford algebra. -/
theorem leftMultiplicationAlgebra_iff_splitCliffordImage (T : EndCZ) :
    T ∈ leftMultiplicationAlgebra ↔
      ∃ c : CliffordAlgebra leftCliffordQuadratic,
        splitOctonionLeftCliffordRepresentation c = T := by
  constructor
  · exact leftMultiplicationAlgebra_mem_splitCliffordImage
  · rintro ⟨c, rfl⟩
    exact splitCliffordRepresentation_mem_leftMultiplicationAlgebra c

/-- Commutator action on the associative endomorphism algebra. -/
def derivationCommutator (D T : EndCZ) : EndCZ := D * T - T * D

/-- Split-octonion derivations act by commutators that preserve the Clifford
image, using its proved equality with the left multiplication algebra. -/
theorem derivationCommutator_mem_leftMultiplicationAlgebra
    (D : EndCZ) (hD : InfoGeometry.Lie.CanonicalZornDerivation.IsDerivation D)
    {T : EndCZ} (hT : T ∈ leftMultiplicationAlgebra) :
    derivationCommutator D T ∈ leftMultiplicationAlgebra := by
  refine Algebra.adjoin_induction
    (p := fun T _ => derivationCommutator D T ∈ leftMultiplicationAlgebra)
    ?_ ?_ ?_ ?_ hT
  · intro T hT
    rcases hT with ⟨x, rfl⟩
    rw [← leftRegular_eq_zMulLinear]
    change (D * leftRegular x - leftRegular x * D) ∈ leftMultiplicationAlgebra
    rw [← LieRing.of_associative_ring_bracket,
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.derivation_lie_leftRegular D hD x]
    exact leftRegular_mem_multiplicationAlgebra (D x)
  · intro r
    change derivationCommutator D (algebraMap ℝ EndCZ r) ∈ leftMultiplicationAlgebra
    rw [derivationCommutator, ← Algebra.commutes r D, sub_self]
    exact leftMultiplicationAlgebra.zero_mem
  · intro S T hS hT hS' hT'
    have hadd : derivationCommutator D (S + T) =
        derivationCommutator D S + derivationCommutator D T := by
      simp only [derivationCommutator, mul_add, add_mul]
      abel
    rw [hadd]
    exact leftMultiplicationAlgebra.add_mem hS' hT'
  · intro S T hS hT hS' hT'
    have hprod : derivationCommutator D (S * T) =
        derivationCommutator D S * T + S * derivationCommutator D T := by
      simp only [derivationCommutator, sub_mul, mul_sub, mul_assoc]
      noncomm_ring
    rw [hprod]
    exact leftMultiplicationAlgebra.add_mem
      (leftMultiplicationAlgebra.mul_mem hS' hT)
      (leftMultiplicationAlgebra.mul_mem hS hT')

/-- Consequently, the commutator action of every split-Zorn derivation
preserves the image of the Clifford representation as a set of operators. -/
theorem derivationCommutator_preserves_splitCliffordImage
    (D : EndCZ) (hD : InfoGeometry.Lie.CanonicalZornDerivation.IsDerivation D)
    {T : EndCZ}
    (hT : ∃ c : CliffordAlgebra leftCliffordQuadratic,
      splitOctonionLeftCliffordRepresentation c = T) :
    ∃ c : CliffordAlgebra leftCliffordQuadratic,
      splitOctonionLeftCliffordRepresentation c = derivationCommutator D T := by
  have hleft : T ∈ leftMultiplicationAlgebra :=
    (leftMultiplicationAlgebra_iff_splitCliffordImage T).2 hT
  exact (leftMultiplicationAlgebra_iff_splitCliffordImage
    (derivationCommutator D T)).1
    (derivationCommutator_mem_leftMultiplicationAlgebra D hD hleft)

/-- The Furey-style left regular operator for the distinguished split axis is
the same operator used by the existing `ellStabilizer` owner. Thus the
infinitesimal stabilizer can be read as the centralizer of that generator
inside the associative endomorphism algebra. -/
theorem ellStabilizer_iff_leftRegular_centralizer
    (D : EndCZ)
    (hD : D ∈ InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations) :
    D ∈ InfoGeometry.Lie.SplitOctonionEllStabilizer.ellStabilizer ↔
      ⁅D, leftRegular InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit⁆ = 0 := by
  have hleft : leftRegular InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit =
      InfoGeometry.Lie.SplitOctonionEllStabilizer.leftMul
        InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit := by
    apply LinearMap.ext
    intro x
    rfl
  rw [hleft]
  exact InfoGeometry.Lie.SplitOctonionEllStabilizer.mem_ellStabilizer_iff_leftMul_centralizer
    D hD

/-- A derivation eigenvector gives the same weight on right-regular
multiplication. This is the right-action counterpart of the existing
left-regular eigenoperator theorem and uses the native Leibniz rule. -/
theorem rightRegular_eigenoperator_of_derivation
    (D : EndCZ)
    (hD : InfoGeometry.Lie.CanonicalZornDerivation.IsDerivation D)
    (x : CZ) (c : ℝ) (hx : D x = c • x) :
    ⁅D, rightRegular x⁆ = c • rightRegular x := by
  rw [LieRing.of_associative_ring_bracket]
  apply LinearMap.ext
  intro y
  change D (y * x) - D y * x = c • (y * x)
  rw [hD y x, hx]
  change D y * x + InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul y (c • x) -
      D y * x = c • (y * x)
  rw [InfoGeometry.Algebra.Zorn.SplitQuaternionCore.zMul_smul_right]
  abel

/-- The upper circular root has Cartan weight `k i` in the right-regular
multiplication representation. This is the right-action counterpart of the
existing left-regular eigenoperator theorem. -/
theorem axialCartan_rightRegular_upper_eigenoperator
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (i : Fin 3) :
    ⁅axialCartanEnd k, rightRegular (chiralUpperBasis i)⁆ =
      k i • rightRegular (chiralUpperBasis i) := by
  exact rightRegular_eigenoperator_of_derivation
    (axialCartanEnd k)
    (InfoGeometry.Lie.SplitOctonionAxialCartanDerivation.axialCartanEnd_isDerivation
      k hk)
    (chiralUpperBasis i) (k i)
    (InfoGeometry.Lie.SplitOctonionAxialCartanDerivation.axialCartanEnd_chiralUpperBasis
      k i)

/-- The lower root has opposite Cartan weight in the right-regular
multiplication representation. -/
theorem axialCartan_rightRegular_lower_eigenoperator
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (i : Fin 3) :
    ⁅axialCartanEnd k, rightRegular (chiralLowerBasis i)⁆ =
      (-k i) • rightRegular (chiralLowerBasis i) := by
  exact rightRegular_eigenoperator_of_derivation
    (axialCartanEnd k)
    (InfoGeometry.Lie.SplitOctonionAxialCartanDerivation.axialCartanEnd_isDerivation
      k hk)
    (chiralLowerBasis i) (-k i)
    (InfoGeometry.Lie.SplitOctonionAxialCartanDerivation.axialCartanEnd_chiralLowerBasis
      k i)

/- The repository's CAS-replayed fourteen-generator split-G₂ basis acts on
both regular representations by differentiating the underlying split-Zorn
element. The exact finite structure-constant replay and its basis alignment
are owned by `CanonicalZornG2CASReplay` and `CanonicalZornG2BasisAlignment`;
the following theorems use the native generator basis after that alignment. -/
theorem casG2RootGenerator_leftRegular_commutator
    (i : Fin 14) (x : CZ) :
    ⁅(InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der),
      leftRegular x⁆ =
      leftRegular
        ((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i :
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der).1 x) := by
  let D : EndCZ :=
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i
  have hD : InfoGeometry.Lie.CanonicalZornDerivation.IsDerivation D :=
    (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i).property
  exact InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.derivation_lie_leftRegular
    D hD x

theorem casG2RootGenerator_rightRegular_commutator
    (i : Fin 14) (x : CZ) :
    ⁅(InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der),
      rightRegular x⁆ =
      rightRegular
        ((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i :
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der).1 x) := by
  let D : EndCZ :=
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i
  have hD : InfoGeometry.Lie.CanonicalZornDerivation.IsDerivation D :=
    (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i).property
  exact InfoGeometry.Canonical.SplitOctonionAutomorphismOperatorBridge.derivation_lie_rightRegular
    D hD x

private theorem leftRegular_sub (u v : CZ) :
    leftRegular (u - v) = leftRegular u - leftRegular v := by
  apply LinearMap.ext
  intro y
  change (u - v) * y = u * y - v * y
  exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.sub_mul u v y

/-- Evaluation of a split-`G₂` derivation on a fixed octonion, followed by
left regular multiplication, is linear in the derivation.  This is the map
that transports the native structure-constant expansion to operators. -/
private def rootActionOnLeftRegular (x : CZ) :
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der →ₗ[ℝ] EndCZ where
  toFun D := leftRegular (D.1 x)
  map_add' D E := by
    apply LinearMap.ext
    intro y
    change ((D.1 x) + (E.1 x)) * y = (D.1 x) * y + (E.1 x) * y
    exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul _ _ _
  map_smul' r D := by
    apply LinearMap.ext
    intro y
    change (r • (D.1 x)) * y = r • ((D.1 x) * y)
    exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul _ _ _

private theorem rightRegular_sub (u v : CZ) :
    rightRegular (u - v) = rightRegular u - rightRegular v := by
  apply LinearMap.ext
  intro y
  change y * (u - v) = y * u - y * v
  exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_sub y u v

/-- Evaluation of a split-`G₂` derivation followed by right regular
multiplication is linear in the derivation. -/
private def rootActionOnRightRegular (x : CZ) :
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der →ₗ[ℝ] EndCZ where
  toFun D := rightRegular (D.1 x)
  map_add' D E := by
    apply LinearMap.ext
    intro y
    change y * ((D.1 x) + (E.1 x)) = y * (D.1 x) + y * (E.1 x)
    exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_add _ _ _
  map_smul' r D := by
    apply LinearMap.ext
    intro y
    change y * (r • (D.1 x)) = r • (y * (D.1 x))
    exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul _ _ _

/-- The structure-constant bracket of the CAS-aligned split-`G₂` basis is
represented on left multiplication operators.  The difference of the two
infinitesimal actions is the regular multiplication operator associated to
the derivation bracket; this keeps the source octonion product distinct from
composition in the associative endomorphism algebra. -/
theorem casG2_bracket_action_leftRegular
    (i j : Fin 14) (x : CZ) :
    ⁅(InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der),
      leftRegular (((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis j :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der).1) x)⁆ -
    ⁅(InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis j :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der),
      leftRegular (((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der).1) x)⁆ =
      leftRegular (((⁅
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i :
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der),
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis j :
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der)⁆ :
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der).1) x) := by
  let Di : EndCZ :=
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i
  let Dj : EndCZ :=
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis j
  rw [casG2RootGenerator_leftRegular_commutator i (Dj x),
    casG2RootGenerator_leftRegular_commutator j (Di x)]
  change leftRegular (Di (Dj x)) - leftRegular (Dj (Di x)) =
    leftRegular (Di (Dj x) - Dj (Di x))
  rw [← leftRegular_sub]

/-- The derivation bracket is represented on right multiplication operators
by the corresponding difference of infinitesimal actions. -/
theorem casG2_bracket_action_rightRegular
    (i j : Fin 14) (x : CZ) :
    ⁅(InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der),
      rightRegular (((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis j :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der).1) x)⁆ -
    ⁅(InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis j :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der),
      rightRegular (((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der).1) x)⁆ =
      rightRegular (((⁅
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i :
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der),
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis j :
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der)⁆ :
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der).1) x) := by
  let Di : EndCZ :=
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i
  let Dj : EndCZ :=
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis j
  rw [casG2RootGenerator_rightRegular_commutator i (Dj x),
    casG2RootGenerator_rightRegular_commutator j (Di x)]
  change rightRegular (Di (Dj x)) - rightRegular (Dj (Di x)) =
    rightRegular (Di (Dj x) - Dj (Di x))
  rw [← rightRegular_sub]

/-- Native root-basis bracket expansion with the coefficients replayed from
the exact rational CAS table.  The operator actions below transport this one
canonical expansion, avoiding a second coefficient source. -/
theorem casG2_native_basis_bracket_expansion (i j : Fin 14) :
    ⁅(InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der),
      (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis j :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der)⁆ =
      ∑ k : Fin 14,
        InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport.structureConstant i j k •
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis k := by
  have hBracket :=
    InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport.bracket_eq_sum_structure_constants i j
  simpa only [InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis_apply]
    using hBracket

/-- The induced action on left regular operators carries the exact native
fourteen-generator structure constants: the bracket action is the finite
linear combination of the corresponding regularized root-generator actions.
The coefficients are the same `structureConstant` values already replayed
against the rational CAS table and aligned to the native basis. -/
theorem casG2_bracket_action_leftRegular_structure_constants
    (i j : Fin 14) (x : CZ) :
    ⁅(InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der),
      leftRegular (((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis j :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der).1) x)⁆ -
    ⁅(InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis j :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der),
      leftRegular (((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der).1) x)⁆ =
      ∑ k : Fin 14,
        InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport.structureConstant i j k •
          leftRegular (((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis k :
            InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der).1) x) := by
  rw [casG2_bracket_action_leftRegular]
  simpa [rootActionOnLeftRegular] using
    congrArg (rootActionOnLeftRegular x) (casG2_native_basis_bracket_expansion i j)

/-- The same CAS bracket acts on the right regular representation with the
same structure constants.  Together with the left-regular theorem this gives
the bilateral split-octonion operator action on the single existing carrier. -/
theorem casG2_bracket_action_rightRegular_structure_constants
    (i j : Fin 14) (x : CZ) :
    ⁅(InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der),
      rightRegular (((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis j :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der).1) x)⁆ -
    ⁅(InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis j :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der),
      rightRegular (((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der).1) x)⁆ =
      ∑ k : Fin 14,
        InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport.structureConstant i j k •
          rightRegular (((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis k :
            InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der).1) x) := by
  rw [casG2_bracket_action_rightRegular]
  simpa [rootActionOnRightRegular] using
    congrArg (rootActionOnRightRegular x) (casG2_native_basis_bracket_expansion i j)

/-- The six-generator split-CAR Clifford action also lands in the same left
multiplication algebra after transporting endomorphisms from the Zorn-vector
carrier to the canonical split-octonion carrier. This identifies the CAR
representation as a subrepresentation of the Furey-style operator algebra;
it does not assert surjectivity onto all endomorphisms. -/
theorem splitCAR_generator_transport (v :
    InfoGeometry.Algebra.ZornPinorReconstruction.V ×
      InfoGeometry.Algebra.ZornPinorReconstruction.V) :
    InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.carrierEndAlgEquiv
      (InfoGeometry.Algebra.ZornLeftCAR.cliffordGenerator v) =
    leftRegular
      (InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.canonicalVectorLinearEquiv.symm
        (InfoGeometry.Algebra.ZornLeftCAR.cliffordVector v)) := by
  let X := InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.canonicalVectorLinearEquiv.symm
    (InfoGeometry.Algebra.ZornLeftCAR.cliffordVector v)
  have hX : InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv X =
      InfoGeometry.Algebra.ZornLeftCAR.cliffordVector v := by
    simp [X]
  apply LinearMap.ext
  intro z
  rw [InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.carrierEndAlgEquiv_apply]
  change InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv.symm
      (InfoGeometry.Algebra.ZornLeftCAR.cliffordVector v *
        InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv z) =
    X * z
  rw [← hX]
  change InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv.symm
      (InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv X)
        (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv z)) = X * z
  rw [← InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_mul,
    Equiv.symm_apply_apply]

/-- The CAR anticommutation relation survives transport to the native
split-octonion carrier. Thus the six-generator Fock action has the same
quadratic polar form when expressed by split-Zorn left multiplication. -/
theorem splitCAR_generator_anticommutator_transport
    (v w : InfoGeometry.Algebra.ZornPinorReconstruction.V ×
      InfoGeometry.Algebra.ZornPinorReconstruction.V) :
    leftRegular
        (InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.canonicalVectorLinearEquiv.symm
          (InfoGeometry.Algebra.ZornLeftCAR.cliffordVector v)) *
      leftRegular
        (InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.canonicalVectorLinearEquiv.symm
          (InfoGeometry.Algebra.ZornLeftCAR.cliffordVector w)) +
    leftRegular
        (InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.canonicalVectorLinearEquiv.symm
          (InfoGeometry.Algebra.ZornLeftCAR.cliffordVector w)) *
      leftRegular
        (InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.canonicalVectorLinearEquiv.symm
          (InfoGeometry.Algebra.ZornLeftCAR.cliffordVector v)) =
      QuadraticMap.polar InfoGeometry.Algebra.ZornLeftCAR.splitQuadratic v w •
        (1 : EndCZ) := by
  have h := InfoGeometry.Algebra.ZornLeftCAR.cliffordGenerator_anticommutator v w
  rw [← splitCAR_generator_transport v, ← splitCAR_generator_transport w]
  simpa only [map_add, map_mul, map_smul, map_one] using
    congrArg
      InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.carrierEndAlgEquiv h

/-- Canonical split-octonion conjugation carries the transported CAR
anticommutator to the right-regular representation. This makes the relation
between the two Fock actions explicit while retaining the split-octonion
conjugation on the generator labels. -/
theorem splitCAR_right_generator_anticommutator_transport
    (v w : InfoGeometry.Algebra.ZornPinorReconstruction.V ×
      InfoGeometry.Algebra.ZornPinorReconstruction.V) :
    rightRegular
        (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
          (InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.canonicalVectorLinearEquiv.symm
            (InfoGeometry.Algebra.ZornLeftCAR.cliffordVector v))) *
      rightRegular
        (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
          (InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.canonicalVectorLinearEquiv.symm
            (InfoGeometry.Algebra.ZornLeftCAR.cliffordVector w))) +
    rightRegular
        (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
          (InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.canonicalVectorLinearEquiv.symm
            (InfoGeometry.Algebra.ZornLeftCAR.cliffordVector w))) *
      rightRegular
        (InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation.canonicalConjLinear
          (InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.canonicalVectorLinearEquiv.symm
            (InfoGeometry.Algebra.ZornLeftCAR.cliffordVector v))) =
      QuadraticMap.polar InfoGeometry.Algebra.ZornLeftCAR.splitQuadratic v w •
        (1 : EndCZ) := by
  have h := splitCAR_generator_anticommutator_transport v w
  have hc := congrArg conjugateEnd h
  rw [conjugateEnd_add, conjugateEnd_mul, conjugateEnd_mul,
    conjugateEnd_smul, conjugateEnd_one,
    conjugateEnd_leftRegular, conjugateEnd_leftRegular] at hc
  exact hc

theorem splitCAR_cliffordImage_mem_leftMultiplicationAlgebra
    (c : CliffordAlgebra InfoGeometry.Algebra.ZornLeftCAR.splitQuadratic) :
    InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.carrierEndAlgEquiv
      (InfoGeometry.Algebra.ZornLeftCAR.cliffordRepresentation c) ∈
        leftMultiplicationAlgebra := by
  let A := InfoGeometry.Algebra.ZornLeftCAR.splitQuadratic
  have hc : c ∈ Algebra.adjoin ℝ (Set.range (CliffordAlgebra.ι A)) := by
    rw [CliffordAlgebra.adjoin_range_ι]
    trivial
  refine Algebra.adjoin_induction
    (p := fun c _ =>
      InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.carrierEndAlgEquiv
        (InfoGeometry.Algebra.ZornLeftCAR.cliffordRepresentation c) ∈
          leftMultiplicationAlgebra) ?_ ?_ ?_ ?_ hc
  · intro x hx
    rcases hx with ⟨v, rfl⟩
    rw [InfoGeometry.Algebra.ZornLeftCAR.cliffordRepresentation_iota]
    let X := InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.canonicalVectorLinearEquiv.symm
        (InfoGeometry.Algebra.ZornLeftCAR.cliffordVector v)
    rw [splitCAR_generator_transport]
    exact leftRegular_mem_multiplicationAlgebra X
  · intro r
    simp
  · intro x y hxy hyx hx hy
    rw [map_add]
    exact leftMultiplicationAlgebra.add_mem hx hy
  · intro x y hxy hyx hx hy
    rw [map_mul]
    exact leftMultiplicationAlgebra.mul_mem hx hy

/-- Furey's full multiplication-operator algebra, formed from both left and
right regular actions on the same split-Zorn carrier. -/
def regularMultiplicationAlgebra : Subalgebra ℝ EndCZ :=
  Algebra.adjoin ℝ (Set.range leftRegular ∪ Set.range rightRegular)

theorem leftRegular_mem_regularMultiplicationAlgebra (x : CZ) :
    leftRegular x ∈ regularMultiplicationAlgebra := by
  apply Algebra.subset_adjoin
  exact Or.inl ⟨x, rfl⟩

theorem rightRegular_mem_regularMultiplicationAlgebra (x : CZ) :
    rightRegular x ∈ regularMultiplicationAlgebra := by
  apply Algebra.subset_adjoin
  exact Or.inr ⟨x, rfl⟩

/-- The unital associative subalgebra generated by right regular multiplication.
The carrier is the same endomorphism algebra as the left multiplication
algebra; only the generating family is changed. -/
def rightMultiplicationAlgebra : Subalgebra ℝ EndCZ :=
  Algebra.adjoin ℝ (Set.range rightRegular)

/- Left regular multiplication by an element of the existing split-quaternion
core preserves that four-dimensional carrier. This is the restricted
endomorphic action of the nested associative slice inside the ambient
nonassociative split octonions. -/
theorem leftRegular_preserves_splitQuaternionCore
    {a : CZ} (ha : a ∈ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.coreSubmodule)
    {x : CZ} (hx : x ∈ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.coreSubmodule) :
    leftRegular a x ∈ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.coreSubmodule := by
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul a x ∈
    InfoGeometry.Algebra.Zorn.SplitQuaternionCore.coreSubmodule
  exact InfoGeometry.Algebra.Zorn.SplitQuaternionCore.core_closed_mul a x ha hx

/- Right regular multiplication by an element of the split-quaternion core
also preserves that carrier. Both sides therefore act on the same nested
slice, while their ambient operator compositions retain the split-octonion
associator defect. -/
theorem rightRegular_preserves_splitQuaternionCore
    {a : CZ} (ha : a ∈ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.coreSubmodule)
    {x : CZ} (hx : x ∈ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.coreSubmodule) :
    rightRegular a x ∈ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.coreSubmodule := by
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul x a ∈
    InfoGeometry.Algebra.Zorn.SplitQuaternionCore.coreSubmodule
  exact InfoGeometry.Algebra.Zorn.SplitQuaternionCore.core_closed_mul x a hx ha

/- On the associative split-quaternion core, composition of left regular
operators agrees with left multiplication by the product. The global
associator defect therefore vanishes on this invariant subcarrier. -/
theorem leftRegular_composition_on_splitQuaternionCore
    {a b x : CZ}
    (ha : a ∈ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.coreSubmodule)
    (hb : b ∈ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.coreSubmodule)
    (hx : x ∈ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.coreSubmodule) :
    (leftRegular a * leftRegular b) x = leftRegular (a * b) x := by
  rw [Module.End.mul_apply]
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul a
      (InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul b x) =
    InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
      (InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul a b) x
  exact (InfoGeometry.Algebra.Zorn.SplitQuaternionCore.assoc a b x ha hb hx).symm

/- The corresponding right-regular composition reverses the order of the
product, exactly as dictated by the associative core multiplication. -/
theorem rightRegular_composition_on_splitQuaternionCore
    {a b x : CZ}
    (ha : a ∈ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.coreSubmodule)
    (hb : b ∈ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.coreSubmodule)
    (hx : x ∈ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.coreSubmodule) :
    (rightRegular a * rightRegular b) x = rightRegular (b * a) x := by
  rw [Module.End.mul_apply]
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
      (InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul x b) a =
    InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul x
      (InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul b a)
  exact InfoGeometry.Algebra.Zorn.SplitQuaternionCore.assoc x b a hx hb ha

/- The mixed left/right regular commutator vanishes when all three entries
lie in the associative split-quaternion core. This local vanishing and the
proved nonzero circular-root example locate the obstruction in the ambient
split-octonion directions. -/
theorem regular_commutator_vanishes_on_splitQuaternionCore
    {a z y : CZ}
    (ha : a ∈ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.coreSubmodule)
    (hz : z ∈ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.coreSubmodule)
    (hy : y ∈ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.coreSubmodule) :
    (leftRegular a * rightRegular z - rightRegular z * leftRegular a) y = 0 := by
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul a
      (InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul y z) -
    InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
      (InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul a y) z = 0
  rw [InfoGeometry.Algebra.Zorn.SplitQuaternionCore.assoc a y z ha hy hz]
  simp

/-- Split-octonion conjugation transports the entire generated left
multiplication algebra into the generated right multiplication algebra. The
generator step is the concrete regular-action exchange; closure under products
uses that conjugation is multiplicative on endomorphisms. -/
theorem conjugateEnd_mem_rightMultiplicationAlgebra
    {T : EndCZ} (hT : T ∈ leftMultiplicationAlgebra) :
    conjugateEnd T ∈ rightMultiplicationAlgebra := by
  refine Algebra.adjoin_induction
    (p := fun T _ => conjugateEnd T ∈ rightMultiplicationAlgebra)
    ?_ ?_ ?_ ?_ hT
  · intro T hT
    rcases hT with ⟨x, rfl⟩
    rw [← leftRegular_eq_zMulLinear x, conjugateEnd_leftRegular]
    exact Algebra.subset_adjoin ⟨_, rfl⟩
  · intro r
    have hscalar : conjugateEnd (algebraMap ℝ EndCZ r) = algebraMap ℝ EndCZ r := by
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (show conjugateEnd (r • (1 : EndCZ)) = r • (1 : EndCZ) by
          rw [conjugateEnd_smul, conjugateEnd_one])
    rw [hscalar]
    exact rightMultiplicationAlgebra.algebraMap_mem r
  · intro S T hST hTS hS hT
    rw [conjugateEnd_add]
    exact rightMultiplicationAlgebra.add_mem hS hT
  · intro S T hST hTS hS hT
    rw [conjugateEnd_mul]
    exact rightMultiplicationAlgebra.mul_mem hS hT

/-- The reverse transport sends the generated right multiplication algebra
into the generated left multiplication algebra. Together, the two transport
theorems identify the conjugation symmetry of Furey's paired regular actions
without identifying either action with split-octonion multiplication as an
associative representation. -/
theorem conjugateEnd_mem_leftMultiplicationAlgebra
    {T : EndCZ} (hT : T ∈ rightMultiplicationAlgebra) :
    conjugateEnd T ∈ leftMultiplicationAlgebra := by
  refine Algebra.adjoin_induction
    (p := fun T _ => conjugateEnd T ∈ leftMultiplicationAlgebra)
    ?_ ?_ ?_ ?_ hT
  · intro T hT
    rcases hT with ⟨x, rfl⟩
    rw [conjugateEnd_rightRegular]
    exact leftRegular_mem_multiplicationAlgebra _
  · intro r
    have hscalar : conjugateEnd (algebraMap ℝ EndCZ r) = algebraMap ℝ EndCZ r := by
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (show conjugateEnd (r • (1 : EndCZ)) = r • (1 : EndCZ) by
          rw [conjugateEnd_smul, conjugateEnd_one])
    rw [hscalar]
    exact leftMultiplicationAlgebra.algebraMap_mem r
  · intro S T hST hTS hS hT
    rw [conjugateEnd_add]
    exact leftMultiplicationAlgebra.add_mem hS hT
  · intro S T hST hTS hS hT
    rw [conjugateEnd_mul]
    exact leftMultiplicationAlgebra.mul_mem hS hT

/-- Conjugation gives an exact membership correspondence between the
generated left and right multiplication algebras. This packages the two
generator transports as an equivalence of the represented operator
subalgebras, while retaining their distinct actions on the nonassociative
split-octonion carrier. -/
theorem conjugateEnd_mem_left_iff_mem_right (T : EndCZ) :
    conjugateEnd T ∈ leftMultiplicationAlgebra ↔
      T ∈ rightMultiplicationAlgebra := by
  constructor
  · intro hT
    have h := conjugateEnd_mem_rightMultiplicationAlgebra hT
    simpa only [conjugateEnd_involutive] using h
  · exact conjugateEnd_mem_leftMultiplicationAlgebra

/-- The equivalent orientation of `conjugateEnd_mem_left_iff_mem_right`:
conjugating an operator in the left multiplication algebra lands in the
right multiplication algebra, and conversely. -/
theorem conjugateEnd_mem_right_iff_mem_left (T : EndCZ) :
    conjugateEnd T ∈ rightMultiplicationAlgebra ↔
      T ∈ leftMultiplicationAlgebra := by
  constructor
  · intro hT
    have h := conjugateEnd_mem_leftMultiplicationAlgebra hT
    simpa only [conjugateEnd_involutive] using h
  · exact conjugateEnd_mem_rightMultiplicationAlgebra

/-- Commutator with a split-octonion derivation preserves the associative
algebra generated by all left and right regular multiplications. The proof
uses the Leibniz rule on generators and the commutator product rule on
compositions; it does not treat the split-octonion product as associative. -/
theorem derivationCommutator_mem_regularMultiplicationAlgebra
    (D : EndCZ) (hD : InfoGeometry.Lie.CanonicalZornDerivation.IsDerivation D)
    {T : EndCZ} (hT : T ∈ regularMultiplicationAlgebra) :
    derivationCommutator D T ∈ regularMultiplicationAlgebra := by
  refine Algebra.adjoin_induction
    (p := fun T _ => derivationCommutator D T ∈ regularMultiplicationAlgebra)
    ?_ ?_ ?_ ?_ hT
  · intro T hT
    rcases hT with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · change (D * leftRegular x - leftRegular x * D) ∈ regularMultiplicationAlgebra
      rw [← LieRing.of_associative_ring_bracket,
        InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.derivation_lie_leftRegular D hD x]
      exact leftRegular_mem_regularMultiplicationAlgebra (D x)
    · change (D * rightRegular x - rightRegular x * D) ∈ regularMultiplicationAlgebra
      have hRight :
          rightRegular x =
            InfoGeometry.Canonical.SplitOctonionAutomorphismOperatorBridge.rightRegular x := by
        apply LinearMap.ext
        intro y
        rfl
      rw [← LieRing.of_associative_ring_bracket, hRight,
        InfoGeometry.Canonical.SplitOctonionAutomorphismOperatorBridge.derivation_lie_rightRegular
          D hD x]
      exact rightRegular_mem_regularMultiplicationAlgebra (D x)
  · intro r
    change derivationCommutator D (algebraMap ℝ EndCZ r) ∈ regularMultiplicationAlgebra
    rw [derivationCommutator]
    rw [← Algebra.commutes r D, sub_self]
    exact regularMultiplicationAlgebra.zero_mem
  · intro S T hS hT hS' hT'
    have hadd : derivationCommutator D (S + T) =
        derivationCommutator D S + derivationCommutator D T := by
      simp only [derivationCommutator, mul_add, add_mul]
      abel
    rw [hadd]
    exact regularMultiplicationAlgebra.add_mem hS' hT'
  · intro S T hS hT hS' hT'
    have hprod : derivationCommutator D (S * T) =
        derivationCommutator D S * T + S * derivationCommutator D T := by
      simp only [derivationCommutator, sub_mul, mul_sub, mul_assoc]
      noncomm_ring
    rw [hprod]
    exact regularMultiplicationAlgebra.add_mem
      (regularMultiplicationAlgebra.mul_mem hS' hT)
      (regularMultiplicationAlgebra.mul_mem hS hT')

/-- The split-octonion associator, with the repository's left-to-right
parenthesization. -/
def splitAssociator (x y z : CZ) : CZ := (x * y) * z - x * (y * z)

/-- The failure of left multiplication to preserve the split-octonion product
is exactly the negative associator, evaluated on the state. -/
theorem left_regular_composition_defect_apply (x y z : CZ) :
    (leftRegular x * leftRegular y - leftRegular (x * y)) z =
      -splitAssociator x y z := by
  rw [LinearMap.sub_apply, Module.End.mul_apply]
  simp only [leftRegular_apply, splitAssociator]
  abel_nf

/-- For fixed `x` and `y`, left multiplication preserves their product under
composition on the whole carrier exactly when the associator with first two
entries `x,y` vanishes on every state. -/
theorem left_regular_multiplicativity_iff_associator_vanishes (x y : CZ) :
    leftRegular x * leftRegular y = leftRegular (x * y) ↔
      ∀ z : CZ, splitAssociator x y z = 0 := by
  constructor
  · intro h z
    have hd :
        (leftRegular x * leftRegular y - leftRegular (x * y)) z = 0 := by
      rw [h]
      simp
    rw [left_regular_composition_defect_apply] at hd
    exact neg_eq_zero.mp hd
  · intro h
    apply LinearMap.ext
    intro z
    have hd := left_regular_composition_defect_apply x y z
    rw [h z] at hd
    simp only [neg_zero, LinearMap.sub_apply] at hd
    exact sub_eq_zero.mp hd

/-- The mixed regular-operator commutator is exactly the negative associator.
This is the concrete split-octonion instance of the generic regular-action
identity, with the native left and right owners. -/
theorem regular_commutator_apply_eq_neg_associator (x z y : CZ) :
    (leftRegular x * rightRegular z - rightRegular z * leftRegular x) y =
      -splitAssociator x y z := by
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
  simp only [leftRegular_apply, rightRegular_apply, splitAssociator]
  abel_nf

/-- Left and right regular multiplication commute exactly when their mixed
associator vanishes on every state. This gives a necessary-and-sufficient
operator criterion, rather than merely identifying a selected nonzero
commutator evaluation. -/
theorem regular_operators_commute_iff_associator_vanishes (x z : CZ) :
    leftRegular x * rightRegular z = rightRegular z * leftRegular x ↔
      ∀ y : CZ, splitAssociator x y z = 0 := by
  constructor
  · intro h y
    have hzero :
        (leftRegular x * rightRegular z - rightRegular z * leftRegular x) y = 0 := by
      rw [h]
      simp
    rw [regular_commutator_apply_eq_neg_associator] at hzero
    exact neg_eq_zero.mp hzero
  · intro h
    apply LinearMap.ext
    intro y
    have hzero :
        (leftRegular x * rightRegular z - rightRegular z * leftRegular x) y = 0 := by
      rw [regular_commutator_apply_eq_neg_associator, h y]
      simp
    exact sub_eq_zero.mp hzero

/-- A Furey-style multiplication-algebra obstruction on the native split
root frame: the mixed commutator of `L_(rootPlus 0)` and `R_(rootPlus 2)` acts
on `rootPlus 1` by the nonzero split Cartan axis. -/
theorem root_frame_regular_commutator_is_split_axis :
    (leftRegular (rootPlus 0) * rightRegular (rootPlus 2) -
      rightRegular (rootPlus 2) * leftRegular (rootPlus 0)) (rootPlus 1) =
      lUnit := by
  rw [regular_commutator_apply_eq_neg_associator]
  change -((rootPlus 0 * rootPlus 1) * rootPlus 2 -
    rootPlus 0 * (rootPlus 1 * rootPlus 2)) = lUnit
  rw [rootPlus_associator_zero_one_two, ← uPlus_sub_uMinus]
  abel_nf

/-- A concrete failure of multiplicativity of the left regular assignment:
the composition defect acts on the third circular root by `lUnit`. -/
theorem root_frame_left_composition_defect_is_split_axis :
    (leftRegular (rootPlus 0) * leftRegular (rootPlus 1) -
      leftRegular (rootPlus 0 * rootPlus 1)) (rootPlus 2) = lUnit := by
  rw [left_regular_composition_defect_apply]
  change -((rootPlus 0 * rootPlus 1) * rootPlus 2 -
    rootPlus 0 * (rootPlus 1 * rootPlus 2)) = lUnit
  rw [rootPlus_associator_zero_one_two, ← uPlus_sub_uMinus]
  abel_nf

/-- The left-regular assignment is not multiplicative on this split root
pair, exactly as predicted by the nonzero octonion associator. -/
theorem root_frame_left_regular_not_multiplicative :
    leftRegular (rootPlus 0) * leftRegular (rootPlus 1) ≠
      leftRegular (rootPlus 0 * rootPlus 1) := by
  intro h
  have heval :
      (leftRegular (rootPlus 0) * leftRegular (rootPlus 1) -
        leftRegular (rootPlus 0 * rootPlus 1)) (rootPlus 2) = 0 := by
    simpa using congrArg (fun T : EndCZ => T (rootPlus 2))
      (sub_eq_zero.mpr h)
  rw [root_frame_left_composition_defect_is_split_axis] at heval
  have hl : lUnit ≠ (0 : CZ) := by
    intro hz
    have hx := congrArg (fun X : CZ => X.x 0) hz
    norm_num [lUnit] at hx
  exact hl heval

/-- The associator-generated operator output belongs to the existing
zero-weight circular Peirce sector.  This links the multiplication-algebra
obstruction to the repository's root grading, rather than introducing a
separate grade label for it. -/
theorem root_frame_regular_commutator_output_mem_zero_grade :
    (leftRegular (rootPlus 0) * rightRegular (rootPlus 2) -
      rightRegular (rootPlus 2) * leftRegular (rootPlus 0)) (rootPlus 1) ∈
      circularGradeSubmodule 0 := by
  rw [root_frame_regular_commutator_is_split_axis, ← uPlus_sub_uMinus]
  exact Submodule.sub_mem _ uPlus_mem_circularGradeSubmodule_zero
    uMinus_mem_circularGradeSubmodule_zero

/-- The split-octonion multiplication operators do not commute on this root
pair.  The failure is exactly the nonzero associator read out by the previous
theorem, rather than an assumed commutativity defect. -/
theorem root_frame_regular_commutator_ne_zero :
    leftRegular (rootPlus 0) * rightRegular (rootPlus 2) -
      rightRegular (rootPlus 2) * leftRegular (rootPlus 0) ≠ 0 := by
  intro h
  have heval :
      (leftRegular (rootPlus 0) * rightRegular (rootPlus 2) -
        rightRegular (rootPlus 2) * leftRegular (rootPlus 0)) (rootPlus 1) = 0 := by
    simpa using congrArg (fun T : EndCZ => T (rootPlus 1)) h
  rw [root_frame_regular_commutator_is_split_axis] at heval
  have hl : lUnit ≠ (0 : CZ) := by
    intro hz
    have hx := congrArg (fun X : CZ => X.x 0) hz
    norm_num [lUnit] at hx
  exact hl heval

/-- The two named root-frame generators fail to commute as elements of the
generated associative multiplication algebra. -/
theorem root_frame_generators_noncommute_in_regularMultiplicationAlgebra :
    (⟨leftRegular (rootPlus 0),
        leftRegular_mem_regularMultiplicationAlgebra (rootPlus 0)⟩ :
      regularMultiplicationAlgebra) *
      ⟨rightRegular (rootPlus 2),
        rightRegular_mem_regularMultiplicationAlgebra (rootPlus 2)⟩ ≠
    (⟨rightRegular (rootPlus 2),
        rightRegular_mem_regularMultiplicationAlgebra (rootPlus 2)⟩ :
      regularMultiplicationAlgebra) *
      ⟨leftRegular (rootPlus 0),
        leftRegular_mem_regularMultiplicationAlgebra (rootPlus 0)⟩ := by
  intro h
  apply root_frame_regular_commutator_ne_zero
  exact sub_eq_zero.mpr (congrArg Subtype.val h)

end InfoGeometry.Lie.SplitOctonionFureyOperatorLift

end
