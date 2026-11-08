/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Singular.MoorePenrose
import InfoGeometry.Core.PeirceGrading

/-!
# Drazin Projection Localization

Algebraic sidecar for Drazin-style localization.

The point is deliberately modest: a Drazin inverse is extracted from explicit
regular-support inverse data, while the singular/nilpotent residue remains
visible as separate data.  No Wedderburn-Artin classification, Moore-Penrose
existence theorem, or global semisimplicity theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DrazinProjectionLocalization

/-- A pair of complementary idempotent projections. -/
structure SelfAdjointIdempotentPair (A : Type*) [Ring A] [StarRing A] where
  support : A
  residue : A
  support_idem : support * support = support
  residue_idem : residue * residue = residue
  support_residue_zero : support * residue = 0
  residue_support_zero : residue * support = 0
  support_add_residue : support + residue = 1
  support_selfAdjoint : star support = support
  residue_selfAdjoint : star residue = residue

namespace SelfAdjointIdempotentPair

variable {A : Type*} [Ring A] [StarRing A]
variable (P : SelfAdjointIdempotentPair A)

end SelfAdjointIdempotentPair

/-- Drazin inverse data for one algebra element. -/
structure DrazinInverseData (A : Type*) [Ring A] where
  element : A
  drazinInverse : A
  support : A
  element_mul_inverse_eq_support : element * drazinInverse = support
  inverse_mul_element_eq_support : drazinInverse * element = support
  commutes : element * drazinInverse = drazinInverse * element
  inverse_element_inverse : drazinInverse * element * drazinInverse = drazinInverse

namespace DrazinInverseData

variable {A : Type*} [Ring A]
variable (D : DrazinInverseData A)

/-- Re-export of the Drazin commutation law. -/
theorem element_mul_inverse_eq_inverse_mul_element :
    D.element * D.drazinInverse = D.drazinInverse * D.element :=
  D.commutes

/-- Re-export of the reflexive Drazin law. -/
theorem inverse_mul_element_mul_inverse :
    D.drazinInverse * D.element * D.drazinInverse = D.drazinInverse :=
  D.inverse_element_inverse

/-- Campbell--Meyer relations for the supplied Drazin inverse data. The
regular part is expressed as the operator product `support * element`, so the
statement remains valid in any associative ring without matrix or spectral
coordinates. -/
theorem campbellMeyer_relations :
    D.drazinInverse * D.element * D.drazinInverse = D.drazinInverse ∧
    D.drazinInverse * D.element = D.element * D.drazinInverse ∧
    D.drazinInverse * D.element * D.element = D.support * D.element := by
  refine ⟨D.inverse_element_inverse, D.element_mul_inverse_eq_inverse_mul_element.symm, ?_⟩
  calc
    D.drazinInverse * D.element * D.element =
        (D.drazinInverse * D.element) * D.element := by rw [mul_assoc]
    _ = D.support * D.element := by
      rw [D.inverse_mul_element_eq_support]

end DrazinInverseData

/-! ## Noncommutative Drazin--Moore--Penrose composition -/

section DrazinMoorePenrose

variable {A : Type*} [Ring A] [StarRing A]

/-- The Drazin--Moore--Penrose composite, with multiplication order explicit. -/
def drazinMoorePenroseComposite
    (drazinInverse element moorePenroseInverse : A) : A :=
  drazinInverse * element * moorePenroseInverse

/-- Complementing an idempotent mass by a supported tripotent gives an
involution. The hypotheses state the exact support laws; no matrix model or
spectral interpretation is required. -/
theorem complementaryMassTripotent_isInvolution {mass dirac : A}
    (hmass : mass * mass = mass)
    (hdirac : dirac * dirac = mass)
    (hmass_dirac : mass * dirac = dirac)
    (hdirac_mass : dirac * mass = dirac) :
    ((1 - mass) + dirac) * ((1 - mass) + dirac) = 1 := by
  noncomm_ring [hmass, hdirac, hmass_dirac, hdirac_mass]

/-- The DMP composite is a reflexive generalized inverse. Its product with the
original operator is the Drazin support. This holds in any associative star
ring; no matrix coordinates or commutative coefficient ring are used. -/
theorem drazinMoorePenroseComposite_reflexive
    (D : DrazinInverseData A)
    {moorePenroseInverse : A}
    (hMP : InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
      D.element moorePenroseInverse) :
    drazinMoorePenroseComposite D.drazinInverse D.element moorePenroseInverse *
        D.element *
        drazinMoorePenroseComposite D.drazinInverse D.element moorePenroseInverse =
      drazinMoorePenroseComposite D.drazinInverse D.element moorePenroseInverse ∧
    drazinMoorePenroseComposite D.drazinInverse D.element moorePenroseInverse *
        D.element = D.support := by
  have hDMP :
      drazinMoorePenroseComposite D.drazinInverse D.element moorePenroseInverse *
          D.element = D.support := by
    unfold drazinMoorePenroseComposite
    calc
      D.drazinInverse * D.element * moorePenroseInverse * D.element =
          D.drazinInverse * (D.element * moorePenroseInverse * D.element) := by
            simp only [mul_assoc]
      _ = D.drazinInverse * D.element := by rw [hMP.1]
      _ = D.support := D.inverse_mul_element_eq_support
  refine ⟨?_, hDMP⟩
  calc
    drazinMoorePenroseComposite D.drazinInverse D.element moorePenroseInverse *
        D.element *
        drazinMoorePenroseComposite D.drazinInverse D.element moorePenroseInverse =
        D.support *
          drazinMoorePenroseComposite D.drazinInverse D.element moorePenroseInverse := by
            rw [hDMP]
    _ = drazinMoorePenroseComposite D.drazinInverse D.element moorePenroseInverse := by
      unfold drazinMoorePenroseComposite
      calc
        D.support * (D.drazinInverse * D.element * moorePenroseInverse) =
            (D.drazinInverse * D.element * D.drazinInverse) *
              D.element * moorePenroseInverse := by
                rw [← D.inverse_mul_element_eq_support]
                simp only [mul_assoc]
        _ = D.drazinInverse * D.element * moorePenroseInverse := by
              rw [D.inverse_element_inverse]

/-- Multiplication of the Drazin--Moore--Penrose composite on the left by
the original operator factors through the Drazin support followed by the
original operator. This is the ordered form of the complementary DMP
factorization and holds in every associative ring. -/
theorem drazinMoorePenroseComposite_left_factorization
    (D : DrazinInverseData A) (moorePenroseInverse : A) :
    D.element *
        drazinMoorePenroseComposite D.drazinInverse D.element moorePenroseInverse =
      D.support * D.element * moorePenroseInverse := by
  unfold drazinMoorePenroseComposite
  calc
    D.element * (D.drazinInverse * D.element * moorePenroseInverse) =
        (D.element * D.drazinInverse) * D.element * moorePenroseInverse := by
          noncomm_ring
    _ = D.support * D.element * moorePenroseInverse := by
          rw [D.element_mul_inverse_eq_support]

/-- A Cartan reflection fixes a Drazin--Moore--Penrose composite whenever its
idempotent commutes with each ordered factor.  The hypotheses are explicit:
the Drazin data alone do not assert compatibility with an unrelated grading. -/
theorem peirceReflection_drazinMoorePenroseComposite_invariant
    {p d e m : A} (hp : p * p = p)
    (hd : p * d = d * p) (he : p * e = e * p) (hm : p * m = m * p) :
    InfoGeometry.Core.PeirceGrading.reflection p *
        drazinMoorePenroseComposite d e m *
        InfoGeometry.Core.PeirceGrading.reflection p =
      drazinMoorePenroseComposite d e m := by
  let x : A := d * e * m
  change InfoGeometry.Core.PeirceGrading.reflection p * x *
      InfoGeometry.Core.PeirceGrading.reflection p = x
  have hcomm : p * x = x * p := by
    calc
      p * x = (p * d) * e * m := by dsimp [x]; noncomm_ring
      _ = (d * p) * e * m := by rw [hd]
      _ = d * (p * e) * m := by noncomm_ring
      _ = d * (e * p) * m := by rw [he]
      _ = d * e * (p * m) := by noncomm_ring
      _ = d * e * (m * p) := by rw [hm]
      _ = x * p := by dsimp [x]; noncomm_ring
  have hreflect : InfoGeometry.Core.PeirceGrading.reflection p * x =
      x * InfoGeometry.Core.PeirceGrading.reflection p := by
    unfold InfoGeometry.Core.PeirceGrading.reflection
    noncomm_ring [hcomm]
  have hreflect_sq : InfoGeometry.Core.PeirceGrading.reflection p *
      InfoGeometry.Core.PeirceGrading.reflection p = 1 := by
    unfold InfoGeometry.Core.PeirceGrading.reflection
    noncomm_ring [hp]
  calc
    InfoGeometry.Core.PeirceGrading.reflection p * x *
        InfoGeometry.Core.PeirceGrading.reflection p =
        x * InfoGeometry.Core.PeirceGrading.reflection p *
          InfoGeometry.Core.PeirceGrading.reflection p := by rw [hreflect]
    _ = x := by
      rw [mul_assoc, hreflect_sq, mul_one]

end DrazinMoorePenrose

/-! ## Finite fiber-product Drazin assembly -/

/--
Fiberwise Drazin data over a product of rings.

This is the first theorem-bearing layer for finite/fiberwise localization:
each fiber supplies Drazin inverse data with its own support projection, and the
product algebra inherits Drazin data pointwise.
-/
structure FiberwiseDrazinData
    (ι : Type*) (R : ι → Type*) [∀ i, Ring (R i)] where
  element : ∀ i, R i
  inverse : ∀ i, R i
  support : ∀ i, R i
  element_mul_inverse_eq_support :
    ∀ i, element i * inverse i = support i
  inverse_mul_element_eq_support :
    ∀ i, inverse i * element i = support i
  commutes :
    ∀ i, element i * inverse i = inverse i * element i
  inverse_element_inverse :
    ∀ i, inverse i * element i * inverse i = inverse i

namespace FiberwiseDrazinData

variable {ι : Type*} {R : ι → Type*} [∀ i, Ring (R i)]
variable (F : FiberwiseDrazinData ι R)

/-- Fiberwise Drazin data assemble into Drazin data on the product algebra. -/
def toProductDrazinInverseData :
    DrazinInverseData (∀ i, R i) where
  element := F.element
  drazinInverse := F.inverse
  support := F.support
  element_mul_inverse_eq_support := by
    funext i
    exact F.element_mul_inverse_eq_support i
  inverse_mul_element_eq_support := by
    funext i
    exact F.inverse_mul_element_eq_support i
  commutes := by
    funext i
    exact F.commutes i
  inverse_element_inverse := by
    funext i
    exact F.inverse_element_inverse i

/-- Product-level commutation law obtained from fiberwise Drazin data. -/
theorem product_commutes :
    F.element * F.inverse = F.inverse * F.element :=
  F.toProductDrazinInverseData.commutes

/-- Product-level left support law obtained from fiberwise Drazin data. -/
theorem product_element_mul_inverse_eq_support :
    F.element * F.inverse = F.support :=
  F.toProductDrazinInverseData.element_mul_inverse_eq_support

/-- Product-level right support law obtained from fiberwise Drazin data. -/
theorem product_inverse_mul_element_eq_support :
    F.inverse * F.element = F.support :=
  F.toProductDrazinInverseData.inverse_mul_element_eq_support

/-- Product-level reflexive law obtained from fiberwise Drazin data. -/
theorem product_reflexive :
    F.inverse * F.element * F.inverse = F.inverse :=
  F.toProductDrazinInverseData.inverse_element_inverse

end FiberwiseDrazinData

/--
External algebra decomposed into Drazin fibers.

This is the theorem-safe socket for later direct-sum/direct-integral models:
a concrete model supplies the ring equivalence to a product of fibers, and the
finite product theorem runs on the product side.
-/
structure DrazinFiberEquivalence
    (A : Type*) [Ring A]
    (ι : Type*) (R : ι → Type*) [∀ i, Ring (R i)] where
  fiberEquiv : A ≃+* (∀ i, R i)
  fiberwise : FiberwiseDrazinData ι R

namespace DrazinFiberEquivalence

variable {A : Type*} [Ring A]
variable {ι : Type*} {R : ι → Type*} [∀ i, Ring (R i)]
variable (E : DrazinFiberEquivalence A ι R)

/-- The product-algebra Drazin data induced by the supplied fiber equivalence. -/
def productDrazinData :
    DrazinInverseData (∀ i, R i) :=
  E.fiberwise.toProductDrazinInverseData

end DrazinFiberEquivalence

/--
Regular core plus singular residue data relative to complementary projections.

`coreInv` is the inverse on the regular support.  `nilpotentPart` records the
singular/residue sector; no claim is made that the total element is globally
invertible.
-/
structure RelativeCoreNilpotentDecomposition (A : Type*) [Ring A] [StarRing A] where
  projections : SelfAdjointIdempotentPair A
  element : A
  regularPart : A
  coreInv : A
  nilpotentPart : A
  element_eq_regular_add_nilpotent :
    element = regularPart + nilpotentPart
  regular_supported_left :
    projections.support * regularPart = regularPart
  regular_supported_right :
    regularPart * projections.support = regularPart
  nilpotent_residue_supported_left :
    projections.residue * nilpotentPart = nilpotentPart
  nilpotent_residue_supported_right :
    nilpotentPart * projections.residue = nilpotentPart
  coreInv_supported_left :
    projections.support * coreInv = coreInv
  coreInv_supported_right :
    coreInv * projections.support = coreInv
  regular_mul_coreInv :
    regularPart * coreInv = projections.support
  coreInv_mul_regular :
    coreInv * regularPart = projections.support
  nilpotent_mul_coreInv :
    nilpotentPart * coreInv = 0
  coreInv_mul_nilpotent :
    coreInv * nilpotentPart = 0
  nilpotent_isNilpotent : IsNilpotent nilpotentPart

namespace RelativeCoreNilpotentDecomposition

variable {A : Type*} [Ring A] [StarRing A]
variable (D : RelativeCoreNilpotentDecomposition A)

/-- The localized Drazin residue is the singular/nilpotent component. -/
def localizedDrazinResidue : A :=
  D.nilpotentPart

/-- The localized Drazin regular core is the supported invertible component. -/
def localizedRegularCore : A :=
  D.regularPart

/-- The localized Drazin inverse is the inverse of the regular core. -/
def localizedRegularInverse : A :=
  D.coreInv

/-- The Drazin residue is left-supported by the residue projection. -/
theorem residue_supported_left :
    D.projections.residue * D.localizedDrazinResidue =
      D.localizedDrazinResidue :=
  D.nilpotent_residue_supported_left

/-- The Drazin residue is right-supported by the residue projection. -/
theorem residue_supported_right :
    D.localizedDrazinResidue * D.projections.residue =
      D.localizedDrazinResidue :=
  D.nilpotent_residue_supported_right

/-- The Drazin residue is invisible to the regular inverse on the left. -/
theorem residue_mul_regularInverse :
    D.localizedDrazinResidue * D.localizedRegularInverse = 0 :=
  D.nilpotent_mul_coreInv

/-- The Drazin residue is invisible to the regular inverse on the right. -/
theorem regularInverse_mul_residue :
    D.localizedRegularInverse * D.localizedDrazinResidue = 0 :=
  D.coreInv_mul_nilpotent

/-- Multiplying the total element by the regular inverse gives the support. -/
theorem element_mul_coreInv_eq_support :
    D.element * D.coreInv = D.projections.support := by
  rw [D.element_eq_regular_add_nilpotent]
  rw [add_mul, D.regular_mul_coreInv, D.nilpotent_mul_coreInv, add_zero]

/-- Multiplying the regular inverse by the total element gives the support. -/
theorem coreInv_mul_element_eq_support :
    D.coreInv * D.element = D.projections.support := by
  rw [D.element_eq_regular_add_nilpotent]
  rw [mul_add, D.coreInv_mul_regular, D.coreInv_mul_nilpotent, add_zero]

/-- The total element commutes with its Drazin inverse. -/
theorem element_coreInv_commutes :
    D.element * D.coreInv = D.coreInv * D.element := by
  rw [D.element_mul_coreInv_eq_support, D.coreInv_mul_element_eq_support]

/-- The Drazin inverse is stable under the usual inverse-element-inverse law. -/
theorem coreInv_element_coreInv_eq_coreInv :
    D.coreInv * D.element * D.coreInv = D.coreInv := by
  rw [D.coreInv_mul_element_eq_support, D.coreInv_supported_left]

/-- Extract Drazin inverse data from the explicit core/residue decomposition. -/
def toDrazinInverseData : DrazinInverseData A where
  element := D.element
  drazinInverse := D.coreInv
  support := D.projections.support
  element_mul_inverse_eq_support := D.element_mul_coreInv_eq_support
  inverse_mul_element_eq_support := D.coreInv_mul_element_eq_support
  commutes := D.element_coreInv_commutes
  inverse_element_inverse := D.coreInv_element_coreInv_eq_coreInv

@[simp]
theorem toDrazinInverseData_element :
    D.toDrazinInverseData.element = D.element :=
  rfl

@[simp]
theorem toDrazinInverseData_inverse :
    D.toDrazinInverseData.drazinInverse = D.localizedRegularInverse :=
  rfl

end RelativeCoreNilpotentDecomposition

/-- Simple residue factors of a semisimple quotient/block decomposition. -/
structure DivisionResidueBlockPacket.{uBlock, uDivision, uProjection} where
  Block : Type uBlock
  DivisionCarrier : Block → Type uDivision
  residueProjection : Block → Type uProjection
  carrier_divisionRing : ∀ b, DivisionRing (DivisionCarrier b)

namespace DivisionResidueBlockPacket

variable (P : DivisionResidueBlockPacket)

end DivisionResidueBlockPacket

/--
A Frobenius functional whose multiplication pairing is nondegenerate.

The pairing is not independent data: it is canonically `ε (a * b)`.  Its
Frobenius associativity therefore follows from associativity of multiplication.
-/
structure FrobeniusSelfDualPacket (A : Type*) [Ring A] where
  functional : A →+ ℝ
  nondegenerate : ∀ a, (∀ b, functional (a * b) = 0) → a = 0

namespace FrobeniusSelfDualPacket

variable {A : Type*} [Ring A]
variable (P : FrobeniusSelfDualPacket A)

/-- The multiplication pairing generated by the Frobenius functional. -/
def pairing (a b : A) : ℝ :=
  P.functional (a * b)

/-- Frobenius invariance is multiplication associativity, not supplied evidence. -/
theorem pairing_mul_left_eq_pairing_mul_right (a b c : A) :
    P.pairing (a * b) c = P.pairing a (b * c) := by
  simp only [pairing, mul_assoc]

/-- Nondegeneracy of the generated multiplication pairing. -/
theorem pairing_nondegenerate (a : A) (h : ∀ b, P.pairing a b = 0) :
    a = 0 :=
  P.nondegenerate a h

end FrobeniusSelfDualPacket

/-- Regular/singular divisor strata controlled by Drazin data. -/
structure SpectralDivisorStratification (A : Type*) [Ring A] [StarRing A] where
  Point : Type*
  weight : Point → A
  drazinAt : Point → RelativeCoreNilpotentDecomposition A
  drazin_weight_eq : ∀ p : Point, (drazinAt p).element = weight p
  regularLocus : Set Point
  singularLocus : Set Point
  locusCover : regularLocus ∪ singularLocus = Set.univ

namespace SpectralDivisorStratification

variable {A : Type*} [Ring A] [StarRing A]
variable (S : SpectralDivisorStratification A)

/-- Every point has Drazin data for its weight. -/
def drazinDataAt (p : S.Point) : DrazinInverseData A :=
  (S.drazinAt p).toDrazinInverseData

/-- The Drazin data element is the stratification weight. -/
theorem drazinDataAt_element_eq_weight (p : S.Point) :
    (S.drazinDataAt p).element = S.weight p :=
  S.drazin_weight_eq p

end SpectralDivisorStratification

end InfoGeometry.OperatorAlgebra.DrazinProjectionLocalization
