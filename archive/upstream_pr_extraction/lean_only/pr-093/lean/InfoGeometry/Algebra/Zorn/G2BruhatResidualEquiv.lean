import InfoGeometry.Algebra.Zorn.G2ResidualSimpleExact
import InfoGeometry.Algebra.Zorn.G2BruhatResidualSimpleEquiv
import InfoGeometry.Algebra.Zorn.G2BruhatResidual
import InfoGeometry.GroupTheory.G2BruhatInversions
import InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
import InfoGeometry.Algebra.Zorn.G2CanonicalResidualPCWords

/-!
# Ordered inversion coordinates for Bruhat residual product images

This owner provides only the finite ordering interface.  It deliberately does
not identify Boolean coordinates with a concrete residual subgroup: that
requires an ordered root-subgroup product and separate injectivity and
surjectivity proofs.
-/

namespace InfoGeometry.Algebra.Zorn.G2BruhatResidualEquiv

open InfoGeometry.Algebra.Zorn.G2BruhatResidual
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.GroupTheory.G2BruhatInversions
open InfoGeometry.Algebra.Zorn.G2ReducedWords
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2ResidualSimpleExact
open InfoGeometry.Algebra.Zorn.G2CorrectedTComplementCard
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2BruhatResidualSimpleEquiv
open InfoGeometry.Algebra.Zorn.G2CanonicalResidualPCWords
open InfoGeometry.Algebra.Zorn.G2RootPCAlignment
open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords

abbrev ZeroBitPCExponent := {e : PCExponent // e 0 = false}

noncomputable def zeroBitPCExponentEquiv :
    ZeroBitPCExponent ≃ (Fin 5 → Bool) where
  toFun e i := e.1 i.succ
  invFun f := ⟨fun i => Fin.cases false (fun j => f j) i, by rfl⟩
  left_inv e := by
    apply Subtype.ext
    funext i
    exact Fin.cases (by simp [e.2]) (fun j => rfl) i
  right_inv f := by
    funext i
    rfl

@[simp] theorem zeroBitPCExponentEquiv_apply
    (e : ZeroBitPCExponent) (i : Fin 5) :
    zeroBitPCExponentEquiv e i = e.1 i.succ := rfl

@[simp] theorem zeroBitPCExponentEquiv_symm_apply
    (f : Fin 5 → Bool) (i : Fin 6) :
    (zeroBitPCExponentEquiv.symm f).1 i = Fin.cases false (fun j => f j) i := rfl

theorem zeroBitPCExponentEquiv_symm_apply_succ
    (f : Fin 5 → Bool) (i : Fin 5) :
    (zeroBitPCExponentEquiv.symm f).1 i.succ = f i := rfl

/-- Concrete parametrization of the corrected simple residual subgroup.
This is intentionally a five-free-bit PC parametrization, not an inversion-root
parametrization: the latter has cardinality eight for this Weyl parameter. -/
noncomputable def correctedSimpleResidualEquiv :
    ZeroBitPCExponent ≃ residualSubgroup (2, true) := by
  let f : ZeroBitPCExponent → residualSubgroup (2, true) := fun e =>
    ⟨G2TwoSylowSubgroup.pcWord e.1, by
      rw [residualSubgroup_simple_eq_correctedTComplementSubgroup]
      exact pcWord_mem_correctedTComplement e.1 e.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro e₁ e₂ h
    apply Subtype.ext
    apply pcWord_injective
    exact congrArg Subtype.val h
  · intro x
    have hx' : (x.1 : SplitOctF2Aut) ∈ zeroBitPCSubgroup := by
      rw [zeroBitPCSubgroup_eq_correctedTComplementSubgroup]
      rw [← residualSubgroup_simple_eq_correctedTComplementSubgroup]
      exact x.2
    rcases hx' with ⟨e, he, hxe⟩
    refine ⟨⟨e, he⟩, ?_⟩
    apply Subtype.ext
    exact hxe

/-- Coordinate form of the corrected simple product-image equivalence. -/
noncomputable def correctedSimpleResidualCoordinateEquiv :
    (Fin 5 → Bool) ≃ residualSubgroup (2, true) :=
  zeroBitPCExponentEquiv.symm.trans correctedSimpleResidualEquiv

theorem correctedSimpleResidualCoordinateEquiv_apply
    (f : Fin 5 → Bool) :
    (correctedSimpleResidualCoordinateEquiv f).1 =
      G2TwoSylowSubgroup.pcWord (zeroBitPCExponentEquiv.symm f).1 := rfl

theorem correctedSimpleResidualCoordinateEquiv_coordinate_readback
    (f : Fin 5 → Bool) (i : Fin 5) :
    (zeroBitPCExponentEquiv
      (correctedSimpleResidualEquiv.symm
        (correctedSimpleResidualCoordinateEquiv f))) i = f i := by
  simpa [correctedSimpleResidualCoordinateEquiv] using
    congrFun (zeroBitPCExponentEquiv.apply_symm_apply f) i

theorem correctedSimpleResidualCoordinateEquiv_card :
    Fintype.card (Fin 5 → Bool) = 32 := by
  simp

theorem correctedSimpleResidual_card_eq_pow_five :
    Nat.card (residualSubgroup (2, true)) = 2 ^ 5 := by
  rw [residualSubgroup_simple_card_eq_32]
  norm_num

/-! The native residual convention at this parameter is not the
inversion-root fiber: its corrected complement has five free bits, whereas
the Weyl inversion data has length three.  Record this as an interface
boundary so downstream owners cannot accidentally promote the wrong carrier
to a Bruhat equivalence. -/
theorem no_bruhatResidual_equiv_correctedSimple :
    ¬ Nonempty (BruhatResidualExponent (2, true) ≃ residualSubgroup (2, true)) := by
  letI : Fintype (residualSubgroup (2, true)) := Fintype.ofFinite _
  rintro ⟨e⟩
  have hcard := Fintype.card_congr e
  rw [bruhatResidualExponent_card] at hcard
  have hlen : dihedralLength (2, true) = 3 := by decide
  rw [hlen] at hcard
  have hres : Fintype.card (residualSubgroup (2, true)) = 32 := by
    simpa only [Nat.card_eq_fintype_card] using residualSubgroup_simple_card_eq_32
  rw [hres] at hcard
  norm_num at hcard

/-! The canonical residual coordinates occupy exactly the PC indices obtained
from the inverted positive roots.  This is the morphic support statement
needed before introducing any quotient coordinates. -/
noncomputable def canonicalActivePCIndices (w : G2WeylElement) : Finset (Fin 6) :=
  (canonicalSignedInversionRoots w).image (fun α => rootPCAlignment α)

noncomputable def inversionRootActiveEquiv (w : G2WeylElement) :
    { α : G2PositiveRoot // α ∈ canonicalSignedInversionRoots w } ≃
      { i : Fin 6 // i ∈ canonicalActivePCIndices w } := by
  let f : { α : G2PositiveRoot //
      α ∈ canonicalSignedInversionRoots w } →
      { i : Fin 6 // i ∈ canonicalActivePCIndices w } := fun α =>
    ⟨rootPCAlignment α.1,
      Finset.mem_image.mpr ⟨α.1, α.2, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro α β h
    apply Subtype.ext
    exact rootPCAlignment.injective (congrArg Subtype.val h)
  · intro i
    rcases Finset.mem_image.mp i.2 with ⟨α, hα, hαi⟩
    exact ⟨⟨α, hα⟩, Subtype.ext hαi⟩

theorem residualToPCExponent_eq_false_of_not_mem_active
    (w : G2WeylElement) (e : CanonicalResidualExponent w) (i : Fin 6)
    (hi : i ∉ canonicalActivePCIndices w) :
    residualToPCExponent w e i = false := by
  classical
  unfold residualToPCExponent
  apply dif_neg
  intro h
  rcases h with ⟨α, hα⟩
  apply hi
  exact Finset.mem_image.mpr ⟨α.1, α.2, hα⟩

theorem residualToPCExponent_active_readback
    (w : G2WeylElement) (e : CanonicalResidualExponent w)
    (α : { α : G2PositiveRoot //
      α ∈ canonicalSignedInversionRoots w }) :
    residualToPCExponent w e (rootPCAlignment α.1) = e α := by
  exact residualToPCExponent_at w e α

def canonicalActiveCoordinateImage (w : G2WeylElement) :
    Set (canonicalActivePCIndices w → Bool) :=
  Set.range (fun e : CanonicalResidualExponent w =>
    fun i => residualToPCExponent w e i.1)

noncomputable def canonicalResidualActiveImageEquiv (w : G2WeylElement) :
    CanonicalResidualExponent w ≃
      {x : canonicalActivePCIndices w → Bool //
        x ∈ canonicalActiveCoordinateImage w} := by
  let f : CanonicalResidualExponent w →
      {x : canonicalActivePCIndices w → Bool //
        x ∈ canonicalActiveCoordinateImage w} := fun e =>
    ⟨fun i => residualToPCExponent w e i.1, ⟨e, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro e₁ e₂ h
    funext α
    have hcoord := congrFun (congrArg Subtype.val h)
      (⟨rootPCAlignment α.1, Finset.mem_image.mpr ⟨α.1, α.2, rfl⟩⟩ :
        canonicalActivePCIndices w)
    change residualToPCExponent w e₁ (rootPCAlignment α.1) =
      residualToPCExponent w e₂ (rootPCAlignment α.1) at hcoord
    rw [residualToPCExponent_active_readback,
      residualToPCExponent_active_readback] at hcoord
    exact hcoord
  · intro x
    rcases x.2 with ⟨e, he⟩
    exact ⟨e, Subtype.ext he⟩

theorem canonicalResidualImage_card :
    Nat.card {x : residualSubgroup (2, true) //
      x ∈ canonicalResidualImage} = 8 := by
  rw [← Nat.card_congr canonicalResidualImageEquiv]
  have hlen : weylLength (weylElementOfNF (2, true)) = 3 := by decide
  rw [Nat.card_eq_fintype_card,
    G2CanonicalResidualFibers.canonicalResidualExponent_card, hlen]
  decide

/-- Canonical ordering of the inversion-root subtype. -/
noncomputable def orderedInversionRoots (p : WeylG2) :
    Fin (dihedralLength p) ≃
      { α : G2PositiveRoot // α ∈ bruhatInversionRoots p } :=
  (Finite.equivFinOfCardEq
      (by
        simp [Nat.card_eq_fintype_card, bruhatInversionRoots_card p])).symm

@[simp]
theorem orderedInversionRoots_apply (p : WeylG2)
    (i : Fin (dihedralLength p)) :
    (orderedInversionRoots p i).1 ∈ bruhatInversionRoots p :=
  (orderedInversionRoots p i).2

theorem orderedInversionRoots_bijective (p : WeylG2) :
    Function.Bijective (orderedInversionRoots p) :=
  (orderedInversionRoots p).bijective

end InfoGeometry.Algebra.Zorn.G2BruhatResidualEquiv
