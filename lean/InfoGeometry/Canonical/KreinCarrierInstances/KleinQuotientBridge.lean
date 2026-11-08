/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KreinCarrierInstances.Carrier
import InfoGeometry.Canonical.KreinCarrierInstances.Datum
import InfoGeometry.Arithmetic.KreinCenteredXiGlideBridge
import InfoGeometry.Topology.KleinBottleQuotient
import InfoGeometry.Topology.KleinAffineBrillouinConjugacy

/-!
# Klein quotient readout of the real double-Krein chart

The L² carrier is a covering chart.  This file gives the explicit coordinate
equivalence to the affine covering plane and proves that the carrier glide
becomes the affine deck generator, hence is identified by the existing Klein
orbit quotient.  The coordinate change is not asserted to preserve the Krein
form.
-/

noncomputable section

namespace InfoGeometry.Canonical.KreinCarrierInstances

open InfoGeometry.Topology.KleinQuotientDeckInvariants
open InfoGeometry.Topology.KleinAffineOrbitQuotient
open InfoGeometry.Topology.KleinBottleQuotient
open InfoGeometry.Arithmetic.KreinCenteredXiGlideBridge
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge

/-- Coordinates on the affine Klein covering plane from the double-real
carrier: exchange the two chart coordinates and normalize the horizontal
half-shift as a unit vertical deck step. -/
def kreinCarrierToKleinCover (p : KleinBottleCarrier) : PlanePoint :=
  (WithLp.snd p, 2 * WithLp.fst p)

/-- The horizontal translation direction in the wallpaper chart, transported
back to the double-real carrier. -/
def kreinTransverseShift : KleinBottleCarrier ≃ KleinBottleCarrier where
  toFun p := WithLp.toLp (2 : ENNReal) (WithLp.fst p, WithLp.snd p + 1)
  invFun p := WithLp.toLp (2 : ENNReal) (WithLp.fst p, WithLp.snd p - 1)
  left_inv p := by
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext <;> simp
  right_inv p := by
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext <;> simp

/-- On the double-real carrier, the glide reverses the transverse shift. This
is the defining semidirect relation of the Klein deck action. -/
theorem kreinGlide_reverses_transverseShift (p : KleinBottleCarrier) :
    MoebiusSymmetry (kreinTransverseShift p) =
      kreinTransverseShift.symm (MoebiusSymmetry p) := by
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext <;> simp [MoebiusSymmetry, kreinTransverseShift]
  all_goals ring

/-- The coordinate readout is an equivalence of covering charts. -/
def kreinKleinCoverEquiv : KleinBottleCarrier ≃ PlanePoint where
  toFun := kreinCarrierToKleinCover
  invFun q := WithLp.toLp (2 : ENNReal) (q.2 / 2, q.1)
  left_inv p := by
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext <;> simp [kreinCarrierToKleinCover]
  right_inv q := by
    rcases q with ⟨x, y⟩
    simp [kreinCarrierToKleinCover]
    ring

/-- The coordinate equivalence is a homeomorphism for the native L² product
topology and the Euclidean product topology on the affine cover. -/
def kreinKleinCoverHomeomorph : KleinBottleCarrier ≃ₜ PlanePoint where
  toEquiv := kreinKleinCoverEquiv
  continuous_toFun := by
    change Continuous (fun p : KleinBottleCarrier =>
      (WithLp.snd p, 2 * WithLp.fst p))
    exact (WithLp.continuous_snd (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)).prodMk
      ((continuous_const : Continuous fun _ : KleinBottleCarrier => (2 : ℝ)).mul
        (WithLp.continuous_fst (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)))
  continuous_invFun := by
    change Continuous (fun q : PlanePoint =>
      WithLp.toLp (2 : ENNReal) (q.2 / 2, q.1))
    exact (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)).comp
      ((continuous_snd.div_const (2 : ℝ)).prodMk continuous_fst)

/-- The coordinate readout is onto the affine covering plane. -/
theorem kreinCarrierToKleinCover_surjective :
    Function.Surjective kreinCarrierToKleinCover := by
  exact kreinKleinCoverEquiv.surjective

/-- In the affine covering coordinates, the double-Krein chart glide is the
standard orientation-reversing Klein deck generator. -/
theorem kreinGlide_becomes_kleinDeck (p : KleinBottleCarrier) :
    kreinCarrierToKleinCover (MoebiusSymmetry p) =
      deckB (kreinCarrierToKleinCover p) := by
  simp [kreinCarrierToKleinCover, MoebiusSymmetry, deckB]
  ring


/-- The double-Krein glide is sewn to the same point by the existing affine
Klein quotient map. -/
theorem kreinGlide_identified_in_klein_quotient (p : KleinBottleCarrier) :
    quotientMap (kreinCarrierToKleinCover (MoebiusSymmetry p)) =
      quotientMap (kreinCarrierToKleinCover p) := by
  rw [kreinGlide_becomes_kleinDeck]
  exact glide_identified_in_quotient (kreinCarrierToKleinCover p)

/-- The transverse shift is also sewn by the existing affine Klein quotient. -/
theorem kreinTransverseShift_identified_in_klein_quotient (p : KleinBottleCarrier) :
    quotientMap (kreinCarrierToKleinCover (kreinTransverseShift p)) =
      quotientMap (kreinCarrierToKleinCover p) := by
  rw [show kreinCarrierToKleinCover (kreinTransverseShift p) =
      deckA (kreinCarrierToKleinCover p) by
        simp [kreinCarrierToKleinCover, kreinTransverseShift, deckA]]
  simpa [deckAct, deckAction, KleinDeckGroup.a, signR, signZ, deckA] using
    quotientMap_deckAct KleinDeckGroup.a (kreinCarrierToKleinCover p)

/-- Every point of the affine Klein quotient has a representative in the
double-real carrier chart. -/
theorem kreinCarrier_chart_surjects_onto_klein_quotient :
    Function.Surjective (fun p : KleinBottleCarrier =>
      quotientMap (kreinCarrierToKleinCover p)) := by
  intro q
  obtain ⟨x, rfl⟩ := quotientMap_surjective q
  obtain ⟨p, hp⟩ := kreinCarrierToKleinCover_surjective x
  exact ⟨p, congrArg quotientMap hp⟩

/-- The affine deck action transported back to the double-real carrier. -/
def kreinCarrierDeckAction (g : InfoGeometry.Topology.KleinAffineOrbitQuotient.Deck)
    (p : KleinBottleCarrier) : KleinBottleCarrier :=
  kreinKleinCoverEquiv.symm
    (InfoGeometry.Topology.KleinAffineOrbitQuotient.deckAct g (kreinCarrierToKleinCover p))

/-- The first deck generator on the carrier is its transverse shift. -/
theorem kreinCarrierDeckAction_a (p : KleinBottleCarrier) :
    kreinCarrierDeckAction KleinDeckGroup.a p = kreinTransverseShift p := by
  apply kreinKleinCoverEquiv.injective
  calc
    kreinKleinCoverEquiv (kreinCarrierDeckAction KleinDeckGroup.a p) =
        deckA (kreinCarrierToKleinCover p) := by
      simp [kreinCarrierDeckAction, InfoGeometry.Topology.KleinAffineOrbitQuotient.deckAct,
        InfoGeometry.Topology.KleinQuotientDeckInvariants.deckAction,
        InfoGeometry.Topology.KleinQuotientDeckInvariants.KleinDeckGroup.a,
        InfoGeometry.Topology.KleinQuotientDeckInvariants.signR,
        InfoGeometry.Topology.KleinQuotientDeckInvariants.signZ, deckA]
    _ = kreinKleinCoverEquiv (kreinTransverseShift p) := by
      simp [kreinKleinCoverEquiv, kreinCarrierToKleinCover,
        kreinTransverseShift, deckA]

/-- The orientation-reversing deck generator on the carrier is the Möbius
glide used to sew the double-real chart. -/
theorem kreinCarrierDeckAction_b (p : KleinBottleCarrier) :
    kreinCarrierDeckAction KleinDeckGroup.b p = MoebiusSymmetry p := by
  apply kreinKleinCoverEquiv.injective
  calc
    kreinKleinCoverEquiv (kreinCarrierDeckAction KleinDeckGroup.b p) =
        deckB (kreinCarrierToKleinCover p) := by
      simp [kreinCarrierDeckAction, InfoGeometry.Topology.KleinAffineOrbitQuotient.deckAct,
        InfoGeometry.Topology.KleinQuotientDeckInvariants.deckAction,
        InfoGeometry.Topology.KleinQuotientDeckInvariants.KleinDeckGroup.b,
        InfoGeometry.Topology.KleinQuotientDeckInvariants.signR,
        InfoGeometry.Topology.KleinQuotientDeckInvariants.signZ, deckB]
    _ = kreinKleinCoverEquiv (MoebiusSymmetry p) :=
      (kreinGlide_becomes_kleinDeck p).symm

/-- The carrier projection identifies exactly the transported deck orbits. -/
theorem kreinCarrierKleinQuotientMap_eq_iff (p q : KleinBottleCarrier) :
    quotientMap (kreinCarrierToKleinCover p) =
      quotientMap (kreinCarrierToKleinCover q) ↔
    ∃ g : InfoGeometry.Topology.KleinAffineOrbitQuotient.Deck, kreinCarrierDeckAction g p = q := by
  rw [quotientMap_eq_iff]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    calc
      kreinCarrierDeckAction g p = kreinKleinCoverEquiv.symm
          (InfoGeometry.Topology.KleinAffineOrbitQuotient.deckAct g
            (kreinCarrierToKleinCover p)) := rfl
      _ = kreinKleinCoverEquiv.symm (kreinCarrierToKleinCover q) :=
        congrArg kreinKleinCoverEquiv.symm hg
      _ = q := kreinKleinCoverEquiv.left_inv q
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    calc
      InfoGeometry.Topology.KleinAffineOrbitQuotient.deckAct g
          (kreinCarrierToKleinCover p) =
          kreinKleinCoverEquiv (kreinKleinCoverEquiv.symm
            (InfoGeometry.Topology.KleinAffineOrbitQuotient.deckAct g
              (kreinCarrierToKleinCover p))) :=
        (kreinKleinCoverEquiv.apply_symm_apply _).symm
      _ = kreinKleinCoverEquiv q := congrArg kreinKleinCoverEquiv hg
      _ = kreinCarrierToKleinCover q := rfl

/-- The reflection induced on the affine cover by the double-real Krein
fundamental symmetry. -/
def kreinCoverParity (q : PlanePoint) : PlanePoint := (-q.1, q.2)

/-- Conjugation by cover parity sends (m,n) to (-m,n). -/
def kreinDeckParity
    (g : InfoGeometry.Topology.KleinAffineOrbitQuotient.Deck) :
    InfoGeometry.Topology.KleinAffineOrbitQuotient.Deck :=
  ⟨-g.m, g.n⟩

/-- Cover parity normalizes every affine deck transformation. -/
theorem kreinCoverParity_deckAct
    (g : InfoGeometry.Topology.KleinAffineOrbitQuotient.Deck) (q : PlanePoint) :
    kreinCoverParity
        (InfoGeometry.Topology.KleinAffineOrbitQuotient.deckAct g q) =
      InfoGeometry.Topology.KleinAffineOrbitQuotient.deckAct
        (kreinDeckParity g) (kreinCoverParity q) := by
  rcases g with ⟨m, n⟩
  rcases q with ⟨x, y⟩
  simp [kreinCoverParity, kreinDeckParity,
    InfoGeometry.Topology.KleinAffineOrbitQuotient.deckAct,
    InfoGeometry.Topology.KleinQuotientDeckInvariants.deckAction]
  ring

/-- The cover reflection descends to an involution of the Klein orbit quotient. -/
def kreinKleinQuotientParity :
    InfoGeometry.Topology.KleinAffineOrbitQuotient.KleinAffineQuotient →
      InfoGeometry.Topology.KleinAffineOrbitQuotient.KleinAffineQuotient :=
  Quotient.lift
    (fun q => quotientMap (kreinCoverParity q))
    (by
      intro q r hqr
      rcases hqr with ⟨g, hgr⟩
      apply (InfoGeometry.Topology.KleinAffineOrbitQuotient.quotientMap_eq_iff _ _).mpr
      refine ⟨kreinDeckParity g, ?_⟩
      calc
        InfoGeometry.Topology.KleinAffineOrbitQuotient.deckAct
            (kreinDeckParity g) (kreinCoverParity q) =
            kreinCoverParity (InfoGeometry.Topology.KleinAffineOrbitQuotient.deckAct g q) :=
          (kreinCoverParity_deckAct g q).symm
        _ = kreinCoverParity r := congrArg kreinCoverParity hgr)

/-- The descended Krein parity is an involution on the Klein bottle quotient. -/
theorem kreinKleinQuotientParity_involutive :
    Function.Involutive kreinKleinQuotientParity := by
  intro q
  refine Quotient.inductionOn q ?_
  intro p
  change kreinKleinQuotientParity (kreinKleinQuotientParity (quotientMap p)) =
    quotientMap p
  change quotientMap (kreinCoverParity (kreinCoverParity p)) = quotientMap p
  simp [kreinCoverParity]

/-- The carrier's existing fundamental symmetry is the cover parity in the
affine Klein chart. -/
theorem fundamentalSymmetryKlein_intertwines_kreinCoverParity
    (p : KleinBottleCarrier) :
    kreinCarrierToKleinCover (fundamentalSymmetryKlein p) =
      kreinCoverParity (kreinCarrierToKleinCover p) := by
  simp [kreinCarrierToKleinCover, kreinCoverParity,
    fundamentalSymmetryKlein_apply]

/-- The fundamental symmetry therefore induces the already-defined parity
involution on the Klein quotient. This identifies reflected representatives;
it does not assert that unrelated functions descend through the glide quotient. -/
theorem fundamentalSymmetryKlein_intertwines_kreinKleinQuotientParity
    (p : KleinBottleCarrier) :
    quotientMap (kreinCarrierToKleinCover (fundamentalSymmetryKlein p)) =
      kreinKleinQuotientParity (quotientMap (kreinCarrierToKleinCover p)) := by
  change quotientMap (kreinCoverParity (kreinCarrierToKleinCover p)) =
    kreinKleinQuotientParity (quotientMap (kreinCarrierToKleinCover p))
  rfl

/-- A quotient point is fixed by descended Krein parity exactly when its first
cover coordinate is half-integral. The additional fixed classes arise from
integer deck translations, so the quotient fixed locus is larger than the
pointwise fixed line on the cover. -/
theorem kreinKleinQuotientParity_fixed_iff_half_integral
    (q : PlanePoint) :
    kreinKleinQuotientParity (quotientMap q) = quotientMap q ↔
      ∃ m : ℤ, (2 : ℝ) * q.1 = m := by
  rcases q with ⟨x, y⟩
  change quotientMap (-x, y) = quotientMap (x, y) ↔
    ∃ m : ℤ, (2 : ℝ) * x = m
  rw [quotientMap_eq_iff]
  constructor
  · rintro ⟨⟨m, n⟩, h⟩
    have hn : n = 0 := by
      have hsecond := congrArg Prod.snd h
      have hnR : (n : ℝ) = 0 := by
        have heq : y + (n : ℝ) = y := by
          simpa [deckAct, deckAction] using hsecond
        linarith
      exact_mod_cast hnR
    subst n
    have hfirst := congrArg Prod.fst h
    simp [deckAct, deckAction, signR, signZ] at hfirst
    refine ⟨m, ?_⟩
    linarith

  · rintro ⟨m, hm⟩
    refine ⟨⟨m, 0⟩, ?_⟩
    apply Prod.ext
    · simp [deckAct, deckAction, signR, signZ]
      linarith
    · simp [deckAct, deckAction]

/-- Every fixed quotient class has a representative on one of two vertical
seams: the integer seam or its half-step translate. -/
theorem kreinKleinQuotientParity_fixed_class_has_seam_representative
    (x y : ℝ)
    (hfix : kreinKleinQuotientParity (quotientMap (x, y)) = quotientMap (x, y)) :
    quotientMap (x, y) = quotientMap (0, y) ∨
      quotientMap (x, y) = quotientMap (1 / 2, y) := by
  have hhalf := (kreinKleinQuotientParity_fixed_iff_half_integral (x, y)).mp hfix
  rcases hhalf with ⟨m, hm⟩
  rcases Int.even_or_odd' m with ⟨j, rfl | rfl⟩
  · left
    have hx : x = (j : ℝ) := by
      push_cast at hm
      linarith
    rw [quotientMap_eq_iff]
    refine ⟨⟨-j, 0⟩, ?_⟩
    apply Prod.ext
    · simp [deckAct, deckAction, signR, signZ, hx]
    · simp [deckAct, deckAction]
  · right
    have hx : x = (j : ℝ) + 1 / 2 := by
      push_cast at hm
      linarith
    rw [quotientMap_eq_iff]
    refine ⟨⟨-j, 0⟩, ?_⟩
    apply Prod.ext
    · simp [deckAct, deckAction, signR, signZ, hx]
    · simp [deckAct, deckAction]

/-- The integer and half-step seam representatives are distinct quotient
classes, so the fixed locus has two genuinely different seam types. -/
theorem kreinKleinQuotient_integer_and_half_seams_disjoint (y z : ℝ) :
    quotientMap (0, y) ≠ quotientMap (1 / 2, z) := by
  intro h
  obtain ⟨⟨m, n⟩, h⟩ := (quotientMap_eq_iff (0, y) (1 / 2, z)).mp h
  have hfirst := congrArg Prod.fst h
  have hm : (m : ℝ) = (1 / 2 : ℝ) := by
    simpa [deckAct, deckAction] using hfirst
  have hmR : (m : ℝ) * 2 = 1 := by linarith
  have hmZ : m * 2 = 1 := by exact_mod_cast hmR
  omega

/-- The descended parity fixed locus is exactly the union of the two seam
orbits represented by first coordinates `0` and `1/2`. -/
theorem kreinKleinQuotientParity_fixed_iff_two_seam_types (x y : ℝ) :
    kreinKleinQuotientParity (quotientMap (x, y)) = quotientMap (x, y) ↔
      quotientMap (x, y) = quotientMap (0, y) ∨
        quotientMap (x, y) = quotientMap (1 / 2, y) := by
  constructor
  · exact kreinKleinQuotientParity_fixed_class_has_seam_representative x y
  · rintro (hzero | hhalf)
    · have hfixed :
          kreinKleinQuotientParity (quotientMap (0, y)) = quotientMap (0, y) := by
        change quotientMap (kreinCoverParity (0, y)) = quotientMap (0, y)
        simp [kreinCoverParity]
      calc
        kreinKleinQuotientParity (quotientMap (x, y)) =
            kreinKleinQuotientParity (quotientMap (0, y)) := congrArg kreinKleinQuotientParity hzero
        _ = quotientMap (0, y) := hfixed
        _ = quotientMap (x, y) := hzero.symm
    · have hfixed :
          kreinKleinQuotientParity (quotientMap (1 / 2, y)) =
            quotientMap (1 / 2, y) := by
        change quotientMap (kreinCoverParity (1 / 2, y)) = quotientMap (1 / 2, y)
        rw [quotientMap_eq_iff]
        refine ⟨⟨1, 0⟩, ?_⟩
        norm_num [kreinCoverParity, deckAct, deckAction, signR, signZ]
      calc
        kreinKleinQuotientParity (quotientMap (x, y)) =
            kreinKleinQuotientParity (quotientMap (1 / 2, y)) := congrArg kreinKleinQuotientParity hhalf
        _ = quotientMap (1 / 2, y) := hfixed
        _ = quotientMap (x, y) := hhalf.symm

/-- In the centered Xi parameter, the quotient fixed classes lie on the
half-integral real-coordinate locus.  This is the quotient-level seam
condition; on the covering carrier, the pointwise fixed locus remains the
single critical line. -/
theorem kreinKleinQuotientParity_fixed_iff_centeredParameter_half_integral
    (p : KleinBottleCarrier) :
    kreinKleinQuotientParity (quotientMap (kreinCarrierToKleinCover p)) =
      quotientMap (kreinCarrierToKleinCover p) ↔
      ∃ m : ℤ, (2 : ℝ) *
        (InfoGeometry.Arithmetic.KreinCenteredXiGlideBridge.kreinCenteredParameter p).re = m := by
  have hfixed := kreinKleinQuotientParity_fixed_iff_half_integral
    (kreinCarrierToKleinCover p)
  have hfixed' :
      (kreinKleinQuotientParity (quotientMap (kreinCarrierToKleinCover p)) =
        quotientMap (kreinCarrierToKleinCover p)) ↔
      ∃ n : ℤ, (2 : ℝ) * WithLp.snd p = n := by
    simpa [kreinCarrierToKleinCover] using hfixed
  have hcoord :
      (InfoGeometry.Arithmetic.KreinCenteredXiGlideBridge.kreinCenteredParameter p).re =
        (1 / 2 : ℝ) - WithLp.snd p := by
    simp [InfoGeometry.Arithmetic.KreinCenteredXiGlideBridge.kreinCenteredParameter,
      InfoGeometry.Arithmetic.KreinCenteredXiGlideBridge.kreinCenteredZetaCoord]
    ring
  rw [hfixed']
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨1 - n, ?_⟩
    rw [hcoord]
    norm_num
    linarith
  · rintro ⟨m, hm⟩
    refine ⟨1 - m, ?_⟩
    rw [hcoord] at hm
    norm_num at hm ⊢
    linarith

/-- Restricting to the open critical strip removes the extra quotient fixed
classes: there, descended parity fixes a class exactly on the critical line. -/
theorem kreinKleinQuotientParity_fixed_iff_criticalLine_of_openStrip
    (p : KleinBottleCarrier)
    (hstrip :
      0 < (InfoGeometry.Arithmetic.KreinCenteredXiGlideBridge.kreinCenteredParameter p).re ∧
      (InfoGeometry.Arithmetic.KreinCenteredXiGlideBridge.kreinCenteredParameter p).re < 1) :
    kreinKleinQuotientParity (quotientMap (kreinCarrierToKleinCover p)) =
      quotientMap (kreinCarrierToKleinCover p) ↔
      InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.OnCriticalLine
        (InfoGeometry.Arithmetic.KreinCenteredXiGlideBridge.kreinCenteredParameter p) := by
  let s := InfoGeometry.Arithmetic.KreinCenteredXiGlideBridge.kreinCenteredParameter p
  have hstrip' : 0 < s.re ∧ s.re < 1 := hstrip
  rw [kreinKleinQuotientParity_fixed_iff_centeredParameter_half_integral]
  constructor
  · rintro ⟨m, hm⟩
    change 2 * s.re = (m : ℝ) at hm
    have hmloR : (0 : ℝ) < (m : ℝ) := by rw [← hm]; linarith [hstrip'.1]
    have hmhiR : (m : ℝ) < 2 := by rw [← hm]; linarith [hstrip'.2]
    have hmlo : 0 < m := by exact_mod_cast hmloR
    have hmhi : m < 2 := by exact_mod_cast hmhiR
    have hmone : m = 1 := by omega
    subst m
    norm_num at hm
    change s.re = 1 / 2
    linarith [hm]
  · intro hcrit
    change s.re = 1 / 2 at hcrit
    have hcrit' :
        (InfoGeometry.Arithmetic.KreinCenteredXiGlideBridge.kreinCenteredParameter p).re =
          1 / 2 := by simpa only [s] using hcrit
    refine ⟨1, ?_⟩
    rw [hcrit']
    norm_num

/-- The double-real carrier, followed by its affine Klein quotient projection,
has exactly the quotient topology: the chart change is a homeomorphism and the
affine orbit projection is the existing quotient map. -/
theorem kreinCarrierKleinQuotientMap_isQuotientMap :
    Topology.IsQuotientMap
      (fun p : KleinBottleCarrier =>
        quotientMap (kreinCarrierToKleinCover p)) := by
  change Topology.IsQuotientMap (quotientMap ∘ kreinKleinCoverHomeomorph)
  exact quotientMap_isQuotient.comp kreinKleinCoverHomeomorph.isQuotientMap

/-- The double-real Krein carrier presents the Brillouin Klein quotient with
its quotient topology through the existing affine-to-Brillouin homeomorphism.
This composes the carrier chart and orbit projection with the established
topological identification; it does not assert a descended Xi function. -/
theorem kreinCarrierToBrillouinKleinQuotient_isQuotientMap :
    Topology.IsQuotientMap
      (fun p : KleinBottleCarrier =>
        InfoGeometry.Topology.KleinAffineBrillouinConjugacy.affineQuotientToBrillouinQuotientHomeomorph
          (quotientMap (kreinCarrierToKleinCover p))) := by
  exact InfoGeometry.Topology.KleinAffineBrillouinConjugacy.affineQuotientToBrillouinQuotientHomeomorph.isQuotientMap.comp
      kreinCarrierKleinQuotientMap_isQuotientMap

/-- The image in the Klein quotient of the analytic Xi zero set on the
double-real carrier. This is an existential image of the covering-space zero
set, not a descended Xi-valued function. -/
def kreinKleinXiZeroImage :
    Set InfoGeometry.Topology.KleinAffineOrbitQuotient.KleinAffineQuotient :=
  {q | ∃ p : KleinBottleCarrier,
    quotientMap (kreinCarrierToKleinCover p) = q ∧
      entireRiemannXi (kreinCenteredParameter p) = 0}

/-- The quotient image of analytic Xi zeros is invariant under the descended
Krein reflection. The reflecting representative remains a zero by the
carrier theorem, and the representative's quotient class is transported by
the proved cover-intertwining law. -/
theorem kreinKleinXiZeroImage_invariant_under_parity (q :
    InfoGeometry.Topology.KleinAffineOrbitQuotient.KleinAffineQuotient) :
    q ∈ kreinKleinXiZeroImage ↔
      kreinKleinQuotientParity q ∈ kreinKleinXiZeroImage := by
  constructor
  · rintro ⟨p, rfl, hzero⟩
    refine ⟨fundamentalSymmetryKlein p, ?_, ?_⟩
    · exact fundamentalSymmetryKlein_intertwines_kreinKleinQuotientParity p
    · exact entireRiemannXi_zero_reflection_of_fundamentalSymmetry hzero
  · intro hq
    have hq' : kreinKleinQuotientParity q ∈ kreinKleinXiZeroImage := hq
    rcases hq' with ⟨p, hp, hzero⟩
    have hzero' := entireRiemannXi_zero_reflection_of_fundamentalSymmetry hzero
    refine ⟨fundamentalSymmetryKlein p, ?_, hzero'⟩
    rw [fundamentalSymmetryKlein_intertwines_kreinKleinQuotientParity]
    rw [hp]
    rw [kreinKleinQuotientParity_involutive]

/-- Krein parity on the Brillouin Klein quotient, transported by the proved
affine-to-Brillouin homeomorphism. -/
def kreinBrillouinQuotientParity
    (q : KleinBottleOrbitQuotient.KleinBrillouinQuotient) :=
  InfoGeometry.Topology.KleinAffineBrillouinConjugacy.affineQuotientToBrillouinQuotientHomeomorph
    (kreinKleinQuotientParity
      (InfoGeometry.Topology.KleinAffineBrillouinConjugacy.affineQuotientToBrillouinQuotientHomeomorph.symm q))

/-- The transported Brillouin parity is an involution. -/
theorem kreinBrillouinQuotientParity_involutive
    (q : KleinBottleOrbitQuotient.KleinBrillouinQuotient) :
    kreinBrillouinQuotientParity (kreinBrillouinQuotientParity q) = q := by
  unfold kreinBrillouinQuotientParity
  rw [InfoGeometry.Topology.KleinAffineBrillouinConjugacy.affineQuotientToBrillouinQuotientHomeomorph.symm_apply_apply]
  rw [kreinKleinQuotientParity_involutive]
  exact InfoGeometry.Topology.KleinAffineBrillouinConjugacy.affineQuotientToBrillouinQuotientHomeomorph.apply_symm_apply q

/-- The analytic Xi-zero image transported to the Brillouin Klein quotient.
It is an image of carrier zeros, rather than a descended Xi function. -/
def kreinBrillouinXiZeroImage :
    Set KleinBottleOrbitQuotient.KleinBrillouinQuotient :=
  InfoGeometry.Topology.KleinAffineBrillouinConjugacy.affineQuotientToBrillouinQuotientHomeomorph ''
    kreinKleinXiZeroImage

/-- The Xi-zero image on the Brillouin Klein quotient is invariant under the
transported Krein parity. -/
theorem kreinBrillouinXiZeroImage_invariant_under_parity
    (q : KleinBottleOrbitQuotient.KleinBrillouinQuotient) :
    q ∈ kreinBrillouinXiZeroImage ↔
      kreinBrillouinQuotientParity q ∈ kreinBrillouinXiZeroImage := by
  have hmem : ∀ z : KleinBottleOrbitQuotient.KleinBrillouinQuotient,
      z ∈ kreinBrillouinXiZeroImage ↔
        InfoGeometry.Topology.KleinAffineBrillouinConjugacy.affineQuotientToBrillouinQuotientHomeomorph.symm z ∈
          kreinKleinXiZeroImage := by
    intro z
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa using hq
    · intro hz
      exact ⟨_, hz, by simp⟩
  rw [hmem, hmem]
  simpa [kreinBrillouinQuotientParity] using
    (kreinKleinXiZeroImage_invariant_under_parity
      (InfoGeometry.Topology.KleinAffineBrillouinConjugacy.affineQuotientToBrillouinQuotientHomeomorph.symm q))

end InfoGeometry.Canonical.KreinCarrierInstances
