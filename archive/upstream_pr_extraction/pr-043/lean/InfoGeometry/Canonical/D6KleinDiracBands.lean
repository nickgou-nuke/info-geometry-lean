import InfoGeometry.Canonical.D6KleinDiracHamiltonian
import InfoGeometry.Canonical.D6GlideSectorBundle
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Conditional real band branches on the finite Klein quotient

The two branches are defined when the orbit-symmetrized Dirac radicand is
nonnegative.  Their glide invariance gives genuine functions on the quotient.
-/

namespace InfoGeometry.Canonical.D6KleinDiracBands

noncomputable section

open InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient
open InfoGeometry.Canonical.D6KleinDiracHamiltonian
open InfoGeometry.Canonical.D6GlideSectorBundle

def radicand (p : TorusCell) : ℝ := orbitX p * orbitY p

def bandPlus (p : TorusCell) : ℝ := Real.sqrt (radicand p)

def bandMinus (p : TorusCell) : ℝ := -bandPlus p

theorem orbitX_glide (p : TorusCell) : orbitX (glide p) = orbitX p := by
  exact orbitSum_glide (fun q => (q.1.val : ℝ)) p

theorem orbitY_glide (p : TorusCell) : orbitY (glide p) = orbitY p := by
  exact orbitSum_glide (fun q => (q.2.val : ℝ)) p

theorem radicand_glide (p : TorusCell) : radicand (glide p) = radicand p := by
  simp [radicand, orbitX_glide p, orbitY_glide p]

theorem bandPlus_glide (p : TorusCell) : bandPlus (glide p) = bandPlus p := by
  simp [bandPlus, radicand_glide p]

theorem bandMinus_glide (p : TorusCell) : bandMinus (glide p) = bandMinus p := by
  simp [bandMinus, bandPlus_glide p]

theorem bandPlus_kleinOrbitRel {p q : TorusCell}
    (h : kleinOrbitRel p q) : bandPlus p = bandPlus q := by
  rcases h with h | h | h | h
  · subst q
    rfl
  · subst q
    exact (bandPlus_glide p).symm
  · subst q
    calc
      bandPlus p = bandPlus (glide p) := (bandPlus_glide p).symm
      _ = bandPlus (glide (glide p)) := (bandPlus_glide (glide p)).symm
      _ = bandPlus (glide2 p) := by rfl
  · subst q
    calc
      bandPlus p = bandPlus (glide p) := (bandPlus_glide p).symm
      _ = bandPlus (glide (glide p)) := (bandPlus_glide (glide p)).symm
      _ = bandPlus (glide (glide (glide p))) :=
        (bandPlus_glide (glide (glide p))).symm
      _ = bandPlus (glide3 p) := by rfl

theorem bandMinus_kleinOrbitRel {p q : TorusCell}
    (h : kleinOrbitRel p q) : bandMinus p = bandMinus q := by
  simpa [bandMinus] using congrArg Neg.neg (bandPlus_kleinOrbitRel h)

def quotientBandPlus : KleinHexQuotient → ℝ :=
  Quotient.lift bandPlus (fun _ _ h => bandPlus_kleinOrbitRel h)

def quotientBandMinus : KleinHexQuotient → ℝ :=
  Quotient.lift bandMinus (fun _ _ h => bandMinus_kleinOrbitRel h)

theorem quotientBandPlus_pullback (p : TorusCell) :
    quotientBandPlus (quotientMap p) = bandPlus p := rfl

theorem quotientBandMinus_pullback (p : TorusCell) :
    quotientBandMinus (quotientMap p) = bandMinus p := rfl

theorem radicand_kleinOrbitRel {p q : TorusCell}
    (h : kleinOrbitRel p q) : radicand p = radicand q := by
  rcases h with h | h | h | h
  · subst q
    rfl
  · subst q
    exact (radicand_glide p).symm
  · subst q
    rw [show glide2 p = glide (glide p) by rfl, radicand_glide,
      radicand_glide]
  · subst q
    calc
      radicand p = radicand (glide p) := (radicand_glide p).symm
      _ = radicand (glide (glide p)) := (radicand_glide (glide p)).symm
      _ = radicand (glide (glide (glide p))) :=
        (radicand_glide (glide (glide p))).symm
      _ = radicand (glide3 p) := by rfl

def quotientRadicand : KleinHexQuotient → ℝ :=
  Quotient.lift radicand (fun _ _ h => radicand_kleinOrbitRel h)

theorem quotientRadicand_pullback (p : TorusCell) :
    quotientRadicand (quotientMap p) = radicand p := rfl

theorem bandPlus_sq (p : TorusCell) (h : 0 ≤ radicand p) :
    bandPlus p ^ 2 = radicand p := by
  simpa [bandPlus] using Real.sq_sqrt h

theorem bandMinus_sq (p : TorusCell) (h : 0 ≤ radicand p) :
    bandMinus p ^ 2 = radicand p := by
  simp [bandMinus, bandPlus_sq p h]

def bandGap (p : TorusCell) : ℝ := bandPlus p - bandMinus p

theorem bandPlus_nonneg (p : TorusCell) : 0 ≤ bandPlus p := by
  exact Real.sqrt_nonneg _

theorem bandMinus_nonpos (p : TorusCell) : bandMinus p ≤ 0 := by
  simp [bandMinus, bandPlus_nonneg p]

theorem bandGap_nonneg (p : TorusCell) : 0 ≤ bandGap p := by
  simp [bandGap, bandMinus]
  linarith [bandPlus_nonneg p]

theorem bandGap_eq_two_bandPlus (p : TorusCell) :
    bandGap p = 2 * bandPlus p := by
  simp [bandGap, bandMinus]
  ring

theorem bandGap_eq_zero_iff (p : TorusCell) (h : 0 ≤ radicand p) :
    bandGap p = 0 ↔ radicand p = 0 := by
  constructor
  · intro hg
    have hp : bandPlus p = 0 := by
      rw [bandGap_eq_two_bandPlus p] at hg
      linarith [bandPlus_nonneg p]
    have hs := bandPlus_sq p h
    rw [hp] at hs
    simpa using hs.symm
  · intro hr
    simp [bandGap, bandMinus, bandPlus, hr]

theorem bandGap_pos_of_radicand_pos (p : TorusCell)
    (h : 0 < radicand p) : 0 < bandGap p := by
  rw [bandGap_eq_two_bandPlus]
  have hs : 0 < bandPlus p := by
    exact Real.sqrt_pos.2 h
  linarith

theorem bandGap_pos_iff_radicand_pos (p : TorusCell)
    (h : 0 ≤ radicand p) :
    0 < bandGap p ↔ 0 < radicand p := by
  constructor
  · intro hg
    by_contra hn
    have hr : radicand p = 0 := le_antisymm (not_lt.mp hn) h
    have hz := (bandGap_eq_zero_iff p h).2 hr
    linarith
  · exact bandGap_pos_of_radicand_pos p

def quotientBandGap (q : KleinHexQuotient) : ℝ :=
  quotientBandPlus q - quotientBandMinus q

def quotientBandTouching (q : KleinHexQuotient) : Prop :=
  quotientBandGap q = 0

theorem quotientBandGap_pullback (p : TorusCell) :
    quotientBandGap (quotientMap p) = bandGap p := rfl

theorem quotientBandTouching_pullback (p : TorusCell) :
    quotientBandTouching (quotientMap p) ↔ bandGap p = 0 := by
  rfl

theorem quotientBandGap_nonneg (q : KleinHexQuotient) :
    0 ≤ quotientBandGap q := by
  refine Quotient.inductionOn q ?_
  intro p
  change 0 ≤ bandGap p
  exact bandGap_nonneg p

theorem quotientBandGap_pos_of_radicand_pos
    (q : KleinHexQuotient)
    (h : 0 < quotientRadicand q) :
    0 < quotientBandGap q := by
  revert h
  refine Quotient.inductionOn q ?_
  intro p h
  have hp : 0 < radicand p := by
    simpa [quotientRadicand] using h
  change 0 < bandGap p
  exact bandGap_pos_of_radicand_pos p hp

theorem quotientBandGap_pos_iff_radicand_pos
    (q : KleinHexQuotient)
    (h : 0 ≤ quotientRadicand q) :
    0 < quotientBandGap q ↔ 0 < quotientRadicand q := by
  revert h
  refine Quotient.inductionOn q ?_
  intro p h
  have hp : 0 ≤ radicand p := by
    simpa [quotientRadicand] using h
  change 0 < bandGap p ↔ 0 < radicand p
  exact bandGap_pos_iff_radicand_pos p hp

theorem quotientBandTouching_iff_radicand_zero
    (q : KleinHexQuotient)
    (h : 0 ≤ quotientRadicand q) :
    quotientBandTouching q ↔ quotientRadicand q = 0 := by
  revert h
  refine Quotient.inductionOn q ?_
  intro p h
  have hp : 0 ≤ radicand p := by
    simpa [quotientRadicand] using h
  simpa [quotientBandTouching, quotientBandGap, quotientRadicand]
    using bandGap_eq_zero_iff p hp

def quotientSpectralPolynomial (q : KleinHexQuotient) (lam : ℝ) : ℝ :=
  lam ^ 2 - quotientRadicand q

theorem quotientSpectralPolynomial_bandPlus
    (q : KleinHexQuotient)
    (h : 0 ≤ quotientRadicand q) :
    quotientSpectralPolynomial q (quotientBandPlus q) = 0 := by
  revert h
  refine Quotient.inductionOn q ?_
  intro p h
  have hp : 0 ≤ radicand p := by
    simpa [quotientRadicand] using h
  simpa [quotientSpectralPolynomial, quotientRadicand]
    using sub_eq_zero.mpr (quotientBandPlus_pullback p ▸ bandPlus_sq p hp)

theorem quotientSpectralPolynomial_bandMinus
    (q : KleinHexQuotient)
    (h : 0 ≤ quotientRadicand q) :
    quotientSpectralPolynomial q (quotientBandMinus q) = 0 := by
  revert h
  refine Quotient.inductionOn q ?_
  intro p h
  have hp : 0 ≤ radicand p := by
    simpa [quotientRadicand] using h
  simpa [quotientSpectralPolynomial, quotientRadicand]
    using sub_eq_zero.mpr (quotientBandMinus_pullback p ▸ bandMinus_sq p hp)

theorem quotientSpectralPolynomial_factorization
    (q : KleinHexQuotient)
    (h : 0 ≤ quotientRadicand q) (lam : ℝ) :
    quotientSpectralPolynomial q lam =
      (lam - quotientBandPlus q) * (lam - quotientBandMinus q) := by
  revert h
  refine Quotient.inductionOn q ?_
  intro p h
  have hp : 0 ≤ radicand p := by
    simpa [quotientRadicand] using h
  change lam ^ 2 - radicand p =
    (lam - bandPlus p) * (lam - bandMinus p)
  rw [show bandMinus p = -bandPlus p by rfl]
  ring_nf
  rw [show bandPlus p ^ 2 = radicand p by exact bandPlus_sq p hp]

theorem quotientSpectralPolynomial_eq_zero_iff
    (q : KleinHexQuotient)
    (h : 0 ≤ quotientRadicand q) (lam : ℝ) :
    quotientSpectralPolynomial q lam = 0 ↔
      lam = quotientBandPlus q ∨ lam = quotientBandMinus q := by
  rw [quotientSpectralPolynomial_factorization q h lam]
  constructor
  · intro hz
    rcases mul_eq_zero.mp hz with hplus | hminus
    · exact Or.inl (sub_eq_zero.mp hplus)
    · exact Or.inr (sub_eq_zero.mp hminus)
  · rintro (rfl | rfl) <;> simp

def sectorBandPlus : D6KleinSectorBundle → ℝ :=
  Quotient.lift (fun p : SectorPoint => quotientBandPlus (quotientMap p.2))
    (fun p q h => by
      have hquot : quotientMap p.2 = quotientMap q.2 :=
        Quotient.sound h.2
      exact congrArg quotientBandPlus hquot)

def sectorBandMinus : D6KleinSectorBundle → ℝ :=
  Quotient.lift (fun p : SectorPoint => quotientBandMinus (quotientMap p.2))
    (fun p q h => by
      have hquot : quotientMap p.2 = quotientMap q.2 :=
        Quotient.sound h.2
      exact congrArg quotientBandMinus hquot)

theorem sectorBandPlus_rotate
    (k : InfoGeometry.Canonical.D6SixModeAction.D6Index)
    (q : D6KleinSectorBundle) :
    sectorBandPlus (quotientSectorRotate k q) = sectorBandPlus q := by
  refine Quotient.inductionOn q ?_
  intro p
  rfl

theorem sectorBandMinus_rotate
    (k : InfoGeometry.Canonical.D6SixModeAction.D6Index)
    (q : D6KleinSectorBundle) :
    sectorBandMinus (quotientSectorRotate k q) = sectorBandMinus q := by
  refine Quotient.inductionOn q ?_
  intro p
  rfl

theorem sectorBandPlus_reflect (q : D6KleinSectorBundle) :
    sectorBandPlus (quotientSectorReflect q) = sectorBandPlus q := by
  refine Quotient.inductionOn q ?_
  intro p
  rfl

theorem sectorBandMinus_reflect (q : D6KleinSectorBundle) :
    sectorBandMinus (quotientSectorReflect q) = sectorBandMinus q := by
  refine Quotient.inductionOn q ?_
  intro p
  rfl

def sectorBandGap (q : D6KleinSectorBundle) : ℝ :=
  sectorBandPlus q - sectorBandMinus q

def sectorBandTouching (q : D6KleinSectorBundle) : Prop :=
  sectorBandGap q = 0

def sectorRadicand : D6KleinSectorBundle → ℝ :=
  Quotient.lift (fun p : SectorPoint => quotientRadicand (quotientMap p.2))
    (fun _ _ h => congrArg quotientRadicand (Quotient.sound h.2))

theorem sectorBandGap_map (s : InfoGeometry.Canonical.D6SixModeAction.D6Index)
    (p : TorusCell) :
    sectorBandGap (sectorMap s p) = quotientBandGap (quotientMap p) := rfl

theorem sectorBandTouching_map
    (s : InfoGeometry.Canonical.D6SixModeAction.D6Index)
    (p : TorusCell) :
    sectorBandTouching (sectorMap s p) ↔
      quotientBandTouching (quotientMap p) := by
  rfl

theorem sectorRadicand_map
    (s : InfoGeometry.Canonical.D6SixModeAction.D6Index)
    (p : TorusCell) :
    sectorRadicand (sectorMap s p) = quotientRadicand (quotientMap p) := rfl

theorem sectorRadicand_rotate
    (k : InfoGeometry.Canonical.D6SixModeAction.D6Index)
    (q : D6KleinSectorBundle) :
    sectorRadicand (quotientSectorRotate k q) = sectorRadicand q := by
  refine Quotient.inductionOn q ?_
  intro p
  rfl

theorem sectorRadicand_reflect (q : D6KleinSectorBundle) :
    sectorRadicand (quotientSectorReflect q) = sectorRadicand q := by
  refine Quotient.inductionOn q ?_
  intro p
  rfl

theorem sectorBandGap_rotate
    (k : InfoGeometry.Canonical.D6SixModeAction.D6Index)
    (q : D6KleinSectorBundle) :
    sectorBandGap (quotientSectorRotate k q) = sectorBandGap q := by
  simp [sectorBandGap, sectorBandPlus_rotate, sectorBandMinus_rotate]

theorem sectorBandGap_reflect (q : D6KleinSectorBundle) :
    sectorBandGap (quotientSectorReflect q) = sectorBandGap q := by
  simp [sectorBandGap, sectorBandPlus_reflect, sectorBandMinus_reflect]

theorem sectorBandTouching_rotate
    (k : InfoGeometry.Canonical.D6SixModeAction.D6Index)
    (q : D6KleinSectorBundle) :
    sectorBandTouching (quotientSectorRotate k q) ↔
      sectorBandTouching q := by
  simp [sectorBandTouching, sectorBandGap_rotate]

theorem sectorBandTouching_reflect (q : D6KleinSectorBundle) :
    sectorBandTouching (quotientSectorReflect q) ↔
      sectorBandTouching q := by
  simp [sectorBandTouching, sectorBandGap_reflect]

theorem sectorBandGap_nonneg (q : D6KleinSectorBundle) :
    0 ≤ sectorBandGap q := by
  refine Quotient.inductionOn q ?_
  intro p
  change 0 ≤ quotientBandGap (quotientMap p.2)
  exact quotientBandGap_nonneg _

theorem sectorBandGap_pos_of_radicand_pos
    (q : D6KleinSectorBundle)
    (h : 0 < sectorRadicand q) :
    0 < sectorBandGap q := by
  revert h
  refine Quotient.inductionOn q ?_
  intro p h
  have hp : 0 < quotientRadicand (quotientMap p.2) := by
    simpa [sectorRadicand] using h
  change 0 < quotientBandGap (quotientMap p.2)
  exact quotientBandGap_pos_of_radicand_pos _ hp

theorem sectorBandGap_pos_iff_radicand_pos
    (q : D6KleinSectorBundle)
    (h : 0 ≤ sectorRadicand q) :
    0 < sectorBandGap q ↔ 0 < sectorRadicand q := by
  revert h
  refine Quotient.inductionOn q ?_
  intro p h
  have hp : 0 ≤ quotientRadicand (quotientMap p.2) := by
    simpa [sectorRadicand] using h
  change 0 < quotientBandGap (quotientMap p.2) ↔
    0 < quotientRadicand (quotientMap p.2)
  exact quotientBandGap_pos_iff_radicand_pos (quotientMap p.2) hp

def sectorSpectralPolynomial (q : D6KleinSectorBundle) (lam : ℝ) : ℝ :=
  lam ^ 2 - sectorRadicand q

theorem sectorSpectralPolynomial_bandPlus
    (q : D6KleinSectorBundle)
    (h : 0 ≤ sectorRadicand q) :
    sectorSpectralPolynomial q (sectorBandPlus q) = 0 := by
  revert h
  refine Quotient.inductionOn q ?_
  intro p h
  have hp : 0 ≤ quotientRadicand (quotientMap p.2) := by
    simpa [sectorRadicand] using h
  simpa [sectorSpectralPolynomial, sectorRadicand]
    using quotientSpectralPolynomial_bandPlus (quotientMap p.2) hp

theorem sectorSpectralPolynomial_bandMinus
    (q : D6KleinSectorBundle)
    (h : 0 ≤ sectorRadicand q) :
    sectorSpectralPolynomial q (sectorBandMinus q) = 0 := by
  revert h
  refine Quotient.inductionOn q ?_
  intro p h
  have hp : 0 ≤ quotientRadicand (quotientMap p.2) := by
    simpa [sectorRadicand] using h
  simpa [sectorSpectralPolynomial, sectorRadicand]
    using quotientSpectralPolynomial_bandMinus (quotientMap p.2) hp

theorem sectorSpectralPolynomial_factorization
    (q : D6KleinSectorBundle)
    (h : 0 ≤ sectorRadicand q) (lam : ℝ) :
    sectorSpectralPolynomial q lam =
      (lam - sectorBandPlus q) * (lam - sectorBandMinus q) := by
  revert h
  refine Quotient.inductionOn q ?_
  intro p h
  have hp : 0 ≤ quotientRadicand (quotientMap p.2) := by
    simpa [sectorRadicand] using h
  change sectorSpectralPolynomial (sectorMap p.1 p.2) lam =
    (lam - sectorBandPlus (sectorMap p.1 p.2)) *
      (lam - sectorBandMinus (sectorMap p.1 p.2))
  simpa [sectorSpectralPolynomial, sectorRadicand]
    using quotientSpectralPolynomial_factorization
      (quotientMap p.2) hp lam

theorem sectorSpectralPolynomial_eq_zero_iff
    (q : D6KleinSectorBundle)
    (h : 0 ≤ sectorRadicand q) (lam : ℝ) :
    sectorSpectralPolynomial q lam = 0 ↔
      lam = sectorBandPlus q ∨ lam = sectorBandMinus q := by
  rw [sectorSpectralPolynomial_factorization q h lam]
  constructor
  · intro hz
    rcases mul_eq_zero.mp hz with hplus | hminus
    · exact Or.inl (sub_eq_zero.mp hplus)
    · exact Or.inr (sub_eq_zero.mp hminus)
  · rintro (rfl | rfl) <;> simp

theorem sectorBandTouching_iff_radicand_zero
    (q : D6KleinSectorBundle)
    (h : 0 ≤ sectorRadicand q) :
    sectorBandTouching q ↔ sectorRadicand q = 0 := by
  revert h
  refine Quotient.inductionOn q ?_
  intro p h
  have hquot : 0 ≤ quotientRadicand (quotientMap p.2) := by
    simpa [sectorRadicand] using h
  simpa [sectorBandTouching, sectorBandGap, sectorRadicand]
    using quotientBandTouching_iff_radicand_zero (quotientMap p.2) hquot

def sectorTouchingLocus : Set D6KleinSectorBundle :=
  {q | sectorBandTouching q}

theorem sectorTouchingLocus_rotate_invariant
    (k : InfoGeometry.Canonical.D6SixModeAction.D6Index)
    (q : D6KleinSectorBundle) :
    q ∈ sectorTouchingLocus ↔ quotientSectorRotate k q ∈ sectorTouchingLocus := by
  simp [sectorTouchingLocus, sectorBandTouching_rotate]

theorem sectorTouchingLocus_reflect_invariant
    (q : D6KleinSectorBundle) :
    q ∈ sectorTouchingLocus ↔ quotientSectorReflect q ∈ sectorTouchingLocus := by
  simp [sectorTouchingLocus, sectorBandTouching_reflect]

theorem sectorSpectralPolynomial_rotate
    (k : InfoGeometry.Canonical.D6SixModeAction.D6Index)
    (q : D6KleinSectorBundle) (lam : ℝ) :
    sectorSpectralPolynomial (quotientSectorRotate k q) lam =
      sectorSpectralPolynomial q lam := by
  simp [sectorSpectralPolynomial, sectorRadicand_rotate]

theorem sectorSpectralPolynomial_reflect
    (q : D6KleinSectorBundle) (lam : ℝ) :
    sectorSpectralPolynomial (quotientSectorReflect q) lam =
      sectorSpectralPolynomial q lam := by
  simp [sectorSpectralPolynomial, sectorRadicand_reflect]

def sectorLocalPartition (β : ℝ) (q : D6KleinSectorBundle) : ℝ :=
  Real.exp (-β * sectorBandPlus q) + Real.exp (-β * sectorBandMinus q)

theorem sectorLocalPartition_pos (β : ℝ) (q : D6KleinSectorBundle) :
    0 < sectorLocalPartition β q := by
  exact add_pos (Real.exp_pos _) (Real.exp_pos _)

theorem sectorLocalPartition_rotate
    (β : ℝ) (k : InfoGeometry.Canonical.D6SixModeAction.D6Index)
    (q : D6KleinSectorBundle) :
    sectorLocalPartition β (quotientSectorRotate k q) =
      sectorLocalPartition β q := by
  simp [sectorLocalPartition, sectorBandPlus_rotate, sectorBandMinus_rotate]

theorem sectorLocalPartition_reflect
    (β : ℝ) (q : D6KleinSectorBundle) :
    sectorLocalPartition β (quotientSectorReflect q) =
      sectorLocalPartition β q := by
  simp [sectorLocalPartition, sectorBandPlus_reflect, sectorBandMinus_reflect]

def sectorPartitionFunction (β : ℝ) : ℝ :=
  ∑ q : D6KleinSectorBundle, sectorLocalPartition β q

theorem sectorPartitionFunction_reindex_rotate
    (β : ℝ)
    (k : InfoGeometry.Canonical.D6SixModeAction.D6Index) :
    (∑ q : D6KleinSectorBundle,
      sectorLocalPartition β (quotientSectorRotate k q)) =
      sectorPartitionFunction β := by
  simpa [sectorPartitionFunction] using
    (Equiv.sum_comp (quotientSectorRotateEquiv k)
      (fun q => sectorLocalPartition β q))

theorem sectorPartitionFunction_reindex_reflect (β : ℝ) :
    (∑ q : D6KleinSectorBundle,
      sectorLocalPartition β (quotientSectorReflect q)) =
      sectorPartitionFunction β := by
  simpa [sectorPartitionFunction] using
    (Equiv.sum_comp quotientSectorReflectEquiv
      (fun q => sectorLocalPartition β q))

end

end InfoGeometry.Canonical.D6KleinDiracBands
