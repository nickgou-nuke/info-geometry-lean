import InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient
import Mathlib.Tactic

/-!
# Bands on the finite Klein Brillouin quotient

Band functions are defined on the quotient carrier itself.  Their pullbacks to
the reciprocal torus are therefore automatically invariant under the glide
orbit relation.  This is the correct finite BZ layer; a Hamiltonian-specific
eigenvalue theorem remains a separate specialization.
-/

namespace InfoGeometry.Canonical.D6KleinBrillouinBands

open InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient

abbrev KleinBand := KleinHexQuotient → ℝ

def bandPullback (E : KleinBand) : TorusCell → ℝ :=
  fun p => E (quotientMap p)

theorem bandPullback_glide (E : KleinBand) (p : TorusCell) :
    bandPullback E (glide p) = bandPullback E p := by
  simp [bandPullback, quotientMap_glide]

theorem bandPullback_glide2 (E : KleinBand) (p : TorusCell) :
    bandPullback E (glide2 p) = bandPullback E p := by
  simp [bandPullback, quotientMap_glide2]

def bandPair := KleinBand × KleinBand

def separatedBands (B : bandPair) : Prop :=
  ∀ q, B.1 q < B.2 q

theorem separatedBands_gap (B : bandPair) (hB : separatedBands B) (q : KleinHexQuotient) :
    0 < B.2 q - B.1 q := by
  linarith [hB q]

def constantBands (eMinus ePlus : ℝ) : bandPair :=
  (fun _ => eMinus, fun _ => ePlus)

theorem constantBands_separated {eMinus ePlus : ℝ} (h : eMinus < ePlus) :
    separatedBands (constantBands eMinus ePlus) := by
  intro q
  exact h

end InfoGeometry.Canonical.D6KleinBrillouinBands
