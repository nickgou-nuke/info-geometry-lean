import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Volume.Pfaffian

/-!
# InfoGeometry.Volume.PfaffianPathBridge

Combinatorial/path-count bridge for determinants and Pfaffians.

The existing `InfoGeometry.Volume.Pfaffian` file owns the conservative
positive-branch identity

  pfaffian(W)^2 = |det W|.

This file records the separate signed combinatorial owner surface:

* determinant = signed source--sink path-family volume;
* Pfaffian = signed fermionic perfect-pairing amplitude;
* Pfaffian² = determinant/even-volume shadow.

The full Lindström--Gessel--Viennot and signed Pfaffian expansion theorems
are witness-gated here.
-/

noncomputable section

namespace InfoGeometry.Volume.PfaffianPathBridge

open scoped BigOperators

/-! ## 1. Source--sink determinant path expansion -/

/--
Finite square source--sink path-matrix packet.

`Index` labels both sources and sinks.  If a future application has separate
source and sink types, add an equivalence `Source ≃ Sink` and transport to this
square form.
-/
structure FinitePathMatrixPacket where
  /-- Source/sink labels. -/
  Index : Type*

  /-- Finite index witness. -/
  indexFinite : Fintype Index

  /-- Decidable equality witness. -/
  indexDecidableEq : DecidableEq Index

  /-- Path type from source `i` to sink `j`. -/
  Path : Index → Index → Type*

  /-- Finite path-set witness. -/
  pathFinite : ∀ i j : Index, Fintype (Path i j)

  /-- Path amplitude. -/
  pathWeight : ∀ {i j : Index}, Path i j → ℝ

  /-- Source--sink path matrix. -/
  matrix : Matrix Index Index ℝ

  /-- Matrix entries are path sums. -/
  matrix_eq_path_sum :
    ∀ i j : Index,
      matrix i j =
        letI : Fintype (Path i j) := pathFinite i j
        Finset.univ.sum
          (fun γ : Path i j => pathWeight γ)

  /-- Determinant/even-volume readout. -/
  determinantReadout : ℝ

  /-- The determinant readout is the determinant of the path matrix. -/
  determinantReadout_eq_det :
    determinantReadout =
      letI : Fintype Index := indexFinite
      letI : DecidableEq Index := indexDecidableEq
      Matrix.det matrix

  /-- Signed expansion over source--sink path families. -/
  signedPathFamilyExpansion : ℝ

  /--
  Witness that the determinant equals the signed path-family expansion.

  This is the determinant expansion owner.  The stronger LGV reduction to
  nonintersecting paths should be a separate witness with graph hypotheses.
  -/
  det_eq_signedPathFamilyExpansion :
    (letI : Fintype Index := indexFinite
     letI : DecidableEq Index := indexDecidableEq
     Matrix.det matrix)
      =
    signedPathFamilyExpansion

/--
The determinant readout is the signed source--sink path-family expansion.
-/
theorem determinant_eq_signed_source_sink_path_sum
    (P : FinitePathMatrixPacket) :
    P.determinantReadout = P.signedPathFamilyExpansion := by
  rw [P.determinantReadout_eq_det]
  exact P.det_eq_signedPathFamilyExpansion

/-! ## 2. Skew pairing / Pfaffian matching expansion -/

/--
A skew boundary pairing matrix.

This is the correct carrier for a signed Pfaffian.
-/
structure SkewPairingMatrixPacket where
  /-- Boundary endpoints / defects to be paired. -/
  Boundary : Type*

  /-- Finite endpoint witness. -/
  boundaryFinite : Fintype Boundary

  /-- Decidable equality witness. -/
  boundaryDecidableEq : DecidableEq Boundary

  /-- Antisymmetric pair-weight matrix. -/
  W : Matrix Boundary Boundary ℝ

  /-- Skewness witness. -/
  skew : ∀ i j : Boundary, W i j = - W j i

/--
Pfaffian matching expansion packet.

`pfaffianAmplitude` is the primitive signed fermionic amplitude.
`determinantEvenVolume` is the even determinant/volume shadow.
-/
structure PfaffianMatchingExpansionPacket where
  /-- Skew pairing matrix data. -/
  skewPairing : SkewPairingMatrixPacket

  /-- Perfect pairings/matchings of the boundary endpoints. -/
  PerfectPairing : Type*

  /-- Finite perfect-pairing witness. -/
  pairingFinite : Fintype PerfectPairing

  /-- Sign of a perfect pairing. Usually ±1. -/
  pairingSign : PerfectPairing → ℝ

  /-- Optional sign normalization. -/
  pairingSign_sq :
    ∀ p : PerfectPairing, pairingSign p ^ 2 = 1

  /-- Product weight of a perfect pairing. -/
  pairingProductWeight : PerfectPairing → ℝ

  /-- Signed matching expansion. -/
  matchingExpansion : ℝ

  /-- Pfaffian amplitude. -/
  pfaffianAmplitude : ℝ

  /-- Even determinant/volume shadow. -/
  determinantEvenVolume : ℝ

  /-- Matching expansion is the signed sum over perfect pairings. -/
  matchingExpansion_sumWitness :
    matchingExpansion =
      letI : Fintype PerfectPairing := pairingFinite
      Finset.univ.sum
        (fun p : PerfectPairing =>
          pairingSign p * pairingProductWeight p)

  /-- Pfaffian equals the signed perfect-matching expansion. -/
  pfaffian_eq_matchingExpansion :
    pfaffianAmplitude = matchingExpansion

  /-- Pfaffian square gives the even determinant/volume shadow. -/
  pfaffian_sq_eq_determinantEvenVolume :
    pfaffianAmplitude ^ 2 = determinantEvenVolume

/--
The signed Pfaffian is the signed sum over perfect pairings.
-/
theorem pfaffian_eq_signed_pairing_sum
    (P : PfaffianMatchingExpansionPacket) :
    P.pfaffianAmplitude =
      (letI : Fintype P.PerfectPairing := P.pairingFinite
       Finset.univ.sum
        (fun p : P.PerfectPairing =>
          P.pairingSign p * P.pairingProductWeight p)) := by
  rw [P.pfaffian_eq_matchingExpansion]
  exact P.matchingExpansion_sumWitness

/--
The determinant/even-volume shadow is the square of the Pfaffian amplitude.
-/
theorem determinant_even_volume_eq_pfaffian_sq
    (P : PfaffianMatchingExpansionPacket) :
    P.determinantEvenVolume = P.pfaffianAmplitude ^ 2 := by
  exact P.pfaffian_sq_eq_determinantEvenVolume.symm

/-! ## 3. Compatibility with positive-branch Pfaffian -/

/--
Compatibility with the existing positive-branch convention.

The existing file owns a nonnegative branch such as

  pf_pos(W)^2 = |det W|.

This witness says that this positive branch is the absolute value of the
signed combinatorial Pfaffian.
-/
structure PositiveBranchPfaffianCompatibility
    (P : PfaffianMatchingExpansionPacket) where

  pf_pos : ℝ

  pf_pos_sq :
    pf_pos ^ 2 = |P.determinantEvenVolume|

  pf_pos_eq_abs_signed :
    pf_pos = |P.pfaffianAmplitude|

/-! ## 4. Chiral arrow interpretation -/

/--
Chiral source/sink path-word data.

`uPlus` and `uMinus` generate directed path words.  The determinant/Pfaffian
readouts are not automatic; they are supplied by the path and pairing packets.
-/
structure ChiralPathWordPacket where
  /-- Ambient operator host. -/
  OperatorAlgebra : Type*

  /-- Positive/source-to-sink chiral arrow. -/
  uPlus : OperatorAlgebra

  /-- Negative/sink-to-source chiral arrow. -/
  uMinus : OperatorAlgebra

  /-- Even return sector generated by `uPlus * uMinus`. -/
  plusMinusReturnSector : Type*

  /-- Even return sector generated by `uMinus * uPlus`. -/
  minusPlusReturnSector : Type*

  /-- Path-word family generated by the chiral arrows. -/
  PathWord : Type*

  /-- Path-word amplitude. -/
  pathWordAmplitude : PathWord → ℝ

  /-- Concrete operator letters carried by each path word. -/
  pathWordLetters : PathWord → List OperatorAlgebra

/--
Full Pfaffian/path bridge packet.

This keeps determinant, Pfaffian, and chiral-arrow interpretations together
without identifying them unless explicit witnesses are present.
-/
structure PfaffianPathBridgePacket where
  /-- Chiral path-word layer. -/
  chiralPaths : ChiralPathWordPacket

  /-- Source--sink determinant path expansion. -/
  determinantPaths : FinitePathMatrixPacket

  /-- Skew pairing / Pfaffian matching expansion. -/
  pfaffianPairings : PfaffianMatchingExpansionPacket

  /--
  Equality identifying the determinant path readout with the even-volume
  readout of the Pfaffian sector.
  -/
  determinantAsEvenPathVolume :
    determinantPaths.determinantReadout =
      pfaffianPairings.determinantEvenVolume

/--
Owner-side bridge theorem currently available from explicit Pfaffian/path data:
the Pfaffian matching packet carries the even-volume shadow identity.

This is the honest theorem currently owed by the packet. Stronger signed path /
chiral-word comparison theorems require witness terms, not just witness types.
-/
theorem constructPfaffianPathBridgeTarget
    (P : PfaffianPathBridgePacket) :
    P.pfaffianPairings.pfaffianAmplitude ^ 2 =
      P.pfaffianPairings.determinantEvenVolume :=
  P.pfaffianPairings.pfaffian_sq_eq_determinantEvenVolume

/-! The two remaining bridge readouts are already owned by the matching packet. -/

theorem pfaffian_eq_fermionic_pairing
    (P : PfaffianPathBridgePacket) :
    P.pfaffianPairings.pfaffianAmplitude =
      P.pfaffianPairings.matchingExpansion :=
  P.pfaffianPairings.pfaffian_eq_matchingExpansion

theorem determinant_even_volume_eq_pfaffian_sq_bridge
    (P : PfaffianPathBridgePacket) :
    P.pfaffianPairings.determinantEvenVolume =
      P.pfaffianPairings.pfaffianAmplitude ^ 2 :=
  determinant_even_volume_eq_pfaffian_sq P.pfaffianPairings

end InfoGeometry.Volume.PfaffianPathBridge
