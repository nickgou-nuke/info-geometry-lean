import InfoGeometry.Canonical.BostConnesKMS
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BostConnesGalois
import InfoGeometry.Canonical.CyclicCocycleCantor
import InfoGeometry.Canonical.DrazinHodgeResidueBridge
import InfoGeometry.Canonical.SouriauDiracHodgeCoupling
import InfoGeometry.Krein.KreinSpace

/-!
# Souriau--Dirac--Hodge Integration in the Hestenes--Krein Lane

This file integrates the existing Bost--Connes multiplicative indexing with
the Hestenes--Krein, Drazin/Hodge, and finite chiral-cocycle owners already
present in the repository.

#### BUCKET 1: CLOSED FINITE THEOREMS

* `krein_rep_generator_mul` and `krein_rep_generator_one` transport the
  multiplicative Bost--Connes generators through a supplied Krein representation.
* `finite_trace_residue_twisted_index_vanishes` instantiates the finite
  trace/residue pairing by the proved Cantor cyclic-cocycle owner.
* `drazin_hodge_residue_readout_eq` reuses the Drazin/Hodge calibration owner.
* `dikin_convergence_estimate` re-exports the proved finite Dikin estimate.
* `galois_transport_on_cyclotomic_generator` transports the Galois action on
  cyclotomic generators through an explicitly supplied Krein representation.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

The Krein representation and Galois transport are conditional on explicit
representation/intertwining fields.  No completed representation theorem or
KMS classification is asserted here.

#### BUCKET 3: OPEN CLOSURE DEBT

* Construct the completed Hestenes--Krein Bost--Connes representation from the
  concrete infinite Cuntz/Krein carrier.
* Prove the analytic normal-cone/self-dual-cone theorem from a completed
  natural-cone owner.
* Upgrade the finite Dikin estimate to the completed spectral/Dikin convergence
  theorem on the Hestenes--Krein normal cone.
-/

open Matrix

open scoped InnerProductSpace

noncomputable section

universe u

namespace InfoGeometry.Canonical.SouriauDiracHodgeIntegration

open InfoGeometry.Arithmetic.BostConnesSystem
open InfoGeometry.Canonical.BostConnesKMS
open InfoGeometry.Canonical.BostConnesGalois
open InfoGeometry.Canonical.SouriauDiracHodgeCoupling
open InfoGeometry.Canonical.DrazinHodgeResidueBridge
open InfoGeometry.Krein

/-! ## 1. Bost--Connes generators on a Hestenes--Krein carrier -/

/--
A Hestenes--Krein representation of the multiplicatively indexed
Bost--Connes Cuntz system.

The carrier is a real Krein space.  The target algebra `Op` may still be the
abstract crossed-product algebra, but its action on the carrier is supplied as
a monoid homomorphism into real continuous endomorphisms.
-/
structure KreinBostConnesRepresentation
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (Op : Type u) [Ring Op] [StarRing Op] where
  /-- Proof-carrying Bost--Connes Cuntz indexing. -/
  cuntz : BostConnesCuntzSystem Op
  /-- Real Hestenes--Krein action of the algebra. -/
  ρ : Op →* (H →L[ℝ] H)

namespace KreinBostConnesRepresentation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H]
variable {Op : Type u} [Ring Op] [StarRing Op]
variable (R : KreinBostConnesRepresentation H Op)

/-- The represented Bost--Connes unit generator acts as the identity. -/
theorem krein_rep_generator_one :
    R.ρ (S R.cuntz 1) = 1 := by
  rw [S_one R.cuntz]
  exact map_one R.ρ

/-- Multiplicative indexing survives transport to the Hestenes--Krein carrier. -/
theorem krein_rep_generator_mul (n m : ℕ+) :
    R.ρ (S R.cuntz (n * m)) = R.ρ (S R.cuntz n) * R.ρ (S R.cuntz m) := by
  rw [S_mul R.cuntz n m]
  exact map_mul R.ρ (S R.cuntz n) (S R.cuntz m)

/-- Prime-power words transport through the same representation map. -/
theorem krein_rep_prime_power (p k : ℕ) [Fact p.Prime] :
    R.ρ (S R.cuntz (⟨p, (Fact.out : p.Prime).pos⟩ ^ k)) =
      R.ρ (S_prime R.cuntz p) ^ k := by
  let pp : ℕ+ := MultiplicativeIndexing.primePNat p (Fact.out : p.Prime)
  change R.ρ (S R.cuntz (pp ^ k)) = R.ρ (S_prime R.cuntz p) ^ k
  calc
    R.ρ (S R.cuntz (pp ^ k))
        = R.ρ ((S R.cuntz pp) ^ k) := by
          rw [S_prime_power R.cuntz p k (Fact.out : p.Prime)]
    _ = R.ρ (S R.cuntz pp) ^ k := map_pow R.ρ (S R.cuntz pp) k
    _ = R.ρ (S_prime R.cuntz p) ^ k := by
          simp [S_prime, pp]

end KreinBostConnesRepresentation

/-! ## 2. Trace/residue instantiation for twisted-index vanishing -/

/--
Finite trace/residue instantiation of the twisted index.

This is the closed finite matrix theorem: the trace functional is the concrete
Cantor chiral cocycle `finiteIndexPairing`, and vanishing is delegated to the
proved `CyclicCocycleCantor.chiral_anomaly_vanishes_at_flat_boundary` owner.
-/
theorem finite_trace_residue_twisted_index_vanishes
    (tilt D D_inv : Matrix (Fin 2) (Fin 2) ℂ)
    (proj : CyclicCocycleCantor.KTheoryProjection 2)
    (hAnti : D * tilt + tilt * D = 0)
    (hComm : D * proj.e = proj.e * D)
    (hDleft : D * D_inv = 1)
    (hDright : D_inv * D = 1) :
    CyclicCocycleCantor.finiteIndexPairing tilt proj = 0 :=
  CyclicCocycleCantor.chiral_anomaly_vanishes_at_flat_boundary
    tilt D D_inv proj hAnti hComm hDleft hDright

/--
Drazin/Hodge residue readout.

Once a Hodge projector is calibrated to the Drazin complementary projector,
every scalar residue/readout sees the same representative through either
projector.
-/
theorem drazin_hodge_residue_readout_eq
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (R : DrazinHodgeResidueCalibration (E := E))
    (φ : E →L[ℝ] ℝ)
    (x : E) :
    φ (R.HarmonicProjector x) = φ (R.CIK.spectralComplementaryProjector x) :=
  R.scalarReadout_harmonicProjector_eq_drazinComplement φ x

/-! ## 3. Finite Dikin convergence estimate -/

/-- The proved finite Dikin/Souriau remainder estimate used by the integration. -/
theorem dikin_convergence_estimate (ε : ℝ) (hε : |ε| ≤ 1) :
    Real.sqrt (2 * ((Real.cos ε - 1) ^ 2 + (Real.sin ε - ε) ^ 2)) ≤
      (2 * Real.sqrt 2) * ε ^ 2 :=
  dikin_bound ε hε

/-! ## 4. Galois/KMS transport through a Hestenes--Krein representation -/

/--
Conditional Galois/KMS transport on a Hestenes--Krein carrier.

This is the correct theorem boundary for the current codebase: a concrete
Hestenes--Krein representation, boundary embedding, Galois automorphism, and
intertwining law are explicit fields.  The file does not assert existence of
the completed representation.
-/
structure GaloisKMSKreinTransport
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C_comm Op G : Type u)
    [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
    [Ring Op] [StarRing Op] [Algebra ℂ Op]
    [GaloisActionData G]
    (e_rep : GroupElementRepresentation C_comm)
    (galoisAut : GaloisAlgebraAutomorphism C_comm e_rep (G := G)) where
  /-- Hestenes--Krein representation of the noncommutative algebra. -/
  ρ : Op →* (H →L[ℝ] H)
  /-- Embedding of commutative boundary observables into the Bost--Connes algebra. -/
  ι : C_comm →ₐ[ℂ] Op
  /-- Galois implementers on the Hestenes--Krein carrier. -/
  U : G → H →L[ℝ] H
  /-- Intertwining of the Galois action with the represented boundary algebra. -/
  intertwines : ∀ (g : G) (A : C_comm),
    U g * ρ (ι A) = ρ (ι (galoisAut.galoisAut g A)) * U g

namespace GaloisKMSKreinTransport

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H]
variable {C_comm Op G : Type u}
variable [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
variable [Ring Op] [StarRing Op] [Algebra ℂ Op]
variable [GaloisActionData G]
variable {e_rep : GroupElementRepresentation C_comm}
variable {galoisAut : GaloisAlgebraAutomorphism C_comm e_rep (G := G)}
variable (T : GaloisKMSKreinTransport H C_comm Op G e_rep galoisAut)

/-- Transport of the Galois action on cyclotomic generators to the Krein carrier. -/
theorem galois_transport_on_cyclotomic_generator
    (g : G) (r : ℚ) :
    T.U g * T.ρ (T.ι (e_rep.e r)) =
      T.ρ (T.ι (e_rep.e (GaloisActionData.actOnQ g r))) * T.U g := by
  rw [← galoisAut.galoisAut_on_generator g r]
  exact T.intertwines g (e_rep.e r)

end GaloisKMSKreinTransport

end InfoGeometry.Canonical.SouriauDiracHodgeIntegration
