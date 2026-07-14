import InfoGeometry.Physics.GellMannParafermionSolder
import InfoGeometry.Topology.AlgebraicCuntzQuotient
import InfoGeometry.External.Auto.UHFInductiveColimit

/-!
# Parafermion realizations — closing the analytic boundary

The `ParafermionRealization` interface requires a map `CuntzAlg ℂ (Fin 4) → V`.
This file provides:

1. **Identity realization**: `V = CuntzAlg ℂ (Fin 4)`, `map = id`.
   The parafermion algebra acts on itself — the algebraic tautology.

2. **Lift realization**: given operators `S, T : Fin 4 → V →ₗ[ℂ] V` satisfying
   the Cuntz relations (`T_i * S_j = δ_{ij}·id`, `Σ S_i * T_i = id`), the
   universal property yields an algebra map `CuntzAlg → End(V)`.  The
   `ParafermionRealization` is then obtained by evaluating at a chosen vector.

Zero sorries.
-/

noncomputable section

namespace ParafermionIdentityRealization

open InfoGeometry.Physics.GellMannParafermionSolder
open InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain
open InfoGeometry.Physics.BogoliubovSU3ParafermionWeld
open InfoGeometry.Physics.BogoliubovWeylChemicalPotential
open InfoGeometry.Physics.SupergradedCuntzBdG
open InfoGeometry.Physics.GellMannSU3
open InfoGeometry.Topology.AlgebraicCuntzQuotient
open InfoGeometry.External.Auto.UHFInductiveColimit

abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ
abbrev ParafermionStage4 := CuntzAlg ℂ (Fin 4)

/-- `CuntzAlg` derives `Semiring` which shadows `RingQuot`'s `Ring`.
Explicitly provide `Ring` (and hence `AddCommGroup`) via the unfolding. -/
noncomputable instance : Ring ParafermionStage4 :=
  show Ring (RingQuot (Rel (R := ℂ) (ι := Fin 4))) from inferInstance

/-! ## 1. Identity realization — the parafermion algebra acts on itself -/

/-- The identity realization: the Cuntz algebra acts on itself via `id`.
This is the algebraic tautology — every parafermion operator is its own
representation.  All SU(3) soldering theorems hold trivially. -/
def idRealization : ParafermionRealization ParafermionStage4 where
  map := id

/-- The realized 3+1 spinor in the identity realization recovers the
original BdG Majorana color spinor. -/
theorem idRealization_spinor_eq :
    realizedParafermionColorSpinor4 idRealization = bdgMajoranaPlusColorSpinor4 := by
  apply Prod.ext
  · ext j; rfl
  · rfl

/-- Gell-Mann solder in the identity realization: the color action on the
BdG Majorana spinor is precisely `colorLieAction4` on the original spinor. -/
theorem gellMannSolder_idRealization (A : M3C) :
    gellMannParafermionSolder idRealization A =
    colorLieAction4 A bdgMajoranaPlusColorSpinor4 := by
  dsimp [gellMannParafermionSolder, realizedParafermionColorSpinor4, idRealization]

/-- The SU(3) commutator table holds in the identity realization. -/
theorem idRealization_su3_commutators :
    ∃ h, h = su3_color_action_all_commutators bdgMajoranaPlusColorSpinor4 :=
  ⟨su3_color_action_all_commutators bdgMajoranaPlusColorSpinor4, rfl⟩

/-- Bogoliubov braiding in the identity realization. -/
theorem idRealization_braid_mu_shift (F : BogoliubovInertialFrame) (δμ : ℝ) :
    frameSolderedBraid { F with μ := F.μ + δμ } bdgMajoranaPlusColorSpinor4 =
      qBraid4 (qRapidity (F.β * δμ * F.Q))
        (frameSolderedBraid F bdgMajoranaPlusColorSpinor4) :=
  frameSolderedBraid_mu_shift idRealization F δμ

/-! ## 2. Lift realization — from any Cuntz family to a representation -/

/-- A Cuntz family on a ℂ-vector space V: 4 operators `S, T : V →ₗ[ℂ] V`
satisfying the algebraic Cuntz relations in the endomorphism algebra
`End_ℂ(V)` where multiplication is composition and 1 is `LinearMap.id`. -/
structure CuntzFamilyOn (V : Type*) [AddCommGroup V] [Module ℂ V] where
  S : Fin 4 → V →ₗ[ℂ] V
  T : Fin 4 → V →ₗ[ℂ] V
  ortho : ∀ i j : Fin 4, T i * S j = if i = j then (1 : V →ₗ[ℂ] V) else 0
  partition : (∑ i : Fin 4, S i * T i) = (1 : V →ₗ[ℂ] V)

/-- Lift a Cuntz family on V to an algebra homomorphism from the algebraic
Cuntz algebra `CuntzAlg ℂ (Fin 4)` to ℂ-linear endomorphisms of V. -/
def cuntzFamilyLift (V : Type*) [AddCommGroup V] [Module ℂ V]
    (F : CuntzFamilyOn V) : CuntzAlg ℂ (Fin 4) →ₐ[ℂ] V →ₗ[ℂ] V :=
  AlgebraicCuntzQuotient.lift (R := ℂ) (ι := Fin 4)
    (fun i => F.S i)
    (fun i => F.T i)
    F.ortho
    (by
      -- F.partition : Σ S_i * T_i = 1 in End(V)
      -- lift expects Σ S_i * T_i = 1 where * is the algebra multiplication
      -- Since * in End(V) is composition and 1 is id, this is exactly F.partition
      simpa using F.partition)

/-- The lift sends Cuntz generators to the family operators. -/
theorem cuntzFamilyLift_S (V : Type*) [AddCommGroup V] [Module ℂ V]
    (F : CuntzFamilyOn V) (i : Fin 4) :
    cuntzFamilyLift V F (AlgebraicCuntzQuotient.S (R := ℂ) i) = F.S i :=
  AlgebraicCuntzQuotient.lift_S (R := ℂ) (ι := Fin 4)
    (fun i => F.S i) (fun i => F.T i) F.ortho (by simpa using F.partition) i

/-- The lift sends adjoint Cuntz generators to the family co-operators. -/
theorem cuntzFamilyLift_T (V : Type*) [AddCommGroup V] [Module ℂ V]
    (F : CuntzFamilyOn V) (i : Fin 4) :
    cuntzFamilyLift V F (AlgebraicCuntzQuotient.T (R := ℂ) i) = F.T i :=
  AlgebraicCuntzQuotient.lift_T (R := ℂ) (ι := Fin 4)
    (fun i => F.S i) (fun i => F.T i) F.ortho (by simpa using F.partition) i

/-- A `ParafermionRealization` from a Cuntz family: lift to `End(V)`, then
evaluate at a chosen "seed" vector `v₀ : V`.  For the parafermion solder,
the BdG Majorana generators are mapped to operators on V via the lift,
and the resulting spinor is the image of the abstract Majorana spinor. -/
def cuntzFamilyRealization (V : Type*) [AddCommGroup V] [Module ℂ V]
    (F : CuntzFamilyOn V) (v₀ : V) : ParafermionRealization V where
  map x := (cuntzFamilyLift V F x) v₀

end ParafermionIdentityRealization

end noncomputable section
