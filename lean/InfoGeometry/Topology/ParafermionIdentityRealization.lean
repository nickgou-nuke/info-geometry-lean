import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.GellMannParafermionSolder

/-!
# Parafermion realizations — finite carrier surface

This file keeps the theorem-honest finite Cuntz-family data used by the Cantor
boundary example.  It does not claim a universal Cuntz-algebra lift unless the
required quotient/universal-property owner is supplied.
-/

noncomputable section

namespace InfoGeometry.Topology.ParafermionIdentityRealization

open InfoGeometry.Physics.GellMannParafermionSolder

abbrev M3C := InfoGeometry.Algebra.FiniteSpin.Mat3C
abbrev ParafermionStage4 := Fin 4 → ℂ

/-- Basis vector in the four-component carrier. -/
def stageBasis (i : Fin 4) : ParafermionStage4 :=
  fun j => if j = i then 1 else 0

/-- The identity finite realization chooses the first three basis vectors as
color components and the fourth as singlet. -/
def idRealization : ParafermionRealization ParafermionStage4 where
  color := fun i => stageBasis ⟨i.val, by omega⟩
  singlet := stageBasis 3

/-- The identity realization reads back its own stored data. -/
theorem idRealization_spinor_eq :
    realizedParafermionColorSpinor4 idRealization = (idRealization.color, idRealization.singlet) := by
  rfl

/-- Gell-Mann solder in the identity realization is just the coefficient-matrix
action on the stored color data. -/
theorem gellMannSolder_idRealization (A : M3C) :
    gellMannParafermionSolder idRealization A =
      colorLieAction4 A (realizedParafermionColorSpinor4 idRealization) := by
  rfl

/-- The finite carrier action leaves the singlet output at zero. -/
theorem idRealization_singlet_zero :
    ∀ A : M3C, (gellMannParafermionSolder idRealization A).2 = 0 := by
  intro A
  exact gellMannParafermionSolder_singlet_zero idRealization A

/-- A Cuntz family on a ℂ-vector space `V`: four operators `S, T : V →ₗ[ℂ] V`
satisfying the algebraic Cuntz relations in `End_ℂ(V)`. -/
structure CuntzFamilyOn (V : Type*) [AddCommGroup V] [Module ℂ V] where
  S : Fin 4 → V →ₗ[ℂ] V
  T : Fin 4 → V →ₗ[ℂ] V
  ortho : ∀ i j : Fin 4, T i * S j = if i = j then (1 : V →ₗ[ℂ] V) else 0
  partition : (∑ i : Fin 4, S i * T i) = (1 : V →ₗ[ℂ] V)

/-- The orthogonality relation stored in a Cuntz family. -/
theorem CuntzFamilyOn.ortho_readout (V : Type*) [AddCommGroup V] [Module ℂ V]
    (F : CuntzFamilyOn V) (i j : Fin 4) :
    F.T i * F.S j = if i = j then (1 : V →ₗ[ℂ] V) else 0 :=
  F.ortho i j

/-- The partition-of-unity relation stored in a Cuntz family. -/
theorem CuntzFamilyOn.partition_readout (V : Type*) [AddCommGroup V] [Module ℂ V]
    (F : CuntzFamilyOn V) :
    (∑ i : Fin 4, F.S i * F.T i) = (1 : V →ₗ[ℂ] V) :=
  F.partition

/-- A realization extracted from a Cuntz family and seed vector.  This is only a
finite readout of the family on the seed; no universal algebra homomorphism is
claimed here. -/
def cuntzFamilyRealization (V : Type*) [AddCommGroup V] [Module ℂ V]
    (F : CuntzFamilyOn V) (v₀ : V) : ParafermionRealization V where
  color := fun i => F.S ⟨i.val, by omega⟩ v₀
  singlet := F.S 3 v₀

end InfoGeometry.Topology.ParafermionIdentityRealization

end noncomputable section
