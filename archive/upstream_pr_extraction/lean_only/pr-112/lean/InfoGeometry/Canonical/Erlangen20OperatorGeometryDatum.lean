import Mathlib

/-!
# Erlangen 2.0 operator-geometry datum

The formal core of the operator-geometric programme is a typed datum rather
than an assertion about a preferred coordinate chart.  A datum consists of a
carrier, an associative operator subalgebra, a represented Lie symmetry, a
family of symmetry-adapted structures, and a family of invariants.  Physical
or geometric readings of these fields are deliberately left outside the
kernel theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum

/-- A theorem-safe Erlangen 2.0 geometry datum.

`representation_mem` records that the represented symmetry acts inside the
chosen associative operator algebra.  The two final fields are intentionally
opaque parameter types: a concrete owner supplies the relevant gradings,
projectors, invariants, or intertwiners without this interface conflating
their meanings.
-/
structure Erlangen20Datum
    (R V 𝔤 𝒮 ℐ : Type*)
    [CommRing R]
    [AddCommGroup V] [Module R V]
    [LieRing 𝔤] [LieAlgebra R 𝔤] where
  operatorAlgebra : Subalgebra R (Module.End R V)
  representation : 𝔤 →ₗ⁅R⁆ Module.End R V
  representation_mem : ∀ X, representation X ∈ operatorAlgebra
  symmetryData : 𝒮
  invariantData : ℐ

namespace Erlangen20Datum

variable {R V 𝔤 𝒮 ℐ : Type*}
  [CommRing R]
  [AddCommGroup V] [Module R V]
  [LieRing 𝔤] [LieAlgebra R 𝔤]

@[simp] theorem representation_mem_operatorAlgebra
    (E : Erlangen20Datum R V 𝔤 𝒮 ℐ) (X : 𝔤) :
    E.representation X ∈ E.operatorAlgebra :=
  E.representation_mem X

theorem representation_map_lie
    (E : Erlangen20Datum R V 𝔤 𝒮 ℐ) (X Y : 𝔤) :
    E.representation ⁅X, Y⁆ =
      E.representation X * E.representation Y -
        E.representation Y * E.representation X := by
  exact E.representation.map_lie X Y

end Erlangen20Datum

/-! A carrier-level intertwiner is kept separate from the six-tuple datum.
This prevents an abstract geometry record from silently identifying two
unrelated carriers. -/

structure OperatorIntertwiner
    (R V W : Type*)
    [CommRing R]
    [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] where
  carrierEquiv : V ≃ₗ[R] W
  source : Module.End R V
  target : Module.End R W
  intertwines : ∀ v, target (carrierEquiv v) = carrierEquiv (source v)

theorem OperatorIntertwiner.target_eq_conjugated
    {R V W : Type*}
    [CommRing R]
    [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    (I : OperatorIntertwiner R V W) :
    I.target =
      I.carrierEquiv.toLinearMap.comp
        (I.source.comp I.carrierEquiv.symm.toLinearMap) := by
  ext w
  have h := I.intertwines (I.carrierEquiv.symm w)
  rw [I.carrierEquiv.apply_symm_apply w] at h
  exact h

theorem OperatorIntertwiner.source_eq_conjugated
    {R V W : Type*}
    [CommRing R]
    [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    (I : OperatorIntertwiner R V W) :
    I.source =
      I.carrierEquiv.symm.toLinearMap.comp
        (I.target.comp I.carrierEquiv.toLinearMap) := by
  ext v
  apply I.carrierEquiv.injective
  change I.carrierEquiv (I.source v) =
    I.carrierEquiv (I.carrierEquiv.symm (I.target (I.carrierEquiv v)))
  rw [I.carrierEquiv.apply_symm_apply]
  exact (I.intertwines v).symm

end InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
