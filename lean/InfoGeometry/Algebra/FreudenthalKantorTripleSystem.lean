import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Algebraic Freudenthal--Kantor triple-system contract

This file records the finite algebraic identities used in the supplied
Freudenthal--Kantor reference.  It is a contract for a triple system, not a
construction of a TKK or Kantor Lie algebra.  In particular, no grading or
analytic/Hermitian positivity is inferred from these fields.
-/

namespace InfoGeometry.Algebra

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

def fktsK (delta : R) (triple : U →ₗ[R] U →ₗ[R] U →ₗ[R] U)
    (x y z : U) : U :=
  triple x z y - delta • triple y z x

structure FreudenthalKantorTripleSystem where
  epsilon : R
  delta : R
  triple : U →ₗ[R] U →ₗ[R] U →ₗ[R] U
  left_identity :
    ∀ x y z w u,
      triple x y (triple z w u) - triple z w (triple x y u) =
        triple (triple x y z) w u +
          epsilon • triple z (triple y x w) u
  k_identity :
    ∀ x y z w u,
      fktsK delta triple (triple x y z) w u +
          fktsK delta triple z (triple x y w) u +
            delta • fktsK delta triple x
              (fktsK delta triple z w y) u = 0

namespace FreudenthalKantorTripleSystem

variable (data : FreudenthalKantorTripleSystem (R := R) (U := U))

def K (x y z : U) : U :=
  fktsK data.delta data.triple x y z

def IsTripotent (c : U) : Prop :=
  data.triple c c c = c

theorem tripotent_readout {c : U} (hc : IsTripotent data c) :
    data.triple c c c = c :=
  hc

def IsBitriponent (c₁ c₂ : U) (α β γ : R) : Prop :=
    data.triple c₁ c₁ c₂ = α • c₂ ∧
    data.triple c₂ c₂ c₁ = α • c₁ ∧
    data.triple c₁ c₂ c₁ = β • c₂ ∧
    data.triple c₂ c₁ c₂ = β • c₁ ∧
    data.triple c₂ c₁ c₁ = γ • c₂ ∧
    data.triple c₁ c₂ c₂ = γ • c₁

theorem left_identity_readout (x y z w u : U) :
    data.triple x y (data.triple z w u) - data.triple z w (data.triple x y u) =
      data.triple (data.triple x y z) w u +
        data.epsilon • data.triple z (data.triple y x w) u :=
  data.left_identity x y z w u

theorem k_identity_readout (x y z w u : U) :
    K data (data.triple x y z) w u +
        K data z (data.triple x y w) u +
          data.delta • K data x (K data z w y) u = 0 :=
  data.k_identity x y z w u

end FreudenthalKantorTripleSystem

end InfoGeometry.Algebra
