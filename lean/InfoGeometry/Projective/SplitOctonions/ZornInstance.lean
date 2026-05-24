import InfoGeometry.Projective.SplitOctonions.ZornConcrete

/-!
# InfoGeometry.Projective.SplitOctonions.ZornInstance

Concrete projective Zorn instance for the local split-octonion boundary.

This file is a thin bridge over `ZornConcrete`. It exposes the concrete
projective datum and polar datum under stable names, without introducing any
additional algebraic claims.
-/

namespace InfoGeometry.Projective.SplitOctonions

universe u v

namespace ZornProjectiveDatum

variable {R : Type u} {V : Type v}
variable [Field R] [AddCommGroup V] [Module R V]

/-- The concrete projective datum on Zorn cells. -/
abbrev projectiveDatum
    (B : V →ₗ[R] V →ₗ[R] R) : ZornProjectiveDatum R V :=
  concreteZornProjectiveDatum (R := R) (V := V) B

end ZornProjectiveDatum

variable {R : Type u} {V : Type v}
variable [Field R] [AddCommGroup V] [Module R V]

/-- The concrete polar datum on Zorn cells. -/
abbrev concretePolarDatum
    (B : V →ₗ[R] V →ₗ[R] R) : ZornProjectiveDatum.PolarDatum R V :=
  ZornProjectiveDatum.PolarDatum.concretePolarDatum (R := R) (V := V) B


end InfoGeometry.Projective.SplitOctonions
