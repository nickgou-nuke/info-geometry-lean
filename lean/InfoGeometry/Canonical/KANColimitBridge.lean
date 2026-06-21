import Mathlib
import InfoGeometry.Canonical.InductiveColimitBridge

/-!
# KAN Colimit Bridge

Theorem-safe colimit socket for KAN/Iwasawa signatures.

A finite KAN decomposition at stage `n` is not final by itself.  The compact
`K`, abelian/hyperbolic `A`, and parabolic/nilpotent `N` signatures must be
compatible with the bonding maps and then read through the inductive-colimit
cone.  This file proves that transport pattern generically.

No analytic Iwasawa decomposition theorem, C*-completion, `O(5,5)` theorem, or
operator-algebraic uniqueness statement is asserted here.  Those belong to
specialized owner modules as explicit witnesses.
-/

namespace InfoGeometry.Canonical.KANColimitBridge

open InfoGeometry.Canonical.InductiveColimitBridge

/-- Finite KAN signatures at a stage. -/
structure KANStageSignatures (Stage : Type*) where
  compactK : Stage → Prop
  hyperbolicA : Stage → Prop
  parabolicN : Stage → Prop
  nilpotentN : Stage → Prop
  tripotentT : Stage → Prop

/-- Limit KAN signatures on the colimit carrier. -/
structure KANLimitSignatures (Limit : Type*) where
  compactKInf : Limit → Prop
  hyperbolicAInf : Limit → Prop
  parabolicNInf : Limit → Prop
  nilpotentNInf : Limit → Prop
  tripotentTInf : Limit → Prop

/--
A sequential KAN tower whose finite signatures are compatible with bonding maps
and have explicit readouts on the colimit carrier.
-/
structure KANColimitTower where
  system : SequentialColimitSystem
  stage : ∀ n : ℕ, KANStageSignatures (system.Stage n)
  limit : KANLimitSignatures system.Limit
  compact_compat : system.CompatibleProperty (fun n x => (stage n).compactK x)
  hyperbolic_compat : system.CompatibleProperty (fun n x => (stage n).hyperbolicA x)
  parabolic_compat : system.CompatibleProperty (fun n x => (stage n).parabolicN x)
  nilpotent_compat : system.CompatibleProperty (fun n x => (stage n).nilpotentN x)
  tripotent_compat : system.CompatibleProperty (fun n x => (stage n).tripotentT x)
  compact_readout : system.LimitReadout (fun n x => (stage n).compactK x) limit.compactKInf
  hyperbolic_readout : system.LimitReadout (fun n x => (stage n).hyperbolicA x) limit.hyperbolicAInf
  parabolic_readout : system.LimitReadout (fun n x => (stage n).parabolicN x) limit.parabolicNInf
  nilpotent_readout : system.LimitReadout (fun n x => (stage n).nilpotentN x) limit.nilpotentNInf
  tripotent_readout : system.LimitReadout (fun n x => (stage n).tripotentT x) limit.tripotentTInf

namespace KANColimitTower

variable (T : KANColimitTower)

/-- Compact `K` signature survives the colimit. -/
theorem compact_colimit {n : ℕ} {x : T.system.Stage n}
    (hx : (T.stage n).compactK x) :
    T.limit.compactKInf (T.system.toLimit n x) :=
  T.compact_readout n x hx

/-- Hyperbolic/abelian `A` signature survives the colimit. -/
theorem hyperbolic_colimit {n : ℕ} {x : T.system.Stage n}
    (hx : (T.stage n).hyperbolicA x) :
    T.limit.hyperbolicAInf (T.system.toLimit n x) :=
  T.hyperbolic_readout n x hx

/-- Parabolic `N` signature survives the colimit. -/
theorem parabolic_colimit {n : ℕ} {x : T.system.Stage n}
    (hx : (T.stage n).parabolicN x) :
    T.limit.parabolicNInf (T.system.toLimit n x) :=
  T.parabolic_readout n x hx

/-- Nilpotent `N²=0`-style signature survives the colimit. -/
theorem nilpotent_colimit {n : ℕ} {x : T.system.Stage n}
    (hx : (T.stage n).nilpotentN x) :
    T.limit.nilpotentNInf (T.system.toLimit n x) :=
  T.nilpotent_readout n x hx

/-- Tripotent/Peirce `T³=T`-style signature survives the colimit. -/
theorem tripotent_colimit {n : ℕ} {x : T.system.Stage n}
    (hx : (T.stage n).tripotentT x) :
    T.limit.tripotentTInf (T.system.toLimit n x) :=
  T.tripotent_readout n x hx

/-- Transport compact signature through finitely many bonding maps before taking the same colimit point. -/
theorem compact_transport_to_colimit
    (n m : ℕ) (x : T.system.Stage n) (hx : (T.stage n).compactK x) :
    T.limit.compactKInf (T.system.toLimit (n + m) (T.system.bondSeq n m x)) :=
  T.compact_readout (n + m) (T.system.bondSeq n m x)
    (T.system.compatibleProperty_bondSeq (fun k y => (T.stage k).compactK y)
      T.compact_compat n m x hx)

/-- Transport hyperbolic signature through finitely many bonding maps before taking the same colimit point. -/
theorem hyperbolic_transport_to_colimit
    (n m : ℕ) (x : T.system.Stage n) (hx : (T.stage n).hyperbolicA x) :
    T.limit.hyperbolicAInf (T.system.toLimit (n + m) (T.system.bondSeq n m x)) :=
  T.hyperbolic_readout (n + m) (T.system.bondSeq n m x)
    (T.system.compatibleProperty_bondSeq (fun k y => (T.stage k).hyperbolicA y)
      T.hyperbolic_compat n m x hx)

/-- Transport parabolic signature through finitely many bonding maps before taking the same colimit point. -/
theorem parabolic_transport_to_colimit
    (n m : ℕ) (x : T.system.Stage n) (hx : (T.stage n).parabolicN x) :
    T.limit.parabolicNInf (T.system.toLimit (n + m) (T.system.bondSeq n m x)) :=
  T.parabolic_readout (n + m) (T.system.bondSeq n m x)
    (T.system.compatibleProperty_bondSeq (fun k y => (T.stage k).parabolicN y)
      T.parabolic_compat n m x hx)

/-- Transport nilpotent signature through finitely many bonding maps before taking the same colimit point. -/
theorem nilpotent_transport_to_colimit
    (n m : ℕ) (x : T.system.Stage n) (hx : (T.stage n).nilpotentN x) :
    T.limit.nilpotentNInf (T.system.toLimit (n + m) (T.system.bondSeq n m x)) :=
  T.nilpotent_readout (n + m) (T.system.bondSeq n m x)
    (T.system.compatibleProperty_bondSeq (fun k y => (T.stage k).nilpotentN y)
      T.nilpotent_compat n m x hx)

/-- Transport tripotent signature through finitely many bonding maps before taking the same colimit point. -/
theorem tripotent_transport_to_colimit
    (n m : ℕ) (x : T.system.Stage n) (hx : (T.stage n).tripotentT x) :
    T.limit.tripotentTInf (T.system.toLimit (n + m) (T.system.bondSeq n m x)) :=
  T.tripotent_readout (n + m) (T.system.bondSeq n m x)
    (T.system.compatibleProperty_bondSeq (fun k y => (T.stage k).tripotentT y)
      T.tripotent_compat n m x hx)

/-- The transported KAN proof concerns the same colimit point as the original representative. -/
theorem transported_point_eq (n m : ℕ) (x : T.system.Stage n) :
    T.system.toLimit (n + m) (T.system.bondSeq n m x) = T.system.toLimit n x :=
  T.system.toLimit_bondSeq n m x

/-- Combined readout: K, A, N, nilpotent, and tripotent signatures survive together. -/
theorem full_KAN_signature_colimit {n : ℕ} {x : T.system.Stage n}
    (hK : (T.stage n).compactK x)
    (hA : (T.stage n).hyperbolicA x)
    (hN : (T.stage n).parabolicN x)
    (hNil : (T.stage n).nilpotentN x)
    (hTri : (T.stage n).tripotentT x) :
    T.limit.compactKInf (T.system.toLimit n x) ∧
      T.limit.hyperbolicAInf (T.system.toLimit n x) ∧
      T.limit.parabolicNInf (T.system.toLimit n x) ∧
      T.limit.nilpotentNInf (T.system.toLimit n x) ∧
      T.limit.tripotentTInf (T.system.toLimit n x) :=
  ⟨T.compact_colimit hK,
    T.hyperbolic_colimit hA,
    T.parabolic_colimit hN,
    T.nilpotent_colimit hNil,
    T.tripotent_colimit hTri⟩

end KANColimitTower

end InfoGeometry.Canonical.KANColimitBridge
