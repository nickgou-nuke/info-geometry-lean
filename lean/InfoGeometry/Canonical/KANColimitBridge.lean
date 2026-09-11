import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

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
  Stage : ℕ → Type u
  stageRing : ∀ n, Ring (Stage n)
  bond : ∀ n, Stage n →+* Stage (n + 1)
  stage : ∀ n : ℕ, KANStageSignatures (Stage n)
  compact_compat : ∀ n x, (stage n).compactK x → (stage (n + 1)).compactK (bond n x)
  hyperbolic_compat : ∀ n x, (stage n).hyperbolicA x → (stage (n + 1)).hyperbolicA (bond n x)
  parabolic_compat : ∀ n x, (stage n).parabolicN x → (stage (n + 1)).parabolicN (bond n x)
  nilpotent_compat : ∀ n x, (stage n).nilpotentN x → (stage (n + 1)).nilpotentN (bond n x)
  tripotent_compat : ∀ n x, (stage n).tripotentT x → (stage (n + 1)).tripotentT (bond n x)

attribute [instance] KANColimitTower.stageRing

namespace KANColimitTower

variable (T : KANColimitTower)

abbrev Limit :=
  InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.DirectLimitSuperClosure T.bond

noncomputable abbrev toLimit (n : ℕ) : T.Stage n →+* T.Limit :=
  InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf T.bond n

def limit : KANLimitSignatures T.Limit where
  compactKInf := fun z => ∃ n x, T.toLimit n x = z ∧ (T.stage n).compactK x
  hyperbolicAInf := fun z => ∃ n x, T.toLimit n x = z ∧ (T.stage n).hyperbolicA x
  parabolicNInf := fun z => ∃ n x, T.toLimit n x = z ∧ (T.stage n).parabolicN x
  nilpotentNInf := fun z => ∃ n x, T.toLimit n x = z ∧ (T.stage n).nilpotentN x
  tripotentTInf := fun z => ∃ n x, T.toLimit n x = z ∧ (T.stage n).tripotentT x

def bondSeq (n m : ℕ) (h : n ≤ n + m) : T.Stage n →+* T.Stage (n + m) :=
  InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.bondMap T.bond n (n + m) h

theorem property_bondSeq
    (P : ∀ n, T.Stage n → Prop)
    (hP : ∀ n x, P n x → P (n + 1) (T.bond n x))
    (n m : ℕ) (x : T.Stage n) (hx : P n x) :
    P (n + m) (T.bondSeq n m (Nat.le_add_right n m) x) := by
  induction m with
  | zero => simpa [bondSeq] using hx
  | succ m ih =>
      change P (n + m + 1)
        (InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.bondMap
          T.bond n (n + m + 1) _ x)
      rw [InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.bondMap_succ
        T.bond n (n + m) (Nat.le_add_right n m)]
      exact hP (n + m) _ ih

/-- Compact `K` signature survives the colimit. -/
theorem compact_colimit {n : ℕ} {x : T.Stage n}
    (hx : (T.stage n).compactK x) :
    (T.limit).compactKInf (T.toLimit n x) := by
  exact ⟨n, x, rfl, hx⟩

/-- Hyperbolic/abelian `A` signature survives the colimit. -/
theorem hyperbolic_colimit {n : ℕ} {x : T.Stage n}
    (hx : (T.stage n).hyperbolicA x) :
    (T.limit).hyperbolicAInf (T.toLimit n x) := by
  exact ⟨n, x, rfl, hx⟩

/-- Parabolic `N` signature survives the colimit. -/
theorem parabolic_colimit {n : ℕ} {x : T.Stage n}
    (hx : (T.stage n).parabolicN x) :
    (T.limit).parabolicNInf (T.toLimit n x) := by
  exact ⟨n, x, rfl, hx⟩

/-- Nilpotent `N²=0`-style signature survives the colimit. -/
theorem nilpotent_colimit {n : ℕ} {x : T.Stage n}
    (hx : (T.stage n).nilpotentN x) :
    (T.limit).nilpotentNInf (T.toLimit n x) := by
  exact ⟨n, x, rfl, hx⟩

/-- Tripotent/Peirce `T³=T`-style signature survives the colimit. -/
theorem tripotent_colimit {n : ℕ} {x : T.Stage n}
    (hx : (T.stage n).tripotentT x) :
    (T.limit).tripotentTInf (T.toLimit n x) := by
  exact ⟨n, x, rfl, hx⟩

/-- Transport compact signature through finitely many bonding maps before taking the same colimit point. -/
theorem compact_transport_to_colimit
    (n m : ℕ) (x : T.Stage n) (hx : (T.stage n).compactK x) :
    (T.limit).compactKInf
      (T.toLimit (n + m) (T.bondSeq n m (Nat.le_add_right n m) x)) := by
  exact T.compact_colimit
    (T.property_bondSeq (fun k y => (T.stage k).compactK y)
      T.compact_compat n m x hx)

/-- Transport hyperbolic signature through finitely many bonding maps before taking the same colimit point. -/
theorem hyperbolic_transport_to_colimit
    (n m : ℕ) (x : T.Stage n) (hx : (T.stage n).hyperbolicA x) :
    (T.limit).hyperbolicAInf
      (T.toLimit (n + m) (T.bondSeq n m (Nat.le_add_right n m) x)) := by
  exact T.hyperbolic_colimit
    (T.property_bondSeq (fun k y => (T.stage k).hyperbolicA y)
      T.hyperbolic_compat n m x hx)

/-- Transport parabolic signature through finitely many bonding maps before taking the same colimit point. -/
theorem parabolic_transport_to_colimit
    (n m : ℕ) (x : T.Stage n) (hx : (T.stage n).parabolicN x) :
    (T.limit).parabolicNInf
      (T.toLimit (n + m) (T.bondSeq n m (Nat.le_add_right n m) x)) := by
  exact T.parabolic_colimit
    (T.property_bondSeq (fun k y => (T.stage k).parabolicN y)
      T.parabolic_compat n m x hx)

/-- Transport nilpotent signature through finitely many bonding maps before taking the same colimit point. -/
theorem nilpotent_transport_to_colimit
    (n m : ℕ) (x : T.Stage n) (hx : (T.stage n).nilpotentN x) :
    (T.limit).nilpotentNInf
      (T.toLimit (n + m) (T.bondSeq n m (Nat.le_add_right n m) x)) := by
  exact T.nilpotent_colimit
    (T.property_bondSeq (fun k y => (T.stage k).nilpotentN y)
      T.nilpotent_compat n m x hx)

/-- Transport tripotent signature through finitely many bonding maps before taking the same colimit point. -/
theorem tripotent_transport_to_colimit
    (n m : ℕ) (x : T.Stage n) (hx : (T.stage n).tripotentT x) :
    (T.limit).tripotentTInf
      (T.toLimit (n + m) (T.bondSeq n m (Nat.le_add_right n m) x)) := by
  exact T.tripotent_colimit
    (T.property_bondSeq (fun k y => (T.stage k).tripotentT y)
      T.tripotent_compat n m x hx)

/-- The transported KAN proof concerns the same colimit point as the original representative. -/
theorem transported_point_eq (n m : ℕ) (x : T.Stage n) :
    T.toLimit (n + m) (T.bondSeq n m (Nat.le_add_right n m) x) = T.toLimit n x :=
  InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf_bondMap
    T.bond n (n + m) (Nat.le_add_right n m) x

/-- Combined readout: K, A, N, nilpotent, and tripotent signatures survive together. -/
theorem full_KAN_signature_colimit {n : ℕ} {x : T.Stage n}
    (hK : (T.stage n).compactK x)
    (hA : (T.stage n).hyperbolicA x)
    (hN : (T.stage n).parabolicN x)
    (hNil : (T.stage n).nilpotentN x)
    (hTri : (T.stage n).tripotentT x) :
    (T.limit).compactKInf (T.toLimit n x) ∧
      (T.limit).hyperbolicAInf (T.toLimit n x) ∧
      (T.limit).parabolicNInf (T.toLimit n x) ∧
      (T.limit).nilpotentNInf (T.toLimit n x) ∧
      (T.limit).tripotentTInf (T.toLimit n x) :=
  ⟨T.compact_colimit hK,
    T.hyperbolic_colimit hA,
    T.parabolic_colimit hN,
    T.nilpotent_colimit hNil,
    T.tripotent_colimit hTri⟩

end KANColimitTower

end InfoGeometry.Canonical.KANColimitBridge
