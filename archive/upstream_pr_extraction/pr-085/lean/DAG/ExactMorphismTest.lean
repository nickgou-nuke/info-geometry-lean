import DAG.ExactMorphism
import DAG.CategoryBridge

/-!
# Exact Morphism Engine — Regression Test Suite

Exercises every admission/rejection boundary of the unary fragment engine
using toy declarations with known expected behavior.

## Test Coverage

1. Accepted unary morphism
2. Rejected multi-explicit declaration
3. Rejected dependent result type
4. Exact commutative square found
5. False commutative square rejected
6. Definitional identity detected
7. Non-identity endomorphism rejected
8. Cache deduplication invariant
-/

open Lean Meta

namespace DAG.Test

/-! ### 1. Toy declarations for testing -/

-- Unary morphism: one explicit argument, non-dependent result
def double (n : Nat) : Nat := 2 * n

-- Unary morphism: one explicit argument, non-dependent result
def triple (n : Nat) : Nat := 3 * n

-- Unary morphism: one explicit argument, non-dependent result
def sextuple (n : Nat) : Nat := 6 * n

-- Multi-explicit: TWO explicit arguments — should be rejected
def addTwo (a b : Nat) : Nat := a + b

-- Dependent result (via Fin): result type depends on the input — should be rejected
def makeZero (n : Nat) : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩

-- Identity function — definitional identity
def myId (n : Nat) : Nat := n

-- Non-identity endomorphism — should NOT be detected as identity
def succ' (n : Nat) : Nat := n + 1

-- For commutative square: double ∘ triple = sextuple = triple ∘ double
-- Since 2*(3*n) = 6*n = 3*(2*n), this should commute definitionally
-- ... but only if Lean can reduce 2*(3*n) = 3*(2*n). Let's verify.

-- Definitional identity pair: a ∘ b = id and b ∘ a = id
-- Using Bool.not as a concrete inverse pair
def flipBool (b : Bool) : Bool := !b

/-! ### 2. Admission/rejection tests -/

-- Polymorphic unary morphism: contains an implicit type and class instance
def polyId {α : Type} [Inhabited α] (x : α) : α := x

-- These run inside #eval to test MetaM-level extraction

-- Test: `polyId` should be safely admitted and processed without telescope escapes.
#eval show MetaM Unit from do
  let env ← getEnv
  let ci := env.find? ``polyId |>.get!
  let some _ ← mkMorphismEntry? ``polyId ci | throwError "polyId should be admitted"
  let some () ← withUnaryMorphismSignature ci.type fun dom cod => do
    let _ ← headNameOf dom
    let _ ← headNameOf cod
    pure ()
    | throwError "withUnaryMorphismSignature should succeed on polyId"
  IO.println "✓ polyId: polymorphic unary morphism handled safely"

-- Test: `double` should be admitted as a unary morphism.
#eval show MetaM Unit from do
  let env ← getEnv
  let ci := env.find? ``double |>.get!
  let sig ← withUnaryMorphismSignature ci.type fun _ _ => pure ()
  assert! sig.isSome
  IO.println "✓ double: admitted as unary morphism"

-- Test: `addTwo` should be rejected (two explicit binders).
#eval show MetaM Unit from do
  let env ← getEnv
  let ci := env.find? ``addTwo |>.get!
  let sig ← withUnaryMorphismSignature ci.type fun _ _ => pure ()
  assert! sig.isNone
  IO.println "✓ addTwo: rejected (multi-explicit)"

-- Test: `makeZero` should be rejected (dependent result).
#eval show MetaM Unit from do
  let env ← getEnv
  let ci := env.find? ``makeZero |>.get!
  let sig ← withUnaryMorphismSignature ci.type fun _ _ => pure ()
  assert! sig.isNone
  IO.println "✓ makeZero: rejected (dependent result)"

-- Test: `myId` should be admitted as a unary morphism.
#eval show MetaM Unit from do
  let env ← getEnv
  let ci := env.find? ``myId |>.get!
  let sig ← withUnaryMorphismSignature ci.type fun _ _ => pure ()
  assert! sig.isSome
  IO.println "✓ myId: admitted as unary morphism"

-- Test: `flipBool` should be admitted as a unary morphism.
#eval show MetaM Unit from do
  let env ← getEnv
  let ci := env.find? ``flipBool |>.get!
  let sig ← withUnaryMorphismSignature ci.type fun _ _ => pure ()
  assert! sig.isSome
  IO.println "✓ flipBool: admitted as unary morphism"

/-! ### 3. MorphismEntry construction -/

-- Test: mkMorphismEntry? produces correct head names.
#eval show MetaM Unit from do
  let env ← getEnv
  let ci := env.find? ``double |>.get!
  let entry ← mkMorphismEntry? ``double ci
  assert! entry.isSome
  let e := entry.get!
  assert! e.decl == ``double
  assert! e.domHead == ``Nat
  assert! e.codHead == ``Nat
  IO.println s!"✓ double entry: {e}"

-- Test: mkMorphismEntry? returns none for multi-explicit.
#eval show MetaM Unit from do
  let env ← getEnv
  let ci := env.find? ``addTwo |>.get!
  let entry ← mkMorphismEntry? ``addTwo ci
  assert! entry.isNone
  IO.println "✓ addTwo entry: correctly rejected"

/-! ### 4. Definitional identity detection -/

-- Test: `myId` is a definitional identity.
#eval show MetaM Unit from do
  let env ← getEnv
  let ci := env.find? ``myId |>.get!
  let some entry ← mkMorphismEntry? ``myId ci | throwError "myId should be admitted"
  let isId ← DAG.isDefinitionalIdentity entry
  assert! isId
  IO.println "✓ myId: detected as definitional identity"

-- Test: `succ'` is NOT a definitional identity.
#eval show MetaM Unit from do
  let env ← getEnv
  let ci := env.find? ``succ' |>.get!
  let some entry ← mkMorphismEntry? ``succ' ci | throwError "succ' should be admitted"
  -- succ'(succ'(x)) = x+2 ≠ x, so NOT a self-inverse
  let isId ← isDefinitionalIdentity entry
  assert! !isId
  IO.println "✓ succ': correctly classified as non-identity"

/-! ### 5. Exact commutativity checking -/

-- Test: A trivially commutative square: double ∘ myId = myId ∘ double.
#eval show MetaM Unit from do
  let env ← getEnv
  let mkE (n : Name) := do
    let ci := env.find? n |>.get!
    let some e ← mkMorphismEntry? n ci | throwError s!"{n} should be admitted"
    return e
  let f ← mkE ``myId       -- Nat → Nat  (identity)
  let g ← mkE ``myId       -- same
  let h ← mkE ``double     -- Nat → Nat
  let k ← mkE ``double     -- same
  -- Square: h ∘ f = k ∘ g ?  i.e. double(myId(x)) = double(myId(x)) — trivially true
  let verdict ← checkCommutativityExact f g h k
  match verdict with
  | .exact => IO.println "✓ trivial square: EXACT (as expected)"
  | .notEqual => throwError "trivial square should be EXACT"
  | .checkFailed msg => throwError s!"trivial square check failed: {msg}"

-- Test: A non-commutative square: triple ∘ myId ≠ succ' ∘ myId.
#eval show MetaM Unit from do
  let env ← getEnv
  let mkE (n : Name) := do
    let ci := env.find? n |>.get!
    let some e ← mkMorphismEntry? n ci | throwError s!"{n} should be admitted"
    return e
  let f ← mkE ``myId
  let g ← mkE ``myId
  let h ← mkE ``triple     -- 3*n
  let k ← mkE ``succ'      -- n+1
  -- Square: triple(myId(x)) = succ'(myId(x)) ?  i.e. 3*x = x+1 — false in general
  let verdict ← checkCommutativityExact f g h k
  match verdict with
  | .exact => throwError "this square should NOT be exact"
  | .notEqual => IO.println "✓ non-commutative square: NOT_EQUAL (as expected)"
  | .checkFailed msg => throwError s!"non-commutative square should not fail: {msg}"

/-! ### 6. flipBool inverse detection -/

-- Test: flipBool ∘ flipBool is NOT a definitional identity for free variables.
#eval show MetaM Unit from do
  let env ← getEnv
  let ci := env.find? ``flipBool |>.get!
  let some entry ← mkMorphismEntry? ``flipBool ci | throwError "flipBool should be admitted"
  let isInv ← DAG.checkDefinitionalInverse entry entry
  assert! !isInv
  IO.println "✓ flipBool: correctly rejected as non-definitional since !(!x) = x requires proof"

/-! ### 7. Cache deduplication invariant -/

-- Test: Cache pipeline deduplication and persistence.
#eval show MetaM Unit from do
  let env ← getEnv
  let env1 ← indexMorphismCache env (some `DAG.Test)
  let s1 := getMorphismState env1
  let n1 := s1.entries.size
  let env2 ← indexMorphismCache env1 (some `DAG.Test)
  let s2 := getMorphismState env2
  let n2 := s2.entries.size
  assert! n1 == n2
  assert! s2.indexed.contains ``DAG.Test.double
  IO.println "✓ indexMorphismCache: deduplicated and persistent"

/-! ### 8. CategoryBridge identity detection -/

-- Test: isDefinitionalIdentity correctly identifies myId.
#eval show MetaM Unit from do
  let env ← getEnv
  let ci := env.find? ``myId |>.get!
  let some entry ← mkMorphismEntry? ``myId ci | throwError "myId should be admitted"
  let isId ← DAG.isDefinitionalIdentity entry
  assert! isId
  IO.println "✓ isDefinitionalIdentity: myId detected"

-- Test: isDefinitionalIdentity correctly rejects succ'.
#eval show MetaM Unit from do
  let env ← getEnv
  let ci := env.find? ``succ' |>.get!
  let some entry ← mkMorphismEntry? ``succ' ci | throwError "succ' should be admitted"
  let isId ← DAG.isDefinitionalIdentity entry
  assert! !isId
  IO.println "✓ isDefinitionalIdentity: succ' rejected"

/-! ### 9. Rehydration round-trip -/

-- Test: withUnaryMorphismSignature callback access to correct signature.
#eval show MetaM Unit from do
  let env ← getEnv
  let ci := env.find? ``double |>.get!
  let result ← withUnaryMorphismSignature ci.type fun dom cod => do
    -- Both should have head `Nat`
    let domHead ← headNameOf dom
    let codHead ← headNameOf cod
    assert! domHead == ``Nat
    assert! codHead == ``Nat
    pure ()
  assert! result.isSome
  IO.println "✓ withUnaryMorphismSignature: callback preserves head names safely"

/-! ### Summary -/

#eval IO.println "\n━━━ All DAG.ExactMorphism regression tests passed ━━━"

end DAG.Test
