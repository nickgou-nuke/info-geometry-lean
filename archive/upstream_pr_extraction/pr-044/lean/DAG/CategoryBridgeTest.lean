import DAG.ExactMorphism
import DAG.CategoryBridge

/-!
# CategoryBridge — Regression Test Suite

Tests the compositional witness verifier boundary.

Coverage:
1. Positive mapped identity case
2. Positive mapped composable-pair witness case
3. Object compatibility failure
4. Missing map skip case
5. No-witness failure case
-/

open Lean Meta

namespace DAG.Test.Category

-- Re-use definitions from ExactMorphismTest
def double (n : Nat) : Nat := 2 * n
def triple (n : Nat) : Nat := 3 * n
def sextuple (n : Nat) : Nat := 6 * n
def myId (n : Nat) : Nat := n
def succ' (n : Nat) : Nat := n + 1
structure X where val : Nat
structure Y where val : Nat
structure Z where val : Nat
def fXY (x : X) : Y := ⟨x.val⟩
def gYZ (y : Y) : Z := ⟨y.val⟩
def compXZ (x : X) : Z := ⟨x.val⟩

open Meta in
def mkE (n : Name) : MetaM MorphismEntry := do
  let env ← getEnv
  let ci := env.find? n |>.get!
  let some entry ← withUnaryMorphismSignature ci.type fun dom cod => do
    let domHead ← headNameOf dom
    let codHead ← headNameOf cod
    pure ({ decl := n, domHead := domHead, codHead := codHead } : MorphismEntry)
    | throwError s!"{n} signature failed"
  pure entry

-- Test environment constructor.
def runBridgeTest (sourceNames targetNames : Array Name) (mMap : MorphismMap) :
    MetaM CompositionalBridgeVerdict := do
  let mut sources := #[]
  for n in sourceNames do sources := sources.push (← mkE n)
  let mut targets := #[]
  for n in targetNames do targets := targets.push (← mkE n)
  verifyCompositionalWitness sources targets mMap

/-! ### 1. Positive mapped identity -/
-- Test: positive mapped identity
#eval show MetaM Unit from do
  let mut objMap : Std.HashMap Name Name := {}
  objMap := objMap.insert ``Nat ``Nat
  let mut mapMap : Std.HashMap Name Name := {}
  mapMap := mapMap.insert ``myId ``myId
  let verdict ← runBridgeTest #[``myId] #[``myId] { objMap, mapMap }
  assert! verdict.allOk
  assert! verdict.identityChecks.size == 1
  let chk := verdict.identityChecks[0]!
  assert! chk.tgtIsIdentity
  IO.println "✓ identity: correctly verified"

/-! ### 2. Positive mapped composable-pair witness -/
-- Test: positive mapped composable-pair witness
#eval show MetaM Unit from do
  let mut objMap : Std.HashMap Name Name := {}
  objMap := objMap.insert ``X ``X |>.insert ``Y ``Y |>.insert ``Z ``Z 
  let mut mapMap : Std.HashMap Name Name := {}
  mapMap := mapMap.insert ``fXY ``fXY |>.insert ``gYZ ``gYZ
  let verdict ← runBridgeTest #[``fXY, ``gYZ] #[``fXY, ``gYZ, ``compXZ] { objMap, mapMap }
  assert! verdict.allOk
  let some chk := verdict.compositionChecks.find? (fun c => c.srcF == ``fXY && c.srcG == ``gYZ)
    | throwError "missing fXY->gYZ check"
  assert! chk.witness == some ``compXZ
  IO.println "✓ composition witness: correctly found compXZ"

/-! ### 3. Object compatibility failure -/
-- Test: object compatibility failure
#eval show MetaM Unit from do
  -- We map myId (Nat → Nat) to myId (Nat → Nat),
  -- but we tell objMap that F(Nat) = String.
  let mut objMap : Std.HashMap Name Name := {}
  objMap := objMap.insert ``Nat ``String
  let mut mapMap : Std.HashMap Name Name := {}
  mapMap := mapMap.insert ``myId ``myId
  let verdict ← runBridgeTest #[``myId] #[``myId] { objMap, mapMap }
  assert! !verdict.allOk
  assert! verdict.identityChecks.size == 1
  let chk := verdict.identityChecks[0]!
  assert! !chk.objectCompatible
  IO.println "✓ object compatibility: correctly rejected"

/-! ### 4. Missing map skip case -/
-- Test: missing map skip case
#eval show MetaM Unit from do
  -- fXY and gYZ are composable, but gYZ is not in mapMap.
  -- The verifier should skip the composition check.
  let mut objMap : Std.HashMap Name Name := {}
  objMap := objMap.insert ``X ``X |>.insert ``Y ``Y |>.insert ``Z ``Z 
  let mut mapMap : Std.HashMap Name Name := {}
  mapMap := mapMap.insert ``fXY ``fXY
  let verdict ← runBridgeTest #[``fXY, ``gYZ] #[``fXY, ``compXZ] { objMap, mapMap }
  assert! verdict.allOk
  let skipped := verdict.compositionChecks.find? (fun c => c.srcF == ``fXY && c.srcG == ``gYZ)
  assert! skipped.isNone
  IO.println "✓ missing map: pair correctly skipped"

/-! ### 5. No-witness failure case -/
-- Test: no-witness failure case
#eval show MetaM Unit from do
  -- fXY and gYZ compose to compXZ. Target vocabulary lacks compXZ!
  let mut objMap : Std.HashMap Name Name := {}
  objMap := objMap.insert ``X ``X |>.insert ``Y ``Y |>.insert ``Z ``Z 
  let mut mapMap : Std.HashMap Name Name := {}
  mapMap := mapMap.insert ``fXY ``fXY |>.insert ``gYZ ``gYZ
  let verdict ← runBridgeTest #[``fXY, ``gYZ] #[``fXY, ``gYZ] { objMap, mapMap }
  assert! !verdict.allOk
  let some chk := verdict.compositionChecks.find? (fun c => c.srcF == ``fXY && c.srcG == ``gYZ)
    | throwError "missing fXY->gYZ check"
  assert! chk.witness.isNone
  IO.println "✓ no-witness: failure correctly detected"

/-! ### Summary -/
#eval IO.println "\n━━━ All DAG.CategoryBridge regression tests passed ━━━"

end DAG.Test.Category
