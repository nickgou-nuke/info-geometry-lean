import DAG.ExactMorphism
import DAG.CategoryBridge
import InfoGeometry.Quantum.RealMajoranaCategory

open Lean Meta
open InfoGeometry.Quantum.RealMajoranaCategory
open CategoryTheory

namespace DAG.Test.Integration

-- 1. Expose functor object maps as top-level declarations (unary morphisms)
noncomputable def forgetToCore_obj (X : PolarizedMajorana) := PolarizedMajorana.forgetToCore.obj X
noncomputable def toRealKVect_obj (X : RealMajoranaCore) := RealMajoranaCore.toRealKVect.obj X
noncomputable def forgetToRealKVect_obj (X : PolarizedMajorana) := PolarizedMajorana.forgetToRealKVect.obj X

-- 2. Expose identity morphisms for object-compatibility testing
noncomputable def pol_id (X : PolarizedMajorana) := X
noncomputable def core_id (X : RealMajoranaCore) := X

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

def runBridgeTest (sourceNames targetNames : Array Name) (mMap : MorphismMap) :
    MetaM CompositionalBridgeVerdict := do
  let mut sources := #[]
  for n in sourceNames do sources := sources.push (← mkE n)
  let mut targets := #[]
  for n in targetNames do targets := targets.push (← mkE n)
  DAG.verifyCompositionalWitness sources targets mMap

/-! ### 1. Positive Compositional Witness for Forgetful Tower (obj maps) -/
#eval show MetaM Unit from do
  -- forgetToCore ⋙ toRealKVect = forgetToRealKVect
  -- The objects are PolarizedMajorana, RealMajoranaCore, RealKCategory.RealKVect
  let mut objMap : Std.HashMap Name Name := {}
  objMap := objMap.insert ``PolarizedMajorana ``PolarizedMajorana |>.insert ``RealMajoranaCore ``RealMajoranaCore |>.insert ``InfoGeometry.Quantum.RealKCategory.RealKVect ``InfoGeometry.Quantum.RealKCategory.RealKVect
  
  let mut mapMap : Std.HashMap Name Name := {}
  mapMap := mapMap.insert ``forgetToCore_obj ``forgetToCore_obj |>.insert ``toRealKVect_obj ``toRealKVect_obj
  
  let verdict ← runBridgeTest #[``forgetToCore_obj, ``toRealKVect_obj] #[``forgetToCore_obj, ``toRealKVect_obj, ``forgetToRealKVect_obj] { objMap, mapMap }
  
  assert! verdict.allOk
  let some chk := verdict.compositionChecks.find? (fun c => c.srcF == ``forgetToCore_obj && c.srcG == ``toRealKVect_obj)
    | throwError "missing composition check for forgetToCore -> toRealKVect"
  assert! chk.witness == some ``forgetToRealKVect_obj
  
  IO.println "✓ Forgetful tower composition: verified"

/-! ### 2. Object-map compatibility -/
#eval show MetaM Unit from do
  -- pol_id: PolarizedMajorana -> PolarizedMajorana
  -- core_id: RealMajoranaCore -> RealMajoranaCore
  -- Mapped properly, this is an identity functor. But what if we break the objMap?
  let mut objMap : Std.HashMap Name Name := {}
  -- map PolarizedMajorana to Eq maliciously instead of RealMajoranaCore
  objMap := objMap.insert ``PolarizedMajorana ``Eq
  
  let mut mapMap : Std.HashMap Name Name := {}
  mapMap := mapMap.insert ``pol_id ``core_id 
  
  let verdict ← runBridgeTest #[``pol_id] #[``core_id] { objMap, mapMap }
  
  assert! !verdict.allOk
  let some chk := verdict.identityChecks.find? (fun c => c.srcDecl == ``pol_id)
    | throwError "missing identity check for pol_id"
  assert! !chk.objectCompatible
  
  IO.println "✓ Object compatibility failure: detected correctly"

/-! ### Summary -/
#eval IO.println "\n━━━ All DAG Integration tests passed ━━━"

end DAG.Test.Integration
