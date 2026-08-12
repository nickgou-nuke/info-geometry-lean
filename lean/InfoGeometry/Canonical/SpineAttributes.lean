import Lean

/-!
# Spine Attributes

Small semantic tags for the canonical InfoGeometry spine.

These tags are intended to be authoritative signals for downstream DAG and
semantic-clustering tools, reducing reliance on naming heuristics.
-/

open Lean

namespace InfoGeometry.Canonical

/-- Small taxonomy for structure-lifting functors in the spine. -/
inductive SpineFunctorKind where
  | lift
  | constructor
  | responder
  deriving BEq, Repr, Inhabited

/-- Marks a declaration as a canonical object in the semantic spine. -/
initialize spineObjectAttr : TagAttribute ←
  registerTagAttribute `spine_object
    "Mark a declaration as a canonical semantic spine object."

/-- Marks a declaration as a canonical morphism in the semantic spine. -/
initialize spineMorphismAttr : TagAttribute ←
  registerTagAttribute `spine_morphism
    "Mark a declaration as a canonical semantic spine morphism."

/-- Marks a declaration as a functorial transport/refinement map in the spine. -/
initialize spineFunctorAttr : TagAttribute ←
  registerTagAttribute `spine_functor
    "Mark a declaration as a canonical semantic spine functor."

/-- Marks a spine functor as a structure-preserving lift between spine layers. -/
initialize spineFunctorLiftAttr : TagAttribute ←
  registerTagAttribute `spine_functor_lift
    "Mark a spine functor as a structure-preserving lift."

/-- Marks a spine functor as a constructor into a canonical spine interface. -/
initialize spineFunctorConstructorAttr : TagAttribute ←
  registerTagAttribute `spine_functor_constructor
    "Mark a spine functor as a constructor into a canonical spine interface."

/-- Marks a spine functor as a response/readout map over a lifted structure. -/
initialize spineFunctorResponderAttr : TagAttribute ←
  registerTagAttribute `spine_functor_responder
    "Mark a spine functor as a response/readout map over a lifted structure."

/-- Ordered list of supported spine tags. -/
def spineTagNames : Array Name :=
  #[ `spine_object
   , `spine_morphism
   , `spine_functor
   , `spine_functor_lift
   , `spine_functor_constructor
   , `spine_functor_responder
   ]

/-- Ordered list of supported spine functor-role tags. -/
def spineFunctorRoleTagNames : Array Name :=
  #[`spine_functor_lift, `spine_functor_constructor, `spine_functor_responder]

/-- Collect all semantic spine tags attached to a declaration. -/
def spineTagsOf (env : Environment) (declName : Name) : Array Name :=
  Id.run do
    let mut tags := #[]
    if spineObjectAttr.hasTag env declName then
      tags := tags.push `spine_object
    if spineMorphismAttr.hasTag env declName then
      tags := tags.push `spine_morphism
    if spineFunctorAttr.hasTag env declName then
      tags := tags.push `spine_functor
    if spineFunctorLiftAttr.hasTag env declName then
      tags := tags.push `spine_functor_lift
    if spineFunctorConstructorAttr.hasTag env declName then
      tags := tags.push `spine_functor_constructor
    if spineFunctorResponderAttr.hasTag env declName then
      tags := tags.push `spine_functor_responder
    tags

/-- String readout of the ordered semantic tags attached to a declaration. -/
def spineTagStringsOf (env : Environment) (declName : Name) : Array String :=
  (spineTagsOf env declName).map Name.toString

/-- Test whether a declaration is marked as a canonical spine object. -/
def isSpineObject (env : Environment) (declName : Name) : Bool :=
  spineObjectAttr.hasTag env declName

/-- Test whether a declaration is marked as a canonical spine morphism. -/
def isSpineMorphism (env : Environment) (declName : Name) : Bool :=
  spineMorphismAttr.hasTag env declName

/-- Test whether a declaration is marked as a canonical spine functor. -/
def isSpineFunctor (env : Environment) (declName : Name) : Bool :=
  spineFunctorAttr.hasTag env declName

/-- Test whether a declaration is tagged as a spine functor-lift. -/
def isSpineFunctorLift (env : Environment) (declName : Name) : Bool :=
  spineFunctorLiftAttr.hasTag env declName

/-- Test whether a declaration is tagged as a spine functor-constructor. -/
def isSpineFunctorConstructor (env : Environment) (declName : Name) : Bool :=
  spineFunctorConstructorAttr.hasTag env declName

/-- Test whether a declaration is tagged as a spine functor-responder. -/
def isSpineFunctorResponder (env : Environment) (declName : Name) : Bool :=
  spineFunctorResponderAttr.hasTag env declName

/-- Collect the functor-role taxonomy attached to a declaration. -/
def spineFunctorKindsOf (env : Environment) (declName : Name) : Array SpineFunctorKind :=
  Id.run do
    let mut kinds := #[]
    if isSpineFunctorLift env declName then
      kinds := kinds.push .lift
    if isSpineFunctorConstructor env declName then
      kinds := kinds.push .constructor
    if isSpineFunctorResponder env declName then
      kinds := kinds.push .responder
    kinds

/-- Return the unique functor-role taxonomy attached to a declaration, if any. -/
def spineFunctorKind? (env : Environment) (declName : Name) : Option SpineFunctorKind :=
  match spineFunctorKindsOf env declName with
  | #[kind] => some kind
  | _ => none

/-- Test whether a declaration belongs to the tagged semantic spine. -/
def isSpineTagged (env : Environment) (declName : Name) : Bool :=
  (spineTagsOf env declName).isEmpty = false

/-- Enumerate all declarations in the environment carrying at least one spine tag. -/
def taggedSpineDecls (env : Environment) : Array Name :=
  env.constants.fold (init := #[]) fun acc declName _ =>
    if isSpineTagged env declName then
      acc.push declName
    else
      acc

end InfoGeometry.Canonical
