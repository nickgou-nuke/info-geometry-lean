import Lean
open Lean

/-!
# DumpLeanGraph — Lean-native proof graph extraction

Three-layer extraction:
  v1: Syntax dump — parse file, traverse Lean.Syntax, emit AST projection
  v2: Environment dump — query Environment.constants, emit ConstantInfo records
  v3: InfoTree dump — capture elaboration-time tactic/goal metadata

Usage:
  lake env lean --run tools/lean_graph/DumpLeanGraph.lean <file.lean> [<file2.lean> ...]

Output: JSONL to stdout (one record per line), logs to stderr.
-/

/-! ## JSON string helpers -/

def quoteJson (s : String) : String := "\"" ++ s ++ "\""

def escapeJson (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n" |>.replace "\t" "\\t"

def jsonPair (key : String) (val : String) : String :=
  quoteJson key ++ ":" ++ val

def jsonObj (pairs : List (String × String)) : String :=
  "{" ++ (",".intercalate (pairs.map (fun (k, v) => jsonPair k v))) ++ "}"

/-! ## Line/column utilities -/

structure SourceRange where
  startLine : Nat
  startCol  : Nat
  endLine   : Nat
  endCol    : Nat
  deriving Inhabited

def SourceRange.toJson (r : SourceRange) : String :=
  jsonObj [
    ("startLine", toString r.startLine),
    ("startCol", toString r.startCol),
    ("endLine", toString r.endLine),
    ("endCol", toString r.endCol)
  ]

/-- Build line-offset array from file content for byte→line:col conversion.
Each entry is the byte offset of the start of a line. -/
partial def buildLineMapAux (lines : List String) (acc : Nat) : List Nat :=
  match lines with
  | [] => [acc]
  | l :: rest => acc :: buildLineMapAux rest (acc + l.length + 1)

def buildLineMap (content : String) : List Nat :=
  buildLineMapAux (content.splitOn "\n") 0

/-- Find the 0-based line index for a byte position. -/
partial def lineForPos (lines : List Nat) (pos : Nat) (idx : Nat := 0) : Nat :=
  match lines with
  | [] => idx
  | [_] => idx
  | _ :: q :: rest =>
    if pos < q then idx
    else lineForPos (q :: rest) pos (idx + 1)

/-- Get the n-th element of a list, returning 0 if out of bounds. -/
def listGet (l : List Nat) (n : Nat) : Nat :=
  match l with
  | [] => 0
  | h :: t => if n == 0 then h else listGet t (n - 1)

/-- Convert a byte position to (0-based line, 0-based col). -/
def byteToLineCol (lines : List Nat) (pos : Nat) : Nat × Nat :=
  let l := lineForPos lines pos
  let lineStart := listGet lines l
  (l, pos - lineStart)

/-! ## Syntax tree traversal -/

/-- Serialize a `Lean.Syntax` node (and its subtree) into a JSON projection. -/
partial def syntaxToJson (stx : Syntax) (lineMap : List Nat) : String :=
  let rangeStr :=
    match stx.getPos?, stx.getTailPos? with
    | some p, some tp =>
      let pNat := p.byteIdx
      let tpNat := tp.byteIdx
      let (sl, sc) := byteToLineCol lineMap pNat
      let (el, ec) := byteToLineCol lineMap tpNat
      SourceRange.toJson { startLine := sl, startCol := sc, endLine := el, endCol := ec }
    | _, _ => "null"
  let kindStr := escapeJson stx.getKind.toString
  if stx.isAtom then
    jsonObj [("kind", quoteJson "atom"), ("syntaxKind", quoteJson kindStr),
      ("range", rangeStr), ("value", quoteJson (escapeJson stx.getAtomVal))]
  else if stx.isIdent then
    jsonObj [("kind", quoteJson "ident"), ("syntaxKind", quoteJson kindStr),
      ("range", rangeStr), ("raw", quoteJson (escapeJson stx.getId.toString))]
  else
    let children := stx.getArgs.toList.map (fun c => syntaxToJson c lineMap)
    let childJson := "[" ++ (",".intercalate children) ++ "]"
    jsonObj [("kind", quoteJson "node"), ("syntaxKind", quoteJson kindStr),
      ("range", rangeStr), ("children", childJson)]

/-! ## Find identifier in a list of syntax nodes -/

partial def findIdent (args : List Syntax) : Name :=
  match args with
  | [] => Name.anonymous
  | c :: rest => if c.isIdent then c.getId else findIdent rest

partial def findIdentOpt (args : List Syntax) (exclude : Name := Name.anonymous) : Option Name :=
  match args with
  | [] => none
  | c :: rest =>
    if c.isIdent && c.getId != exclude then some c.getId
    else findIdentOpt rest exclude

mutual
  partial def findFirstAtomVal (stx : Syntax) : String :=
    if stx.isAtom then stx.getAtomVal
    else findFirstAtomValInList stx.getArgs.toList

  partial def findFirstAtomValInList (args : List Syntax) : String :=
    match args with
    | [] => ""
    | c :: rest =>
      let found := findFirstAtomVal c
      if found.isEmpty then findFirstAtomValInList rest
      else found
end

/-! ## Command-level extraction from a parsed file -/

structure DeclInfo where
  keyword    : String
  name       : String
  fullName   : String
  syntaxJson : String
  deriving Inhabited

/-- Extract `DeclInfo` from a `Parser.Command.declaration` syntax node. -/
def extractDecl (declCmd : Syntax) (ns : Name) (lineMap : List Nat) : Option DeclInfo :=
  let declBody := declCmd[1]
  let kw := findFirstAtomVal declBody
  let declId := declBody[1]
  let declName := findIdent (declId.getArgs.toList)
  if declName == Name.anonymous then none
  else
    let fullName :=
      if ns == Name.anonymous then declName
      else ns.str declName.toString
    let syntaxJson := syntaxToJson declCmd lineMap
    some { keyword := kw, name := declName.toString, fullName := fullName.toString, syntaxJson }

/-! ## File-level parsing -/

structure FileParseResult where
  commands      : Array Syntax
  decls         : Array DeclInfo
  moduleNameOpt : Option Name
  deriving Inhabited

/-- Parse a `.lean` file and extract syntax and declaration info.
Uses an empty environment — sufficient for syntax extraction without custom elaborators. -/
def parseFileForSyntax (filePath : String) : IO FileParseResult := do
  let content ← IO.FS.readFile filePath
  let lineMap := buildLineMap content
  let inputCtx := Parser.mkInputContext content filePath
  let env ← mkEmptyEnvironment
  let moduleName : Name :=
    Name.mkSimple (filePath.replace "/" "." |>.replace ".lean" "")
  let pmctx := Parser.ParserModuleContext.mk env {} moduleName []
  let (_headerSyntax, mps, msgs) ← Parser.parseHeader inputCtx
  let mut currentMps := mps
  let mut currentMsgs := msgs
  let mut allCmds : Array Syntax := #[]
  for _ in [0:10000] do
    let oldPos := currentMps.pos
    let (cmd, newMps, newMsgs) := Parser.parseCommand inputCtx pmctx currentMps currentMsgs
    currentMps := newMps
    currentMsgs := newMsgs
    if newMps.pos == oldPos then break
    allCmds := allCmds.push cmd
  -- Extract declarations with namespace tracking
  let mut decls : Array DeclInfo := #[]
  let mut currentNamespace := Name.anonymous
  /- Track every syntactic scope.  A namespace frame stores its parent name;
  a section frame stores `none` because closing a section must not alter the
  current namespace. -/
  let mut scopeStack : List (Option Name) := []
  for cmd in allCmds do
    let kind := cmd.getKind
    if kind == ``Parser.Command.declaration then
      if let some di := extractDecl cmd currentNamespace lineMap then
        decls := decls.push di
    else if kind == ``Parser.Command.namespace then
      if let some nsName := findIdentOpt (cmd.getArgs.toList) `namespace then
        scopeStack := some currentNamespace :: scopeStack
        currentNamespace :=
          if currentNamespace == Name.anonymous then nsName
          else currentNamespace.str nsName.toString
    else if kind == ``Parser.Command.section then
      scopeStack := none :: scopeStack
    else if kind == ``Parser.Command.end then
      match scopeStack with
      | some parent :: rest =>
        currentNamespace := parent
        scopeStack := rest
      | none :: rest =>
        scopeStack := rest
      | [] =>
        currentNamespace := Name.anonymous
  return { commands := allCmds, decls, moduleNameOpt := some moduleName }

/-! ## v2: Environment dump — declaration metadata from elaborated modules -/

def ourPrefixes : List String :=
  ["ChiralCausalCone", "ChiralTensor", "TLChain",
   "JonesBraid", "YangBaxter", "B3Presented",
   "BraidIdeal", "IdealDescent", "BaxterAnchor", "B3Representation",
   "AlgebraicCuntzQuotient", "CStarCuntzTensorQuotient",
   "ComplexStarCuntzRedesign", "SupergradedCuntzBdG",
   "HestenesCuntzSpacetimeAlgebra", "HestenesCuntzPhaseSpace",
   "BogoliubovWeylChemicalPotential", "RelativeModularStateDikin",
   "RescaledPhaseVolumeCanonical", "GaugeUHFLift",
   "WeylGaugeColimitWeld", "WeylColimitCanonicalLimit",
   "BogoliubovSU3ParafermionWeld", "BogoliubovSU3ParafermionProofChain",
   "WeylSU3ColorSymmetry", "GellMannParafermionSolder",
   "ParafermionIdentityRealization", "CantorBoundaryCuntzFamily",
   "WeylSolderedParafermionSymmetry", "CuntzBoundarySolderRealization",
   "GellMannParafermionRealizationRoutesSynthesis",
   "BogoliubovBraidGraphWeld", "ColorCARStandardModel",
   "FureyCharges", "GellMannCartan", "GellMannSU3",
   "arithmetic", "finiteArithmetic", "finiteZeta", "boltzmann",
   "rh", "RHStatement", "HilbertPolyaShape", "hilbert_polya",
   "criticalDamping", "complexTemperature", "hagedornTemperature",
   "PrimonSuperThermo", "MajoranaPrimonSpectralBridge",
   "PrimonHilbertPolyaSeparation", "PrimonBosonFermionDuality",
   "PrimonCoarseGraining", "PrimonCoarseGrainedHilbertPolyaPotential",
   "JaynesLDDPGNSColimit", "ContinuumAsColimitCounting",
   "CurryHowardLambekColimit", "Clifford55AnomalyOSP",
   "ProjectiveAffineConformalClosure55", "TwistorParafermionBoundary",
   "CP3CantorGeometricObstruction", "HillWheelerProjection", "HillWheelerUniversalProjection",
   "SU3LoopBraidCuntzBoundary", "SU3LoopBraidDuality",
   "HolographicGaugeSymmetryUniqueness", "GravitationalQuantumBraidDuality",
   "SUNQuantumBraidDuality", "TopologicalColorCrystalFormal", "SolovievQPNMChiralCuntz",
   "SpectralCPTKleinBottle"]

def isOurs (name : Name) : Bool :=
  ourPrefixes.any (fun p => name.toString.startsWith p)

def kindString (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .opaqueInfo _ => "opaque"
  | _ => "other"

def envDeclToJson (name : Name) (ci : ConstantInfo) : String :=
  let deps := (ci.getUsedConstantsAsSet.toList.filter isOurs).map Name.toString
  let depStrs := deps.map (fun d => quoteJson (escapeJson d))
  let depJson := "[" ++ (",".intercalate depStrs) ++ "]"
  let typeStr := escapeJson (toString ci.type)
  jsonObj [
    ("name", quoteJson (escapeJson name.toString)),
    ("kind", quoteJson (kindString ci)),
    ("type", quoteJson typeStr),
    ("hasValue", if ci.value?.isSome then "true" else "false"),
    ("isUnsafe", if ci.isUnsafe then "true" else "false"),
    ("isAxiom", match ci with | .axiomInfo _ => "true" | _ => "false"),
    ("deps", depJson)
  ]

/-! ## Main -/

def main (args : List String) : IO Unit := do
  if args.isEmpty then
    IO.eprintln "Usage: lake env lean --run tools/lean_graph/DumpLeanGraph.lean <file.lean> [<file2.lean> ...]"
    return

  -- Syntax dump for each file
  for filePath in args do
    if !((filePath.endsWith ".lean")) then
      IO.eprintln s!"Skipping non-.lean file: {filePath}"
      continue
    IO.eprintln s!"[dump] syntax: {filePath}"
    let result ← parseFileForSyntax filePath
    for di in result.decls do
      let line := jsonObj [
        ("layer", quoteJson "syntax"),
        ("file", quoteJson (escapeJson filePath)),
        ("name", quoteJson (escapeJson di.fullName)),
        ("keyword", quoteJson di.keyword),
        ("syntax", di.syntaxJson)
      ]
      IO.println line

  IO.eprintln "[dump] note: environment layer available via 'lake env lean tools/ExtractGraph.lean'"
  IO.eprintln "[dump] done."
