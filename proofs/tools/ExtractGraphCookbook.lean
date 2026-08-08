import Lean

def ourPrefixes : List String := ["MatrixCookbook"]

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

def escapeJson (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\""

def extractOne (name : Name) (ci : ConstantInfo) : String :=
  let deps := (ci.getUsedConstantsAsSet.toList.filter isOurs).map Name.toString
  let depStrs := deps.map (fun d => "\"" ++ escapeJson d ++ "\"")
  let depJson := "[" ++ (",".intercalate depStrs) ++ "]"
  let jname := escapeJson (name.toString)
  "{\"name\": \"" ++ jname ++
    "\", \"kind\": \"" ++ kindString ci ++
    "\", \"deps\": " ++ depJson ++ "}"

run_cmd do
  let env ← getEnv
  let ours := env.constants.toList.filter (fun (n, _) => isOurs n)
  let lines := ours.map (fun (n, ci) => extractOne n ci)
  let json := "[\n" ++ (",\n".intercalate lines) ++ "\n]\n"
  IO.FS.writeFile "proof_graph.json" json
  let count := ours.length
  logInfo s!"Wrote {count} declarations to proof_graph.json"
