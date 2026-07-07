theorem buildCantorRep_one_is_jw_rep :
    IsJWCantorRepresentation 1 (buildCantorRep 1) := by
  constructor
  · intro k
    fin_cases k
    apply LinearMap.ext
    intro f
    ext x
    -- Unfolds `buildCantorRep 1 (jwCreation 1 0)`
    -- into `wittCreationBase` mapping the $|0⟩ ↦ |1⟩` bit flip on `CantorAddress 1`