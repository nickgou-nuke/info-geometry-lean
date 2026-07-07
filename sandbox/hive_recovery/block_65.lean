/-- The concrete n-depth representation map satisfies the Jordan-Wigner constraints. -/
theorem buildCantorRep_one_is_jw_rep :
    IsJWCantorRepresentation 1 (buildCantorRep 1) := by
  constructor
  · intro k
    fin_cases k
    apply LinearMap.ext
    intro f
    ext x
    -- Explicit calculation of the base wittCreationBase matrix action
    sorry
  · intro k
    fin_cases k
    apply LinearMap.ext
    intro f
    ext x
    -- Explicit calculation of the base wittAnnihilationBase matrix action
    sorry