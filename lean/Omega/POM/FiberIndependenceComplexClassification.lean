import Mathlib.Tactic

namespace Omega.POM

/-- The fiber independence complex of a disjoint union of paths is either contractible or
homotopy equivalent to a single sphere, according to the mod-`3` path classification and the join
decomposition of the components.
    thm:pom-fiber-independence-complex-classification -/
theorem paper_pom_fiber_independence_complex_classification
    {pathCaseClassification badModThreeComponent allComponentsAvoidBadModThree
        joinDecomposition contractibleCase sphereCase : Prop}
    (hPathCaseClassification : pathCaseClassification)
    (hJoinDecomposition : joinDecomposition)
    (classifyPathComponents :
      pathCaseClassification → badModThreeComponent ∨ allComponentsAvoidBadModThree)
    (badModThreeComponentForcesContraction :
      badModThreeComponent → joinDecomposition → contractibleCase)
    (allGoodComponentsGiveSphere :
      allComponentsAvoidBadModThree → joinDecomposition → sphereCase) :
    contractibleCase ∨ sphereCase := by
  rcases classifyPathComponents hPathCaseClassification with hBad | hGood
  · exact Or.inl <| badModThreeComponentForcesContraction hBad hJoinDecomposition
  · exact Or.inr <| allGoodComponentsGiveSphere hGood hJoinDecomposition

end Omega.POM
