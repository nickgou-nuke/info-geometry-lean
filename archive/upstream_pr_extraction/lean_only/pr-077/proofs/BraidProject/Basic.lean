import proofs.BraidProject.InductiveColimitComplement
import proofs.BraidProject.BraidMonoid
import proofs.BraidProject.BraidGroup
import proofs.BraidProject.Grids
import proofs.BraidProject.GridsTwo
import proofs.BraidProject.Stability
import proofs.BraidProject.ListBoolFacts
import proofs.BraidProject.AcrossStrands
import proofs.BraidProject.InductionWithBounds
import proofs.BraidProject.FlipBraid
import proofs.BraidProject.Cancellability
import proofs.BraidProject.Reversing
import proofs.BraidProject.FusedMonoid
import proofs.BraidProject.PartialGrids

/-!
# Buildable BraidProject Root

The upstream root imports `BraidProject.Basic`, but the file was absent in the
cloned repository. Keep the root conservative and buildable on Lean 4.28.0 by
importing the generator-index colimit complement first.
-/
