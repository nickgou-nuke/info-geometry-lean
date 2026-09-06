import proofs.DeterminantInvariance
import proofs.StructureTensor
import proofs.PatchRepresentation
import proofs.CartanDecomposition
import proofs.DihedralEquivariance
import proofs.RankOneEigenvectors
import proofs.KreinDoubling
import proofs.NambuGorkovSpinor
import proofs.BogoliubovRindler
import proofs.QuantumDeformation
import proofs.SplitOctonionZorn

/-!
# Root Module for the Cartan-Krein Contour Filter

This module packages the complete information-geometric formalism 
developed for filtering image patches through a null-cone mapping.
The mathematics transitions from the 2x2 local gradients 
to the 8D split octonion composition algebra.

## Modules:
1. `PatchRepresentation` : Null cone det(M)=0 is rigorously mapped to rank 1 (pure 1D contours).
2. `StructureTensor` / `CartanDecomposition` : Symm/Skew decomposition and positive definition.
3. `DihedralEquivariance` : Proof that the structure tensor rotates exactly with the gradient D4 action.
4. `SplitOctonionZorn` : The overarching (4,4) composition algebra modeling coupled patches.
-/
