import proofs.ChiralStokesPauliBasis

/-!
# Named adapter for Stokes coordinates

The registered tuple-based Stokes owner remains unchanged.  This adapter gives
named fields in the semantic order `(A0,A1,A2,A3)` while making the underlying
right-associated product order explicit.
-/

noncomputable section
namespace ChiralStokesNamedAdapter

open TwoSheetThreeColorWeyl
open ChiralStokesCoordinates

structure StokesData where
  A0 : M3C
  A1 : M3C
  A2 : M3C
  A3 : M3C

 def toQuad (S : StokesData) : StokesQuad :=
  (S.A0, (S.A3, (S.A1, S.A2)))

def fromQuad (S : StokesQuad) : StokesData where
  A0 := S.1
  A1 := S.2.2.1
  A2 := S.2.2.2
  A3 := S.2.1

theorem fromQuad_toQuad (S : StokesData) : fromQuad (toQuad S) = S := by
  cases S
  rfl

theorem toQuad_fromQuad (S : StokesQuad) : toQuad (fromQuad S) = S := by
  rcases S with ⟨A0, A3, A1, A2⟩
  rfl

end ChiralStokesNamedAdapter
end noncomputable section
