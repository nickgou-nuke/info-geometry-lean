import proofs.ChiralStokesNamedAdapter

/-!
# Krein action on named Stokes channels

This owner proves the diagonal channel law on named Stokes data.  The bridge
from this coordinate action to the full `M6C` Krein adjoint is intentionally a
separate theorem owner.
-/

noncomputable section
namespace TwoSheetKreinStokesCoordinates

open ChiralStokesNamedAdapter
open TwoSheetThreeColorWeyl

 def kreinStokes (S : StokesData) : StokesData where
  A0 := Matrix.conjTranspose S.A0
  A1 := Matrix.conjTranspose S.A1
  A2 := -Matrix.conjTranspose S.A2
  A3 := -Matrix.conjTranspose S.A3

@[simp] theorem kreinStokes_involutive (S : StokesData) :
    kreinStokes (kreinStokes S) = S := by
  cases S
  simp [kreinStokes]

theorem kreinStokes_A0 (S : StokesData) :
    (kreinStokes S).A0 = Matrix.conjTranspose S.A0 := rfl

theorem kreinStokes_A1 (S : StokesData) :
    (kreinStokes S).A1 = Matrix.conjTranspose S.A1 := rfl

theorem kreinStokes_A2 (S : StokesData) :
    (kreinStokes S).A2 = -Matrix.conjTranspose S.A2 := rfl

theorem kreinStokes_A3 (S : StokesData) :
    (kreinStokes S).A3 = -Matrix.conjTranspose S.A3 := rfl

end TwoSheetKreinStokesCoordinates
end noncomputable section
