import InfoGeometry.Quantum.Fock
import InfoGeometry.Quantum.RealMajorana

/-!
# InfoGeometry.Quantum.NoncommutativeFockBridge

Bridge for the noncommutative sector on the Fock-style carrier.

The commutative diagonal sector is handled separately by the weighted
`Fin n → ℂ` model.  Here we only name the full operator sector already owned by
`RealMajorana` and the projector split owned by `Fock`.
-/

noncomputable section

namespace NoncommutativeFockBridge

open InfoGeometry.Krein
open InfoGeometry.Quantum
open RealMajorana

open scoped InnerProductSpace

variable {S : Type}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]

/-- The Fock split is the internal creation/annihilation decomposition. -/
theorem fock_creation_add_annihilation :
    creationOp (E := S) + annihilationOp (E := S)
      = ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace S) := by
  simpa using creation_add_annihilation (E := S)

/-- The creation and annihilation channels are orthogonal projectors. -/
theorem fock_creation_annihilation_orthogonal :
    (creationOp (E := S)).comp (annihilationOp (E := S)) = 0 := by
  simpa using creation_annihilation_orthogonal (E := S)

/-- The annihilation channel kills the vacuum vector. -/
theorem fock_annihilation_kills_vacuum :
    annihilationOp (E := S) 0 = 0 := by
  simpa using annihilation_kills_vacuum_vector (E := S)

/--
The full noncommutative sector is represented by the real Majorana CAR map on
the carrier.
-/
theorem noncommutative_sector_CAR
    (M : RealMajoranaDatum (S := S)) :
    MajoranaCARWitness (S := S) (fun u v => inner ℝ u v) M.gamma := by
  simpa using M.car_realization_of_clifford

/-- Bogoliubov transport preserves the full CAR witness. -/
theorem noncommutative_sector_CAR_transport
    (M : RealMajoranaDatum (S := S))
    (T : RealBogoliubovTransform (S := S) M) :
    MajoranaCARWitness (S := S) (fun u v => inner ℝ u v)
      (T.transportGamma) := by
  simpa using T.car_realization_of_clifford

/-- Bogoliubov transport preserves the Weyl-plus sector. -/
theorem bogoliubov_maps_weylPlus
    (M : RealMajoranaDatum (S := S))
    (T : RealBogoliubovTransform (S := S) M)
    (x : S) (hx : x ∈ M.weylPlus) :
    T.B x ∈ T.transportWeylPlus := by
  exact T.map_weylPlus x hx

/-- Bogoliubov transport preserves the Weyl-minus sector. -/
theorem bogoliubov_maps_weylMinus
    (M : RealMajoranaDatum (S := S))
    (T : RealBogoliubovTransform (S := S) M)
    (x : S) (hx : x ∈ M.weylMinus) :
    T.B x ∈ T.transportWeylMinus := by
  exact T.map_weylMinus x hx

end NoncommutativeFockBridge
