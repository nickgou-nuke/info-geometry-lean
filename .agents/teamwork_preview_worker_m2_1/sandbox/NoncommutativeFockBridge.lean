import InfoGeometry.Quantum.Fock
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.RealMajorana

/-!
# InfoGeometry.Quantum.NoncommutativeFockBridge

Bridge for the noncommutative sector on the Fock-style carrier.

The commutative diagonal sector is handled separately by the weighted
`Fin n → ℂ` model. Here we only name the full operator sector already owned by
`RealMajorana` and the projector split owned by `Fock`.

## CAS Idempotence & Braiding Verification
The algebraic identities of the Clifford projectors $P_\pm = \frac{1 \pm \gamma}{2}$
satisfy $P_\pm^2 = P_\pm$, $P_+ P_- = 0$, and $P_+ + P_- = \mathrm{Id}$.
These are certified by:
- `tools/gap/clifford_braiding_center.g` (Clifford central core and involution parity in $D_8$)
- `tools/infra/galgebra_clifford_peirce.py` (GaAlgebra/Clifford Peirce decomposition,
  projector idempotence `OP1^2 = OP1`, `OP2^2 = OP2`, and orthogonality `OP1 * OP2 = 0`)
-/

noncomputable section

namespace InfoGeometry.Quantum.NoncommutativeFockBridge

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
  exact creation_add_annihilation (E := S)

/-- The creation and annihilation channels are orthogonal projectors. -/
theorem fock_creation_annihilation_orthogonal :
    (creationOp (E := S)).comp (annihilationOp (E := S)) = 0 := by
  exact creation_annihilation_orthogonal (E := S)

/-- The annihilation channel kills the vacuum vector. -/
theorem fock_annihilation_kills_vacuum :
    annihilationOp (E := S) 0 = 0 := by
  exact annihilation_kills_vacuum_vector (E := S)

/--
The creation operator is idempotent: `P₊ ∘ P₊ = P₊`.
CAS Certificate: Verified by `tools/gap/clifford_braiding_center.g` and
`tools/infra/galgebra_clifford_peirce.py`.
-/
theorem fock_creation_idempotent :
    (creationOp (E := S)).comp (creationOp (E := S)) = creationOp (E := S) := by
  rw [creation_eq_plus_projector]
  exact gradePlusProj_idempotent (E := S)

/--
The annihilation operator is idempotent: `P₋ ∘ P₋ = P₋`.
CAS Certificate: Verified by `tools/gap/clifford_braiding_center.g` and
`tools/infra/galgebra_clifford_peirce.py`.
-/
theorem fock_annihilation_idempotent :
    (annihilationOp (E := S)).comp (annihilationOp (E := S)) = annihilationOp (E := S) := by
  rw [annihilation_eq_minus_projector]
  exact gradeMinusProj_idempotent (E := S)

/--
The annihilation and creation channels are orthogonal: `P₋ ∘ P₊ = 0`.
CAS Certificate: Verified by `tools/gap/clifford_braiding_center.g` and
`tools/infra/galgebra_clifford_peirce.py`.
-/
theorem fock_annihilation_creation_orthogonal :
    (annihilationOp (E := S)).comp (creationOp (E := S)) = 0 := by
  rw [creation_eq_plus_projector, annihilation_eq_minus_projector]
  exact gradeMinusProj_comp_gradePlusProj (E := S)

/--
Formal CAS Clifford projector idempotence certificate packet ($P_\pm^2 = P_\pm$, $P_+ P_- = 0$, $P_- P_+ = 0$).
Referencing CAS verification in `tools/gap/clifford_braiding_center.g` and
`tools/infra/galgebra_clifford_peirce.py`.
-/
structure CliffordProjectorIdempotenceCertificate (E : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  plus_idempotent :
    (creationOp (E := E)).comp (creationOp (E := E)) = creationOp (E := E)
  minus_idempotent :
    (annihilationOp (E := E)).comp (annihilationOp (E := E)) = annihilationOp (E := E)
  orthogonal_plus_minus :
    (creationOp (E := E)).comp (annihilationOp (E := E)) = 0
  orthogonal_minus_plus :
    (annihilationOp (E := E)).comp (creationOp (E := E)) = 0
  completeness :
    creationOp (E := E) + annihilationOp (E := E) = ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)

/--
The canonical CAS Clifford projector idempotence certificate for `DoubledSpace S`.
Referenced CAS scripts:
- `tools/gap/clifford_braiding_center.g` (central core and involution sign parity)
- `tools/infra/galgebra_clifford_peirce.py` (Peirce ladder decomposition and projector idempotence:
  `OP1^2 = OP1`, `OP2^2 = OP2`, `OP1 * OP2 = 0`, `OP1 + OP2 = I`).
-/
theorem cas_clifford_projector_idempotence_certificate :
    CliffordProjectorIdempotenceCertificate S := {
  plus_idempotent := fock_creation_idempotent
  minus_idempotent := fock_annihilation_idempotent
  orthogonal_plus_minus := fock_creation_annihilation_orthogonal
  orthogonal_minus_plus := fock_annihilation_creation_orthogonal
  completeness := fock_creation_add_annihilation
}

/--
Formal CAS Clifford projector idempotence and orthogonality theorem ($P_\pm^2 = P_\pm$, $P_+ P_- = 0$).
Referencing CAS verification in `tools/gap/clifford_braiding_center.g` and
`tools/infra/galgebra_clifford_peirce.py`.
-/
theorem fock_clifford_projector_idempotence :
    ((creationOp (E := S)).comp (creationOp (E := S)) = creationOp (E := S)) ∧
    ((annihilationOp (E := S)).comp (annihilationOp (E := S)) = annihilationOp (E := S)) ∧
    ((creationOp (E := S)).comp (annihilationOp (E := S)) = 0) := by
  exact ⟨fock_creation_idempotent, fock_annihilation_idempotent, fock_creation_annihilation_orthogonal⟩

/--
The full noncommutative sector is represented by the real Majorana CAR map on
the carrier.
-/
theorem noncommutative_sector_CAR
    (M : RealMajoranaDatum (S := S)) :
    MajoranaCARWitness (S := S) (fun u v => inner ℝ u v) M.gamma := by
  exact M.car_realization_of_clifford

/-- Bogoliubov transport preserves the full CAR witness. -/
theorem noncommutative_sector_CAR_transport
    (M : RealMajoranaDatum (S := S))
    (T : RealBogoliubovTransform (S := S) M) :
    MajoranaCARWitness (S := S) (fun u v => inner ℝ u v)
      (T.transportGamma) := by
  exact T.car_realization_of_clifford

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

end InfoGeometry.Quantum.NoncommutativeFockBridge
