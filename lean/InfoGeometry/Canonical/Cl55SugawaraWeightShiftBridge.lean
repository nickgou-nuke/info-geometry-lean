import InfoGeometry.Clifford.Cl55VirasoroWeightShiftBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SugawaraFiveGradingObstruction

/-! Comparison of the native Sugawara and Clifford weight-shift mechanisms.
The two carriers remain distinct; this file records only the shared shift law. -/
namespace InfoGeometry.Canonical.Cl55SugawaraWeightShiftBridge

open InfoGeometry.Canonical.SugawaraFiveGradingObstruction
open InfoGeometry.Clifford.Clifford55
open VirasoroProject

theorem finite_and_sugawara_weight_shift
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (J : ℤ → V →ₗ[𝕜] V)
    (trunc : ∀ v, Filter.atTop.Eventually (fun l => J l v = 0))
    (hcomm : ∀ m n, (J m).commutator (J n) =
      if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0)
    (n m : ℤ) :
    (sugawaraGen trunc n).commutator (J m) = -m • J (n + m) := by
  exact sugawara_current_mode_shift J trunc hcomm n m

theorem cl55_creation_weight_shift (i : Fin 5) (k : ℤ) {X : Cl55}
    (hX : X ∈ cl55GradeSubmodule k) :
    creation55 i * X ∈ cl55GradeSubmodule (1 + k) :=
  creation55_shifts_grade i k hX

theorem cl55_annihilation_weight_shift (i : Fin 5) (k : ℤ) {X : Cl55}
    (hX : X ∈ cl55GradeSubmodule k) :
    annihilation55 i * X ∈ cl55GradeSubmodule (-1 + k) :=
  annihilation55_shifts_grade i k hX

theorem cl55_creation_commutator_weight_shift (i : Fin 5) (k : ℤ) {X : Cl55}
    (hX : X ∈ cl55GradeSubmodule k) :
    creation55 i * X - X * creation55 i ∈
      cl55GradeSubmodule (1 + k) :=
  creation55_commutator_shifts_grade i k hX

theorem cl55_annihilation_commutator_weight_shift (i : Fin 5) (k : ℤ) {X : Cl55}
    (hX : X ∈ cl55GradeSubmodule k) :
    annihilation55 i * X - X * annihilation55 i ∈
      cl55GradeSubmodule (-1 + k) :=
  annihilation55_commutator_shifts_grade i k hX

end InfoGeometry.Canonical.Cl55SugawaraWeightShiftBridge
