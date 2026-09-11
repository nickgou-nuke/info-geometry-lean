import InfoGeometry.Projective.HadjiivanovFiniteLaurentModeColimitProjection
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Realification of the finite Laurent-mode connection cone

The Hestenes--Krein consumer is real-linear, whereas the Laurent-mode tower is
naturally complex-linear.  This owner performs only restriction of scalars
from `ℂ` to `ℝ` and proves that all cone and connection intertwining laws are
retained.  It introduces no topology or analytic limit.
-/

namespace InfoGeometry.Projective.HadjiivanovFiniteLaurentModeRealification

open HadjiivanovLogConnectionColimitBridge
open HadjiivanovLogConnectionBridge
open HadjiivanovFiniteLaurentModeTower
open HadjiivanovFiniteLaurentModeColimitProjection

noncomputable section

variable (A : ℕ → Type*)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module ℂ (A n)]
variable (A_inf : Type*) [AddCommGroup A_inf] [Module ℂ A_inf]

/-- Restrict a complex-linear connection cone to its underlying real-linear
cone.  The carriers and functions are unchanged. -/
def realifyConnectionColimitCone
    (C : ConnectionColimitCone (R := ℂ) A A_inf) :
    ConnectionColimitCone (R := ℝ) A A_inf where
  iota n := (C.iota n).restrictScalars ℝ
  psi n := (C.psi n).restrictScalars ℝ
  psi_comm n := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun (C.psi_comm n) x
  stageConnection n := (C.stageConnection n).restrictScalars ℝ
  ambientConnection := C.ambientConnection.restrictScalars ℝ
  stageConnection_comm n := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun (C.stageConnection_comm n) x
  ambientConnection_comm n := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun (C.ambientConnection_comm n) x

namespace realifyConnectionColimitCone

variable (C : ConnectionColimitCone (R := ℂ) A A_inf)

@[simp] theorem iota_apply (n : ℕ) (x : A n) :
    (realifyConnectionColimitCone A A_inf C).iota n x = C.iota n x := rfl

@[simp] theorem psi_apply (n : ℕ) (x : A n) :
    (realifyConnectionColimitCone A A_inf C).psi n x = C.psi n x := rfl

@[simp] theorem stageConnection_apply (n : ℕ) (x : A n) :
    (realifyConnectionColimitCone A A_inf C).stageConnection n x =
      C.stageConnection n x := rfl

@[simp] theorem ambientConnection_apply (x : A_inf) :
    (realifyConnectionColimitCone A A_inf C).ambientConnection x =
      C.ambientConnection x := rfl

end realifyConnectionColimitCone

/-- Concrete real-linear cone associated to a supplied ambient realization of
the finite Laurent-mode logarithmic connection tower. -/
def realifiedFiniteModeConnectionCone
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : LogResidue V)
    (A_inf : Type*) [AddCommGroup A_inf] [Module ℂ A_inf]
    (psi : ∀ n, LaurentModeTower V n →ₗ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (modeBond n) = psi n)
    (ambientConnection : A_inf →ₗ[ℂ] A_inf)
    (ambientConnection_comm : ∀ n,
      ambientConnection.comp (psi n) =
        (psi n).comp (finiteModeConnection R n)) :
    ConnectionColimitCone (R := ℝ) (LaurentModeTower V) A_inf :=
  realifyConnectionColimitCone (LaurentModeTower V) A_inf
    (finiteModeConnectionCone R A_inf psi psi_comm
      ambientConnection ambientConnection_comm)

end

end InfoGeometry.Projective.HadjiivanovFiniteLaurentModeRealification
