import InfoGeometry.Projective.HadjiivanovLogConnectionReadoutBridge
import InfoGeometry.Canonical.TensorTowerColimit

/-!
# Colimit projection contract for logarithmic connections

This owner does not manufacture an analytic limit.  It packages the exact
linear cone data required by the repository's `TensorTowerColimit` owner and
proves that a compatible family of finite algebraic connection operators is
preserved by every finite bonding iterate and by the supplied ambient cone.

An actual Hestenes--Krein or analytic consumer must provide the ambient carrier,
cone maps, and compatibility witnesses explicitly.
-/

namespace InfoGeometry.Projective.HadjiivanovLogConnectionColimitBridge

noncomputable section

variable {R : Type*} [CommRing R]
variable (A : ℕ → Type*) [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
variable (A_inf : Type*) [AddCommGroup A_inf] [Module R A_inf]

/-- Typed finite-stage/ambient cone for a compatible connection family. -/
structure ConnectionColimitCone where
  iota : ∀ n, A n →ₗ[R] A (n + 1)
  psi : ∀ n, A n →ₗ[R] A_inf
  psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n
  stageConnection : ∀ n, A n →ₗ[R] A n
  ambientConnection : A_inf →ₗ[R] A_inf
  stageConnection_comm : ∀ n,
    (stageConnection (n + 1)).comp (iota n) =
      (iota n).comp (stageConnection n)
  ambientConnection_comm : ∀ n,
    ambientConnection.comp (psi n) = (psi n).comp (stageConnection n)

namespace ConnectionColimitCone

variable (C : ConnectionColimitCone (R := R) A A_inf)

/-- Every finite bonding iterate intertwines the staged connections. -/
theorem stageConnection_iota_seq (n m : ℕ) :
    (C.stageConnection (n + m)).comp
        (iota_seq A C.iota n m) =
      (iota_seq A C.iota n m).comp
        (C.stageConnection n) := by
  induction m with
  | zero =>
      simp [iota_seq]
  | succ m ih =>
      simp only [iota_seq]
      rw [← LinearMap.comp_assoc]
      have hcomm :
          (C.stageConnection (n + (m + 1))).comp (C.iota (n + m)) =
            (C.iota (n + m)).comp (C.stageConnection (n + m)) := by
        simpa [Nat.add_assoc] using C.stageConnection_comm (n + m)
      rw [hcomm, LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]

/-- The ambient cone map is independent of the chosen later representative. -/
theorem psi_iota_seq (n m : ℕ) :
    (C.psi (n + m)).comp (iota_seq A C.iota n m) =
      C.psi n := by
  exact psi_comp_iota_seq A C.iota A_inf C.psi C.psi_comm n m

/-- Connection application commutes with projection to the supplied ambient
colimit carrier, even after any finite number of bonding steps. -/
theorem ambientConnection_after_iota_seq
    (n m : ℕ) (x : A n) :
    C.ambientConnection
        (C.psi (n + m) (iota_seq A C.iota n m x)) =
      C.psi n (C.stageConnection n x) := by
  have hpsi := LinearMap.congr_fun (psi_iota_seq A A_inf C n m) x
  change C.psi (n + m) (iota_seq A C.iota n m x) = C.psi n x at hpsi
  rw [hpsi]
  have hcomm := LinearMap.congr_fun (C.ambientConnection_comm n) x
  exact hcomm

end ConnectionColimitCone

end

end InfoGeometry.Projective.HadjiivanovLogConnectionColimitBridge
