import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Topological.FibonacciCasimir

/-!
# InfoGeometry.Topological.FibonacciColimit

Algebraic direct-limit theorems for the finite Fibonacci braid matrices.

This file uses the repository direct-limit API directly.  If a finite stage in a
commutative-ring tower carries the Fibonacci scalar equations and the Artin
matrix equality, then the canonical image of those scalars carries the same
equations in the algebraic direct limit.  The trace, determinant, and
discriminant Casimirs of `B = F R F` also survive this transport.
-/

noncomputable section

set_option autoImplicit false

namespace InfoGeometry.Topological.FibonacciAnyons

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

universe u

/--
The finite Fibonacci Artin relation survives canonical transport into an
algebraic direct limit.
-/
theorem fibonacci_colimit_artin_relation_of_finite_stage
    {Stage : Nat → Type u} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (n : Nat) (q qInv τ sqrtτ : Stage n)
    (hArtin :
      R_matrixOf q qInv * B_matrixOf q qInv τ sqrtτ * R_matrixOf q qInv =
        B_matrixOf q qInv τ sqrtτ * R_matrixOf q qInv *
          B_matrixOf q qInv τ sqrtτ) :
    R_matrixOf (directLimitOf (Stage := Stage) bond n q)
        (directLimitOf (Stage := Stage) bond n qInv) *
        B_matrixOf (directLimitOf (Stage := Stage) bond n q)
          (directLimitOf (Stage := Stage) bond n qInv)
          (directLimitOf (Stage := Stage) bond n τ)
          (directLimitOf (Stage := Stage) bond n sqrtτ) *
        R_matrixOf (directLimitOf (Stage := Stage) bond n q)
          (directLimitOf (Stage := Stage) bond n qInv) =
      B_matrixOf (directLimitOf (Stage := Stage) bond n q)
          (directLimitOf (Stage := Stage) bond n qInv)
          (directLimitOf (Stage := Stage) bond n τ)
          (directLimitOf (Stage := Stage) bond n sqrtτ) *
        R_matrixOf (directLimitOf (Stage := Stage) bond n q)
          (directLimitOf (Stage := Stage) bond n qInv) *
          B_matrixOf (directLimitOf (Stage := Stage) bond n q)
            (directLimitOf (Stage := Stage) bond n qInv)
            (directLimitOf (Stage := Stage) bond n τ)
            (directLimitOf (Stage := Stage) bond n sqrtτ) := by
  exact fibonacci_artin_relation_map (directLimitOf (Stage := Stage) bond n)
    q qInv τ sqrtτ hArtin

/--
The inverse-pair relation survives canonical transport into an algebraic direct
limit.
-/
theorem fibonacci_colimit_inverse_relation_of_finite_stage
    {Stage : Nat → Type u} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (n : Nat) (q qInv : Stage n)
    (h : q * qInv = 1) :
    directLimitOf (Stage := Stage) bond n q *
        directLimitOf (Stage := Stage) bond n qInv = 1 := by
  simpa [map_mul, map_one] using congrArg (directLimitOf (Stage := Stage) bond n) h

/--
The golden-ratio relation survives canonical transport into an algebraic direct
limit.
-/
theorem fibonacci_colimit_tau_relation_of_finite_stage
    {Stage : Nat → Type u} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (n : Nat) (τ : Stage n)
    (h : τ ^ 2 + τ = 1) :
    directLimitOf (Stage := Stage) bond n τ ^ 2 +
        directLimitOf (Stage := Stage) bond n τ = 1 := by
  simpa [map_pow, map_add, map_one] using
    congrArg (directLimitOf (Stage := Stage) bond n) h

/--
The square-root relation for the Fibonacci fusion entry survives canonical
transport into an algebraic direct limit.
-/
theorem fibonacci_colimit_sqrt_tau_relation_of_finite_stage
    {Stage : Nat → Type u} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (n : Nat) (τ sqrtτ : Stage n)
    (h : sqrtτ ^ 2 = τ) :
    directLimitOf (Stage := Stage) bond n sqrtτ ^ 2 =
      directLimitOf (Stage := Stage) bond n τ := by
  simpa [map_pow] using congrArg (directLimitOf (Stage := Stage) bond n) h

/--
The phase-to-golden-ratio relation survives canonical transport into an
algebraic direct limit.
-/
theorem fibonacci_colimit_phase_relation_of_finite_stage
    {Stage : Nat → Type u} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (n : Nat) (q qInv τ : Stage n)
    (h : q ^ 2 + qInv ^ 2 = τ) :
    directLimitOf (Stage := Stage) bond n q ^ 2 +
        directLimitOf (Stage := Stage) bond n qInv ^ 2 =
      directLimitOf (Stage := Stage) bond n τ := by
  simpa [map_pow, map_add] using congrArg (directLimitOf (Stage := Stage) bond n) h

/-! ## Direct-limit Casimir readouts -/

/--
The trace Casimir of `B = F R F` survives transport from a finite stage into
the algebraic direct limit.
-/
theorem fibonacci_colimit_trace_casimir_of_finite_stage
    {Stage : Nat → Type u} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (n : Nat) (q qInv τ sqrtτ : Stage n)
    (hτ : τ ^ 2 + τ = 1)
    (hsqrtτ : sqrtτ ^ 2 = τ) :
    trace2
        (B_matrixOf
          (directLimitOf (Stage := Stage) bond n q)
          (directLimitOf (Stage := Stage) bond n qInv)
          (directLimitOf (Stage := Stage) bond n τ)
          (directLimitOf (Stage := Stage) bond n sqrtτ)) =
      trace2
        (R_matrixOf
          (directLimitOf (Stage := Stage) bond n q)
          (directLimitOf (Stage := Stage) bond n qInv)) := by
  let φ : Stage n →+* DirectLimitSuperClosure (Stage := Stage) bond :=
    directLimitOf (Stage := Stage) bond n
  have hFstage : F_matrixOf τ sqrtτ * F_matrixOf τ sqrtτ = 1 :=
    F_involution τ sqrtτ hτ hsqrtτ
  have hF_limit :
      F_matrixOf (φ τ) (φ sqrtτ) * F_matrixOf (φ τ) (φ sqrtτ) =
        (1 : Matrix (Fin 2) (Fin 2) (DirectLimitSuperClosure (Stage := Stage) bond)) := by
    have hMap := congrArg (mapMatrix φ) hFstage
    rw [mapMatrix_mul, mapMatrix_F] at hMap
    rw [mapMatrix_one] at hMap
    exact hMap
  exact
    trace2_B_eq_trace2_R_of_F_involution
      (φ q) (φ qInv) (φ τ) (φ sqrtτ)
      hF_limit

/--
The determinant Casimir of `B = F R F` survives transport from a finite stage
into the algebraic direct limit.
-/
theorem fibonacci_colimit_det_casimir_of_finite_stage
    {Stage : Nat → Type u} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (n : Nat) (q qInv τ sqrtτ : Stage n)
    (hτ : τ ^ 2 + τ = 1)
    (hsqrtτ : sqrtτ ^ 2 = τ) :
    det2
        (B_matrixOf
          (directLimitOf (Stage := Stage) bond n q)
          (directLimitOf (Stage := Stage) bond n qInv)
          (directLimitOf (Stage := Stage) bond n τ)
          (directLimitOf (Stage := Stage) bond n sqrtτ)) =
      det2
        (R_matrixOf
          (directLimitOf (Stage := Stage) bond n q)
          (directLimitOf (Stage := Stage) bond n qInv)) := by
  let φ : Stage n →+* DirectLimitSuperClosure (Stage := Stage) bond :=
    directLimitOf (Stage := Stage) bond n
  have hFstage : F_matrixOf τ sqrtτ * F_matrixOf τ sqrtτ = 1 :=
    F_involution τ sqrtτ hτ hsqrtτ
  have hF_limit :
      F_matrixOf (φ τ) (φ sqrtτ) * F_matrixOf (φ τ) (φ sqrtτ) =
        (1 : Matrix (Fin 2) (Fin 2) (DirectLimitSuperClosure (Stage := Stage) bond)) := by
    have hMap := congrArg (mapMatrix φ) hFstage
    rw [mapMatrix_mul, mapMatrix_F] at hMap
    rw [mapMatrix_one] at hMap
    exact hMap
  exact
    det2_B_eq_det2_R_of_F_involution
      (φ q) (φ qInv) (φ τ) (φ sqrtτ)
      hF_limit

/--
The characteristic-discriminant Casimir of `B = F R F` survives transport from
a finite stage into the algebraic direct limit.
-/
theorem fibonacci_colimit_discriminant_casimir_of_finite_stage
    {Stage : Nat → Type u} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (n : Nat) (q qInv τ sqrtτ : Stage n)
    (hτ : τ ^ 2 + τ = 1)
    (hsqrtτ : sqrtτ ^ 2 = τ) :
    discriminant2
        (B_matrixOf
          (directLimitOf (Stage := Stage) bond n q)
          (directLimitOf (Stage := Stage) bond n qInv)
          (directLimitOf (Stage := Stage) bond n τ)
          (directLimitOf (Stage := Stage) bond n sqrtτ)) =
      discriminant2
        (R_matrixOf
          (directLimitOf (Stage := Stage) bond n q)
          (directLimitOf (Stage := Stage) bond n qInv)) := by
  let φ : Stage n →+* DirectLimitSuperClosure (Stage := Stage) bond :=
    directLimitOf (Stage := Stage) bond n
  have hFstage : F_matrixOf τ sqrtτ * F_matrixOf τ sqrtτ = 1 :=
    F_involution τ sqrtτ hτ hsqrtτ
  have hF_limit :
      F_matrixOf (φ τ) (φ sqrtτ) * F_matrixOf (φ τ) (φ sqrtτ) =
        (1 : Matrix (Fin 2) (Fin 2) (DirectLimitSuperClosure (Stage := Stage) bond)) := by
    have hMap := congrArg (mapMatrix φ) hFstage
    rw [mapMatrix_mul, mapMatrix_F] at hMap
    rw [mapMatrix_one] at hMap
    exact hMap
  exact
    discriminant2_B_eq_discriminant2_R_of_F_involution
      (φ q) (φ qInv) (φ τ) (φ sqrtτ)
      hF_limit

end InfoGeometry.Topological.FibonacciAnyons
