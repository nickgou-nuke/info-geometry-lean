/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/
import InfoGeometry.Arithmetic.PrimeMajoranaCAR
import InfoGeometry.Algebra.InfiniteInductiveSUSY

/-!
# Infinite Majorana CAR Extension via Inductive Direct Limit

This module formalizes the infinite-dimensional direct-limit transport for
Majorana prime generators.

The first theorem is the generic finite-stage image invariant for the local
CAR closure. The second layer generalizes the same induction pattern to the
derived `parityOp` observable of a transported `ExteriorCARPair` chain.

No analytic completion is claimed.
-/

open InfoGeometry.Arithmetic.PrimeMajoranaCAR
open InfoGeometry.Algebra.InfiniteInductiveSUSY

namespace InfoGeometry.Arithmetic.PrimeMajoranaInfiniteCAR

variable (A : ℕ → Type*) [∀ n : ℕ, Ring (A n)]
variable (L : Type*) [Ring L]
variable (φ : ∀ n : ℕ, A n →+* A (Nat.succ n))
variable (ι : ∀ n : ℕ, A n →+* L)

/--
Finite-stage CAR image invariant for a transported `ExteriorCARPair` chain.

This is the direct infinite-target version of the local split-Majorana pair:
`ε² = ι² = 0` and `{ε,ι} = 1` are preserved in every compatible image.
-/
theorem infinite_majorana_car_closure
    (Q R H Z : ∀ n : ℕ, A n)
    (hQ0 : Q 0 * Q 0 = 0)
    (hR0 : R 0 * R 0 = 0)
    (hclosure0 : anticomm (Q 0) (R 0) = H 0 + Z 0)
    (hZQ0 : Z 0 * Q 0 = Q 0 * Z 0)
    (hZR0 : Z 0 * R 0 = R 0 * Z 0)
    (hQstep : ∀ n : ℕ, Q (Nat.succ n) = φ n (Q n))
    (hRstep : ∀ n : ℕ, R (Nat.succ n) = φ n (R n))
    (hHstep : ∀ n : ℕ, H (Nat.succ n) = φ n (H n))
    (hZstep : ∀ n : ℕ, Z (Nat.succ n) = φ n (Z n)) :
    ∀ n : ℕ,
      ι n (Q n) * ι n (Q n) = 0 ∧
      ι n (R n) * ι n (R n) = 0 ∧
      anticomm (ι n (Q n)) (ι n (R n)) = ι n (H n) + ι n (Z n) ∧
      ι n (Z n) * ι n (Q n) = ι n (Q n) * ι n (Z n) ∧
      ι n (Z n) * ι n (R n) = ι n (R n) * ι n (Z n) ∧
      ι n (Q n + R n) * ι n (Q n + R n) = ι n (H n) + ι n (Z n) := by
  intro n
  exact limit_image_inductive_susy_closure φ ι Q R H Z hQ0 hR0 hclosure0 hZQ0 hZR0 hQstep hRstep hHstep hZstep n

/-- Stepwise transport of `cMajorana = ε + ι` in a finite Majorana tower. -/
theorem exteriorCARPair_cMajorana_step
    (P : ∀ n : ℕ, ExteriorCARPair (A n))
    (h_eps : ∀ n : ℕ, φ n (P n).eps = (P (Nat.succ n)).eps)
    (h_iota : ∀ n : ℕ, φ n (P n).iota = (P (Nat.succ n)).iota)
    (n : ℕ) :
    φ n ((P n).cMajorana) = (P (Nat.succ n)).cMajorana := by
  dsimp [InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair.cMajorana]
  rw [map_add, h_eps n, h_iota n]

/-- Stepwise transport of `dMajorana = ε - ι` in a finite Majorana tower. -/
theorem exteriorCARPair_dMajorana_step
    (P : ∀ n : ℕ, ExteriorCARPair (A n))
    (h_eps : ∀ n : ℕ, φ n (P n).eps = (P (Nat.succ n)).eps)
    (h_iota : ∀ n : ℕ, φ n (P n).iota = (P (Nat.succ n)).iota)
    (n : ℕ) :
    φ n ((P n).dMajorana) = (P (Nat.succ n)).dMajorana := by
  dsimp [InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair.dMajorana]
  rw [map_sub, h_eps n, h_iota n]

/-- Stepwise transport of the local number operator `N = ε ι`. -/
theorem exteriorCARPair_numberOp_step
    (P : ∀ n : ℕ, ExteriorCARPair (A n))
    (h_eps : ∀ n : ℕ, φ n (P n).eps = (P (Nat.succ n)).eps)
    (h_iota : ∀ n : ℕ, φ n (P n).iota = (P (Nat.succ n)).iota)
    (n : ℕ) :
    φ n ((P n).numberOp) = (P (Nat.succ n)).numberOp := by
  dsimp [InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair.numberOp]
  rw [map_mul, h_eps n, h_iota n]

/-- Stepwise transport of the local parity operator `Π = c d`. -/
theorem exteriorCARPair_parityOp_step
    (P : ∀ n : ℕ, ExteriorCARPair (A n))
    (h_eps : ∀ n : ℕ, φ n (P n).eps = (P (Nat.succ n)).eps)
    (h_iota : ∀ n : ℕ, φ n (P n).iota = (P (Nat.succ n)).iota)
    (n : ℕ) :
    φ n ((P n).parityOp) = (P (Nat.succ n)).parityOp := by
  simp [InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair.parityOp,
    InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair.cMajorana,
    InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair.dMajorana,
    map_add, map_sub, map_mul, h_eps n, h_iota n]

/--
The transported CAR pair satisfies the local CAR laws in every finite-stage
image inside the explicit target ring.
-/
theorem exteriorCARPair_limit_image_car
    (P : ∀ n : ℕ, ExteriorCARPair (A n))
    (h_eps : ∀ n : ℕ, φ n (P n).eps = (P (Nat.succ n)).eps)
    (h_iota : ∀ n : ℕ, φ n (P n).iota = (P (Nat.succ n)).iota) :
    ∀ n : ℕ,
      ι n ((P n).eps) * ι n ((P n).eps) = 0 ∧
      ι n ((P n).iota) * ι n ((P n).iota) = 0 ∧
      anticomm (ι n ((P n).eps)) (ι n ((P n).iota)) = 1 := by
  intro n
  have h :=
    limit_image_inductive_susy_closure
      (A := A) (L := L) φ ι
      (Q := fun n => (P n).eps)
      (R := fun n => (P n).iota)
      (H := fun n => (1 : A n))
      (Z := fun n => (0 : A n))
      (hQ0 := (P 0).eps_sq_zero)
      (hR0 := (P 0).iota_sq_zero)
      (hclosure0 := by
        simpa [InfoGeometry.Arithmetic.PrimeMajoranaCAR.anticomm] using
          (P 0).eps_iota_add_iota_eps)
      (hZQ0 := by simp)
      (hZR0 := by simp)
      (hQstep := by
        intro n
        simpa using (h_eps n).symm)
      (hRstep := by
        intro n
        simpa using (h_iota n).symm)
      (hHstep := by
        intro n
        simp)
      (hZstep := by
        intro n
        simp)
      n
  rcases h with ⟨hQ, hR, hQR, _, _, _⟩
  exact ⟨hQ, hR, by simpa using hQR⟩

/-- The compatible cone reads back the transported `c = ε + ι` Majorana at stage zero. -/
theorem exteriorCARPair_cMajorana_limit_image
    (P : ∀ n : ℕ, ExteriorCARPair (A n))
    (h_eps : ∀ n : ℕ, φ n (P n).eps = (P (Nat.succ n)).eps)
    (h_iota : ∀ n : ℕ, φ n (P n).iota = (P (Nat.succ n)).iota)
    (hcone : CompatibleCone φ ι) :
    ∀ n : ℕ,
      ι n ((P n).cMajorana) = ι 0 ((P 0).cMajorana) := by
  intro n
  have hstep : ∀ n : ℕ, φ n ((P n).cMajorana) = (P (Nat.succ n)).cMajorana := by
    intro n
    exact exteriorCARPair_cMajorana_step A φ P h_eps h_iota n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        ι (n + 1) ((P (n + 1)).cMajorana)
            = ι (n + 1) (φ n ((P n).cMajorana)) := by
                rw [hstep n]
        _ = ι n ((P n).cMajorana) := hcone n ((P n).cMajorana)
        _ = ι 0 ((P 0).cMajorana) := ih

/-- The compatible cone reads back the transported `d = ε - ι` Majorana at stage zero. -/
theorem exteriorCARPair_dMajorana_limit_image
    (P : ∀ n : ℕ, ExteriorCARPair (A n))
    (h_eps : ∀ n : ℕ, φ n (P n).eps = (P (Nat.succ n)).eps)
    (h_iota : ∀ n : ℕ, φ n (P n).iota = (P (Nat.succ n)).iota)
    (hcone : CompatibleCone φ ι) :
    ∀ n : ℕ,
      ι n ((P n).dMajorana) = ι 0 ((P 0).dMajorana) := by
  intro n
  have hstep : ∀ n : ℕ, φ n ((P n).dMajorana) = (P (Nat.succ n)).dMajorana := by
    intro n
    exact exteriorCARPair_dMajorana_step A φ P h_eps h_iota n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        ι (n + 1) ((P (n + 1)).dMajorana)
            = ι (n + 1) (φ n ((P n).dMajorana)) := by
                rw [hstep n]
        _ = ι n ((P n).dMajorana) := hcone n ((P n).dMajorana)
        _ = ι 0 ((P 0).dMajorana) := ih

/-- The compatible cone reads back the transported number operator at stage zero. -/
theorem exteriorCARPair_numberOp_limit_image
    (P : ∀ n : ℕ, ExteriorCARPair (A n))
    (h_eps : ∀ n : ℕ, φ n (P n).eps = (P (Nat.succ n)).eps)
    (h_iota : ∀ n : ℕ, φ n (P n).iota = (P (Nat.succ n)).iota)
    (hcone : CompatibleCone φ ι) :
    ∀ n : ℕ,
      ι n ((P n).numberOp) = ι 0 ((P 0).numberOp) := by
  intro n
  have hstep : ∀ n : ℕ, φ n ((P n).numberOp) = (P (Nat.succ n)).numberOp := by
    intro n
    exact exteriorCARPair_numberOp_step A φ P h_eps h_iota n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        ι (n + 1) ((P (n + 1)).numberOp)
            = ι (n + 1) (φ n ((P n).numberOp)) := by
                rw [hstep n]
        _ = ι n ((P n).numberOp) := hcone n ((P n).numberOp)
        _ = ι 0 ((P 0).numberOp) := ih

/-- The compatible cone reads back the transported parity operator at stage zero. -/
theorem exteriorCARPair_parityOp_limit_image
    (P : ∀ n : ℕ, ExteriorCARPair (A n))
    (h_eps : ∀ n : ℕ, φ n (P n).eps = (P (Nat.succ n)).eps)
    (h_iota : ∀ n : ℕ, φ n (P n).iota = (P (Nat.succ n)).iota)
    (hcone : CompatibleCone φ ι) :
    ∀ n : ℕ,
      ι n ((P n).parityOp) = ι 0 ((P 0).parityOp) := by
  intro n
  have hstep : ∀ n : ℕ, φ n ((P n).parityOp) = (P (Nat.succ n)).parityOp := by
    intro n
    simp [InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair.parityOp,
      InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair.cMajorana,
      InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair.dMajorana,
      map_add, map_sub, map_mul, h_eps n, h_iota n]
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        ι (n + 1) ((P (n + 1)).parityOp)
            = ι (n + 1) (φ n ((P n).parityOp)) := by
                rw [hstep n]
        _ = ι n ((P n).parityOp) := hcone n ((P n).parityOp)
        _ = ι 0 ((P 0).parityOp) := ih

/-- The image of the transported number operator remains idempotent at every stage. -/
theorem exteriorCARPair_limit_image_numberOp_idem
    (P : ∀ n : ℕ, ExteriorCARPair (A n)) :
    ∀ n : ℕ,
      ι n ((P n).numberOp) * ι n ((P n).numberOp) = ι n ((P n).numberOp) := by
  intro n
  simpa using congrArg (ι n) ((P n).numberOp_idem)

/--
The image of the transported parity operator satisfies `Π = 1 - 2N` at every stage.
-/
theorem exteriorCARPair_limit_image_parityOp_eq_one_sub_two_numberOp
    (P : ∀ n : ℕ, ExteriorCARPair (A n)) :
    ∀ n : ℕ,
      ι n ((P n).parityOp) = 1 - (2 : L) * ι n ((P n).numberOp) := by
  intro n
  have h2 : ι n (2 : A n) = (2 : L) := by
    simpa using (map_natCast (ι n) 2)
  calc
    ι n ((P n).parityOp) = ι n (1 - (2 : A n) * (P n).numberOp) := by
      simpa using congrArg (ι n) ((P n).parityOp_eq_one_sub_two_numberOp)
    _ = 1 - ι n (2 : A n) * ι n ((P n).numberOp) := by
      simp
    _ = 1 - (2 : L) * ι n ((P n).numberOp) := by
      rw [h2]
/--
Finite split-Majorana laws hold in every finite-stage image in the target ring.

This is an image-local algebraic statement: it proves the involution and
anticommutation identities for the explicit images `ι n`, not for arbitrary
operators of `L`.
-/
theorem exteriorCARPair_limit_image_majorana_laws
    (P : ∀ n : ℕ, ExteriorCARPair (A n)) :
    ∀ n : ℕ,
      ι n ((P n).cMajorana) * ι n ((P n).cMajorana) = 1 ∧
      ι n ((P n).dMajorana) * ι n ((P n).dMajorana) = -1 ∧
      ι n ((P n).cMajorana) * ι n ((P n).dMajorana) +
          ι n ((P n).dMajorana) * ι n ((P n).cMajorana) = 0 ∧
      ι n ((P n).parityOp) * ι n ((P n).parityOp) = 1 := by
  intro n
  exact
    ⟨by simpa using congrArg (ι n) ((P n).cMajorana_sq),
      by simpa using congrArg (ι n) ((P n).dMajorana_sq),
      by simpa using congrArg (ι n) ((P n).cMajorana_dMajorana_anticomm_zero),
      by simpa using congrArg (ι n) ((P n).parityOp_sq)⟩

end InfoGeometry.Arithmetic.PrimeMajoranaInfiniteCAR
