import InfoGeometry.Algebra.FiniteInductiveSUSY
import InfoGeometry.External.Auto.FractalKleinSUSYFramework

/-!
# Infinite target images of a finite inductive SUSY chain

This is the refined finite-to-infinite step for the finite inductive SUSY
owner slice.

No topological completion, colimit universal property, or analytic convergence
is asserted.  The infinite target is an explicit ring `L`, and each finite
stage maps into it by a ring homomorphism.  The theorem proves only the
algebraic image laws that follow from the finite chain and those maps.

This is the same discipline as the external Virasoro lane: infinite objects are
reached through explicit mode/cone maps, and every closure law is checked on
finite algebraic data before being transported.
-/

noncomputable section

namespace InfoGeometry.Algebra.InfiniteInductiveSUSY

open InfoGeometry.Algebra.FiniteInductiveSUSY

variable {A : ℕ → Type*} [∀ n : ℕ, Ring (A n)]
variable {L : Type*} [Ring L]

/--
A compatible algebraic cone from the finite inductive system into an infinite
target ring.

This is a plain predicate, not a packet: it says the two ways of sending a
stage-`n` element into `L` agree.
-/
def CompatibleCone
    (φ : ∀ n : ℕ, A n →+* A (Nat.succ n))
    (ι : ∀ n : ℕ, A n →+* L) : Prop :=
  ∀ (n : ℕ) (x : A n), ι (Nat.succ n) (φ n x) = ι n x

/--
If the stage data are transported by the bonding maps, their images in a
compatible infinite target are independent of one finite step.
-/
theorem compatibleCone_image_step
    (φ : ∀ n : ℕ, A n →+* A (Nat.succ n))
    (ι : ∀ n : ℕ, A n →+* L)
    (hcone : CompatibleCone φ ι)
    (Q : ∀ n : ℕ, A n)
    (hQstep : ∀ n : ℕ, Q (Nat.succ n) = φ n (Q n))
    (n : ℕ) :
    ι (Nat.succ n) (Q (Nat.succ n)) = ι n (Q n) := by
  rw [hQstep n]
  exact hcone n (Q n)

/--
Image nilpotency in an infinite target.

For every finite stage, the image of the transported odd charge remains
square-zero in the target ring.
-/
theorem limit_image_nilpotent_chain
    (φ : ∀ n : ℕ, A n →+* A (Nat.succ n))
    (ι : ∀ n : ℕ, A n →+* L)
    (Q : ∀ n : ℕ, A n)
    (hQ0 : Q 0 * Q 0 = 0)
    (hQstep : ∀ n : ℕ, Q (Nat.succ n) = φ n (Q n)) :
    ∀ n : ℕ, ι n (Q n) * ι n (Q n) = 0 := by
  intro n
  have hQn : Q n * Q n = 0 :=
    nilpotent_chain φ Q hQ0 hQstep n
  have h := congrArg (ι n) hQn
  simpa using h

/--
Image odd-odd closure in an infinite target.

The central-charge closure relation is first proved at finite stage `n`, then
transported by the explicit ring homomorphism `ι n`.
-/
theorem limit_image_superclosure_chain
    (φ : ∀ n : ℕ, A n →+* A (Nat.succ n))
    (ι : ∀ n : ℕ, A n →+* L)
    (Q R H Z : ∀ n : ℕ, A n)
    (hclosure0 : anticomm (Q 0) (R 0) = H 0 + Z 0)
    (hQstep : ∀ n : ℕ, Q (Nat.succ n) = φ n (Q n))
    (hRstep : ∀ n : ℕ, R (Nat.succ n) = φ n (R n))
    (hHstep : ∀ n : ℕ, H (Nat.succ n) = φ n (H n))
    (hZstep : ∀ n : ℕ, Z (Nat.succ n) = φ n (Z n)) :
    ∀ n : ℕ,
      anticomm (ι n (Q n)) (ι n (R n)) = ι n (H n) + ι n (Z n) := by
  intro n
  have hcln : anticomm (Q n) (R n) = H n + Z n :=
    superclosure_chain φ Q R H Z hclosure0 hQstep hRstep hHstep hZstep n
  exact map_superclosure (ι n) (Q n) (R n) (H n) (Z n) hcln

/--
Image centrality against the two transported odd charges in an infinite target.
-/
theorem limit_image_central_commutes_with_two_charges_chain
    (φ : ∀ n : ℕ, A n →+* A (Nat.succ n))
    (ι : ∀ n : ℕ, A n →+* L)
    (Q R Z : ∀ n : ℕ, A n)
    (hZQ0 : Z 0 * Q 0 = Q 0 * Z 0)
    (hZR0 : Z 0 * R 0 = R 0 * Z 0)
    (hQstep : ∀ n : ℕ, Q (Nat.succ n) = φ n (Q n))
    (hRstep : ∀ n : ℕ, R (Nat.succ n) = φ n (R n))
    (hZstep : ∀ n : ℕ, Z (Nat.succ n) = φ n (Z n)) :
    ∀ n : ℕ,
      ι n (Z n) * ι n (Q n) = ι n (Q n) * ι n (Z n) ∧
      ι n (Z n) * ι n (R n) = ι n (R n) * ι n (Z n) := by
  intro n
  have hcentral :
      Z n * Q n = Q n * Z n ∧ Z n * R n = R n * Z n :=
    central_commutes_with_two_charges_chain
      φ Q R Z hZQ0 hZR0 hQstep hRstep hZstep n
  constructor
  · have h := congrArg (ι n) hcentral.1
    simpa using h
  · have h := congrArg (ι n) hcentral.2
    simpa using h

/--
Image Dirac-square closure in an infinite target.

This is the honest algebraic limit statement: for every finite stage seen
inside `L`, the image of the total odd charge has square equal to the image of
the Hamiltonian-plus-central lane.
-/
theorem limit_image_dirac_square_closure_chain
    (φ : ∀ n : ℕ, A n →+* A (Nat.succ n))
    (ι : ∀ n : ℕ, A n →+* L)
    (Q R H Z : ∀ n : ℕ, A n)
    (hQ0 : Q 0 * Q 0 = 0)
    (hR0 : R 0 * R 0 = 0)
    (hclosure0 : anticomm (Q 0) (R 0) = H 0 + Z 0)
    (hQstep : ∀ n : ℕ, Q (Nat.succ n) = φ n (Q n))
    (hRstep : ∀ n : ℕ, R (Nat.succ n) = φ n (R n))
    (hHstep : ∀ n : ℕ, H (Nat.succ n) = φ n (H n))
    (hZstep : ∀ n : ℕ, Z (Nat.succ n) = φ n (Z n)) :
    ∀ n : ℕ,
      ι n (Q n + R n) * ι n (Q n + R n) = ι n (H n) + ι n (Z n) := by
  intro n
  have hsq : (Q n + R n) * (Q n + R n) = H n + Z n :=
    dirac_square_closure_chain
      φ Q R H Z hQ0 hR0 hclosure0 hQstep hRstep hHstep hZstep n
  have h := congrArg (ι n) hsq
  simpa using h

/--
The full finite-to-infinite image invariant.

The output packages the direct conclusions as a conjunction of propositions,
not as stored theorem fields.  The statement remains image-local: it does not
claim that arbitrary target elements are generated by the finite images.
-/
theorem limit_image_inductive_susy_closure
    (φ : ∀ n : ℕ, A n →+* A (Nat.succ n))
    (ι : ∀ n : ℕ, A n →+* L)
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
  exact
    ⟨limit_image_nilpotent_chain φ ι Q hQ0 hQstep n,
      limit_image_nilpotent_chain φ ι R hR0 hRstep n,
      limit_image_superclosure_chain
        φ ι Q R H Z hclosure0 hQstep hRstep hHstep hZstep n,
      (limit_image_central_commutes_with_two_charges_chain
        φ ι Q R Z hZQ0 hZR0 hQstep hRstep hZstep n).1,
      (limit_image_central_commutes_with_two_charges_chain
        φ ι Q R Z hZQ0 hZR0 hQstep hRstep hZstep n).2,
      limit_image_dirac_square_closure_chain
        φ ι Q R H Z hQ0 hR0 hclosure0 hQstep hRstep hHstep hZstep n⟩

end InfoGeometry.Algebra.InfiniteInductiveSUSY
