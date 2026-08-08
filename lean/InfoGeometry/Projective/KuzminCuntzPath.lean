import Mathlib.Tactic
import InfoGeometry.Algebra.QCCRKuzmin
import InfoGeometry.Algebra.CuntzToeplitzStarHom

/-!
# Kuzmin q-CCR → Cuntz–Toeplitz Transmutation Socket

This file packages the algebraic side of Alexey Kuzmin's `q`-CCR corridor as a
Lean-readable socket.  It provides:

* a local `q`-CCR presentation structure over a `CommRing` with `StarRing`;
* endpoint extraction lemmas for CAR (`q=-1`) and CCR (`q=1`);
* an explicit Toeplitz endpoint (`q=0`) readout;
* a transmutation socket that assumes (as a property) a star-ring equivalence to
  the algebraic Cuntz–Toeplitz algebra.

No full C*-isomorphism theorem is proved in this file; those analytical claims are
kept as an explicit premise via the `toCuntzToeplitz` field.
-/

namespace InfoGeometry.Projective.KuzminCuntzPath

open InfoGeometry.Algebra.QCCR.Kuzmin
open InfoGeometry.Algebra.CuntzTensorQuotient

/--
The local finite `q`-CCR datum (n=2) in a commutative star ring.
-/
structure QCCRSeed (R : Type*) [CommRing R] [StarRing R] where
  q : R
  annihilation : Fin 2 → R
  creation : Fin 2 → R
  hstar : ∀ i, star (annihilation i) = creation i
  hrel : ∀ i j,
    creation i * annihilation j = (if i = j then 1 else 0) + q * (annihilation j * creation i)

/--
A conservative transmutation socket for Kuzmin's corridor.

The `toCuntzToeplitz` field is intentionally explicit and property-only: it
models the claimed algebraic bridge without asserting an analytic construction.
-/
structure QCCRToCuntzSocket (R : Type*) [CommRing R] [StarRing R] where
  seed : QCCRSeed R
  toCuntzToeplitz : R ≃⋆+* CuntzToeplitzAlg 2

/--
From the seed assumptions at `q = -1`, the CAR anticommutation channel reads as
expected:

`a_i^* a_j + a_j a_i^* = δ_{ij}`.
-/
theorem seed_car_from_minus_one
    {R : Type*} [CommRing R] [StarRing R]
    (H : QCCRSeed R)
    (hq : H.q = (-1 : R))
    (i j : Fin 2) :
    H.creation i * H.annihilation j + H.annihilation j * H.creation i =
      (if i = j then 1 else 0) := by
  have hrel : ∀ i j : Fin 2,
      H.creation i * H.annihilation j =
        (if i = j then 1 else 0) + (-1 : R) * (H.annihilation j * H.creation i) := by
    intro a b
    simpa [hq] using H.hrel a b
  exact finite_car_anticommutation (a := H.annihilation) (astar := H.creation)
    H.hstar hrel i j

/--
From the seed assumptions at `q = 1`, the CCR commutator channel reads as
expected:

`a_i^* a_j - a_j a_i^* = δ_{ij}`.
-/
theorem seed_ccr_from_plus_one
    {R : Type*} [CommRing R] [StarRing R]
    (H : QCCRSeed R)
    (hq : H.q = (1 : R))
    (i j : Fin 2) :
    H.creation i * H.annihilation j - H.annihilation j * H.creation i =
      (if i = j then 1 else 0) := by
  have hrel : ∀ i j : Fin 2,
      H.creation i * H.annihilation j =
        (if i = j then 1 else 0) + (1 : R) * (H.annihilation j * H.creation i) := by
    intro a b
    simpa [hq] using H.hrel a b
  exact finite_ccr_commutation (a := H.annihilation) (astar := H.creation)
    H.hstar hrel i j

/--
At `q = 0`, the seed data satisfy the Cuntz–Toeplitz orthogonality relation
`a_i^* a_j = δ_{ij}`.
-/
theorem seed_toeplitz_limit
    {R : Type*} [CommRing R] [StarRing R]
    (H : QCCRSeed R)
    (hq : H.q = (0 : R))
    (i j : Fin 2) :
    H.creation i * H.annihilation j =
      (if i = j then 1 else 0) := by
  simpa [hq] using H.hrel i j

/--
Transported Toeplitz orthogonality under an explicit isomorphism to
`CuntzToeplitzAlg 2`.
-/
theorem transported_toeplitz_orthogonality
    {R : Type*} [CommRing R] [StarRing R]
    (H : QCCRToCuntzSocket R)
    (hq : H.seed.q = (0 : R))
    (i j : Fin 2) :
    H.toCuntzToeplitz (H.seed.creation i) * H.toCuntzToeplitz (H.seed.annihilation j) =
      (if i = j then 1 else 0) := by
  have h0 := seed_toeplitz_limit (H := H.seed) hq i j
  simpa using congrArg H.toCuntzToeplitz h0

/--
Conservative CAR readout under an assumed transmutation socket.
-/
theorem transmutation_car_packet
    {R : Type*} [CommRing R] [StarRing R]
    (H : QCCRToCuntzSocket R)
    (hcar : H.seed.q = (-1 : R))
    (i j : Fin 2) :
    H.seed.creation i * H.seed.annihilation j + H.seed.annihilation j * H.seed.creation i =
      (if i = j then 1 else 0) := by
  exact seed_car_from_minus_one (H := H.seed) hcar i j

/--
A packet-style consequence statement mirroring the requested physical interface.
-/
structure KuzminCuntzPathPacket (R : Type*) [CommRing R] [StarRing R] where
  q : R
  seed : QCCRSeed R
  toCuntzToeplitz : R ≃⋆+* CuntzToeplitzAlg 2
  q_norm : q = seed.q

/--
Conservative specialization: a path packet is present exactly as an explicit
property (no hidden completion).
-/
theorem path_packet_is_explicit
    {R : Type*} [CommRing R] [StarRing R]
    (P : KuzminCuntzPathPacket R) :
    P.seed.q = P.q := by
  simp [P.q_norm]

end InfoGeometry.Projective.KuzminCuntzPath
