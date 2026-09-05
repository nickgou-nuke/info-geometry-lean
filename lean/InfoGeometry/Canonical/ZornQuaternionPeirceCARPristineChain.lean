import InfoGeometry.Canonical.ZornQuaternionPeirceCAR

/-!
# Pristine Zorn quaternion/Peirce reconstruction chain

This capstone records only theorem-supported algebra:

1. complementary orthogonal diagonal idempotents;
2. upper/lower nilpotent Peirce corners;
3. their binary contraction anticommutator;
4. negative and split Clifford polarization identities;
5. associativity on the quaternionic paravector slice;
6. a convention-correct quaternion-unit multiplication table;
7. a concrete associator witness outside that slice.

No physical vacuum, particle, superconducting, `Pin`-group, Fock-space, or
full CAR-algebra semantics is inferred from these identities.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornQuaternionPeirceCARPristineChain

open InfoGeometry.Canonical.ZornVectorMatrixExplicit
open InfoGeometry.Canonical.ZornQuaternionPeirceCAR

/-- The two diagonal idempotents and the two Peirce roots form the exact
idempotent/nilpotent skeleton of the reconstruction. -/
theorem pristine_peirce_skeleton (u v : Vec3) :
    zornMul leftIdempotent leftIdempotent = leftIdempotent ∧
      zornMul rightIdempotent rightIdempotent = rightIdempotent ∧
      zornMul leftIdempotent rightIdempotent = 0 ∧
      zornMul rightIdempotent leftIdempotent = 0 ∧
      leftIdempotent + rightIdempotent = zornOne ∧
      zornMul (upperRoot u) (upperRoot u) = 0 ∧
      zornMul (lowerRoot v) (lowerRoot v) = 0 ∧
      zornMul leftIdempotent (upperRoot u) = upperRoot u ∧
      zornMul (upperRoot u) rightIdempotent = upperRoot u ∧
      zornMul rightIdempotent (lowerRoot v) = lowerRoot v ∧
      zornMul (lowerRoot v) leftIdempotent = lowerRoot v := by
  exact ⟨leftIdempotent_sq, rightIdempotent_sq,
    leftIdempotent_mul_rightIdempotent,
    rightIdempotent_mul_leftIdempotent,
    leftIdempotent_add_rightIdempotent,
    upperRoot_sq_zero u, lowerRoot_sq_zero v,
    leftIdempotent_mul_upperRoot u,
    upperRoot_mul_rightIdempotent u,
    rightIdempotent_mul_lowerRoot v,
    lowerRoot_mul_leftIdempotent v⟩

/-- Exact binary contraction and Clifford polarization packet. -/
theorem pristine_binary_clifford_packet (u v : Vec3) :
    zornMul (upperRoot u) (lowerRoot v) =
        dot3 u v • leftIdempotent ∧
      zornMul (lowerRoot v) (upperRoot u) =
        dot3 u v • rightIdempotent ∧
      zornMul (upperRoot u) (lowerRoot v) +
          zornMul (lowerRoot v) (upperRoot u) =
        dot3 u v • zornOne ∧
      zornMul (negativeCliffordGenerator u) (negativeCliffordGenerator v) +
          zornMul (negativeCliffordGenerator v) (negativeCliffordGenerator u) =
        (-2 * dot3 u v) • zornOne ∧
      zornMul (splitCliffordGenerator u) (splitCliffordGenerator v) +
          zornMul (splitCliffordGenerator v) (splitCliffordGenerator u) =
        (2 * dot3 u v) • zornOne ∧
      zornMul (negativeCliffordGenerator u) (splitCliffordGenerator v) +
          zornMul (splitCliffordGenerator v) (negativeCliffordGenerator u) = 0 := by
  exact ⟨upperRoot_mul_lowerRoot u v,
    lowerRoot_mul_upperRoot u v,
    peirce_CAR u v,
    negativeCliffordGenerator_anticommutator u v,
    splitCliffordGenerator_anticommutator u v,
    negative_split_anticommutator_zero u v⟩

/-- The two nilpotent roots are exactly the half-sum and half-difference of
the positive- and negative-square Clifford frames. -/
theorem pristine_root_reconstruction (u : Vec3) :
    splitCliffordGenerator u = upperRoot u + lowerRoot u ∧
      negativeCliffordGenerator u = upperRoot u - lowerRoot u ∧
      upperRoot u =
        (1 / 2 : ℝ) •
          (splitCliffordGenerator u + negativeCliffordGenerator u) ∧
      lowerRoot u =
        (1 / 2 : ℝ) •
          (splitCliffordGenerator u - negativeCliffordGenerator u) := by
  exact ⟨splitCliffordGenerator_eq_upper_add_lower u,
    negativeCliffordGenerator_eq_upper_sub_lower u,
    upperRoot_eq_half_split_add_negative u,
    lowerRoot_eq_half_split_sub_negative u⟩

/-- Associativity is valid on the quaternionic slice and fails on the ambient
Zorn carrier. These facts must not be conflated. -/
theorem pristine_associativity_boundary
    (a b c : ℝ) (u v w : Vec3) :
    zornMul (zornMul (paravectorZorn a u) (paravectorZorn b v))
        (paravectorZorn c w) =
      zornMul (paravectorZorn a u)
        (zornMul (paravectorZorn b v) (paravectorZorn c w)) ∧
      zornMul (zornMul (upperRoot e1) (upperRoot e2)) (upperRoot e3) ≠
        zornMul (upperRoot e1)
          (zornMul (upperRoot e2) (upperRoot e3)) := by
  exact ⟨paravectorZorn_assoc a b c u v w,
    zornMul_not_associative_witness⟩

/-- Convention-correct quaternionic multiplication together with ambient
nonassociativity. -/
theorem pristine_quaternion_table_and_ambient_boundary :
    (zornMul qI qI = qNegOne ∧
      zornMul qJ qJ = qNegOne ∧
      zornMul qK qK = qNegOne ∧
      zornMul qI qJ = qK ∧
      zornMul qJ qK = qI ∧
      zornMul qK qI = qJ ∧
      zornMul qJ qI = -qK ∧
      zornMul qK qJ = -qI ∧
      zornMul qI qK = -qJ) ∧
    zornMul (zornMul (upperRoot e1) (upperRoot e2)) (upperRoot e3) ≠
      zornMul (upperRoot e1)
        (zornMul (upperRoot e2) (upperRoot e3)) := by
  exact ⟨quaternion_table_packet, zornMul_not_associative_witness⟩

/-- Complete theorem-safe reconstruction packet. -/
theorem zorn_quaternion_peirce_car_pristine_chain
    (a b c : ℝ) (u v w : Vec3) :
    (zornMul leftIdempotent leftIdempotent = leftIdempotent ∧
      zornMul rightIdempotent rightIdempotent = rightIdempotent ∧
      leftIdempotent + rightIdempotent = zornOne) ∧
    (zornMul (upperRoot u) (upperRoot u) = 0 ∧
      zornMul (lowerRoot v) (lowerRoot v) = 0 ∧
      zornMul (upperRoot u) (lowerRoot v) +
          zornMul (lowerRoot v) (upperRoot u) =
        dot3 u v • zornOne) ∧
    (zornMul (negativeCliffordGenerator u) (negativeCliffordGenerator v) +
          zornMul (negativeCliffordGenerator v) (negativeCliffordGenerator u) =
        (-2 * dot3 u v) • zornOne ∧
      zornMul (splitCliffordGenerator u) (splitCliffordGenerator v) +
          zornMul (splitCliffordGenerator v) (splitCliffordGenerator u) =
        (2 * dot3 u v) • zornOne) ∧
    (zornMul (zornMul (paravectorZorn a u) (paravectorZorn b v))
          (paravectorZorn c w) =
        zornMul (paravectorZorn a u)
          (zornMul (paravectorZorn b v) (paravectorZorn c w))) ∧
    zornMul (zornMul (upperRoot e1) (upperRoot e2)) (upperRoot e3) ≠
      zornMul (upperRoot e1)
        (zornMul (upperRoot e2) (upperRoot e3)) := by
  exact ⟨⟨leftIdempotent_sq, rightIdempotent_sq,
      leftIdempotent_add_rightIdempotent⟩,
    ⟨upperRoot_sq_zero u, lowerRoot_sq_zero v, peirce_CAR u v⟩,
    ⟨negativeCliffordGenerator_anticommutator u v,
      splitCliffordGenerator_anticommutator u v⟩,
    paravectorZorn_assoc a b c u v w,
    zornMul_not_associative_witness⟩

end InfoGeometry.Canonical.ZornQuaternionPeirceCARPristineChain
