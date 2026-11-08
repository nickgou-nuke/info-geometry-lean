import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.FiniteStageInvariantTransport

Concrete finite-stage invariant transport lemmas.

If a bonding map between finite operator stages is an algebra homomorphism, then
the defining local identities are transported exactly:

* square-zero / nilpotency;
* idempotency;
* anticommutator closure;
* commutator closure;
* projector decompositions;
* central-lane commutation on the image.

No wrappers.
No placeholder proofs.
No inductive-limit claim.
-/

namespace InfoGeometry.Canonical.FiniteStageInvariantTransport

section RingStage

variable {𝕜 A B : Type*}
variable [CommSemiring 𝕜]
variable [Ring A] [Ring B]
variable [Algebra 𝕜 A] [Algebra 𝕜 B]

/--
Square-zero elements are preserved by an algebra homomorphism.

This is the transport lemma for odd nilpotent transitions:
`Q² = 0 ⟹ f(Q)² = 0`.
-/
theorem algHom_map_square_zero
    (f : A →ₐ[𝕜] B)
    {Q : A}
    (hQ : Q * Q = 0) :
    f Q * f Q = 0 := by
  rw [← map_mul, hQ, map_zero]

/--
Idempotents are preserved by an algebra homomorphism.

This transports local projectors:
`P² = P ⟹ f(P)² = f(P)`.
-/
theorem algHom_map_idempotent
    (f : A →ₐ[𝕜] B)
    {P : A}
    (hP : P * P = P) :
    f P * f P = f P := by
  rw [← map_mul, hP]

/--
Zero anticommutators are preserved by an algebra homomorphism.

This transports odd-odd closure:
`Q₁Q₂ + Q₂Q₁ = 0 ⟹ f(Q₁)f(Q₂)+f(Q₂)f(Q₁)=0`.
-/
theorem algHom_map_anticomm_zero
    (f : A →ₐ[𝕜] B)
    {Q₁ Q₂ : A}
    (hQ : Q₁ * Q₂ + Q₂ * Q₁ = 0) :
    f Q₁ * f Q₂ + f Q₂ * f Q₁ = 0 := by
  rw [← map_mul, ← map_mul, ← map_add, hQ, map_zero]

/--
Anticommutator closure is preserved by an algebra homomorphism.

If `{Q₁,Q₂}=H` in the source stage, then `{f(Q₁),f(Q₂)}=f(H)` in the
target stage.
-/
theorem algHom_map_anticomm_eq
    (f : A →ₐ[𝕜] B)
    {Q₁ Q₂ H : A}
    (hQ : Q₁ * Q₂ + Q₂ * Q₁ = H) :
    f Q₁ * f Q₂ + f Q₂ * f Q₁ = f H := by
  rw [← map_mul, ← map_mul, ← map_add, hQ]

/--
Commutator closure is preserved by an algebra homomorphism.

If `[X,Y]=Z` in the source stage, then `[f(X),f(Y)]=f(Z)` in the target stage.
-/
theorem algHom_map_commutator_eq
    (f : A →ₐ[𝕜] B)
    {X Y Z : A}
    (hXY : X * Y - Y * X = Z) :
    f X * f Y - f Y * f X = f Z := by
  rw [← map_mul, ← map_mul, ← map_sub, hXY]

/--
Zero commutators are preserved by an algebra homomorphism.

This is the commuting-sector transport lemma.
-/
theorem algHom_map_commutator_zero
    (f : A →ₐ[𝕜] B)
    {X Y : A}
    (hXY : X * Y - Y * X = 0) :
    f X * f Y - f Y * f X = 0 := by
  rw [← map_mul, ← map_mul, ← map_sub, hXY, map_zero]

/--
A central element remains central on the image of the bonding map.

This is the correct finite-stage form of central-lane transport:
`C` commutes with every source element, hence `f(C)` commutes with every
transported source element.
-/
theorem algHom_map_central_on_image
    (f : A →ₐ[𝕜] B)
    {C : A}
    (hC : ∀ X : A, C * X = X * C)
    (X : A) :
    f C * f X = f X * f C := by
  rw [← map_mul, ← map_mul, hC X]

/--
Orthogonal projectors remain orthogonal after transport.
-/
theorem algHom_map_projector_orthogonal
    (f : A →ₐ[𝕜] B)
    {P Q : A}
    (hPQ : P * Q = 0) :
    f P * f Q = 0 := by
  rw [← map_mul, hPQ, map_zero]

/--
A two-projector decomposition of the identity is preserved.

This transports the parity/projector split:
`P₊ + P₋ = 1`.
-/
theorem algHom_map_projector_sum_one
    (f : A →ₐ[𝕜] B)
    {Pplus Pminus : A}
    (hSum : Pplus + Pminus = 1) :
    f Pplus + f Pminus = 1 := by
  rw [← map_add, hSum, map_one]

end RingStage

section Reflection

variable {𝕜 A B : Type*}
variable [CommSemiring 𝕜]
variable [Ring A] [Ring B]
variable [Algebra 𝕜 A] [Algebra 𝕜 B]

/--
Injective bonding maps reflect square-zero identities.

This is useful for direct-limit embeddings: if the transported operator squares
to zero and the bonding map is injective, then the source operator was already
square-zero.
-/
theorem algHom_reflect_square_zero_of_injective
    (f : A →ₐ[𝕜] B)
    (hf : Function.Injective f)
    {Q : A}
    (hQ : f Q * f Q = 0) :
    Q * Q = 0 := by
  apply hf
  rw [map_mul, map_zero]
  exact hQ

/--
Injective bonding maps reflect idempotency.
-/
theorem algHom_reflect_idempotent_of_injective
    (f : A →ₐ[𝕜] B)
    (hf : Function.Injective f)
    {P : A}
    (hP : f P * f P = f P) :
    P * P = P := by
  apply hf
  rw [map_mul]
  exact hP

/--
Injective bonding maps reflect zero anticommutators.
-/
theorem algHom_reflect_anticomm_zero_of_injective
    (f : A →ₐ[𝕜] B)
    (hf : Function.Injective f)
    {Q₁ Q₂ : A}
    (hQ : f Q₁ * f Q₂ + f Q₂ * f Q₁ = 0) :
    Q₁ * Q₂ + Q₂ * Q₁ = 0 := by
  apply hf
  rw [map_add, map_mul, map_mul, map_zero]
  exact hQ

/--
Injective bonding maps reflect commutator identities.
-/
theorem algHom_reflect_commutator_eq_of_injective
    (f : A →ₐ[𝕜] B)
    (hf : Function.Injective f)
    {X Y Z : A}
    (hXY : f X * f Y - f Y * f X = f Z) :
    X * Y - Y * X = Z := by
  apply hf
  rw [map_sub, map_mul, map_mul]
  exact hXY

end Reflection

end InfoGeometry.Canonical.FiniteStageInvariantTransport
