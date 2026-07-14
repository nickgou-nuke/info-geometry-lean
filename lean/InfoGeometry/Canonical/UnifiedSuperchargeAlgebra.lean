import InfoGeometry.Quantum.SuperchargeMultiplet
import InfoGeometry.Canonical.SuperchargeTransportBridge
import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.DrazinCentralChargeBridge
import InfoGeometry.Canonical.OperatorialCentralCharge
import InfoGeometry.Canonical.KKTClosureSymmetry
import InfoGeometry.Canonical.KramersSuperchargeBridge
import InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.UnifiedSuperchargeAlgebra

open InfoGeometry.Krein
open InfoGeometry.Quantum
open InfoGeometry.Canonical
open InfoGeometry.Canonical.SuperchargeTransportBridge
open InfoGeometry.Canonical.OperatorialCentralCharge

/--
The square of a recursively extended odd supercharge.

For `Qnext = Q + R`, the new square is the old square plus the
odd--odd cross bracket plus the new square.
-/
@[rep_depth thermo]
theorem recursive_supercharge_square
    {A : Type*} [Ring A]
    (Q R : A) :
    (Q + R) * (Q + R) =
      Q * Q + (Q * R + R * Q) + R * R := by
  noncomm_ring

/--
Square class is preserved under algebra transport by a ring equivalence.

This is the algebraic "same geometry class under coordinate transport" lemma:
transport can move representatives, but does not change the square law itself.
-/
@[rep_depth thermo]
theorem square_transport_preserved
    {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B) (x : A) :
    e (x * x) = e x * e x := by
  simpa using (map_mul e x x).symm

/--
Similarity/conjugation transports squares covariantly:
`(u x u⁻¹)^2 = u (x^2) u⁻¹`.
-/
@[rep_depth thermo]
theorem conjugation_square_covariant
    {A : Type*} [Ring A]
    (u : Units A) (x : A) :
    (↑u * x * ↑u⁻¹) * (↑u * x * ↑u⁻¹)
      = ↑u * (x * x) * ↑u⁻¹ := by
  calc
    (↑u * x * ↑u⁻¹) * (↑u * x * ↑u⁻¹)
        = ↑u * x * (↑u⁻¹ * ↑u) * x * ↑u⁻¹ := by noncomm_ring
    _ = ↑u * x * 1 * x * ↑u⁻¹ := by rw [Units.inv_mul]
    _ = ↑u * (x * x) * ↑u⁻¹ := by noncomm_ring

/--
Conjugation preserves hyperbolic square law `x² = 1`.
-/
@[rep_depth thermo]
theorem conjugation_preserves_square_one
    {A : Type*} [Ring A]
    (u : Units A) (x : A)
    (hx : x * x = 1) :
    (↑u * x * ↑u⁻¹) * (↑u * x * ↑u⁻¹) = 1 := by
  calc
    (↑u * x * ↑u⁻¹) * (↑u * x * ↑u⁻¹)
        = ↑u * (x * x) * ↑u⁻¹ := conjugation_square_covariant u x
    _ = ↑u * 1 * ↑u⁻¹ := by rw [hx]
    _ = 1 := by simp

/--
Conjugation preserves elliptic square law `x² = -1`.
-/
@[rep_depth thermo]
theorem conjugation_preserves_square_neg_one
    {A : Type*} [Ring A]
    (u : Units A) (x : A)
    (hx : x * x = -(1 : A)) :
    (↑u * x * ↑u⁻¹) * (↑u * x * ↑u⁻¹) = -(1 : A) := by
  calc
    (↑u * x * ↑u⁻¹) * (↑u * x * ↑u⁻¹)
        = ↑u * (x * x) * ↑u⁻¹ := conjugation_square_covariant u x
    _ = ↑u * (-(1 : A)) * ↑u⁻¹ := by rw [hx]
    _ = -(1 : A) := by simp

@[rep_depth thermo]
theorem conjugation_preserves_square_zero_local
    {A : Type*} [Ring A]
    (u : Units A) (x : A)
    (hx : x * x = 0) :
    (↑u * x * ↑u⁻¹) * (↑u * x * ↑u⁻¹) = 0 := by
  calc
    (↑u * x * ↑u⁻¹) * (↑u * x * ↑u⁻¹)
        = ↑u * (x * x) * ↑u⁻¹ := conjugation_square_covariant u x
    _ = ↑u * 0 * ↑u⁻¹ := by rw [hx]
    _ = 0 := by simp

/--
With explicit non-degeneracy `1 ≠ -1`, conjugation cannot flip a
hyperbolic square law into an elliptic one.
-/
@[rep_depth thermo]
theorem conjugation_cannot_flip_square_one_to_neg_one
    {A : Type*} [Ring A]
    (u : Units A) (x : A)
    (hneq : (1 : A) ≠ -(1 : A))
    (hx : x * x = 1) :
    (↑u * x * ↑u⁻¹) * (↑u * x * ↑u⁻¹) ≠ -(1 : A) := by
  intro hflip
  have hone : (↑u * x * ↑u⁻¹) * (↑u * x * ↑u⁻¹) = 1 :=
    conjugation_preserves_square_one u x hx
  exact hneq (hone.symm.trans hflip)

/--
Conjugation preserves the full local square-law trichotomy:
`x² ∈ {-1, 0, 1}` is invariant under similarity.
-/
@[rep_depth thermo]
theorem conjugation_preserves_square_trichotomy
    {A : Type*} [Ring A]
    (u : Units A) (x : A) :
    ((x * x = (1 : A)) →
      (↑u * x * ↑u⁻¹) * (↑u * x * ↑u⁻¹) = (1 : A)) ∧
    ((x * x = (0 : A)) →
      (↑u * x * ↑u⁻¹) * (↑u * x * ↑u⁻¹) = (0 : A)) ∧
    ((x * x = (-(1 : A))) →
      (↑u * x * ↑u⁻¹) * (↑u * x * ↑u⁻¹) = (-(1 : A))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hx1
    exact conjugation_preserves_square_one u x hx1
  · intro hx0
    exact conjugation_preserves_square_zero_local u x hx0
  · intro hxm1
    exact conjugation_preserves_square_neg_one u x hxm1

/--
Square-class incompatibility in nondegenerate characteristic:
an element cannot satisfy both `x² = 1` and `x² = -1` when `1 ≠ -1`.
-/
@[rep_depth thermo]
theorem square_one_and_neg_one_incompatible
    {A : Type*} [Ring A]
    {x : A}
    (hneq : (1 : A) ≠ -(1 : A))
    (h1 : x * x = 1)
    (hneg1 : x * x = -(1 : A)) :
    False := by
  exact hneq (h1.symm.trans hneg1)

/--
If `1 ≠ 0`, an element cannot satisfy both `x² = 1` and `x² = 0`.
-/
@[rep_depth thermo]
theorem square_one_and_zero_incompatible
    {A : Type*} [Ring A]
    {x : A}
    (h10 : (1 : A) ≠ 0)
    (h1 : x * x = 1)
    (h0 : x * x = 0) :
    False := by
  exact h10 (h1.symm.trans h0)

/--
If `1 ≠ 0`, an element cannot satisfy both `x² = 0` and `x² = -1`.
-/
@[rep_depth thermo]
theorem square_zero_and_neg_one_incompatible
    {A : Type*} [Ring A]
    {x : A}
    (h10 : (1 : A) ≠ 0)
    (h0 : x * x = 0)
    (hneg1 : x * x = -(1 : A)) :
    False := by
  have h0eqneg1 : (0 : A) = -(1 : A) := h0.symm.trans hneg1
  have h1eq0 : (1 : A) = (0 : A) := by
    have := congrArg Neg.neg h0eqneg1
    simpa using this.symm
  exact h10 h1eq0

/--
Exclusive trichotomy at one element (under explicit nondegeneracy):
`x² = 1`, `x² = 0`, and `x² = -1` are pairwise incompatible.
-/
@[rep_depth thermo]
theorem square_class_trichotomy_exclusive
    {A : Type*} [Ring A]
    {x : A}
    (h10 : (1 : A) ≠ 0)
    (h1neg1 : (1 : A) ≠ -(1 : A)) :
    ¬ ((x * x = (1 : A)) ∧ (x * x = (0 : A))) ∧
    ¬ ((x * x = (1 : A)) ∧ (x * x = (-(1 : A)))) ∧
    ¬ ((x * x = (0 : A)) ∧ (x * x = (-(1 : A)))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact square_one_and_zero_incompatible h10 h.1 h.2
  · intro h
    exact square_one_and_neg_one_incompatible h1neg1 h.1 h.2
  · intro h
    exact square_zero_and_neg_one_incompatible h10 h.1 h.2

/--
Parabolic predicate for a local generator: square-zero.
-/
@[rep_depth thermo]
def isParabolic
    {V : Type*} [Mul V] [Zero V]
    (v : V) : Prop :=
  v * v = 0

/--
Chiral null-cone carrier with a star involution and square-zero/parabolic
equivalence surface.
-/
@[rep_depth thermo]
class ChiralCone (V : Type*) extends AddCommGroup V, Mul V, Zero V where
  starInvolution : V → V
  nilpotent_core : ∀ v : V, (v * v = 0) ↔ isParabolic v

/--
In any `ChiralCone`, square-zero implies parabolic by definition.
-/
@[rep_depth thermo]
theorem chiralCone_nilpotent_isParabolic
    {V : Type*} [ChiralCone V] {v : V}
    (hv : v * v = 0) :
    isParabolic v := by
  exact (ChiralCone.nilpotent_core v).1 hv

/--
In any `ChiralCone`, parabolic implies square-zero by definition.
-/
@[rep_depth thermo]
theorem chiralCone_isParabolic_nilpotent
    {V : Type*} [ChiralCone V] {v : V}
    (hv : isParabolic v) :
    v * v = 0 := by
  exact (ChiralCone.nilpotent_core v).2 hv

/--
Two null-cone generators with square-zero hypotheses are parabolic.
-/
@[rep_depth thermo]
theorem chiral_null_generators_parabolic
    {V : Type*} [ChiralCone V]
    {ePlus eMinus : V}
    (hPlus : ePlus * ePlus = 0)
    (hMinus : eMinus * eMinus = 0) :
    isParabolic ePlus ∧ isParabolic eMinus := by
  exact ⟨chiralCone_nilpotent_isParabolic hPlus,
    chiralCone_nilpotent_isParabolic hMinus⟩

/--
Three-way square class used in the Cayley--Klein local corridor.
-/
@[rep_depth thermo]
inductive CKSignature where
  | elliptic
  | parabolic
  | hyperbolic
  deriving DecidableEq, Repr

/--
Predicate-level encoding of the local square law over `ℂ`.
-/
@[rep_depth thermo]
def hasCKSignature (z : ℂ) (σ : CKSignature) : Prop :=
  match σ with
  | CKSignature.elliptic => z * z = -1
  | CKSignature.parabolic => z * z = 0
  | CKSignature.hyperbolic => z * z = 1

/--
Square-class action induced by one complex Wick twist.
-/
@[rep_depth thermo]
def wickCKMap : CKSignature → CKSignature
  | CKSignature.hyperbolic => CKSignature.elliptic
  | CKSignature.elliptic => CKSignature.hyperbolic
  | CKSignature.parabolic => CKSignature.parabolic

/--
The Wick square-class action is an involution.
-/
@[rep_depth thermo]
theorem wickCKMap_involutive (σ : CKSignature) :
    wickCKMap (wickCKMap σ) = σ := by
  cases σ <;> rfl

/--
Square equation `z² = 1` gives hyperbolic signature.
-/
@[rep_depth thermo]
theorem hasCKSignature_of_square_eq_one
    {z : ℂ} (h : z * z = 1) :
    hasCKSignature z CKSignature.hyperbolic := by
  simpa [hasCKSignature] using h

/--
Square equation `z² = 0` gives parabolic signature.
-/
@[rep_depth thermo]
theorem hasCKSignature_of_square_eq_zero
    {z : ℂ} (h : z * z = 0) :
    hasCKSignature z CKSignature.parabolic := by
  simpa [hasCKSignature] using h

/--
Square equation `z² = -1` gives elliptic signature.
-/
@[rep_depth thermo]
theorem hasCKSignature_of_square_eq_neg_one
    {z : ℂ} (h : z * z = -1) :
    hasCKSignature z CKSignature.elliptic := by
  simpa [hasCKSignature] using h

/--
Conjugation preserves hyperbolic square law `x² = 1` via constructive signature witness.
-/
@[rep_depth thermo]
theorem conjugation_preserves_square_one_of_witness
    (u : Units ℂ) (x : ℂ)
    (hx : hasCKSignature x CKSignature.hyperbolic) :
    (↑u * x * ↑u⁻¹) * (↑u * x * ↑u⁻¹) = 1 := by
  rw [hasCKSignature] at hx
  exact conjugation_preserves_square_one u x hx

/--
Ring-equivalence transport preserves hyperbolic class membership (`x² = 1`).
-/
@[rep_depth thermo]
theorem hasHyperbolic_transport
    {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B) (x : A) :
    (x * x = (1 : A)) ↔ (e x * e x = (1 : B)) := by
  constructor
  · intro hx
    calc
      e x * e x = e (x * x) := by symm; simpa using (map_mul e x x)
      _ = e 1 := by rw [hx]
      _ = (1 : B) := by simp
  · intro hx
    have hmap : e (x * x) = (1 : B) := by
      calc
        e (x * x) = e x * e x := by simpa using (map_mul e x x)
        _ = 1 := hx
    exact e.injective (by simpa using hmap)

/--
Ring-equivalence transport preserves parabolic class membership (`x² = 0`).
-/
@[rep_depth thermo]
theorem hasParabolic_transport
    {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B) (x : A) :
    (x * x = (0 : A)) ↔ (e x * e x = (0 : B)) := by
  constructor
  · intro hx
    calc
      e x * e x = e (x * x) := by symm; simpa using (map_mul e x x)
      _ = e 0 := by rw [hx]
      _ = (0 : B) := by simp
  · intro hx
    have hmap : e (x * x) = (0 : B) := by
      calc
        e (x * x) = e x * e x := by simpa using (map_mul e x x)
        _ = 0 := hx
    exact e.injective (by simpa using hmap)

/--
Ring-equivalence transport preserves elliptic class membership (`x² = -1`).
-/
@[rep_depth thermo]
theorem hasElliptic_transport
    {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B) (x : A) :
    (x * x = (-(1 : A))) ↔ (e x * e x = (-(1 : B))) := by
  constructor
  · intro hx
    calc
      e x * e x = e (x * x) := by symm; simpa using (map_mul e x x)
      _ = e (-(1 : A)) := by rw [hx]
      _ = (-(1 : B)) := by simp
  · intro hx
    have hmap : e (x * x) = (-(1 : B)) := by
      calc
        e (x * x) = e x * e x := by simpa using (map_mul e x x)
        _ = (-(1 : B)) := hx
    exact e.injective (by simpa using hmap)

/--
Transport cannot flip hyperbolic to parabolic class under nondegeneracy.
-/
@[rep_depth thermo]
theorem transport_hyperbolic_not_parabolic
    {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B) (x : A)
    (h10 : (1 : B) ≠ 0)
    (hx : x * x = (1 : A)) :
    e x * e x ≠ (0 : B) := by
  intro h0
  have h1 : e x * e x = (1 : B) := (hasHyperbolic_transport e x).1 hx
  exact h10 (h1.symm.trans h0)

/--
Transport cannot flip parabolic to elliptic class under nondegeneracy.
-/
@[rep_depth thermo]
theorem transport_parabolic_not_elliptic
    {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B) (x : A)
    (h10 : (1 : B) ≠ 0)
    (hx : x * x = (0 : A)) :
    e x * e x ≠ (-(1 : B)) := by
  intro hneg
  have h0 : e x * e x = (0 : B) := (hasParabolic_transport e x).1 hx
  have h0eqneg1 : (0 : B) = (-(1 : B)) := by
    calc
      (0 : B) = e x * e x := h0.symm
      _ = (-(1 : B)) := hneg
  have h0eq1 : (0 : B) = (1 : B) := by
    have : (-(0 : B)) = (-(-(1 : B))) := congrArg Neg.neg h0eqneg1
    simpa using this
  exact h10 h0eq1.symm

/--
Transport cannot flip hyperbolic to elliptic class under explicit
`1 ≠ -1` in the codomain.
-/
@[rep_depth thermo]
theorem transport_hyperbolic_not_elliptic_via_signature
    {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B) (x : A)
    (h1neg1 : (1 : B) ≠ -(1 : B))
    (hx : x * x = (1 : A)) :
    e x * e x ≠ (-(1 : B)) := by
  intro hneg
  have h1 : e x * e x = (1 : B) := (hasHyperbolic_transport e x).1 hx
  exact h1neg1 (h1.symm.trans hneg)

/--
Bundled transport no-flip corridor:
under explicit codomain nondegeneracy, ring-equivalence transport cannot send
`x² = 1` to `0` or `-1`, and cannot send `x² = 0` to `-1`.
-/
@[rep_depth thermo]
theorem transport_square_class_no_flip_bundle
    {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B) (x y : A)
    (h10 : (1 : B) ≠ 0)
    (h1neg1 : (1 : B) ≠ -(1 : B))
    (hx1 : x * x = (1 : A))
    (hy0 : y * y = (0 : A)) :
    (e x * e x ≠ (0 : B)) ∧
    (e x * e x ≠ (-(1 : B))) ∧
    (e y * e y ≠ (-(1 : B))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact transport_hyperbolic_not_parabolic e x h10 hx1
  · exact transport_hyperbolic_not_elliptic_via_signature e x h1neg1 hx1
  · exact transport_parabolic_not_elliptic e y h10 hy0

/--
Square-class signatures are disjoint on `ℂ`.
An element cannot satisfy two different `CKSignature` square laws.
-/
@[rep_depth thermo]
theorem hasCKSignature_unique
    {z : ℂ} {σ τ : CKSignature}
    (hσ : hasCKSignature z σ)
    (hτ : hasCKSignature z τ) :
    σ = τ := by
  cases σ <;> cases τ
  · rfl
  · exfalso
    have h1 : z * z = (-1 : ℂ) := by simpa [hasCKSignature] using hσ
    have h2 : z * z = (0 : ℂ) := by simpa [hasCKSignature] using hτ
    have h : (-1 : ℂ) = (0 : ℂ) := h1.symm.trans h2
    norm_num at h
  · exfalso
    have h1 : z * z = (-1 : ℂ) := by simpa [hasCKSignature] using hσ
    have h2 : z * z = (1 : ℂ) := by simpa [hasCKSignature] using hτ
    have h : (-1 : ℂ) = (1 : ℂ) := h1.symm.trans h2
    norm_num at h
  · exfalso
    have h1 : z * z = (0 : ℂ) := by simpa [hasCKSignature] using hσ
    have h2 : z * z = (-1 : ℂ) := by simpa [hasCKSignature] using hτ
    have h : (0 : ℂ) = (-1 : ℂ) := h1.symm.trans h2
    norm_num at h
  · rfl
  · exfalso
    have h1 : z * z = (0 : ℂ) := by simpa [hasCKSignature] using hσ
    have h2 : z * z = (1 : ℂ) := by simpa [hasCKSignature] using hτ
    have h : (0 : ℂ) = (1 : ℂ) := h1.symm.trans h2
    norm_num at h
  · exfalso
    have h1 : z * z = (1 : ℂ) := by simpa [hasCKSignature] using hσ
    have h2 : z * z = (-1 : ℂ) := by simpa [hasCKSignature] using hτ
    have h : (1 : ℂ) = (-1 : ℂ) := h1.symm.trans h2
    norm_num at h
  · exfalso
    have h1 : z * z = (1 : ℂ) := by simpa [hasCKSignature] using hσ
    have h2 : z * z = (0 : ℂ) := by simpa [hasCKSignature] using hτ
    have h : (1 : ℂ) = (0 : ℂ) := h1.symm.trans h2
    norm_num at h
  · rfl

/--
Complex Wick specialization:
if `B² = 1`, then `(I*B)² = -1`.
-/
@[rep_depth thermo]
theorem wick_twist_complex_hyperbolic_to_elliptic
    {B : ℂ}
    (hB : B * B = 1) :
    (Complex.I * B) * (Complex.I * B) = -1 := by
  calc
    (Complex.I * B) * (Complex.I * B)
        = (Complex.I * Complex.I) * (B * B) := by ring
    _ = (-1) * 1 := by rw [Complex.I_mul_I, hB]
    _ = -1 := by simp

/--
Complex Wick specialization:
if `B² = -1`, then `(I*B)² = 1`.
-/
@[rep_depth thermo]
theorem wick_twist_complex_elliptic_to_hyperbolic
    {B : ℂ}
    (hB : B * B = -1) :
    (Complex.I * B) * (Complex.I * B) = 1 := by
  calc
    (Complex.I * B) * (Complex.I * B)
        = (Complex.I * Complex.I) * (B * B) := by ring
    _ = (-1) * (-1) := by rw [Complex.I_mul_I, hB]
    _ = 1 := by norm_num

/--
Complex Wick specialization:
if `B² = 0`, then `(I*B)² = 0`.
-/
@[rep_depth thermo]
theorem wick_twist_complex_parabolic_fixed
    {B : ℂ}
    (hB : B * B = 0) :
    (Complex.I * B) * (Complex.I * B) = 0 := by
  calc
    (Complex.I * B) * (Complex.I * B)
        = (Complex.I * Complex.I) * (B * B) := by ring
    _ = (-1) * 0 := by rw [Complex.I_mul_I, hB]
    _ = 0 := by simp

/--
Wick transport on the complex square classes.
-/
@[rep_depth thermo]
theorem wick_twist_complex_signature_transport
    {B : ℂ} :
    (hasCKSignature B CKSignature.hyperbolic →
      hasCKSignature (Complex.I * B) CKSignature.elliptic) ∧
    (hasCKSignature B CKSignature.elliptic →
      hasCKSignature (Complex.I * B) CKSignature.hyperbolic) ∧
    (hasCKSignature B CKSignature.parabolic →
      hasCKSignature (Complex.I * B) CKSignature.parabolic) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact wick_twist_complex_hyperbolic_to_elliptic h
  · intro h
    exact wick_twist_complex_elliptic_to_hyperbolic h
  · intro h
    exact wick_twist_complex_parabolic_fixed h

/--
Case-split Wick image law on `CKSignature` over `ℂ`.

`I`-twist maps:
- hyperbolic ↦ elliptic
- elliptic ↦ hyperbolic
- parabolic ↦ parabolic
-/
@[rep_depth thermo]
theorem wick_twist_complex_signature_image
    {B : ℂ} {σ : CKSignature}
    (hσ : hasCKSignature B σ) :
    hasCKSignature (Complex.I * B) (wickCKMap σ) := by
  cases σ
  · simpa [hasCKSignature] using wick_twist_complex_elliptic_to_hyperbolic hσ
  · simpa [hasCKSignature] using wick_twist_complex_parabolic_fixed hσ
  · simpa [hasCKSignature] using wick_twist_complex_hyperbolic_to_elliptic hσ

/--
Double complex Wick twist is period-2 at the square-class level:
the induced `CKSignature` returns to the original class.
-/
@[rep_depth thermo]
theorem wick_twist_complex_signature_period_two
    {B : ℂ} {σ : CKSignature}
    (hσ : hasCKSignature B σ) :
    hasCKSignature (Complex.I * (Complex.I * B)) σ := by
  cases σ
  · -- elliptic -> hyperbolic -> elliptic
    have h1 : hasCKSignature (Complex.I * B) CKSignature.hyperbolic := by
      simpa [hasCKSignature] using wick_twist_complex_elliptic_to_hyperbolic hσ
    simpa [hasCKSignature, mul_assoc] using
      (wick_twist_complex_hyperbolic_to_elliptic (B := Complex.I * B) h1)
  · -- parabolic fixed by Wick
    have h0 : hasCKSignature (Complex.I * B) CKSignature.parabolic := by
      simpa [hasCKSignature] using wick_twist_complex_parabolic_fixed hσ
    simpa [hasCKSignature, mul_assoc] using
      (wick_twist_complex_parabolic_fixed (B := Complex.I * B) h0)
  · -- hyperbolic -> elliptic -> hyperbolic
    have hm1 : hasCKSignature (Complex.I * B) CKSignature.elliptic := by
      simpa [hasCKSignature] using wick_twist_complex_hyperbolic_to_elliptic hσ
    simpa [hasCKSignature, mul_assoc] using
      (wick_twist_complex_elliptic_to_hyperbolic (B := Complex.I * B) hm1)

/--
Two-step signature transport through `wickCKMap` collapses to identity.
This is the signature-level companion of `wick_twist_complex_signature_period_two`.
-/
@[rep_depth thermo]
theorem wick_twist_complex_signature_period_two_via_map
    {B : ℂ} {σ : CKSignature}
    (hσ : hasCKSignature B σ) :
    hasCKSignature (Complex.I * (Complex.I * B)) (wickCKMap (wickCKMap σ)) := by
  simpa [wickCKMap_involutive] using
    (wick_twist_complex_signature_period_two (B := B) (σ := σ) hσ)

/--
One-step complex Wick transport, packed as an explicit implication.
-/
@[rep_depth thermo]
theorem wick_twist_complex_signature_forward
    {B : ℂ} {τ : CKSignature}
    (h : hasCKSignature B τ) :
    hasCKSignature (Complex.I * B) (wickCKMap τ) :=
  wick_twist_complex_signature_image (B := B) (σ := τ) h

/--
Forward transport, packaged from the image theorem.
-/
@[rep_depth thermo]
theorem wick_twist_complex_signature_forward'
    {B : ℂ} {τ : CKSignature}
    (h : hasCKSignature B τ) :
    hasCKSignature (Complex.I * B) (wickCKMap τ) := by
  exact wick_twist_complex_signature_forward (B := B) (τ := τ) h

/--
Bundled one-step complex Wick signature transport.
-/
@[rep_depth thermo]
theorem wick_twist_complex_signature_transport_iff
    {B : ℂ} {τ : CKSignature} :
    hasCKSignature B τ ↔
      hasCKSignature (Complex.I * B) (wickCKMap τ) := by
  constructor
  · intro h
    exact wick_twist_complex_signature_forward (B := B) (τ := τ) h
  · intro h
    have h2map : hasCKSignature (Complex.I * (Complex.I * B)) (wickCKMap (wickCKMap τ)) :=
      wick_twist_complex_signature_forward (B := Complex.I * B) (τ := wickCKMap τ) h
    have h2 : hasCKSignature (Complex.I * (Complex.I * B)) τ := by
      simpa [wickCKMap_involutive] using h2map
    have h3 : hasCKSignature (-B) τ := by
      have hmul : Complex.I * (Complex.I * B) = -B := by
        calc
          Complex.I * (Complex.I * B) = (Complex.I * Complex.I) * B := by
            rw [← mul_assoc]
          _ = (-1 : ℂ) * B := by
            rw [Complex.I_mul_I]
          _ = -B := by
            simp
      simpa [hmul] using h2
    cases τ <;> simpa [hasCKSignature] using h3

/--
Complex Wick cannot remain hyperbolic under nondegenerate square class:
if `B² = 1`, then `((I*B)² = 1)` is impossible.
-/
@[rep_depth thermo]
theorem wick_twist_complex_not_square_one
    {B : ℂ}
    (hB : B * B = 1) :
    (Complex.I * B) * (Complex.I * B) ≠ 1 := by
  intro hsq1
  have hsqNeg : (Complex.I * B) * (Complex.I * B) = -1 :=
    wick_twist_complex_hyperbolic_to_elliptic hB
  have hneq : (1 : ℂ) ≠ -(1 : ℂ) := by norm_num
  exact square_one_and_neg_one_incompatible (A := ℂ) (x := Complex.I * B) hneq hsq1 hsqNeg

/--
Wick-type twist: if `ω² = -1` and `ω` commutes with `B`, then
`(ωB)² = -(B²)`.
-/
@[rep_depth thermo]
theorem wick_twist_square_flip
    {A : Type*} [Ring A]
    (ω B : A)
    (hω : ω * ω = -(1 : A))
    (hcomm : ω * B = B * ω) :
    (ω * B) * (ω * B) = -(B * B) := by
  calc
    (ω * B) * (ω * B) = ω * ω * (B * B) := by
      calc
        (ω * B) * (ω * B) = ω * (B * ω) * B := by noncomm_ring
        _ = ω * (ω * B) * B := by rw [hcomm]
        _ = ω * ω * (B * B) := by noncomm_ring
    _ = (-(1 : A)) * (B * B) := by rw [hω]
    _ = -(B * B) := by simp

/--
Wick specialization: a hyperbolic generator (`B² = 1`) is sent to an elliptic
generator (`(ωB)² = -1`) when twisted by a commuting imaginary unit
(`ω² = -1`).
-/
@[rep_depth thermo]
theorem wick_twist_hyperbolic_to_elliptic
    {A : Type*} [Ring A]
    (ω B : A)
    (hω : ω * ω = -(1 : A))
    (hcomm : ω * B = B * ω)
    (hB : B * B = (1 : A)) :
    (ω * B) * (ω * B) = -(1 : A) := by
  calc
    (ω * B) * (ω * B) = -(B * B) := wick_twist_square_flip ω B hω hcomm
    _ = -(1 : A) := by simpa [hB]

/--
Wick specialization in the reverse direction:
an elliptic generator (`B² = -1`) is sent to a hyperbolic generator
(`(ωB)² = 1`) when twisted by a commuting imaginary unit (`ω² = -1`).
-/
@[rep_depth thermo]
theorem wick_twist_elliptic_to_hyperbolic
    {A : Type*} [Ring A]
    (ω B : A)
    (hω : ω * ω = -(1 : A))
    (hcomm : ω * B = B * ω)
    (hB : B * B = (-(1 : A))) :
    (ω * B) * (ω * B) = (1 : A) := by
  calc
    (ω * B) * (ω * B) = -(B * B) := wick_twist_square_flip ω B hω hcomm
    _ = (1 : A) := by simpa [hB]

/--
Transport/conjugation corollary: if `x² = κ` then transported element keeps
the same square class, i.e. `(e x)² = e κ`.
-/
@[rep_depth thermo]
theorem square_class_transport
    {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B) (x κ : A)
    (hx : x * x = κ) :
    e x * e x = e κ := by
  calc
    e x * e x = e (x * x) := by simpa using (map_mul e x x)
    _ = e κ := by simpa [hx]

/--
Transport cannot flip `+1` to `-1` when the codomain is not characteristic `2`.

If `x² = 1` in `A`, then for any ring equivalence `e : A ≃+* B`,
`(e x)² = -1` would force `2 = 0` in `B`, hence contradiction whenever
`(2 : B) ≠ 0`.
-/
@[rep_depth thermo]
theorem transport_hyperbolic_not_elliptic
    {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B) (x : A)
    (htwo_ne_zero : (2 : B) ≠ 0)
    (hx : x * x = (1 : A)) :
    e x * e x ≠ (-(1 : B)) := by
  intro hneg
  have hsq : e x * e x = (1 : B) := by
    simpa [hx] using (square_class_transport e x (1 : A) hx)
  have hone_neg_one : (1 : B) = (-(1 : B)) := by
    calc
      (1 : B) = e x * e x := hsq.symm
      _ = (-(1 : B)) := hneg
  have hsum : (1 : B) + 1 = (-(1 : B)) + 1 := by
    exact congrArg (fun t : B => t + 1) hone_neg_one
  have htwo_eq_zero : (2 : B) = 0 := by
    calc
      (2 : B) = (1 : B) + 1 := by norm_num
      _ = (-(1 : B)) + 1 := hsum
      _ = 0 := by simp
  exact htwo_ne_zero htwo_eq_zero

/--
Transport vs continuation dichotomy (algebraic corridor).

Similarity/conjugation preserves the hyperbolic square class `(+1)`, while a
commuting Wick-type twist by `ω² = -1` flips the same generator to elliptic
square class `(-1)`.
-/
@[rep_depth thermo]
theorem transport_vs_wick_dichotomy
    {A : Type*} [Ring A]
    (u : Units A) (ω B : A)
    (hB : B * B = (1 : A))
    (hω : ω * ω = -(1 : A))
    (hcomm : ω * B = B * ω) :
    ((↑u * B * ↑u⁻¹) * (↑u * B * ↑u⁻¹) = (1 : A))
      ∧ ((ω * B) * (ω * B) = -(1 : A)) := by
  refine ⟨?_, ?_⟩
  · exact conjugation_preserves_square_one u B hB
  · exact wick_twist_hyperbolic_to_elliptic ω B hω hcomm hB

/--
In non-characteristic-`2` rings, transport and Wick outcomes are distinct:
the transported hyperbolic square (`+1`) cannot equal the Wick elliptic square
(`-1`).
-/
@[rep_depth thermo]
theorem transport_vs_wick_distinct_square_classes
    {A : Type*} [Ring A]
    (u : Units A) (ω B : A)
    (htwo_ne_zero : (2 : A) ≠ 0)
    (hB : B * B = (1 : A))
    (hω : ω * ω = -(1 : A))
    (hcomm : ω * B = B * ω) :
    ((↑u * B * ↑u⁻¹) * (↑u * B * ↑u⁻¹))
      ≠ ((ω * B) * (ω * B)) := by
  intro heq
  have hsqT :
      ((↑u * B * ↑u⁻¹) * (↑u * B * ↑u⁻¹)) = (1 : A) :=
    conjugation_preserves_square_one u B hB
  have hsqW :
      ((ω * B) * (ω * B)) = (-(1 : A)) :=
    wick_twist_hyperbolic_to_elliptic ω B hω hcomm hB
  have hone_neg :
      (1 : A) = (-(1 : A)) := by
    calc
      (1 : A) = ((↑u * B * ↑u⁻¹) * (↑u * B * ↑u⁻¹)) := hsqT.symm
      _ = ((ω * B) * (ω * B)) := heq
      _ = (-(1 : A)) := hsqW
  have hsum : (1 : A) + 1 = (-(1 : A)) + 1 := congrArg (fun t : A => t + 1) hone_neg
  have htwo_eq_zero : (2 : A) = 0 := by
    calc
      (2 : A) = (1 : A) + 1 := by norm_num
      _ = (-(1 : A)) + 1 := hsum
      _ = 0 := by simp
  exact htwo_ne_zero htwo_eq_zero

/--
Conjugation preserves parabolic square class (`x² = 0`).
-/
@[rep_depth thermo]
theorem conjugation_preserves_square_zero_basic
    {A : Type*} [Ring A]
    (u : Units A) (x : A)
    (hx : x * x = (0 : A)) :
    ((↑u * x * ↑u⁻¹) * (↑u * x * ↑u⁻¹)) = (0 : A) := by
  calc
    ((↑u * x * ↑u⁻¹) * (↑u * x * ↑u⁻¹))
        = ↑u * (x * x) * ↑u⁻¹ := conjugation_square_covariant u x
    _ = ↑u * 0 * ↑u⁻¹ := by rw [hx]
    _ = 0 := by simp

/--
Wick twist preserves parabolic nilpotency:
if `B² = 0`, then `(ωB)² = 0` under the same commuting hypothesis.
-/
@[rep_depth thermo]
theorem wick_twist_parabolic_stable
    {A : Type*} [Ring A]
    (ω B : A)
    (hω : ω * ω = -(1 : A))
    (hcomm : ω * B = B * ω)
    (hB : B * B = (0 : A)) :
    (ω * B) * (ω * B) = (0 : A) := by
  calc
    (ω * B) * (ω * B) = -(B * B) := wick_twist_square_flip ω B hω hcomm
    _ = -(0 : A) := by rw [hB]
    _ = 0 := by simp

/--
Two-way Wick class flip bundle on one corridor:
`+1 → -1`, `-1 → +1`, and `0 → 0` under the same commuting twist data.
-/
@[rep_depth thermo]
theorem wick_twist_square_class_bundle
    {A : Type*} [Ring A]
    (ω Bh Be Bp : A)
    (hω : ω * ω = -(1 : A))
    (hcomm_h : ω * Bh = Bh * ω)
    (hcomm_e : ω * Be = Be * ω)
    (hcomm_p : ω * Bp = Bp * ω)
    (hBh : Bh * Bh = (1 : A))
    (hBe : Be * Be = (-(1 : A)))
    (hBp : Bp * Bp = (0 : A)) :
    ((ω * Bh) * (ω * Bh) = (-(1 : A))) ∧
    ((ω * Be) * (ω * Be) = (1 : A)) ∧
    ((ω * Bp) * (ω * Bp) = (0 : A)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact wick_twist_hyperbolic_to_elliptic ω Bh hω hcomm_h hBh
  · exact wick_twist_elliptic_to_hyperbolic ω Be hω hcomm_e hBe
  · exact wick_twist_parabolic_stable ω Bp hω hcomm_p hBp

/--
If both odd layers are nilpotent, the square of the recursive supercharge is
exactly the odd--odd anticommutator.

This is the algebraic origin of the central charge in the recursive SUSY lane.
-/
@[rep_depth thermo]
theorem recursive_nilpotent_supercharge_square_eq_anticommutator
    {A : Type*} [Ring A]
    {Q R : A}
    (hQ : Q * Q = 0)
    (hR : R * R = 0) :
    (Q + R) * (Q + R) = Q * R + R * Q := by
  calc
    (Q + R) * (Q + R)
        = Q * Q + (Q * R + R * Q) + R * R := by
          exact recursive_supercharge_square Q R
    _ = 0 + (Q * R + R * Q) + 0 := by
          rw [hQ, hR]
    _ = Q * R + R * Q := by
          simp

/--
Central-charge extraction from two nilpotent recursive supercharges.

If the odd--odd cross bracket is `Z`, then the square of the extended
supercharge is exactly `Z`.
-/
@[rep_depth thermo]
theorem recursive_nilpotent_supercharge_square_eq_centralCharge
    {A : Type*} [Ring A]
    {Q R Z : A}
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hZ : Q * R + R * Q = Z) :
    (Q + R) * (Q + R) = Z := by
  rw [recursive_nilpotent_supercharge_square_eq_anticommutator hQ hR]
  exact hZ

/-! ## Finite inductive preservation of SUSY central-charge closure -/

/--
Ring homomorphisms preserve square-zero elements.
-/
@[rep_depth thermo]
theorem ringHom_preserves_square_zero
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B)
    {Q : A}
    (hQ : Q * Q = 0) :
    φ Q * φ Q = 0 := by
  simpa using congrArg φ hQ

/--
Ring homomorphisms preserve odd--odd anticommutators.
-/
@[rep_depth thermo]
theorem ringHom_map_anticommutator
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B)
    (Q R : A) :
    φ (Q * R + R * Q) = φ Q * φ R + φ R * φ Q := by
  simp

/--
Ring homomorphisms preserve centrality on the image.

For non-surjective bonding maps this is the correct statement: the transported
central term commutes with transported observables. Global centrality in the
larger algebra needs surjectivity or an extra centralizer theorem.
-/
@[rep_depth thermo]
theorem ringHom_preserves_central_on_image
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B)
    {Z : A}
    (hCentral : ∀ X : A, Z * X = X * Z) :
    ∀ X : A, φ Z * φ X = φ X * φ Z := by
  intro X
  simpa using congrArg φ (hCentral X)

/--
Surjective ring homomorphisms preserve global centrality.
-/
@[rep_depth thermo]
theorem ringHom_preserves_central_surjective
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B)
    (hSurj : Function.Surjective φ)
    {Z : A}
    (hCentral : ∀ X : A, Z * X = X * Z) :
    ∀ Y : B, φ Z * Y = Y * φ Z := by
  intro Y
  rcases hSurj Y with ⟨X, rfl⟩
  exact ringHom_preserves_central_on_image φ hCentral X

/--
Ring homomorphism transport of the recursive central-charge law.

This is the finite functorial step: if a stage has `Q² = R² = 0` and
`{Q,R}=Z`, then the transported stage has `(φ Q + φ R)² = φ Z`.
-/
@[rep_depth thermo]
theorem ringHom_transport_recursive_centralCharge
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B)
    {Q R Z : A}
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hZ : Q * R + R * Q = Z) :
    (φ Q + φ R) * (φ Q + φ R) = φ Z := by
  have h := congrArg φ
    (recursive_nilpotent_supercharge_square_eq_centralCharge
      (Q := Q) (R := R) (Z := Z) hQ hR hZ)
  simpa using h

/--
One finite inductive step.

A bonding map `φₙ : Aₙ → Aₙ₊₁` preserving the named elements transports:
* square-zero of both odd charges;
* odd--odd central closure;
* recursive square/central-charge law.
-/
@[rep_depth thermo]
theorem inductive_step_transport_recursive_susy
    {Stage : ℕ → Type*} [∀ n, Ring (Stage n)]
    (φ : ∀ n, Stage n →+* Stage (n + 1))
    (n : ℕ)
    {Q R Z : Stage n}
    {Q' R' Z' : Stage (n + 1)}
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hZ : Q * R + R * Q = Z)
    (hQ' : Q' = φ n Q)
    (hR' : R' = φ n R)
    (hZ' : Z' = φ n Z) :
    Q' * Q' = 0 ∧
      R' * R' = 0 ∧
      Q' * R' + R' * Q' = Z' ∧
      (Q' + R') * (Q' + R') = Z' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hQ']
    exact ringHom_preserves_square_zero (φ n) hQ
  · rw [hR']
    exact ringHom_preserves_square_zero (φ n) hR
  · rw [hQ', hR', hZ']
    calc
      φ n Q * φ n R + φ n R * φ n Q
          = φ n (Q * R + R * Q) := by
            exact (ringHom_map_anticommutator (φ n) Q R).symm
      _ = φ n Z := by
            rw [hZ]
  · rw [hQ', hR', hZ']
    exact ringHom_transport_recursive_centralCharge (φ n) hQ hR hZ

/--
Inductive-step preservation of centrality on the transported image.

This is the correct statement for injective/bonding maps: `φ Z` commutes with
all elements coming from the previous stage.
-/
@[rep_depth thermo]
theorem inductive_step_preserves_central_on_image
    {Stage : ℕ → Type*} [∀ n, Ring (Stage n)]
    (φ : ∀ n, Stage n →+* Stage (n + 1))
    (n : ℕ)
    {Z : Stage n}
    (hCentral : ∀ X : Stage n, Z * X = X * Z) :
    ∀ X : Stage n, φ n Z * φ n X = φ n X * φ n Z :=
  ringHom_preserves_central_on_image (φ n) hCentral

/--
If the odd--odd cross bracket is a central element `Z`, then the recursive
supercharge square is central.
-/
@[rep_depth thermo]
theorem recursive_supercharge_square_is_central
    {A : Type*} [Ring A]
    {Q R Z : A}
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hZ : Q * R + R * Q = Z)
    (hCentral : ∀ X : A, Z * X = X * Z) :
    ∀ X : A, ((Q + R) * (Q + R)) * X = X * ((Q + R) * (Q + R)) := by
  intro X
  rw [recursive_nilpotent_supercharge_square_eq_centralCharge hQ hR hZ]
  exact hCentral X

/--
Finite three-layer expansion. This is the next step toward the recursive tower.
-/
@[rep_depth thermo]
theorem three_supercharge_square
    {A : Type*} [Ring A]
    (Q₁ Q₂ Q₃ : A) :
    (Q₁ + Q₂ + Q₃) * (Q₁ + Q₂ + Q₃) =
      Q₁ * Q₁ + Q₂ * Q₂ + Q₃ * Q₃
      + (Q₁ * Q₂ + Q₂ * Q₁)
      + (Q₁ * Q₃ + Q₃ * Q₁)
      + (Q₂ * Q₃ + Q₃ * Q₂) := by
  noncomm_ring

/--
Three-layer nilpotent reduction.

If each odd layer squares to zero, the square of the finite three-layer
supercharge is exactly the sum of pairwise odd--odd anticommutators.
-/
@[rep_depth thermo]
theorem three_nilpotent_supercharge_square_eq_pairwise_anticommutators
    {A : Type*} [Ring A]
    {Q₁ Q₂ Q₃ : A}
    (h1 : Q₁ * Q₁ = 0)
    (h2 : Q₂ * Q₂ = 0)
    (h3 : Q₃ * Q₃ = 0) :
    (Q₁ + Q₂ + Q₃) * (Q₁ + Q₂ + Q₃) =
      (Q₁ * Q₂ + Q₂ * Q₁)
      + (Q₁ * Q₃ + Q₃ * Q₁)
      + (Q₂ * Q₃ + Q₃ * Q₂) := by
  calc
    (Q₁ + Q₂ + Q₃) * (Q₁ + Q₂ + Q₃)
        = Q₁ * Q₁ + Q₂ * Q₂ + Q₃ * Q₃
          + (Q₁ * Q₂ + Q₂ * Q₁)
          + (Q₁ * Q₃ + Q₃ * Q₁)
          + (Q₂ * Q₃ + Q₃ * Q₂) := by
            exact three_supercharge_square Q₁ Q₂ Q₃
    _ = 0 + 0 + 0
          + (Q₁ * Q₂ + Q₂ * Q₁)
          + (Q₁ * Q₃ + Q₃ * Q₁)
          + (Q₂ * Q₃ + Q₃ * Q₂) := by
            rw [h1, h2, h3]
    _ = (Q₁ * Q₂ + Q₂ * Q₁)
          + (Q₁ * Q₃ + Q₃ * Q₁)
          + (Q₂ * Q₃ + Q₃ * Q₂) := by
            simp

/--
Three-layer central-lane extraction from pairwise odd--odd brackets.

If each pairwise anticommutator is identified with a central-lane term
`Z₁₂, Z₁₃, Z₂₃`, then the square of the extended odd supercharge is their sum.
-/
@[rep_depth thermo]
theorem three_nilpotent_supercharge_square_eq_pairwise_centralSum
    {A : Type*} [Ring A]
    {Q₁ Q₂ Q₃ Z₁₂ Z₁₃ Z₂₃ : A}
    (h1 : Q₁ * Q₁ = 0)
    (h2 : Q₂ * Q₂ = 0)
    (h3 : Q₃ * Q₃ = 0)
    (h12 : Q₁ * Q₂ + Q₂ * Q₁ = Z₁₂)
    (h13 : Q₁ * Q₃ + Q₃ * Q₁ = Z₁₃)
    (h23 : Q₂ * Q₃ + Q₃ * Q₂ = Z₂₃) :
    (Q₁ + Q₂ + Q₃) * (Q₁ + Q₂ + Q₃) = Z₁₂ + Z₁₃ + Z₂₃ := by
  rw [three_nilpotent_supercharge_square_eq_pairwise_anticommutators h1 h2 h3]
  rw [h12, h13, h23]

/--
Finite `N=2` odd--odd closure with explicit Hamiltonian and central lanes.

This states the graded SUSY split in direct algebraic form:
`{Q₁,Q₂} = H₁₂ + Z₁₂`.
-/
@[rep_depth thermo]
theorem n2_supercharge_anticommutator_split
    {A : Type*} [Ring A]
    {Q₁ Q₂ H₁₂ Z₁₂ : A}
    (hsplit : Q₁ * Q₂ + Q₂ * Q₁ = H₁₂ + Z₁₂) :
    Q₁ * Q₂ + Q₂ * Q₁ = H₁₂ + Z₁₂ := hsplit

/--
Duality transport of an odd--odd anticommutator.

Assume an explicit transport map `Dual : A → B` that preserves addition and
multiplication. Then odd--odd brackets are transported exactly.
-/
@[rep_depth thermo]
theorem duality_transports_oddOdd_anticommutator
    {A B : Type*} [Ring A] [Ring B]
    (Dual : A → B)
    (hAdd : ∀ x y : A, Dual (x + y) = Dual x + Dual y)
    (hMul : ∀ x y : A, Dual (x * y) = Dual x * Dual y)
    (Q₁ Q₂ : A) :
    Dual (Q₁ * Q₂ + Q₂ * Q₁)
      = (Dual Q₁) * (Dual Q₂) + (Dual Q₂) * (Dual Q₁) := by
  rw [hAdd, hMul, hMul]

/--
Duality transport of finite `N=2` SUSY closure with central lane preservation.

If `Dual` is additive/multiplicative and sends `H₁₂ ↦ H'₁₂`,
`Z₁₂ ↦ Z'₁₂`, then it transports
`{Q₁,Q₂} = H₁₂ + Z₁₂` to
`{Dual Q₁, Dual Q₂} = H'₁₂ + Z'₁₂`.
-/
@[rep_depth thermo]
theorem duality_transports_n2_supercharge_split
    {A B : Type*} [Ring A] [Ring B]
    (Dual : A → B)
    (hAdd : ∀ x y : A, Dual (x + y) = Dual x + Dual y)
    (hMul : ∀ x y : A, Dual (x * y) = Dual x * Dual y)
    {Q₁ Q₂ H₁₂ Z₁₂ : A}
    {H'₁₂ Z'₁₂ : B}
    (hsplit : Q₁ * Q₂ + Q₂ * Q₁ = H₁₂ + Z₁₂)
    (hH : Dual H₁₂ = H'₁₂)
    (hZ : Dual Z₁₂ = Z'₁₂) :
    (Dual Q₁) * (Dual Q₂) + (Dual Q₂) * (Dual Q₁) = H'₁₂ + Z'₁₂ := by
  have hL :
      Dual (Q₁ * Q₂ + Q₂ * Q₁)
        = (Dual Q₁) * (Dual Q₂) + (Dual Q₂) * (Dual Q₁) := by
    exact duality_transports_oddOdd_anticommutator Dual hAdd hMul Q₁ Q₂
  have hR : Dual (Q₁ * Q₂ + Q₂ * Q₁) = H'₁₂ + Z'₁₂ := by
    calc
      Dual (Q₁ * Q₂ + Q₂ * Q₁) = Dual (H₁₂ + Z₁₂) := by rw [hsplit]
      _ = Dual H₁₂ + Dual Z₁₂ := by rw [hAdd]
      _ = H'₁₂ + Z'₁₂ := by rw [hH, hZ]
  exact hL.symm.trans hR

/--
Finite D-brane boundary nilpotency as a differential law: `∂² = 0`.
-/
@[rep_depth thermo]
theorem dbrane_boundary_sq_zero
    {C : Type*} [AddGroup C]
    (boundary : C →+ C)
    (hboundary2 : boundary.comp boundary = 0) :
    boundary.comp boundary = 0 := hboundary2

/--
Image-to-kernel consequence of finite boundary nilpotency:
`im ∂ ⊆ ker ∂`.
-/
@[rep_depth thermo]
theorem dbrane_boundary_image_subset_kernel
    {C : Type*} [AddGroup C]
    (boundary : C →+ C)
    (hboundary2 : boundary.comp boundary = 0) :
    ∀ x : C, boundary (boundary x) = 0 := by
  intro x
  have h := congrArg (fun f : C →+ C => f x) hboundary2
  simpa using h

/--
Finite conserved charge under SUSY-generated exact updates.

If a charge functional `J` annihilates boundaries (`J ∘ ∂ = 0`), then
the update `x ↦ x + ∂y` preserves `J`.
-/
@[rep_depth thermo]
theorem dbrane_charge_conserved_under_exact_update
    {C A : Type*} [AddGroup C] [AddGroup A]
    (boundary : C →+ C)
    (J : C →+ A)
    (hclosed : J.comp boundary = 0)
    (x y : C) :
    J (x + boundary y) = J x := by
  have hcy : J (boundary y) = 0 := by
    have h := congrArg (fun f : C →+ A => f y) hclosed
    simpa using h
  calc
    J (x + boundary y) = J x + J (boundary y) := by simp
    _ = J x + 0 := by rw [hcy]
    _ = J x := by simp

/--
Duality equivalence laws as explicit inverse identities.
-/
@[rep_depth thermo]
theorem duality_inverse_laws
    {A B : Type*}
    (Dual : A → B)
    (DualInv : B → A)
    (hLeft : ∀ a : A, DualInv (Dual a) = a)
    (hRight : ∀ b : B, Dual (DualInv b) = b) :
    (∀ a : A, DualInv (Dual a) = a) ∧
    (∀ b : B, Dual (DualInv b) = b) := by
  exact ⟨hLeft, hRight⟩

/--
Duality transport of `N=2` SUSY split with explicit inverse laws available.

This extends `duality_transports_n2_supercharge_split` by carrying the
equivalence hypotheses in the same theorem surface.
-/
@[rep_depth thermo]
theorem duality_equiv_transports_n2_supercharge_split
    {A B : Type*} [Ring A] [Ring B]
    (Dual : A → B)
    (DualInv : B → A)
    (hLeftInv : ∀ a : A, DualInv (Dual a) = a)
    (hRightInv : ∀ b : B, Dual (DualInv b) = b)
    (hAdd : ∀ x y : A, Dual (x + y) = Dual x + Dual y)
    (hMul : ∀ x y : A, Dual (x * y) = Dual x * Dual y)
    {Q₁ Q₂ H₁₂ Z₁₂ : A}
    {H'₁₂ Z'₁₂ : B}
    (hsplit : Q₁ * Q₂ + Q₂ * Q₁ = H₁₂ + Z₁₂)
    (hH : Dual H₁₂ = H'₁₂)
    (hZ : Dual Z₁₂ = Z'₁₂) :
    (Dual Q₁) * (Dual Q₂) + (Dual Q₂) * (Dual Q₁) = H'₁₂ + Z'₁₂ := by
  let _ := duality_inverse_laws Dual DualInv hLeftInv hRightInv
  exact duality_transports_n2_supercharge_split Dual hAdd hMul hsplit hH hZ

/--
Finite-stage invariant packet in symmetry-adapted local coordinates.

This captures the algebraic closure lanes used in the finite inductive corridor.
-/
@[rep_depth thermo]
structure SupergradedClosureAt (A : Type*) [Ring A] where
  is_odd : A → Prop
  is_even : A → Prop
  is_central : A → Prop
  odd_nilpotency : ∀ x, is_odd x → x * x = 0
  odd_odd_closure : ∀ x y, is_odd x → is_odd y → is_even (x * y + y * x)
  central_lane : ∀ c x, is_central c → c * x = x * c
  projector_identity : ∃ P, is_even P ∧ P * P = P

/--
Bonding intertwiner between two finite stages.

The map is a ring homomorphism and explicitly transports grading lanes.
-/
@[rep_depth thermo]
structure BondingIntertwiner {A B : Type*} [Ring A] [Ring B]
    (invA : SupergradedClosureAt A) (invB : SupergradedClosureAt B) where
  map : A →+* B
  preserves_odd : ∀ x, invA.is_odd x → invB.is_odd (map x)
  preserves_even : ∀ x, invA.is_even x → invB.is_even (map x)
  preserves_central : ∀ c, invA.is_central c → invB.is_central (map c)

/--
Odd nilpotency transports along a valid bonding intertwiner.
-/
@[rep_depth thermo]
theorem invariant_transport_stable
    {A B : Type*} [Ring A] [Ring B]
    (invA : SupergradedClosureAt A)
    (invB : SupergradedClosureAt B)
    (f : BondingIntertwiner invA invB)
    (x : A) (hx : invA.is_odd x) :
    (f.map x) * (f.map x) = 0 := by
  have hodd : invB.is_odd (f.map x) := f.preserves_odd x hx
  exact invB.odd_nilpotency (f.map x) hodd

/--
Odd--odd closure transports along a valid bonding intertwiner.
-/
@[rep_depth thermo]
theorem oddOdd_closure_transport_stable
    {A B : Type*} [Ring A] [Ring B]
    (invA : SupergradedClosureAt A)
    (invB : SupergradedClosureAt B)
    (f : BondingIntertwiner invA invB)
    (x y : A)
    (hx : invA.is_odd x) (hy : invA.is_odd y) :
    invB.is_even ((f.map x) * (f.map y) + (f.map y) * (f.map x)) := by
  have hA : invA.is_even (x * y + y * x) := invA.odd_odd_closure x y hx hy
  have hB : invB.is_even (f.map (x * y + y * x)) := f.preserves_even _ hA
  simpa [map_add, map_mul, add_comm, add_left_comm, add_assoc] using hB

/--
Central-lane commutation transports along a valid bonding intertwiner.
-/
@[rep_depth thermo]
theorem central_lane_transport_stable
    {A B : Type*} [Ring A] [Ring B]
    (invA : SupergradedClosureAt A)
    (invB : SupergradedClosureAt B)
    (f : BondingIntertwiner invA invB)
    (c x : A)
    (hc : invA.is_central c) :
    (f.map c) * (f.map x) = (f.map x) * (f.map c) := by
  have hcx : c * x = x * c := invA.central_lane c x hc
  have hmap : f.map (c * x) = f.map (x * c) := congrArg f.map hcx
  simpa [map_mul] using hmap

/--
Projector existence transports along a valid bonding intertwiner.
-/
@[rep_depth thermo]
theorem projector_identity_transport_exists
    {A B : Type*} [Ring A] [Ring B]
    (invA : SupergradedClosureAt A)
    (invB : SupergradedClosureAt B)
    (f : BondingIntertwiner invA invB) :
    ∃ P : B, invB.is_even P ∧ P * P = P := by
  rcases invA.projector_identity with ⟨P, hEvenP, hIdemP⟩
  refine ⟨f.map P, f.preserves_even P hEvenP, ?_⟩
  simpa [map_mul] using congrArg f.map hIdemP

/--
Finite recursive iterator for an endomap along the discrete inductive chain.
-/
@[rep_depth thermo]
def iterMap {A : Type*} (Φ : A → A) : ℕ → A → A
  | 0, x => x
  | n + 1, x => Φ (iterMap Φ n x)

/--
For an endo intertwiner on one stage, odd-lane membership is stable under all
finite iterates.
-/
@[rep_depth thermo]
theorem iterate_preserves_odd_lane
    {A : Type*} [Ring A]
    (inv : SupergradedClosureAt A)
    (f : BondingIntertwiner inv inv)
    (x : A) (hx : inv.is_odd x) :
    ∀ n : ℕ, inv.is_odd (iterMap f.map n x) := by
  intro n
  induction n with
  | zero =>
      simpa [iterMap] using hx
  | succ n ih =>
      simpa [iterMap] using f.preserves_odd (iterMap f.map n x) ih

/--
For an endo intertwiner on one stage, even-lane membership is stable under all
finite iterates.
-/
@[rep_depth thermo]
theorem iterate_preserves_even_lane
    {A : Type*} [Ring A]
    (inv : SupergradedClosureAt A)
    (f : BondingIntertwiner inv inv)
    (x : A) (hx : inv.is_even x) :
    ∀ n : ℕ, inv.is_even (iterMap f.map n x) := by
  intro n
  induction n with
  | zero =>
      simpa [iterMap] using hx
  | succ n ih =>
      simpa [iterMap] using f.preserves_even (iterMap f.map n x) ih

/--
For an endo intertwiner on one stage, central-lane membership is stable under
all finite iterates.
-/
@[rep_depth thermo]
theorem iterate_preserves_central_lane
    {A : Type*} [Ring A]
    (inv : SupergradedClosureAt A)
    (f : BondingIntertwiner inv inv)
    (x : A) (hx : inv.is_central x) :
    ∀ n : ℕ, inv.is_central (iterMap f.map n x) := by
  intro n
  induction n with
  | zero =>
      simpa [iterMap] using hx
  | succ n ih =>
      simpa [iterMap] using f.preserves_central (iterMap f.map n x) ih

/--
For an endo intertwiner on one stage, odd nilpotency is stable along the full
finite inductive chain of iterates.
-/
@[rep_depth thermo]
theorem iterate_odd_nilpotency_stable
    {A : Type*} [Ring A]
    (inv : SupergradedClosureAt A)
    (f : BondingIntertwiner inv inv)
    (x : A) (hx : inv.is_odd x) :
    ∀ n : ℕ, (iterMap f.map n x) * (iterMap f.map n x) = 0 := by
  intro n
  have hodd : inv.is_odd (iterMap f.map n x) :=
    iterate_preserves_odd_lane inv f x hx n
  exact inv.odd_nilpotency _ hodd

/--
Recursive transport map from stage `0` to stage `n` along a finite chain of
bonding intertwiners.
-/
@[rep_depth thermo]
def chainTransportFromZero
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (inv : ∀ n, SupergradedClosureAt (Chain n))
    (link : ∀ n, BondingIntertwiner (inv n) (inv (n + 1))) :
    ∀ n, (Chain 0) →+* (Chain n)
  | 0 => RingHom.id (Chain 0)
  | n + 1 => (link n).map.comp (chainTransportFromZero Chain inv link n)

/--
Odd-lane membership is transported from stage `0` to any finite stage `n`
along the chain intertwiners.
-/
@[rep_depth thermo]
theorem chain_odd_lane_transport_from_zero
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (inv : ∀ n, SupergradedClosureAt (Chain n))
    (link : ∀ n, BondingIntertwiner (inv n) (inv (n + 1)))
    (x : Chain 0) (hx : (inv 0).is_odd x) :
    ∀ n, (inv n).is_odd (chainTransportFromZero Chain inv link n x) := by
  intro n
  induction n with
  | zero =>
      simpa [chainTransportFromZero] using hx
  | succ n ih =>
      exact (link n).preserves_odd _ ih

/--
Odd nilpotency is transported from stage `0` to any finite stage `n` along the
chain intertwiners.
-/
@[rep_depth thermo]
theorem chain_odd_nilpotency_transport_from_zero
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (inv : ∀ n, SupergradedClosureAt (Chain n))
    (link : ∀ n, BondingIntertwiner (inv n) (inv (n + 1)))
    (x : Chain 0) (hx : (inv 0).is_odd x) :
    ∀ n, (chainTransportFromZero Chain inv link n x) *
      (chainTransportFromZero Chain inv link n x) = 0 := by
  intro n
  have hodd : (inv n).is_odd (chainTransportFromZero Chain inv link n x) :=
    chain_odd_lane_transport_from_zero Chain inv link x hx n
  exact (inv n).odd_nilpotency _ hodd

/--
Even-lane membership is transported from stage `0` to any finite stage `n`
along the chain intertwiners.
-/
@[rep_depth thermo]
theorem chain_even_lane_transport_from_zero
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (inv : ∀ n, SupergradedClosureAt (Chain n))
    (link : ∀ n, BondingIntertwiner (inv n) (inv (n + 1)))
    (x : Chain 0) (hx : (inv 0).is_even x) :
    ∀ n, (inv n).is_even (chainTransportFromZero Chain inv link n x) := by
  intro n
  induction n with
  | zero =>
      simpa [chainTransportFromZero] using hx
  | succ n ih =>
      exact (link n).preserves_even _ ih

/--
Central-lane membership is transported from stage `0` to any finite stage `n`
along the chain intertwiners.
-/
@[rep_depth thermo]
theorem chain_central_lane_transport_from_zero
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (inv : ∀ n, SupergradedClosureAt (Chain n))
    (link : ∀ n, BondingIntertwiner (inv n) (inv (n + 1)))
    (x : Chain 0) (hx : (inv 0).is_central x) :
    ∀ n, (inv n).is_central (chainTransportFromZero Chain inv link n x) := by
  intro n
  induction n with
  | zero =>
      simpa [chainTransportFromZero] using hx
  | succ n ih =>
      exact (link n).preserves_central _ ih

/--
Odd--odd closure transport from stage `0` to any finite stage `n`.
-/
@[rep_depth thermo]
theorem chain_oddOdd_closure_transport_from_zero
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (inv : ∀ n, SupergradedClosureAt (Chain n))
    (link : ∀ n, BondingIntertwiner (inv n) (inv (n + 1)))
    (x y : Chain 0)
    (hx : (inv 0).is_odd x)
    (hy : (inv 0).is_odd y) :
    ∀ n,
      (inv n).is_even
        ((chainTransportFromZero Chain inv link n x) *
          (chainTransportFromZero Chain inv link n y) +
         (chainTransportFromZero Chain inv link n y) *
          (chainTransportFromZero Chain inv link n x)) := by
  intro n
  have hxN : (inv n).is_odd (chainTransportFromZero Chain inv link n x) :=
    chain_odd_lane_transport_from_zero Chain inv link x hx n
  have hyN : (inv n).is_odd (chainTransportFromZero Chain inv link n y) :=
    chain_odd_lane_transport_from_zero Chain inv link y hy n
  exact (inv n).odd_odd_closure _ _ hxN hyN

/--
Central-lane commutation is transported from stage `0` to any finite stage `n`.
-/
@[rep_depth thermo]
theorem chain_central_commutation_transport_from_zero
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (inv : ∀ n, SupergradedClosureAt (Chain n))
    (link : ∀ n, BondingIntertwiner (inv n) (inv (n + 1)))
    (c x : Chain 0)
    (hc : (inv 0).is_central c) :
    ∀ n,
      (chainTransportFromZero Chain inv link n c) *
        (chainTransportFromZero Chain inv link n x)
      =
      (chainTransportFromZero Chain inv link n x) *
        (chainTransportFromZero Chain inv link n c) := by
  intro n
  have hcN : (inv n).is_central (chainTransportFromZero Chain inv link n c) :=
    chain_central_lane_transport_from_zero Chain inv link c hc n
  exact (inv n).central_lane _ _ hcN

/--
Nambu-Gorkov doubled spinor carrier (finite algebraic form).
-/
@[rep_depth thermo]
abbrev NambuSpinor (A : Type*) := A × A

/--
`τ₃` grading on the doubled Nambu-Gorkov carrier.
-/
@[rep_depth thermo]
def nambuTau3 {A : Type*} [AddCommGroup A] : NambuSpinor A →+ NambuSpinor A where
  toFun v := (v.1, -v.2)
  map_zero' := by simp
  map_add' x y := by
    ext <;> simp [add_comm, add_left_comm, add_assoc]

/--
Particle-hole swap on the doubled Nambu-Gorkov carrier.
-/
@[rep_depth thermo]
def nambuSwap {A : Type*} [AddCommGroup A] : NambuSpinor A →+ NambuSpinor A where
  toFun v := (v.2, v.1)
  map_zero' := by simp
  map_add' x y := by
    ext <;> simp [add_comm, add_left_comm, add_assoc]

/--
`τ₃` is involutive.
-/
@[rep_depth thermo]
theorem nambuTau3_involutive
    {A : Type*} [AddCommGroup A] (v : NambuSpinor A) :
    nambuTau3 (nambuTau3 v) = v := by
  ext <;> simp [nambuTau3]

/--
Particle-hole swap is involutive.
-/
@[rep_depth thermo]
theorem nambuSwap_involutive
    {A : Type*} [AddCommGroup A] (v : NambuSpinor A) :
    nambuSwap (nambuSwap v) = v := by
  ext <;> rfl

/--
Block-diagonal operator on doubled Nambu-Gorkov carrier.
-/
@[rep_depth thermo]
def nambuBlockDiag {A : Type*} [AddCommGroup A]
    (a d : A →+ A) : NambuSpinor A →+ NambuSpinor A where
  toFun v := (a v.1, d v.2)
  map_zero' := by simp
  map_add' x y := by
    ext <;> simp [add_comm, add_left_comm, add_assoc]

/--
Off-block-diagonal operator on doubled Nambu-Gorkov carrier.
-/
@[rep_depth thermo]
def nambuBlockOffDiag {A : Type*} [AddCommGroup A]
    (b c : A →+ A) : NambuSpinor A →+ NambuSpinor A where
  toFun v := (b v.2, c v.1)
  map_zero' := by simp
  map_add' x y := by
    ext <;> simp [add_comm, add_left_comm, add_assoc]

/--
Full `2×2` Nambu-Gorkov block operator in component form.
-/
@[rep_depth thermo]
def nambuBlockFull {A : Type*} [AddCommGroup A]
    (a b c d : A →+ A) : NambuSpinor A →+ NambuSpinor A where
  toFun v := (a v.1 + b v.2, c v.1 + d v.2)
  map_zero' := by simp
  map_add' x y := by
    ext <;> simp [add_comm, add_left_comm, add_assoc]

/--
Any finite Nambu block operator decomposes into diagonal + off-diagonal lanes.
-/
@[rep_depth thermo]
theorem nambuBlock_decomposition
    {A : Type*} [AddCommGroup A]
    (a b c d : A →+ A) (v : NambuSpinor A) :
    nambuBlockFull a b c d v = nambuBlockDiag a d v + nambuBlockOffDiag b c v := by
  ext <;> simp [nambuBlockFull, nambuBlockDiag, nambuBlockOffDiag, add_comm, add_left_comm, add_assoc]

/--
Pure diagonal specialization of the full Nambu block.
-/
@[rep_depth thermo]
theorem nambuBlockFull_diag_case
    {A : Type*} [AddCommGroup A]
    (a d : A →+ A) (v : NambuSpinor A) :
    nambuBlockFull a 0 0 d v = nambuBlockDiag a d v := by
  ext <;> simp [nambuBlockFull, nambuBlockDiag]

/--
Pure off-diagonal specialization of the full Nambu block.
-/
@[rep_depth thermo]
theorem nambuBlockFull_offdiag_case
    {A : Type*} [AddCommGroup A]
    (b c : A →+ A) (v : NambuSpinor A) :
    nambuBlockFull 0 b c 0 v = nambuBlockOffDiag b c v := by
  ext <;> simp [nambuBlockFull, nambuBlockOffDiag]

/--
Pointwise square expansion of a full Nambu-Gorkov block.

This is the concrete `2×2` operator composition law separating diagonal and
off-diagonal coupling contributions at second order.
-/
@[rep_depth thermo]
theorem nambuBlockFull_sq_expansion
    {A : Type*} [AddCommGroup A]
    (a b c d : A →+ A) (v : NambuSpinor A) :
    nambuBlockFull a b c d (nambuBlockFull a b c d v)
      =
    (a (a v.1) + a (b v.2) + (b (c v.1) + b (d v.2)),
      c (a v.1) + c (b v.2) + (d (c v.1) + d (d v.2))) := by
  ext <;> simp [nambuBlockFull, add_assoc, add_comm, add_left_comm]

/--
If the pairing channels are pairwise-zero (`b ∘ c = 0`, `c ∘ b = 0`), the full
Nambu square drops the pure off-diagonal round-trip terms.
-/
@[rep_depth thermo]
theorem nambuBlockFull_sq_of_offdiag_pairwise_zero
    {A : Type*} [AddCommGroup A]
    (a b c d : A →+ A)
    (hbc : ∀ x : A, b (c x) = 0)
    (hcb : ∀ x : A, c (b x) = 0)
    (v : NambuSpinor A) :
    nambuBlockFull a b c d (nambuBlockFull a b c d v)
      =
    (a (a v.1) + a (b v.2) + b (d v.2),
      c (a v.1) + d (c v.1) + d (d v.2)) := by
  calc
    nambuBlockFull a b c d (nambuBlockFull a b c d v)
        =
      (a (a v.1) + a (b v.2) + (b (c v.1) + b (d v.2)),
        c (a v.1) + c (b v.2) + (d (c v.1) + d (d v.2))) := by
          simpa using nambuBlockFull_sq_expansion a b c d v
    _ =
      (a (a v.1) + a (b v.2) + b (d v.2),
        c (a v.1) + d (c v.1) + d (d v.2)) := by
          simp [hbc, hcb, add_assoc, add_comm, add_left_comm]

/--
If all mixed couplings and off-diagonal round-trips vanish, the full Nambu
square collapses to pure diagonal second-order dynamics.
-/
@[rep_depth thermo]
theorem nambuBlockFull_sq_pure_diag_of_cross_zero
    {A : Type*} [AddCommGroup A]
    (a b c d : A →+ A)
    (hab : ∀ x : A, a (b x) = 0)
    (hbd : ∀ x : A, b (d x) = 0)
    (hca : ∀ x : A, c (a x) = 0)
    (hdc : ∀ x : A, d (c x) = 0)
    (hbc : ∀ x : A, b (c x) = 0)
    (hcb : ∀ x : A, c (b x) = 0)
    (v : NambuSpinor A) :
    nambuBlockFull a b c d (nambuBlockFull a b c d v)
      = (a (a v.1), d (d v.2)) := by
  calc
    nambuBlockFull a b c d (nambuBlockFull a b c d v)
        =
      (a (a v.1) + a (b v.2) + b (d v.2),
        c (a v.1) + d (c v.1) + d (d v.2)) := by
          exact nambuBlockFull_sq_of_offdiag_pairwise_zero a b c d hbc hcb v
    _ = (a (a v.1), d (d v.2)) := by
          simp [hab, hbd, hca, hdc, add_assoc]

/--
Operator-form collapse of the full Nambu square to a diagonal square under
vanishing mixed/off-diagonal couplings.
-/
@[rep_depth thermo]
theorem nambuBlockFull_sq_eq_diag_comp_of_cross_zero
    {A : Type*} [AddCommGroup A]
    (a b c d : A →+ A)
    (hab : ∀ x : A, a (b x) = 0)
    (hbd : ∀ x : A, b (d x) = 0)
    (hca : ∀ x : A, c (a x) = 0)
    (hdc : ∀ x : A, d (c x) = 0)
    (hbc : ∀ x : A, b (c x) = 0)
    (hcb : ∀ x : A, c (b x) = 0) :
    ∀ v : NambuSpinor A,
      nambuBlockFull a b c d (nambuBlockFull a b c d v)
        = nambuBlockDiag (a.comp a) (d.comp d) v := by
  intro v
  calc
    nambuBlockFull a b c d (nambuBlockFull a b c d v)
        = (a (a v.1), d (d v.2)) := by
          exact nambuBlockFull_sq_pure_diag_of_cross_zero a b c d hab hbd hca hdc hbc hcb v
    _ = nambuBlockDiag (a.comp a) (d.comp d) v := by
          rfl

/--
Finite doubled Nambu--Gorkov operator over additive endomorphisms.

`diag11/diag22` are block-diagonal lanes (Dirac/Weyl-type),
`off12/off21` are off-diagonal lanes (Majorana/pairing-type).
-/
@[rep_depth thermo]
structure NambuGorkovOp (A : Type*) [AddCommGroup A] where
  diag11 : A →+ A
  off12 : A →+ A
  off21 : A →+ A
  diag22 : A →+ A

/-- Realize a `NambuGorkovOp` as a single block operator on doubled spinors. -/
@[rep_depth thermo]
def NambuGorkovOp.toBlockHom
    {A : Type*} [AddCommGroup A]
    (N : NambuGorkovOp A) : NambuSpinor A →+ NambuSpinor A :=
  nambuBlockFull N.diag11 N.off12 N.off21 N.diag22

/--
Pointwise square expansion for the doubled Nambu--Gorkov operator.
-/
@[rep_depth thermo]
theorem NambuGorkovOp.square_apply
    {A : Type*} [AddCommGroup A]
    (N : NambuGorkovOp A) (v : NambuSpinor A) :
    N.toBlockHom (N.toBlockHom v) =
      (N.diag11 (N.diag11 v.1) + N.diag11 (N.off12 v.2)
        + N.off12 (N.off21 v.1) + N.off12 (N.diag22 v.2),
       N.off21 (N.diag11 v.1) + N.off21 (N.off12 v.2)
        + N.diag22 (N.off21 v.1) + N.diag22 (N.diag22 v.2)) := by
  simpa [NambuGorkovOp.toBlockHom, add_assoc] using
    nambuBlockFull_sq_expansion N.diag11 N.off12 N.off21 N.diag22 v

/--
`τ₃` anticommutes with off-diagonal Nambu blocks:
`τ₃ ∘ O = - O ∘ τ₃`.
-/
@[rep_depth thermo]
theorem nambuTau3_offDiag_anticomm
    {A : Type*} [AddCommGroup A]
    (b c : A →+ A) (v : NambuSpinor A) :
    nambuTau3 (nambuBlockOffDiag b c v) =
      - (nambuBlockOffDiag b c (nambuTau3 v)) := by
  ext <;> simp [nambuTau3, nambuBlockOffDiag, add_comm, add_left_comm, add_assoc]

/--
`τ₃` commutes with diagonal Nambu blocks:
`τ₃ ∘ D = D ∘ τ₃`.
-/
@[rep_depth thermo]
theorem nambuTau3_diag_comm
    {A : Type*} [AddCommGroup A]
    (a d : A →+ A) (v : NambuSpinor A) :
    nambuTau3 (nambuBlockDiag a d v) =
      nambuBlockDiag a d (nambuTau3 v) := by
  ext <;> simp [nambuTau3, nambuBlockDiag]

/--
`τ₃` grading split on a full Nambu block:
diagonal part commutes, off-diagonal part anticommutes.
-/
@[rep_depth thermo]
theorem nambuTau3_full_split
    {A : Type*} [AddCommGroup A]
    (a b c d : A →+ A) (v : NambuSpinor A) :
    nambuTau3 (nambuBlockFull a b c d v) =
      nambuBlockDiag a d (nambuTau3 v) - nambuBlockOffDiag b c (nambuTau3 v) := by
  ext <;> simp [nambuTau3, nambuBlockFull, nambuBlockDiag, nambuBlockOffDiag,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/--
Square of an off-diagonal Nambu block is diagonal in the doubled carrier.
-/
@[rep_depth thermo]
theorem nambuBlockOffDiag_sq
    {A : Type*} [AddCommGroup A]
    (b c : A →+ A) (v : NambuSpinor A) :
    nambuBlockOffDiag b c (nambuBlockOffDiag b c v) = (b (c v.1), c (b v.2)) := by
  ext <;> rfl

/--
If `b ∘ c = 0` and `c ∘ b = 0` pointwise, then the off-diagonal Nambu block is
square-zero.
-/
@[rep_depth thermo]
theorem nambuBlockOffDiag_sq_zero_of_pairwise_zero
    {A : Type*} [AddCommGroup A]
    (b c : A →+ A)
    (hbc : ∀ x : A, b (c x) = 0)
    (hcb : ∀ x : A, c (b x) = 0) :
    ∀ v : NambuSpinor A,
      nambuBlockOffDiag b c (nambuBlockOffDiag b c v) = (0, 0) := by
  intro v
  ext <;> simp [nambuBlockOffDiag, hbc, hcb]

/--
Operator-form nilpotence: if `b ∘ c = 0` and `c ∘ b = 0`, then the
off-diagonal Nambu block squares to the zero endomorphism.
-/
@[rep_depth thermo]
theorem nambuBlockOffDiag_sq_zero_hom_of_pairwise_zero
    {A : Type*} [AddCommGroup A]
    (b c : A →+ A)
    (hbc : ∀ x : A, b (c x) = 0)
    (hcb : ∀ x : A, c (b x) = 0) :
    (nambuBlockOffDiag b c).comp (nambuBlockOffDiag b c) = 0 := by
  ext v <;> simp [nambuBlockOffDiag, hbc, hcb]

/--
Off-diagonal Nambu block has nilpotent index at most `2` under pairwise-zero
composition assumptions.
-/
@[rep_depth thermo]
theorem nambuBlockOffDiag_nilpotent_index_two
    {A : Type*} [AddCommGroup A]
    (b c : A →+ A)
    (hbc : ∀ x : A, b (c x) = 0)
    (hcb : ∀ x : A, c (b x) = 0) :
    ∀ v : NambuSpinor A,
      nambuBlockOffDiag b c (nambuBlockOffDiag b c v) = (0, 0) ∧
      nambuBlockOffDiag b c
        (nambuBlockOffDiag b c (nambuBlockOffDiag b c v)) = (0, 0) := by
  intro v
  refine ⟨?h2, ?h3⟩
  · exact nambuBlockOffDiag_sq_zero_of_pairwise_zero b c hbc hcb v
  · rw [nambuBlockOffDiag_sq_zero_of_pairwise_zero b c hbc hcb v]
    simp [nambuBlockOffDiag]

/--
Operator-power stabilization on the off-diagonal Nambu lane.

Under pairwise-zero composition (`b ∘ c = 0`, `c ∘ b = 0`), the off-diagonal
operator satisfies a finite Drazin-style stabilization pattern:
its square and cube are both zero on every vector.
-/
@[rep_depth thermo]
theorem nambuBlockOffDiag_drazin_stabilization
    {A : Type*} [AddCommGroup A]
    (b c : A →+ A)
    (hbc : ∀ x : A, b (c x) = 0)
    (hcb : ∀ x : A, c (b x) = 0) :
    ∀ v : NambuSpinor A,
      let O := nambuBlockOffDiag b c
      O (O v) = (0, 0) ∧ O (O (O v)) = (0, 0) := by
  intro v
  simpa using nambuBlockOffDiag_nilpotent_index_two b c hbc hcb v

/--
Finite `Op^k` stabilization identity for the off-diagonal Nambu operator:
`O^2 v = O^3 v` (both vanish) under pairwise-zero composition.
-/
@[rep_depth thermo]
theorem nambuBlockOffDiag_opk_stabilizes_at_two
    {A : Type*} [AddCommGroup A]
    (b c : A →+ A)
    (hbc : ∀ x : A, b (c x) = 0)
    (hcb : ∀ x : A, c (b x) = 0) :
    ∀ v : NambuSpinor A,
      nambuBlockOffDiag b c (nambuBlockOffDiag b c v)
        =
      nambuBlockOffDiag b c (nambuBlockOffDiag b c (nambuBlockOffDiag b c v)) := by
  intro v
  have h := nambuBlockOffDiag_nilpotent_index_two b c hbc hcb v
  rcases h with ⟨h2, h3⟩
  rw [h3, h2]

/--
Pointwise square expansion for a sum of two endomorphisms on an additive lane.
-/
@[rep_depth thermo]
theorem endo_add_sq_pointwise
    {A : Type*} [AddCommGroup A]
    (b c : A →+ A) (x : A) :
    (b + c) ((b + c) x) = b (b x) + (b (c x) + (c (b x) + c (c x))) := by
  simp [add_assoc, add_comm, add_left_comm]

/--
If two endomorphisms are square-zero and satisfy CAR anticommutation
`b(c x) + c(b x) = x`, then `(b + c)^2 = id` pointwise.
-/
@[rep_depth thermo]
theorem endo_car_sum_sq_id
    {A : Type*} [AddCommGroup A]
    (b c : A →+ A)
    (hbb : ∀ x : A, b (b x) = 0)
    (hcc : ∀ x : A, c (c x) = 0)
    (hcar : ∀ x : A, b (c x) + c (b x) = x) :
    ∀ x : A, (b + c) ((b + c) x) = x := by
  intro x
  calc
    (b + c) ((b + c) x)
        = b (b x) + (b (c x) + (c (b x) + c (c x))) := by
            simpa using endo_add_sq_pointwise b c x
    _ = 0 + (b (c x) + (c (b x) + 0)) := by rw [hbb x, hcc x]
    _ = b (c x) + c (b x) := by abel
    _ = x := hcar x

/--
Square-class trichotomy for additive endomorphisms:
- hyperbolic: `∀ x, T (T x) = x`
- parabolic: `∀ x, T (T x) = 0`
- elliptic: `∀ x, T (T x) = -x`
-/
@[rep_depth thermo]
def hasEndoSquareClass
    {A : Type*} [AddCommGroup A]
    (T : A →+ A) (σ : CKSignature) : Prop :=
  match σ with
  | CKSignature.hyperbolic => ∀ x : A, T (T x) = x
  | CKSignature.parabolic => ∀ x : A, T (T x) = 0
  | CKSignature.elliptic => ∀ x : A, T (T x) = -x

/--
For a CAR nilpotent pair, the sum channel is hyperbolic:
`(b + c)^2 = id`.
-/
@[rep_depth thermo]
theorem endo_car_sum_has_hyperbolic_square
    {A : Type*} [AddCommGroup A]
    (b c : A →+ A)
    (hbb : ∀ x : A, b (b x) = 0)
    (hcc : ∀ x : A, c (c x) = 0)
    (hcar : ∀ x : A, b (c x) + c (b x) = x) :
    hasEndoSquareClass (b + c) CKSignature.hyperbolic := by
  intro x
  simpa [hasEndoSquareClass] using endo_car_sum_sq_id b c hbb hcc hcar x

/--
For a nilpotent pair with pairwise zero composites, the off-diagonal lane is
parabolic: `O^2 = 0`.
-/
@[rep_depth thermo]
theorem nambu_offdiag_has_parabolic_square
    {A : Type*} [AddCommGroup A]
    (b c : A →+ A)
    (hbc : ∀ x : A, b (c x) = 0)
    (hcb : ∀ x : A, c (b x) = 0) :
    hasEndoSquareClass (nambuBlockOffDiag b c) CKSignature.parabolic := by
  intro v
  simpa [hasEndoSquareClass] using
    nambuBlockOffDiag_sq_zero_of_pairwise_zero b c hbc hcb v

/--
For a CAR nilpotent pair, the difference channel is elliptic:
`(b - c)^2 = -id`.
-/
@[rep_depth thermo]
theorem endo_car_diff_sq_neg_id
    {A : Type*} [AddCommGroup A]
    (b c : A →+ A)
    (hbb : ∀ x : A, b (b x) = 0)
    (hcc : ∀ x : A, c (c x) = 0)
    (hcar : ∀ x : A, b (c x) + c (b x) = x) :
    ∀ x : A, (b - c) ((b - c) x) = -x := by
  intro x
  calc
    (b - c) ((b - c) x)
        = b (b x) - b (c x) - c (b x) + c (c x) := by
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ = 0 - b (c x) - c (b x) + 0 := by rw [hbb x, hcc x]
    _ = -(b (c x) + c (b x)) := by abel
    _ = -x := by rw [hcar x]

/--
Endomorphism-level elliptic square for the CAR difference channel:
`(b - c)^2 = -id`.
-/
@[rep_depth thermo]
theorem endo_car_diff_has_elliptic_square
    {A : Type*} [AddCommGroup A]
    (b c : A →+ A)
    (hbb : ∀ x : A, b (b x) = 0)
    (hcc : ∀ x : A, c (c x) = 0)
    (hcar : ∀ x : A, b (c x) + c (b x) = x) :
    hasEndoSquareClass (b - c) CKSignature.elliptic := by
  intro x
  simpa [hasEndoSquareClass] using endo_car_diff_sq_neg_id b c hbb hcc hcar x

/--
For a concrete doubled Nambu--Gorkov operator, if the off-diagonal composites
vanish, then the off-diagonal lane is parabolic.
-/
@[rep_depth thermo]
theorem NambuGorkovOp.offdiag_has_parabolic_square
    {A : Type*} [AddCommGroup A]
    (N : NambuGorkovOp A)
    (h12_21 : ∀ x : A, N.off12 (N.off21 x) = 0)
    (h21_12 : ∀ x : A, N.off21 (N.off12 x) = 0) :
    hasEndoSquareClass (nambuBlockOffDiag N.off12 N.off21) CKSignature.parabolic := by
  exact nambu_offdiag_has_parabolic_square N.off12 N.off21 h12_21 h21_12

/--
Local CAR nilpotent pair recovers the hyperbolic/elliptic split-Majorana lanes:
`(b + c)^2 = id` and `(b - c)^2 = -id`.
-/
@[rep_depth thermo]
theorem majorana_split_square_classes
    {A : Type*} [AddCommGroup A]
    (b c : A →+ A)
    (hbb : ∀ x : A, b (b x) = 0)
    (hcc : ∀ x : A, c (c x) = 0)
    (hcar : ∀ x : A, b (c x) + c (b x) = x) :
    hasEndoSquareClass (b + c) CKSignature.hyperbolic ∧
    hasEndoSquareClass (b - c) CKSignature.elliptic := by
  refine ⟨?_, ?_⟩
  · exact endo_car_sum_has_hyperbolic_square b c hbb hcc hcar
  · exact endo_car_diff_has_elliptic_square b c hbb hcc hcar

/--
Owner-side rigidity theorem on the CAR/Majorana lane:
on a nontrivial space, the hyperbolic channel `(b + c)^2 = id` cannot collapse
to parabolic `(b + c)^2 = 0`.
-/
@[rep_depth thermo]
theorem majorana_plus_not_parabolic_of_nontrivial
    {A : Type*} [AddCommGroup A] [Nontrivial A]
    (b c : A →+ A)
    (hbb : ∀ x : A, b (b x) = 0)
    (hcc : ∀ x : A, c (c x) = 0)
    (hcar : ∀ x : A, b (c x) + c (b x) = x) :
    ¬ hasEndoSquareClass (b + c) CKSignature.parabolic := by
  have hh : hasEndoSquareClass (b + c) CKSignature.hyperbolic :=
    endo_car_sum_has_hyperbolic_square b c hbb hcc hcar
  intro hp
  have h1 : ∀ x : A, (b + c) ((b + c) x) = x := hh
  have h0 : ∀ x : A, (b + c) ((b + c) x) = 0 := hp
  rcases exists_ne (0 : A) with ⟨x, hx⟩
  exact hx ((h1 x).symm.trans (h0 x))

/--
Owner-side CAR rigidity on the Majorana-plus lane, witness-free:
under `NoZeroSMulDivisors ℤ A` and nontriviality, hyperbolic excludes elliptic.
-/
@[rep_depth thermo]
theorem majorana_plus_not_elliptic
    {A : Type*} [AddCommGroup A] [NoZeroSMulDivisors ℤ A] [Nontrivial A]
    (b c : A →+ A)
    (hbb : ∀ x : A, b (b x) = 0)
    (hcc : ∀ x : A, c (c x) = 0)
    (hcar : ∀ x : A, b (c x) + c (b x) = x) :
    ¬ hasEndoSquareClass (b + c) CKSignature.elliptic := by
  intro he
  rcases exists_ne (0 : A) with ⟨x, hx⟩
  have hsum : x + x = 0 := by
    calc
      x + x = ((b + c) ((b + c) x)) + x := by
        rw [(endo_car_sum_has_hyperbolic_square b c hbb hcc hcar) x]
      _ = (-x) + x := by rw [he x]
      _ = 0 := by simp
  have hsmul : (2 : ℤ) • x = 0 := by
    simpa [two_zsmul] using hsum
  have hcase : (2 : ℤ) = 0 ∨ x = 0 :=
    NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero hsmul
  cases hcase with
  | inl h2 =>
      norm_num at h2
  | inr hx0 =>
      exact hx hx0

/--
Closed integer-carrier endpoint (no local assumptions):
on `A = ℤ`, the CAR Majorana-plus hyperbolic lane excludes elliptic collapse.
-/
@[rep_depth thermo]
theorem majorana_plus_not_elliptic_int
    (b c : ℤ →+ ℤ)
    (hbb : ∀ x : ℤ, b (b x) = 0)
    (hcc : ∀ x : ℤ, c (c x) = 0)
    (hcar : ∀ x : ℤ, b (c x) + c (b x) = x) :
    ¬ hasEndoSquareClass (b + c) CKSignature.elliptic := by
  exact majorana_plus_not_elliptic (A := ℤ) b c hbb hcc hcar

/--
Nambu off-diagonal CAR identity at the doubled level:
if both channels satisfy CAR and are square-zero, then the doubled off-diagonal
sum-square acts as identity on each component.
-/
@[rep_depth thermo]
theorem nambu_offdiag_car_sum_sq_id
    {A : Type*} [AddCommGroup A]
    (b c : A →+ A)
    (hbb : ∀ x : A, b (b x) = 0)
    (hcc : ∀ x : A, c (c x) = 0)
    (hcar : ∀ x : A, b (c x) + c (b x) = x) :
    ∀ v : NambuSpinor A,
      ((b + c) ((b + c) v.1), (b + c) ((b + c) v.2)) = v := by
  intro v
  ext <;> simp [endo_car_sum_sq_id, hbb, hcc, hcar]

/--
Concrete Cantor/prime CAR bridge:
the creation/annihilation sum-square is identity on each prime mode.

This is the concrete finite `Nambu/CAR` realization of `(ε + ι)^2 = 1`.
-/
@[rep_depth thermo]
theorem primeCantor_creation_annihilation_sum_sq_id
    {P : InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.PrimeCutoff}
    (p : InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.PrimeMode P)
    (f : InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.CantorField P)
    (S : InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.Vertex P) :
    (InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.annihilationPush p
      (InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.annihilationPush p f
       + InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.creationPush p f) S)
    +
    (InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.creationPush p
      (InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.annihilationPush p f
       + InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.creationPush p f) S)
    = f S := by
  have hsum :
      (InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.annihilationPush p f
        + InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.creationPush p f)
      =
      InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.majoranaPlusPush p f := by
    funext T
    simp [InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.majoranaPlusPush, add_comm]
  rw [hsum]
  simpa [InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.majoranaPlusPush, add_comm]
    using InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.majoranaPlusPush_sq_identity p f S

/--
If a symmetry endomap preserves addition pointwise, then every finite iterate
preserves addition.
-/
@[rep_depth thermo]
theorem iterate_preserves_add
    {A : Type*} [Add A]
    (Φ : A → A)
    (hAdd : ∀ x y : A, Φ (x + y) = Φ x + Φ y) :
    ∀ n : ℕ, ∀ x y : A, iterMap Φ n (x + y) =
      iterMap Φ n x + iterMap Φ n y := by
  intro n
  induction n with
  | zero =>
      intro x y
      rfl
  | succ n ih =>
      intro x y
      simp [iterMap, hAdd, ih]

/--
If a symmetry endomap preserves multiplication pointwise, then every finite
iterate preserves multiplication.
-/
@[rep_depth thermo]
theorem iterate_preserves_mul
    {A : Type*} [Mul A]
    (Φ : A → A)
    (hMul : ∀ x y : A, Φ (x * y) = Φ x * Φ y) :
    ∀ n : ℕ, ∀ x y : A, iterMap Φ n (x * y) =
      iterMap Φ n x * iterMap Φ n y := by
  intro n
  induction n with
  | zero =>
      intro x y
      rfl
  | succ n ih =>
      intro x y
      simp [iterMap, hMul, ih]

/--
If an iterate-chain map preserves multiplication and fixes a constant `κ`,
then the square-law `x² = κ` is stable at every finite depth.
-/
@[rep_depth thermo]
theorem iterate_preserves_square_class_const
    {A : Type*} [Mul A]
    (Φ : A → A)
    (hMul : ∀ x y : A, Φ (x * y) = Φ x * Φ y)
    (κ : A)
    (hκ : Φ κ = κ)
    {x : A}
    (hx : x * x = κ) :
    ∀ n : ℕ, (iterMap Φ n x) * (iterMap Φ n x) = κ := by
  intro n
  induction n with
  | zero =>
      simpa [iterMap] using hx
  | succ n ih =>
      calc
        (iterMap Φ (n + 1) x) * (iterMap Φ (n + 1) x)
            = Φ ((iterMap Φ n x) * (iterMap Φ n x)) := by
                simp [iterMap, hMul]
        _ = Φ κ := by rw [ih]
        _ = κ := hκ

/-- `N=2` square-law checkpoint along the inductive/tensor chain. -/
@[rep_depth thermo]
theorem iterate_square_class_const_N2
    {A : Type*} [Mul A]
    (Φ : A → A)
    (hMul : ∀ x y : A, Φ (x * y) = Φ x * Φ y)
    (κ : A)
    (hκ : Φ κ = κ)
    {x : A}
    (hx : x * x = κ) :
    (iterMap Φ 2 x) * (iterMap Φ 2 x) = κ := by
  simpa using iterate_preserves_square_class_const Φ hMul κ hκ hx 2

/-- `N=4` square-law checkpoint along the inductive/tensor chain. -/
@[rep_depth thermo]
theorem iterate_square_class_const_N4
    {A : Type*} [Mul A]
    (Φ : A → A)
    (hMul : ∀ x y : A, Φ (x * y) = Φ x * Φ y)
    (κ : A)
    (hκ : Φ κ = κ)
    {x : A}
    (hx : x * x = κ) :
    (iterMap Φ 4 x) * (iterMap Φ 4 x) = κ := by
  simpa using iterate_preserves_square_class_const Φ hMul κ hκ hx 4

/-- `N=8` square-law checkpoint along the inductive/tensor chain. -/
@[rep_depth thermo]
theorem iterate_square_class_const_N8
    {A : Type*} [Mul A]
    (Φ : A → A)
    (hMul : ∀ x y : A, Φ (x * y) = Φ x * Φ y)
    (κ : A)
    (hκ : Φ κ = κ)
    {x : A}
    (hx : x * x = κ) :
    (iterMap Φ 8 x) * (iterMap Φ 8 x) = κ := by
  simpa using iterate_preserves_square_class_const Φ hMul κ hκ hx 8

/-- Hyperbolic lane (`κ = 1`) is stable at depth `N=2`. -/
@[rep_depth thermo]
theorem iterate_square_one_N2
    {A : Type*} [MulOneClass A]
    (Φ : A → A)
    (hMul : ∀ x y : A, Φ (x * y) = Φ x * Φ y)
    (h1 : Φ (1 : A) = 1)
    {x : A}
    (hx : x * x = (1 : A)) :
    (iterMap Φ 2 x) * (iterMap Φ 2 x) = (1 : A) := by
  simpa using iterate_square_class_const_N2 Φ hMul (1 : A) h1 hx

/-- Hyperbolic lane (`κ = 1`) is stable at depth `N=4`. -/
@[rep_depth thermo]
theorem iterate_square_one_N4
    {A : Type*} [MulOneClass A]
    (Φ : A → A)
    (hMul : ∀ x y : A, Φ (x * y) = Φ x * Φ y)
    (h1 : Φ (1 : A) = 1)
    {x : A}
    (hx : x * x = (1 : A)) :
    (iterMap Φ 4 x) * (iterMap Φ 4 x) = (1 : A) := by
  simpa using iterate_square_class_const_N4 Φ hMul (1 : A) h1 hx

/-- Hyperbolic lane (`κ = 1`) is stable at depth `N=8`. -/
@[rep_depth thermo]
theorem iterate_square_one_N8
    {A : Type*} [MulOneClass A]
    (Φ : A → A)
    (hMul : ∀ x y : A, Φ (x * y) = Φ x * Φ y)
    (h1 : Φ (1 : A) = 1)
    {x : A}
    (hx : x * x = (1 : A)) :
    (iterMap Φ 8 x) * (iterMap Φ 8 x) = (1 : A) := by
  simpa using iterate_square_class_const_N8 Φ hMul (1 : A) h1 hx

/-- Parabolic lane (`κ = 0`) is stable at depth `N=2`. -/
@[rep_depth thermo]
theorem iterate_square_zero_N2
    {A : Type*} [MulZeroOneClass A]
    (Φ : A → A)
    (hMul : ∀ x y : A, Φ (x * y) = Φ x * Φ y)
    (h0 : Φ (0 : A) = 0)
    {x : A}
    (hx : x * x = (0 : A)) :
    (iterMap Φ 2 x) * (iterMap Φ 2 x) = (0 : A) := by
  simpa using iterate_square_class_const_N2 Φ hMul (0 : A) h0 hx

/-- Parabolic lane (`κ = 0`) is stable at depth `N=4`. -/
@[rep_depth thermo]
theorem iterate_square_zero_N4
    {A : Type*} [MulZeroOneClass A]
    (Φ : A → A)
    (hMul : ∀ x y : A, Φ (x * y) = Φ x * Φ y)
    (h0 : Φ (0 : A) = 0)
    {x : A}
    (hx : x * x = (0 : A)) :
    (iterMap Φ 4 x) * (iterMap Φ 4 x) = (0 : A) := by
  simpa using iterate_square_class_const_N4 Φ hMul (0 : A) h0 hx

/-- Parabolic lane (`κ = 0`) is stable at depth `N=8`. -/
@[rep_depth thermo]
theorem iterate_square_zero_N8
    {A : Type*} [MulZeroOneClass A]
    (Φ : A → A)
    (hMul : ∀ x y : A, Φ (x * y) = Φ x * Φ y)
    (h0 : Φ (0 : A) = 0)
    {x : A}
    (hx : x * x = (0 : A)) :
    (iterMap Φ 8 x) * (iterMap Φ 8 x) = (0 : A) := by
  simpa using iterate_square_class_const_N8 Φ hMul (0 : A) h0 hx

/-- Elliptic lane (`κ = -1`) is stable at depth `N=2`. -/
@[rep_depth thermo]
theorem iterate_square_neg_one_N2
    {A : Type*} [Ring A]
    (Φ : A → A)
    (hMul : ∀ x y : A, Φ (x * y) = Φ x * Φ y)
    (hneg1 : Φ (-(1 : A)) = -(1 : A))
    {x : A}
    (hx : x * x = (-(1 : A))) :
    (iterMap Φ 2 x) * (iterMap Φ 2 x) = (-(1 : A)) := by
  simpa using iterate_square_class_const_N2 Φ hMul (-(1 : A)) hneg1 hx

/-- Elliptic lane (`κ = -1`) is stable at depth `N=4`. -/
@[rep_depth thermo]
theorem iterate_square_neg_one_N4
    {A : Type*} [Ring A]
    (Φ : A → A)
    (hMul : ∀ x y : A, Φ (x * y) = Φ x * Φ y)
    (hneg1 : Φ (-(1 : A)) = -(1 : A))
    {x : A}
    (hx : x * x = (-(1 : A))) :
    (iterMap Φ 4 x) * (iterMap Φ 4 x) = (-(1 : A)) := by
  simpa using iterate_square_class_const_N4 Φ hMul (-(1 : A)) hneg1 hx

/-- Elliptic lane (`κ = -1`) is stable at depth `N=8`. -/
@[rep_depth thermo]
theorem iterate_square_neg_one_N8
    {A : Type*} [Ring A]
    (Φ : A → A)
    (hMul : ∀ x y : A, Φ (x * y) = Φ x * Φ y)
    (hneg1 : Φ (-(1 : A)) = -(1 : A))
    {x : A}
    (hx : x * x = (-(1 : A))) :
    (iterMap Φ 8 x) * (iterMap Φ 8 x) = (-(1 : A)) := by
  simpa using iterate_square_class_const_N8 Φ hMul (-(1 : A)) hneg1 hx

/--
Bundled `N=2/4/8` trichotomy checkpoints along a multiplicative inductive chain.
-/
@[rep_depth thermo]
theorem iterate_square_trichotomy_bundle_N2_N4_N8
    {A : Type*} [Ring A]
    (Φ : A → A)
    (hMul : ∀ x y : A, Φ (x * y) = Φ x * Φ y)
    (h1 : Φ (1 : A) = 1)
    (h0 : Φ (0 : A) = 0)
    (hneg1 : Φ (-(1 : A)) = -(1 : A))
    {xh xp xe : A}
    (hh : xh * xh = (1 : A))
    (hp : xp * xp = (0 : A))
    (he : xe * xe = (-(1 : A))) :
    ((iterMap Φ 2 xh) * (iterMap Φ 2 xh) = (1 : A)) ∧
    ((iterMap Φ 4 xh) * (iterMap Φ 4 xh) = (1 : A)) ∧
    ((iterMap Φ 8 xh) * (iterMap Φ 8 xh) = (1 : A)) ∧
    ((iterMap Φ 2 xp) * (iterMap Φ 2 xp) = (0 : A)) ∧
    ((iterMap Φ 4 xp) * (iterMap Φ 4 xp) = (0 : A)) ∧
    ((iterMap Φ 8 xp) * (iterMap Φ 8 xp) = (0 : A)) ∧
    ((iterMap Φ 2 xe) * (iterMap Φ 2 xe) = (-(1 : A))) ∧
    ((iterMap Φ 4 xe) * (iterMap Φ 4 xe) = (-(1 : A))) ∧
    ((iterMap Φ 8 xe) * (iterMap Φ 8 xe) = (-(1 : A))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact iterate_square_one_N2 Φ hMul h1 hh
  · exact iterate_square_one_N4 Φ hMul h1 hh
  · exact iterate_square_one_N8 Φ hMul h1 hh
  · exact iterate_square_zero_N2 Φ hMul h0 hp
  · exact iterate_square_zero_N4 Φ hMul h0 hp
  · exact iterate_square_zero_N8 Φ hMul h0 hp
  · exact iterate_square_neg_one_N2 Φ hMul hneg1 he
  · exact iterate_square_neg_one_N4 Φ hMul hneg1 he
  · exact iterate_square_neg_one_N8 Φ hMul hneg1 he

/--
Finite inductive-chain stability of the `N=2` odd--odd closure split.

If a symmetry endomap `Φ` preserves `+` and `*`, and fixes the even Hamiltonian
and central lanes, then the relation
`{Q₁,Q₂} = H₁₂ + Z₁₂`
is preserved at every finite stage of the iterated chain.
-/
@[rep_depth thermo]
theorem n2_supercharge_split_stable_along_iterate
    {A : Type*} [Ring A]
    (Φ : A → A)
    (hAdd : ∀ x y : A, Φ (x + y) = Φ x + Φ y)
    (hMul : ∀ x y : A, Φ (x * y) = Φ x * Φ y)
    {Q₁ Q₂ H₁₂ Z₁₂ : A}
    (hsplit : Q₁ * Q₂ + Q₂ * Q₁ = H₁₂ + Z₁₂)
    (hHfix : Φ H₁₂ = H₁₂)
    (hZfix : Φ Z₁₂ = Z₁₂) :
    ∀ n : ℕ,
      (iterMap Φ n Q₁) * (iterMap Φ n Q₂)
        + (iterMap Φ n Q₂) * (iterMap Φ n Q₁)
        = H₁₂ + Z₁₂ := by
  intro n
  induction n with
  | zero =>
      simpa using hsplit
  | succ n ih =>
      have hStep := duality_transports_n2_supercharge_split
        (Dual := Φ) (hAdd := hAdd) (hMul := hMul)
        (Q₁ := iterMap Φ n Q₁)
        (Q₂ := iterMap Φ n Q₂)
        (H₁₂ := H₁₂) (Z₁₂ := Z₁₂)
        (H'₁₂ := H₁₂) (Z'₁₂ := Z₁₂)
        ih hHfix hZfix
      simpa [iterMap] using hStep

/--
Finite Bott-style tensor tower size recursion:
each added local `Cl(1,1) ≃ M₂(ℝ)` cell doubles the linear size.
-/
@[rep_depth thermo]
theorem bott_tensor_size_step (N : ℕ) :
    2 ^ (N + 1) = 2 ^ N * 2 := by
  simpa [pow_succ, Nat.mul_comm] using (pow_succ 2 N)

/--
`N` local `Cl(1,1)` cells correspond to matrix size `2^N`.

This is the arithmetic size lane behind
`Cl(1,1)^{⊗ N} ~ M_{2^N}(ℝ)`.
-/
@[rep_depth thermo]
theorem cl11_tensor_matrix_size (N : ℕ) :
    (2 ^ N : ℕ) = 2 ^ N := rfl

/-- `N=2` checkpoint: size `4`. -/
@[rep_depth thermo]
theorem cl11_tensor_matrix_size_N2 :
    (2 ^ 2 : ℕ) = 4 := by decide

/-- `N=4` checkpoint: size `16`. -/
@[rep_depth thermo]
theorem cl11_tensor_matrix_size_N4 :
    (2 ^ 4 : ℕ) = 16 := by decide

/-- `N=8` checkpoint: size `256`. -/
@[rep_depth thermo]
theorem cl11_tensor_matrix_size_N8 :
    (2 ^ 8 : ℕ) = 256 := by decide

/--
Finite central-lane cutoff sum (pairwise odd--odd bracket sum).

This is the theorem-safe finite object:
`Z_N = ∑_{i<j≤N} z(i,j)` represented over `Finset`.
-/
@[rep_depth thermo]
theorem finite_central_lane_cutoff_def
    {A : Type*} [AddCommMonoid A]
    (N : ℕ)
    (z : ℕ → ℕ → A) :
    Finset.sum (Finset.range (N + 1))
        (fun i => Finset.sum (Finset.Icc (i + 1) N) (fun j => z i j))
      =
    Finset.sum (Finset.range (N + 1))
        (fun i => Finset.sum (Finset.Icc (i + 1) N) (fun j => z i j)) := rfl

/--
Finite tensor-size composition law for the Bott/tensor tower:
`2^(N+M) = 2^N * 2^M`.
-/
@[rep_depth thermo]
theorem bott_tensor_size_add (N M : ℕ) :
    2 ^ (N + M) = (2 ^ N) * (2 ^ M) := by
  simpa using Nat.pow_add 2 N M

/--
Finite central-lane recurrence (cutoff extension by one level).

The `N+1` cutoff equals the old cutoff `N` plus all new pairs ending at `N+1`.
-/
@[rep_depth thermo]
theorem finite_central_lane_cutoff_succ
    {A : Type*} [AddCommMonoid A]
    (N : ℕ)
    (z : ℕ → ℕ → A) :
    (Finset.sum (Finset.range (N + 2))
      (fun i => Finset.sum (Finset.Icc (i + 1) (N + 1)) (fun j => z i j)))
      =
    (Finset.sum (Finset.range (N + 1))
      (fun i => Finset.sum (Finset.Icc (i + 1) N) (fun j => z i j)))
      +
    (Finset.sum (Finset.range (N + 1)) (fun i => z i (N + 1))) := by
  calc
    Finset.sum (Finset.range (N + 2))
        (fun i => Finset.sum (Finset.Icc (i + 1) (N + 1)) (fun j => z i j))
      =
        Finset.sum (Finset.range (N + 1))
          (fun i => Finset.sum (Finset.Icc (i + 1) (N + 1)) (fun j => z i j)) := by
          rw [Finset.sum_range_succ]
          simp
    _ =
        Finset.sum (Finset.range (N + 1))
          (fun i => Finset.sum (Finset.Icc (i + 1) N) (fun j => z i j) + z i (N + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hiLe : i + 1 ≤ N + 1 := Nat.succ_le_succ (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
          have hIccInsert : insert (N + 1) (Finset.Icc (i + 1) N) = Finset.Icc (i + 1) (N + 1) :=
            Finset.insert_Icc_right_eq_Icc_add_one hiLe
          have hnotMem : (N + 1) ∉ Finset.Icc (i + 1) N := by simp
          calc
            Finset.sum (Finset.Icc (i + 1) (N + 1)) (fun j => z i j)
              =
                Finset.sum (insert (N + 1) (Finset.Icc (i + 1) N)) (fun j => z i j) := by
                  rw [hIccInsert]
            _ =
                Finset.sum (Finset.Icc (i + 1) N) (fun j => z i j) + z i (N + 1) := by
                  rw [Finset.sum_insert hnotMem]
                  simp [add_comm, add_left_comm, add_assoc]
    _ =
        (Finset.sum (Finset.range (N + 1))
          (fun i => Finset.sum (Finset.Icc (i + 1) N) (fun j => z i j)))
        +
        (Finset.sum (Finset.range (N + 1)) (fun i => z i (N + 1))) := by
          rw [Finset.sum_add_distrib]

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Xc" => InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore E
local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
Repo-specific unified supercharge package.

This fuses:
1. primitive doubled-carrier supercharges `(QΠ, QJ)`,
2. transported supercharges on the quasilattice lane,
3. projected Drazin/Penrose odd supercharge `QD`,
4. and the external topological central charge lane.
-/
@[rep_depth transport]
structure UnifiedSuperchargePackage where
  primitive : InfoGeometry.Quantum.SuperchargeMultiplet (E := E)
  kernel : CertifiedInverseKernel H₂

namespace UnifiedSuperchargePackage

variable (U : UnifiedSuperchargePackage (E := E))

/-- Primitive parity/triality supercharge `QΠ`. -/
abbrev QPi : Xc →ₗ[ℝ] Xc := U.primitive.parity.Q

/-- Primitive modular supercharge `QJ`. -/
abbrev QJ : H₂ →L[ℝ] H₂ := U.primitive.modular.Q

/-- Primitive phase channel `K = QΠ QJ = J ε`. -/
noncomputable abbrev phaseChannel : Xc →ₗ[ℝ] Xc := U.primitive.phaseChannel

/-- Projected Drazin odd supercharge `QD = χ_R - χ_L`. -/
noncomputable abbrev QD : EndH :=
  InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge U.kernel

/-- Projected left chiral supercharge `Q_L = χ_L = [P_D, P_L]`. -/
noncomputable abbrev QL : EndH := U.kernel.chiralAnomaly

/-- Projected right chiral supercharge `Q_R = χ_R = [P_D, P_R]`. -/
noncomputable abbrev QR : EndH := U.kernel.rightChiralAnomaly

/-- Projected Drazin spectral projector `P_D`. -/
noncomputable abbrev PD : EndH := U.kernel.spectralProjector

/-- Projected Moore–Penrose left projector `P_L`. -/
noncomputable abbrev PL : EndH := U.kernel.metricProjector

/-- Projected Moore–Penrose right projector `P_R`. -/
noncomputable abbrev PR : EndH := U.kernel.mpRangeProjector

/-- Projected Drazin even Hamiltonian candidate `HD = QD²`. -/
noncomputable abbrev HD : EndH :=
  InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK U.kernel

/-- Spectral grading of the projected lane. -/
noncomputable abbrev GammaS : EndH := U.kernel.toInformationCartanTriple.GammaS

/-- Primitive parity/modular anticommutator vanishes. -/
theorem primitive_anticommutator_eq_zero :
    InfoGeometry.Quantum.RealMajoranaCategory.anticommutator
      (QPi U) ((QJ U).toLinearMap) = 0 := by
  exact InfoGeometry.Quantum.SuperchargeMultiplet.parity_modular_anticommutator_eq_zero
    (E := E) U.primitive

/-- Primitive phase channel as the internal doubled real phase axis `K = J ∘ ε`. -/
theorem primitive_phaseChannel_eq_phaseAxis :
    phaseChannel U =
      ((modular_j (E := E)).toLinearMap).comp ((spectral_epsilon (E := E)).toLinearMap) := by
  have hComplex :
      phaseChannel U = (complex_i (E := E)).toLinearMap := by
    exact InfoGeometry.Quantum.SuperchargeMultiplet.phaseChannel_eq_complexI
      (E := E) U.primitive
  calc
    phaseChannel U = (complex_i (E := E)).toLinearMap := hComplex
    _ =
      ((modular_j (E := E)).toLinearMap).comp ((spectral_epsilon (E := E)).toLinearMap) := by
        rfl

/--
Legacy compatibility alias:
the internal phase axis `K = J ∘ ε` coincides with the historical `complex_i`
surface.
-/
theorem primitive_phaseChannel_eq_complexI :
    phaseChannel U = (complex_i (E := E)).toLinearMap := by
  exact InfoGeometry.Quantum.SuperchargeMultiplet.phaseChannel_eq_complexI
    (E := E) U.primitive

/-- Primitive phase channel squares to `-Id`. -/
theorem primitive_phaseChannel_sq_eq_neg_id :
    (phaseChannel U).comp (phaseChannel U) = -((LinearMap.id : Xc →ₗ[ℝ] Xc)) := by
  exact InfoGeometry.Quantum.SuperchargeMultiplet.phaseChannel_sq_eq_neg_id
    (E := E) U.primitive

/-- The projected supercharge is odd in the Drazin spectral grading. -/
theorem projected_supercharge_is_odd :
    InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK (GammaS U) (QD U) = 0 := by
  simpa [QD, GammaS] using
    (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge_is_oddK
      (CIK := U.kernel))

/-- The projected kinetic operator is even/compact in the Drazin grading. -/
theorem projected_hamiltonian_is_even :
    let T := U.kernel.toInformationCartanTriple
    T.IsSpectralCompact (HD U) := by
  simpa [HD] using
    (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK_isSpectralCompact
      (CIK := U.kernel))

/-- The projected supercharge admits the exact dilation-gap commutator presentation. -/
theorem projected_supercharge_eq_two_commutator :
    QD U = (2 : ℝ) •
      InfoGeometry.Canonical.DrazinSupercharge.commutatorK U.kernel.spectralProjector U.kernel.dilationGap := by
  simpa [QD] using
    (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge_eq_two_smul_commutatorK_spectralProjector_dilationGap
      (CIK := U.kernel))

/-- Projected right/left decomposition `Q_D = Q_R - Q_L`. -/
theorem projected_supercharge_eq_sub_chiral :
    QD U = QR U - QL U := by
  rfl

/-- Left projected supercharge as commutator `[P_D, P_L]`. -/
theorem projected_left_eq_commutator_PD_PL :
    QL U =
      InfoGeometry.Canonical.DrazinSupercharge.commutator (PD U) (PL U) := by
  rfl

/-- Right projected supercharge as commutator `[P_D, P_R]`. -/
theorem projected_right_eq_commutator_PD_PR :
    QR U =
      InfoGeometry.Canonical.DrazinSupercharge.commutator (PD U) (PR U) := by
  rfl

/-- Projected even Hamiltonian as a square `H_D = Q_D²`. -/
theorem projected_hamiltonian_eq_square :
    HD U = (QD U) * (QD U) := by
  rfl

/--
Scaled kinetic lane extracted from the projected odd-odd Drazin bracket.

This is the repo-native translation candidate on the chiral-charge / Drazin lane:
the canonical kinetic remainder in the internal split of `Q_D²`.
-/
@[rep_depth transport]
noncomputable def drazinTranslationCandidate : EndH :=
  InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPartK U.kernel

/--
The repo-owned Drazin translation candidate is spectrally compact on the
current owner slice.

This follows because it is the canonical kinetic remainder inside the even
superHamiltonian split, and both the full superHamiltonian and the defect
compression commute with the spectral grading `Γ_S`.
-/
@[rep_depth transport, capstone]
theorem drazinTranslationCandidate_isSpectralCompact :
    U.kernel.IsSpectralCompact (drazinTranslationCandidate U) := by
  rw [InfoGeometry.Canonical.CertifiedInverseKernel.isSpectralCompact_iff_commute_GammaS
    (CIK := U.kernel) (X := drazinTranslationCandidate U)]
  have hSH :
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK U.kernel
        * U.kernel.GammaS
        =
      U.kernel.GammaS
        * InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK U.kernel := by
    exact
      (InfoGeometry.Canonical.CertifiedInverseKernel.isSpectralCompact_iff_commute_GammaS
        (CIK := U.kernel)
        (X := InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK U.kernel)).1
        (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK_isSpectralCompact
          (CIK := U.kernel))
  have hZ :
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK U.kernel
        * U.kernel.GammaS
        =
      U.kernel.GammaS
        * InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK U.kernel := by
    exact
      (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK_isDrazinLaneCentralK
        (CIK := U.kernel)).2.eq
  unfold drazinTranslationCandidate
  change
      (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPart U.kernel)
        * U.kernel.GammaS
        =
      U.kernel.GammaS
        * (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPart U.kernel)
  unfold InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPart
  calc
    (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonian U.kernel
        - InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentral U.kernel)
        * U.kernel.GammaS
      =
        InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK U.kernel
          * U.kernel.GammaS
          -
        InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK U.kernel
          * U.kernel.GammaS := by
            simp [sub_mul, InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK,
              InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK]
    _ =
        U.kernel.GammaS
          * InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK U.kernel
          -
        U.kernel.GammaS
          * InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK U.kernel := by
            rw [hSH, hZ]
    _ =
        U.kernel.GammaS
          * (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonian U.kernel
              - InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentral U.kernel) := by
            simp [InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK,
              InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK,
              sub_eq_add_neg, mul_add]

/--
Scaled central lane carried by the KKT notation `Z_D`.

We package the odd-odd bracket in the direct form
`{Q_D, Q_D} = 2 • translationCandidate + centralCandidate`,
so the central candidate is stored with the factor of `2` absorbed.
-/
@[rep_depth transport]
noncomputable def drazinCentralCandidate : EndH :=
  (2 : ℝ) • InfoGeometry.Canonical.KKTClosure.ZD U.kernel

/--
Scaled defect-supported channel on the direct Drazin owner lane.

This is definitionally the same channel as the KKT-side central candidate,
written in the underlying Drazin owner vocabulary.
-/
@[rep_depth transport]
noncomputable def drazinDefectCandidate : EndH :=
  (2 : ℝ) •
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK U.kernel

/-- KKT-central and direct Drazin-defect channels coincide definitionally. -/
@[rep_depth transport]
theorem drazinCentralCandidate_eq_defectCandidate :
    drazinCentralCandidate U = drazinDefectCandidate U := by
  rfl

/--
Projected odd-odd Drazin bracket in repo-native split form:
`{Q_D, Q_D} = 2 • translationCandidate + centralCandidate`.
-/
@[rep_depth transport, capstone]
theorem projected_oddOdd_bracket_eq_two_smul_translation_plus_central :
    InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK (QD U) (QD U)
      = (2 : ℝ) • drazinTranslationCandidate U + drazinCentralCandidate U := by
  calc
    InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK (QD U) (QD U)
        = (2 : ℝ) • (HD U) := by
            simp [InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK,
              InfoGeometry.Canonical.DrazinSupercharge.anticommutator,
              QD, HD, two_smul,
              InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK,
              InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonian]
    _ = (2 : ℝ) •
          (drazinTranslationCandidate U
            + InfoGeometry.Canonical.KKTClosure.ZD U.kernel) := by
          have hSplit :=
            InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK_eq_canonicalKineticPartK_plus_canonicalDefectCentralK
              (CIK := U.kernel)
          exact congrArg (fun X => (2 : ℝ) • X) (by simpa [HD, drazinTranslationCandidate, InfoGeometry.Canonical.KKTClosure.ZD] using hSplit)
    _ = (2 : ℝ) • drazinTranslationCandidate U + drazinCentralCandidate U := by
          simp [drazinCentralCandidate, smul_add]

/--
Central term extracted from the projected odd-odd Drazin bracket.

This is the finite N=2-style closure readout:
`Z_D = {Q_D,Q_D} - 2P_D`.

It is an algebraic consequence of the already-owned projected odd-odd bracket
split, not a new wrapper.
-/
@[rep_depth transport]
theorem drazinCentralCandidate_eq_oddOdd_bracket_sub_two_smul_translation :
    drazinCentralCandidate U =
      InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK (QD U) (QD U)
        - (2 : ℝ) • drazinTranslationCandidate U := by
  rw [projected_oddOdd_bracket_eq_two_smul_translation_plus_central (U := U)]
  abel

/--
Defect-supported central term extracted from the projected odd-odd Drazin
bracket.
-/
@[rep_depth transport]
theorem drazinDefectCandidate_eq_oddOdd_bracket_sub_two_smul_translation :
    drazinDefectCandidate U =
      InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK (QD U) (QD U)
        - (2 : ℝ) • drazinTranslationCandidate U := by
  rw [← drazinCentralCandidate_eq_defectCandidate (U := U)]
  exact drazinCentralCandidate_eq_oddOdd_bracket_sub_two_smul_translation (U := U)

/--
Equivalent defect-language readout of the same odd-odd Drazin bracket.
-/
@[rep_depth transport]
theorem projected_oddOdd_bracket_eq_two_smul_translation_plus_defect :
    InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK (QD U) (QD U)
      = (2 : ℝ) • drazinTranslationCandidate U + drazinDefectCandidate U := by
  rw [projected_oddOdd_bracket_eq_two_smul_translation_plus_central (U := U)]
  rw [drazinCentralCandidate_eq_defectCandidate]

/--
Best available repo-native paired odd candidate on the Drazin lane.

At present this is a Majorana-conjugate witness rather than a fully independent
owner-defined `Q̄_D`: it is `Q_D` viewed through the Majorana fixed-sector bridge.
-/
@[rep_depth transport]
noncomputable def drazinMajoranaConjugateCandidate : EndH :=
  QD U

/--
Under Majorana compatibility with both anomaly channels, the current paired odd
candidate collapses to the owned Drazin supercharge itself.
-/
@[rep_depth transport]
theorem drazinMajoranaConjugateCandidate_eq_QD_of_commute_chi
    (M : InfoGeometry.Canonical.HestenesRealStructures.MajoranaRealStructure (E := E))
    (_hCL : Commute M.C (U.kernel.chiralAnomaly))
    (_hCR : Commute M.C (U.kernel.rightChiralAnomaly)) :
    drazinMajoranaConjugateCandidate U = QD U := by
  rfl

/--
For the current Majorana-paired candidate, the paired odd-odd bracket reduces to
the already owned self-bracket of `Q_D`.
-/
@[rep_depth transport]
theorem paired_oddOdd_majoranaBracket_eq_selfBracket_of_commute_chi
    (M : InfoGeometry.Canonical.HestenesRealStructures.MajoranaRealStructure (E := E))
    (hCL : Commute M.C (U.kernel.chiralAnomaly))
    (hCR : Commute M.C (U.kernel.rightChiralAnomaly)) :
    InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK
        (QD U) (drazinMajoranaConjugateCandidate U)
      =
    InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK (QD U) (QD U) := by
  rw [drazinMajoranaConjugateCandidate_eq_QD_of_commute_chi (U := U) (M := M) hCL hCR]

/--
Conditional paired-bracket translation/central readout.

This is the strongest current owner-safe statement: once the paired odd candidate
is identified with `Q_D` through the Majorana-compatible anomaly corridor, the
paired bracket inherits the already proved Drazin split.
-/
@[rep_depth transport]
theorem paired_oddOdd_majoranaBracket_eq_two_smul_translation_plus_central_of_commute_chi
    (M : InfoGeometry.Canonical.HestenesRealStructures.MajoranaRealStructure (E := E))
    (hCL : Commute M.C (U.kernel.chiralAnomaly))
    (hCR : Commute M.C (U.kernel.rightChiralAnomaly)) :
    InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK
        (QD U) (drazinMajoranaConjugateCandidate U)
      =
    (2 : ℝ) • drazinTranslationCandidate U + drazinCentralCandidate U := by
  rw [paired_oddOdd_majoranaBracket_eq_selfBracket_of_commute_chi (U := U) (M := M) hCL hCR]
  exact projected_oddOdd_bracket_eq_two_smul_translation_plus_central (U := U)

/--
Central term extracted from the Majorana-compatible paired odd-odd bracket.
-/
@[rep_depth transport]
theorem drazinCentralCandidate_eq_paired_majoranaBracket_sub_two_smul_translation_of_commute_chi
    (M : InfoGeometry.Canonical.HestenesRealStructures.MajoranaRealStructure (E := E))
    (hCL : Commute M.C (U.kernel.chiralAnomaly))
    (hCR : Commute M.C (U.kernel.rightChiralAnomaly)) :
    drazinCentralCandidate U =
      InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK
          (QD U) (drazinMajoranaConjugateCandidate U)
        - (2 : ℝ) • drazinTranslationCandidate U := by
  rw [paired_oddOdd_majoranaBracket_eq_two_smul_translation_plus_central_of_commute_chi
    (U := U) (M := M) hCL hCR]
  abel

/--
Equivalent defect-language version of the conditional paired-bracket readout.
-/
@[rep_depth transport]
theorem paired_oddOdd_majoranaBracket_eq_two_smul_translation_plus_defect_of_commute_chi
    (M : InfoGeometry.Canonical.HestenesRealStructures.MajoranaRealStructure (E := E))
    (hCL : Commute M.C (U.kernel.chiralAnomaly))
    (hCR : Commute M.C (U.kernel.rightChiralAnomaly)) :
    InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK
        (QD U) (drazinMajoranaConjugateCandidate U)
      =
    (2 : ℝ) • drazinTranslationCandidate U + drazinDefectCandidate U := by
  rw [paired_oddOdd_majoranaBracket_eq_selfBracket_of_commute_chi (U := U) (M := M) hCL hCR]
  exact projected_oddOdd_bracket_eq_two_smul_translation_plus_defect (U := U)

/--
Nontrivial Kramers-conjugated odd candidate on the Drazin lane.

Unlike the Majorana witness above, this really uses an external symmetry action:
`Θ * Q_D * Θ`.
-/
@[rep_depth transport]
noncomputable def drazinKramersConjugateCandidate
    (S : InfoGeometry.Canonical.HestenesRealStructures.KramersSymmetry (E := E)) : EndH :=
  S.Θ * QD U * S.Θ

/-- Paired odd-odd bracket using the Kramers-conjugated Drazin candidate. -/
@[rep_depth transport]
noncomputable def pairedOddOddKramersBracket
    (S : InfoGeometry.Canonical.HestenesRealStructures.KramersSymmetry (E := E)) : EndH :=
  InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK
    (QD U) (drazinKramersConjugateCandidate U S)

/--
If the Kramers symmetry commutes with `Γ_S`, the Kramers-conjugated Drazin odd
candidate remains odd.
-/
@[rep_depth transport, capstone]
theorem drazinKramersConjugateCandidate_is_odd_of_commute_GammaS
    (S : InfoGeometry.Canonical.HestenesRealStructures.KramersSymmetry (E := E))
    (hThetaGamma : Commute S.Θ (GammaS U)) :
    InfoGeometry.Canonical.DrazinSupercharge.anticommutator
      (GammaS U) (drazinKramersConjugateCandidate U S) = 0 := by
  simpa [drazinKramersConjugateCandidate, GammaS, QD] using
    (InfoGeometry.Canonical.KramersSuperchargeBridge.kramers_conjugated_qD_is_odd_of_commute_GammaS
      (E := E) (CIK := U.kernel) (S := S) hThetaGamma)

/--
Owner-readout transfer for the Kramers-paired bracket.

This is the strongest current owner-safe theorem: if a concrete Kramers symmetry
is additionally shown to identify its conjugated odd lane with the owner `Q_D`,
then the bracket inherits the already formalized Drazin translation/central split.
-/
@[rep_depth transport]
theorem pairedOddOddKramersBracket_eq_ownerReadout
    (S : InfoGeometry.Canonical.HestenesRealStructures.KramersSymmetry (E := E))
    (hPair : drazinKramersConjugateCandidate U S = QD U) :
    pairedOddOddKramersBracket U S
      = (2 : ℝ) • drazinTranslationCandidate U + drazinCentralCandidate U := by
  unfold pairedOddOddKramersBracket
  rw [hPair]
  exact projected_oddOdd_bracket_eq_two_smul_translation_plus_central (U := U)

/-- Projected odd/even closure under the spectral grading `Γ_S`. -/
theorem projected_odd_even_closure :
    InfoGeometry.Canonical.DrazinSupercharge.anticommutator (GammaS U) (QD U) = 0
      ∧
    (let T := U.kernel.toInformationCartanTriple;
      T.IsSpectralCompact (HD U))
      ∧
    (let T := U.kernel.toInformationCartanTriple;
      T.spectralAdjointFlow T.GammaS 0 (HD U) = HD U) := by
  refine ⟨projected_supercharge_is_odd U, ?_, ?_⟩
  · exact projected_hamiltonian_is_even U
  ·
    have hFix :=
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonian_fixed_under_spectralGradingFlow
        (CIK := U.kernel) 0
    simpa [HD] using hFix

end UnifiedSuperchargePackage

end Core

section Transported

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Transport package for the primitive supercharges on the quasilattice lane.
-/
@[rep_depth transport]
structure TransportedSuperchargePackage where
  V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)

namespace TransportedSuperchargePackage

variable (T : TransportedSuperchargePackage (E := E))

/-- Transported parity supercharge `QΠ(t)`. -/
noncomputable abbrev QPi_t (t : ℝ) : EndH :=
  transportedParitySupercharge (E := E) T.V t

/-- Transported modular supercharge `QJ(t)`. -/
noncomputable abbrev QJ_t (t : ℝ) : EndH :=
  transportedModularSupercharge (E := E) T.V t

/-- Primitive transported anticommutator vanishes at time zero. -/
theorem transported_primitive_anticommutator_zero :
    InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator
      (E := E) (modular_j (E := E)) (spectral_epsilon (E := E)) = 0 := by
  exact parity_modular_anticommutator_eq_zero (E := E)

/-- The transported parity supercharge satisfies the quasilattice commutator law. -/
theorem deriv_QPi_t (t : ℝ) :
    deriv (fun s => QPi_t T s) t
      =
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
      (E := E) T.V.connectionGenerator (QPi_t T t) := by
  simpa [QPi_t] using deriv_transportedParitySupercharge (E := E) T.V t

/-- The transported modular supercharge satisfies the quasilattice commutator law. -/
theorem deriv_QJ_t (t : ℝ) :
    deriv (fun s => QJ_t T s) t
      =
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
      (E := E) T.V.connectionGenerator (QJ_t T t) := by
  simpa [QJ_t] using deriv_transportedModularSupercharge (E := E) T.V t

/-- Second derivative of the transported parity supercharge lands in the weak-owner Lichnerowicz Hessian. -/
theorem deriv2_QPi_t_eq_operatorInformationHessian :
    let X := T.V.connectionGenerator
    deriv (fun t => deriv (fun s => QPi_t T s) t) 0
      =
    InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationHessian
      (E := E) X (modular_j (E := E)) := by
  simpa [QPi_t] using
    deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationHessian (E := E) T.V

/-- Second derivative of the transported parity supercharge splits into metric and curvature parts. -/
theorem deriv2_QPi_t_eq_metricPart_add_half_curvaturePart :
    let X := T.V.connectionGenerator
    deriv (fun t => deriv (fun s => QPi_t T s) t) 0
      =
    InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationMetricPart
      (E := E) X X (modular_j (E := E))
      + ((2 : ℝ)⁻¹) •
        InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationCurvaturePart
          (E := E) X X (modular_j (E := E)) := by
  simpa [QPi_t] using
    deriv2_transportedParitySupercharge_at_zero_eq_metricPart_add_half_curvaturePart
      (E := E) T.V

end TransportedSuperchargePackage

end Transported

section TopologicalCentralCharge

open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Krein
open InfoGeometry.Canonical.OperatorialCentralCharge

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E

/--
Topological central charge package:
the external central supercharge is the analytical index already owned by the repo.
-/
@[rep_depth transport]
structure TopologicalCentralChargePackage where
  X : RealSplitKreinDiracFredholmModule A B H₂
  hX : ChiralFredholmSurface X
  Zop : ℤ
  hZop :
    Zop = operatorialCentralCharge (A := A) (B := B) (E := E) X hX

namespace TopologicalCentralChargePackage

variable (Z : TopologicalCentralChargePackage (A := A) (B := B) (E := E))

/-- The external central supercharge is exactly the repo-owned analytical index. -/
theorem Zop_eq_analyticIndex :
    Z.Zop = operatorialCentralCharge (A := A) (B := B) (E := E) Z.X Z.hX :=
  Z.hZop

/-- The external central supercharge is transport invariant. -/
theorem Zop_transport_invariant
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (s t : ℝ) :
    quasilatticeAnalyticalIndex V Z.X s
        (quasilatticeChiralFredholmSurfaceOf (E := E) V Z.X Z.hX hEven s)
      =
    quasilatticeAnalyticalIndex V Z.X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V Z.X Z.hX hEven t) := by
  simpa using
    operatorialCentralCharge_transport_invariant
      (A := A) (B := B) (E := E) V Z.X Z.hX hEven s t

end TopologicalCentralChargePackage

end TopologicalCentralCharge

section Fusion

open InfoGeometry.Canonical.SuperchargeCentralChargeClosure
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Krein

variable {A B F : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable [KreinSpace (DoubledSpace F)] [KreinGradedModule (DoubledSpace F)]

local notation "H₂" => DoubledSpace F

/--
Unified central supercharge theorem:
combines projected Drazin evenness/flow invariance with the root transported
supercharge Lichnerowicz/central-charge closure package.
-/
@[rep_depth transport]
theorem unified_central_supercharge_theorem
    (U : UnifiedSuperchargePackage (E := F))
    (Tpkg : TransportedSuperchargePackage (E := F))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) Tpkg.V.connectionGenerator)
    (τ t : ℝ) :
    (let T := U.kernel.toInformationCartanTriple;
      T.IsSpectralCompact
          (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK U.kernel)
        ∧
      T.spectralAdjointFlow T.GammaS τ
          (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK U.kernel)
        =
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK U.kernel)
      ∧
    rootGapHessianClosure (E := F) Tpkg.V
      ∧
    (quasilatticeAnalyticalIndex Tpkg.V X t
        (quasilatticeChiralFredholmSurfaceOf (E := F) Tpkg.V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := F) X hX)
      ∧
    (operatorialCentralCharge (A := A) (B := B) (E := F) X hX ≠ 0 →
      quasilatticeAnalyticalIndex Tpkg.V X t
          (quasilatticeChiralFredholmSurfaceOf (E := F) Tpkg.V X hX hEven t)
        ≠ 0) := by
  exact InfoGeometry.Canonical.DrazinSupercharge.central_supercharge_theorem_with_drazin_evenness
    (A := A) (B := B) (F := F) U.kernel Tpkg.V X hX hEven τ t

/--
Cross-family compatibility ledger on the unified lane.
-/
@[rep_depth transport]
theorem unified_cross_family_compatibility
    (U : UnifiedSuperchargePackage (E := F))
    (Tpkg : TransportedSuperchargePackage (E := F))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) Tpkg.V.connectionGenerator)
    (τ t : ℝ) :
    (InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK
        (UnifiedSuperchargePackage.GammaS U)
        (UnifiedSuperchargePackage.QD U)
      = 0)
      ∧
    (let Xv := Tpkg.V.connectionGenerator;
      deriv (fun t => deriv (fun s => TransportedSuperchargePackage.QPi_t Tpkg s) t) 0
        =
      InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationMetricPart
        (E := F) Xv Xv (modular_j (E := F))
        + ((2 : ℝ)⁻¹) •
          InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationCurvaturePart
            (E := F) Xv Xv (modular_j (E := F)))
      ∧
    rootGapHessianClosure (E := F) Tpkg.V
      ∧
    (quasilatticeAnalyticalIndex Tpkg.V X t
        (quasilatticeChiralFredholmSurfaceOf (E := F) Tpkg.V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := F) X hX)
      ∧
    (operatorialCentralCharge (A := A) (B := B) (E := F) X hX ≠ 0 →
      quasilatticeAnalyticalIndex Tpkg.V X t
          (quasilatticeChiralFredholmSurfaceOf (E := F) Tpkg.V X hX hEven t)
        ≠ 0) := by
  refine ⟨UnifiedSuperchargePackage.projected_supercharge_is_odd U, ?_, ?_, ?_, ?_⟩
  · exact TransportedSuperchargePackage.deriv2_QPi_t_eq_metricPart_add_half_curvaturePart Tpkg
  · exact (unified_central_supercharge_theorem
      (A := A) (B := B) (F := F) U Tpkg X hX hEven τ t).2.1
  · exact (unified_central_supercharge_theorem
      (A := A) (B := B) (F := F) U Tpkg X hX hEven τ t).2.2.1
  · exact (unified_central_supercharge_theorem
      (A := A) (B := B) (F := F) U Tpkg X hX hEven τ t).2.2.2

end Fusion

section NambuGorkovLinearPacket

open scoped BigOperators

variable {𝕜 E : Type*}
variable [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]

/--
Minimal Krein-like datum for linear formalization: a fundamental symmetry
`J` that is involutive.
-/
structure KreinLikeData where
  J : E →ₗ[𝕜] E
  J_involutive : J.comp J = LinearMap.id

/--
Linear doubled Nambu-Gorkov operator packet:
diagonal channel (`diag`) and anomalous channel (`offdiag`).
-/
structure NambuGorkovLinearOp where
  diag : E →ₗ[𝕜] E
  offdiag : E →ₗ[𝕜] E

/-- Full operator is diagonal plus off-diagonal channels. -/
def NambuGorkovLinearOp.full (T : NambuGorkovLinearOp (𝕜 := 𝕜) (E := E)) : E →ₗ[𝕜] E :=
  T.diag + T.offdiag

/-- Swapped full operator (particle-hole channel swap). -/
def NambuGorkovLinearOp.fullSwap (T : NambuGorkovLinearOp (𝕜 := 𝕜) (E := E)) : E →ₗ[𝕜] E :=
  T.offdiag + T.diag

@[simp] theorem NambuGorkovLinearOp.full_apply
    (T : NambuGorkovLinearOp (𝕜 := 𝕜) (E := E)) (x : E) :
    T.full x = T.diag x + T.offdiag x := rfl

@[simp] theorem NambuGorkovLinearOp.fullSwap_apply
    (T : NambuGorkovLinearOp (𝕜 := 𝕜) (E := E)) (x : E) :
    T.fullSwap x = T.offdiag x + T.diag x := rfl

theorem NambuGorkovLinearOp.full_eq_fullSwap
    (T : NambuGorkovLinearOp (𝕜 := 𝕜) (E := E)) :
    T.full = T.fullSwap := by
  ext x
  simp [NambuGorkovLinearOp.full, NambuGorkovLinearOp.fullSwap, add_comm]

theorem NambuGorkovLinearOp.full_of_offdiag_zero
    (T : NambuGorkovLinearOp (𝕜 := 𝕜) (E := E))
    (hOff : T.offdiag = 0) :
    T.full = T.diag := by
  ext x
  simp [NambuGorkovLinearOp.full, hOff]

/--
Square-class for linear operators, mirroring `{-1,0,1}`:
- hyperbolic: `T ∘ T = id`
- parabolic:  `T ∘ T = 0`
- elliptic:   `T ∘ T = -id`
-/
def hasLinearSquareClass (T : E →ₗ[𝕜] E) (σ : CKSignature) : Prop :=
  match σ with
  | CKSignature.hyperbolic => T.comp T = LinearMap.id
  | CKSignature.parabolic => T.comp T = 0
  | CKSignature.elliptic => T.comp T = -LinearMap.id

theorem hasLinearSquareClass_hyperbolic_iff
    (T : E →ₗ[𝕜] E) :
    hasLinearSquareClass T CKSignature.hyperbolic ↔ T.comp T = LinearMap.id := Iff.rfl

theorem hasLinearSquareClass_parabolic_iff
    (T : E →ₗ[𝕜] E) :
    hasLinearSquareClass T CKSignature.parabolic ↔ T.comp T = 0 := Iff.rfl

theorem hasLinearSquareClass_elliptic_iff
    (T : E →ₗ[𝕜] E) :
    hasLinearSquareClass T CKSignature.elliptic ↔ T.comp T = -LinearMap.id := Iff.rfl

theorem offdiag_parabolic_of_square_zero
    (T : NambuGorkovLinearOp (𝕜 := 𝕜) (E := E))
    (h : T.offdiag.comp T.offdiag = 0) :
    hasLinearSquareClass T.offdiag CKSignature.parabolic := by
  simpa [hasLinearSquareClass] using h

theorem diag_hyperbolic_of_square_id
    (T : NambuGorkovLinearOp (𝕜 := 𝕜) (E := E))
    (h : T.diag.comp T.diag = LinearMap.id) :
    hasLinearSquareClass T.diag CKSignature.hyperbolic := by
  simpa [hasLinearSquareClass] using h

theorem diag_elliptic_of_square_neg_id
    (T : NambuGorkovLinearOp (𝕜 := 𝕜) (E := E))
    (h : T.diag.comp T.diag = -LinearMap.id) :
    hasLinearSquareClass T.diag CKSignature.elliptic := by
  simpa [hasLinearSquareClass] using h

/--
Bogoliubov mixing generator (linear finite packet):
the anomalous/off-diagonal lane of a doubled Nambu--Gorkov operator.
-/
def bogoliubovMixingGenerator
    (T : NambuGorkovLinearOp (𝕜 := 𝕜) (E := E)) : E →ₗ[𝕜] E :=
  T.offdiag

/--
Hyperbolic sector statement for the Bogoliubov mixing generator:
if the anomalous lane squares to identity, it is in square-class `+1`.
-/
theorem bogoliubov_generator_hyperbolic_of_square_id
    (T : NambuGorkovLinearOp (𝕜 := 𝕜) (E := E))
    (h : (bogoliubovMixingGenerator (𝕜 := 𝕜) (E := E) T).comp
          (bogoliubovMixingGenerator (𝕜 := 𝕜) (E := E) T) = LinearMap.id) :
    hasLinearSquareClass
      (bogoliubovMixingGenerator (𝕜 := 𝕜) (E := E) T) CKSignature.hyperbolic := by
  simpa [hasLinearSquareClass] using h

/--
Equivalent packet form: if `offdiag² = id`, then the off-diagonal Nambu lane
is hyperbolic (`Op² = +1`).
-/
theorem offdiag_hyperbolic_of_square_id
    (T : NambuGorkovLinearOp (𝕜 := 𝕜) (E := E))
    (h : T.offdiag.comp T.offdiag = LinearMap.id) :
    hasLinearSquareClass T.offdiag CKSignature.hyperbolic := by
  simpa [bogoliubovMixingGenerator] using
    bogoliubov_generator_hyperbolic_of_square_id (𝕜 := 𝕜) (E := E) T h

/--
Minimal Drazin-index-1 surrogate on the off-diagonal lane:
strict nilpotency (`T² = 0`).
-/
def hasDrazinIndexOneSurrogate (T : E →ₗ[𝕜] E) : Prop :=
  T.comp T = 0

theorem hasDrazinIndexOneSurrogate_iff_parabolic
    (T : E →ₗ[𝕜] E) :
    hasDrazinIndexOneSurrogate T ↔ hasLinearSquareClass T CKSignature.parabolic := by
  rfl

theorem offdiag_hasDrazinIndexOneSurrogate_of_square_zero
    (T : NambuGorkovLinearOp (𝕜 := 𝕜) (E := E))
    (h : T.offdiag.comp T.offdiag = 0) :
    hasDrazinIndexOneSurrogate T.offdiag := h

theorem linear_square_hyperbolic_not_parabolic
    (T : E →ₗ[𝕜] E)
    (hneq : (LinearMap.id : E →ₗ[𝕜] E) ≠ 0)
    (hh : hasLinearSquareClass T CKSignature.hyperbolic)
    (hp : hasLinearSquareClass T CKSignature.parabolic) :
    False := by
  have h1 : T.comp T = LinearMap.id := by simpa [hasLinearSquareClass] using hh
  have h0 : T.comp T = 0 := by simpa [hasLinearSquareClass] using hp
  exact hneq (h1.symm.trans h0)

theorem linear_square_hyperbolic_not_elliptic
    (T : E →ₗ[𝕜] E)
    (hneq : (LinearMap.id : E →ₗ[𝕜] E) ≠ -LinearMap.id)
    (hh : hasLinearSquareClass T CKSignature.hyperbolic)
    (he : hasLinearSquareClass T CKSignature.elliptic) :
    False := by
  have h1 : T.comp T = LinearMap.id := by simpa [hasLinearSquareClass] using hh
  have hm1 : T.comp T = -LinearMap.id := by simpa [hasLinearSquareClass] using he
  exact hneq (h1.symm.trans hm1)

theorem linear_square_parabolic_not_elliptic
    (T : E →ₗ[𝕜] E)
    (hneq : (0 : E →ₗ[𝕜] E) ≠ -LinearMap.id)
    (hp : hasLinearSquareClass T CKSignature.parabolic)
    (he : hasLinearSquareClass T CKSignature.elliptic) :
    False := by
  have h0 : T.comp T = 0 := by simpa [hasLinearSquareClass] using hp
  have hm1 : T.comp T = -LinearMap.id := by simpa [hasLinearSquareClass] using he
  exact hneq (h0.symm.trans hm1)

theorem hasLinearSquareClass_neg_iff
    (T : E →ₗ[𝕜] E) (σ : CKSignature) :
    hasLinearSquareClass (-T) σ ↔ hasLinearSquareClass T σ := by
  cases σ <;> constructor <;> intro h
  · simpa [hasLinearSquareClass, LinearMap.comp_neg, LinearMap.neg_comp, neg_neg] using h
  · simpa [hasLinearSquareClass, LinearMap.comp_neg, LinearMap.neg_comp, neg_neg] using h
  · simpa [hasLinearSquareClass, LinearMap.comp_neg, LinearMap.neg_comp, neg_neg] using h
  · simpa [hasLinearSquareClass, LinearMap.comp_neg, LinearMap.neg_comp, neg_neg] using h
  · simpa [hasLinearSquareClass, LinearMap.comp_neg, LinearMap.neg_comp, neg_neg] using h
  · simpa [hasLinearSquareClass, LinearMap.comp_neg, LinearMap.neg_comp, neg_neg] using h

section ComplexWickLinear

variable {F : Type*}
variable [AddCommGroup F] [Module ℂ F]

/-- Complex Wick twist on linear maps: `(I • T)^2 = -(T^2)`. -/
theorem complex_wick_linear_square_flip
    (T : F →ₗ[ℂ] F) :
    (Complex.I • T).comp (Complex.I • T) = -(T.comp T) := by
  ext x
  simp [LinearMap.comp_apply, smul_smul, Complex.I_mul_I]

theorem complex_wick_linear_hyperbolic_to_elliptic
    (T : F →ₗ[ℂ] F)
    (h : hasLinearSquareClass T CKSignature.hyperbolic) :
    hasLinearSquareClass (Complex.I • T) CKSignature.elliptic := by
  have hsq : T.comp T = LinearMap.id := by simpa [hasLinearSquareClass] using h
  have hflip : (Complex.I • T).comp (Complex.I • T) = -(T.comp T) :=
    complex_wick_linear_square_flip T
  have hres : (Complex.I • T).comp (Complex.I • T) = -LinearMap.id := by
    simpa [hsq] using hflip
  simpa [hasLinearSquareClass] using hres

theorem complex_wick_linear_elliptic_to_hyperbolic
    (T : F →ₗ[ℂ] F)
    (h : hasLinearSquareClass T CKSignature.elliptic) :
    hasLinearSquareClass (Complex.I • T) CKSignature.hyperbolic := by
  have hsq : T.comp T = -LinearMap.id := by simpa [hasLinearSquareClass] using h
  have hflip : (Complex.I • T).comp (Complex.I • T) = -(T.comp T) :=
    complex_wick_linear_square_flip T
  have hres : (Complex.I • T).comp (Complex.I • T) = LinearMap.id := by
    simpa [hsq, neg_neg] using hflip
  simpa [hasLinearSquareClass] using hres

theorem complex_wick_linear_parabolic_fixed
    (T : F →ₗ[ℂ] F)
    (h : hasLinearSquareClass T CKSignature.parabolic) :
    hasLinearSquareClass (Complex.I • T) CKSignature.parabolic := by
  have hsq : T.comp T = 0 := by simpa [hasLinearSquareClass] using h
  have hflip : (Complex.I • T).comp (Complex.I • T) = -(T.comp T) :=
    complex_wick_linear_square_flip T
  have hres : (Complex.I • T).comp (Complex.I • T) = 0 := by
    simpa [hsq] using hflip
  simpa [hasLinearSquareClass] using hres

theorem complex_wick_linear_signature_transport_iff
    (T : F →ₗ[ℂ] F) (σ : CKSignature) :
    hasLinearSquareClass T σ ↔
      hasLinearSquareClass (Complex.I • T) (wickCKMap σ) := by
  cases σ
  · constructor
    · intro h
      simpa [wickCKMap] using complex_wick_linear_elliptic_to_hyperbolic (T := T) h
    · intro h
      have h' : hasLinearSquareClass (Complex.I • T) CKSignature.hyperbolic := by
        simpa [wickCKMap] using h
      have h2 : hasLinearSquareClass (Complex.I • (Complex.I • T)) CKSignature.elliptic :=
        complex_wick_linear_hyperbolic_to_elliptic (T := (Complex.I • T)) h'
      exact (hasLinearSquareClass_neg_iff (T := T) (σ := CKSignature.elliptic)).1 <|
        by simpa [smul_smul, Complex.I_mul_I] using h2
  · constructor
    · intro h
      simpa [wickCKMap] using complex_wick_linear_parabolic_fixed (T := T) h
    · intro h
      have h' : hasLinearSquareClass (Complex.I • T) CKSignature.parabolic := by
        simpa [wickCKMap] using h
      have h2 : hasLinearSquareClass (Complex.I • (Complex.I • T)) CKSignature.parabolic :=
        complex_wick_linear_parabolic_fixed (T := (Complex.I • T)) h'
      exact (hasLinearSquareClass_neg_iff (T := T) (σ := CKSignature.parabolic)).1 <|
        by simpa [smul_smul, Complex.I_mul_I] using h2
  · constructor
    · intro h
      simpa [wickCKMap] using complex_wick_linear_hyperbolic_to_elliptic (T := T) h
    · intro h
      have h' : hasLinearSquareClass (Complex.I • T) CKSignature.elliptic := by
        simpa [wickCKMap] using h
      have h2 : hasLinearSquareClass (Complex.I • (Complex.I • T)) CKSignature.hyperbolic :=
        complex_wick_linear_elliptic_to_hyperbolic (T := (Complex.I • T)) h'
      exact (hasLinearSquareClass_neg_iff (T := T) (σ := CKSignature.hyperbolic)).1 <|
        by simpa [smul_smul, Complex.I_mul_I] using h2

/-! ## Elliptic sector: Wick rotation and Matsubara lattice -/

/--
Scalar Wick continuation of a hyperbolic generator:
if `B² = 1`, then `(iB)² = -1`.
-/
@[rep_depth thermo]
theorem wick_hyperbolic_to_elliptic_scalar
    {B : ℂ}
    (hB : B * B = 1) :
    (Complex.I * B) * (Complex.I * B) = -1 := by
  exact wick_twist_complex_hyperbolic_to_elliptic hB

/--
Linear Wick continuation of a hyperbolic generator:
if `T² = id`, then `(i • T)² = -id`.
-/
@[rep_depth thermo]
theorem wick_hyperbolic_to_elliptic_linear
    {F : Type*} [AddCommGroup F] [Module ℂ F]
    (T : F →ₗ[ℂ] F)
    (h : hasLinearSquareClass T CKSignature.hyperbolic) :
    hasLinearSquareClass (Complex.I • T) CKSignature.elliptic := by
  exact complex_wick_linear_hyperbolic_to_elliptic (T := T) h

/--
Bosonic Matsubara frequency lattice:
`ω_n = (2π n)/β`.
-/
@[rep_depth thermo]
noncomputable def matsubaraFrequency (β : ℝ) (n : ℤ) : ℝ :=
  (2 * Real.pi * n) / β

/--
Odd symmetry of Matsubara frequencies: `ω_{-n} = -ω_n`.
-/
@[rep_depth thermo]
theorem matsubaraFrequency_neg
    (β : ℝ) (n : ℤ) :
    matsubaraFrequency β (-n) = -matsubaraFrequency β n := by
  unfold matsubaraFrequency
  calc
    (2 * Real.pi * ((-n : ℤ) : ℝ)) / β
        = (-(2 * Real.pi * ((n : ℤ) : ℝ))) / β := by
            simp [mul_assoc, mul_comm, mul_left_comm]
    _ = -((2 * Real.pi * ((n : ℤ) : ℝ)) / β) := by ring
    _ = -matsubaraFrequency β n := by rfl

/--
Matsubara lattice is discrete/injective in index when `β ≠ 0`.
-/
@[rep_depth thermo]
theorem matsubaraFrequency_injective
    {β : ℝ}
    (hβ : β ≠ 0) :
    Function.Injective (matsubaraFrequency β) := by
  intro m n hmn
  have hmul : (2 * Real.pi * (m : ℝ)) = (2 * Real.pi * (n : ℝ)) := by
    have hβ' : (β : ℝ) ≠ 0 := hβ
    exact (div_left_inj' hβ').1 hmn
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by
    exact mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hmnr : (m : ℝ) = (n : ℝ) := by
    exact (mul_right_inj' h2pi).1 (by simpa [mul_assoc, mul_comm, mul_left_comm] using hmul)
  exact Int.cast_inj.mp hmnr

/--
Zero mode characterization on the Matsubara lattice (`β ≠ 0`):
`ω_n = 0` iff `n = 0`.
-/
@[rep_depth thermo]
theorem matsubaraFrequency_eq_zero_iff
    {β : ℝ}
    (hβ : β ≠ 0)
    (n : ℤ) :
    matsubaraFrequency β n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have hinj := matsubaraFrequency_injective (β := β) hβ
    have h0 : matsubaraFrequency β n = matsubaraFrequency β 0 := by
      simpa [matsubaraFrequency] using h
    exact hinj h0
  · intro hn
    simp [matsubaraFrequency, hn]

end ComplexWickLinear

end NambuGorkovLinearPacket

section HyperbolicSectorAPI

variable {A : Type*} [AddCommGroup A]

/--
Hyperbolic Bogoliubov sector (operator-level):
the generator squares to `+1` in the endomorphism square-class sense.
-/
@[rep_depth thermo]
theorem bogoliubov_hyperbolic_sector
    (B : A →+ A)
    (h : ∀ x : A, B (B x) = x) :
    hasEndoSquareClass B CKSignature.hyperbolic := by
  simpa [hasEndoSquareClass] using h

/--
Nambu off-diagonal lane is parabolic when strictly nilpotent (`Op² = 0`).
This is the complementary transition lane to the hyperbolic sector.
-/
@[rep_depth thermo]
theorem nambu_offdiag_parabolic_sector
    (b c : A →+ A)
    (hbc : ∀ x : A, b (c x) = 0)
    (hcb : ∀ x : A, c (b x) = 0) :
    hasEndoSquareClass (nambuBlockOffDiag b c) CKSignature.parabolic := by
  simpa using nambu_offdiag_has_parabolic_square (A := A) b c hbc hcb

/--
Krein-gap-style hyperbolic channel on the mixing generator:
for a CAR nilpotent pair, the `b + c` lane is hyperbolic (`Op² = +1`).
-/
@[rep_depth thermo]
theorem krein_gap_hyperbolic_mixing_sector
    (b c : A →+ A)
    (hbb : ∀ x : A, b (b x) = 0)
    (hcc : ∀ x : A, c (c x) = 0)
    (hcar : ∀ x : A, b (c x) + c (b x) = x) :
    hasEndoSquareClass (b + c) CKSignature.hyperbolic := by
  simpa using endo_car_sum_has_hyperbolic_square (A := A) b c hbb hcc hcar

/--
Non-collapse of the hyperbolic Bogoliubov lane:
if `B² = id`, it cannot also be parabolic when `1 ≠ 0`.
-/
@[rep_depth thermo]
theorem bogoliubov_hyperbolic_not_parabolic
    [Nontrivial A]
    (B : A →+ A)
    (hh : hasEndoSquareClass B CKSignature.hyperbolic) :
    ¬ hasEndoSquareClass B CKSignature.parabolic := by
  intro hp
  have h1 : ∀ x : A, B (B x) = x := hh
  have h0 : ∀ x : A, B (B x) = 0 := hp
  rcases exists_ne (0 : A) with ⟨x, hx⟩
  exact hx ((h1 x).symm.trans (h0 x))

/--
Non-collapse of the hyperbolic Bogoliubov lane, witness-free:
if `B² = id`, it cannot also be elliptic under
`NoZeroSMulDivisors ℤ A` and nontriviality.
-/
@[rep_depth thermo]
theorem bogoliubov_hyperbolic_not_elliptic
    [NoZeroSMulDivisors ℤ A] [Nontrivial A]
    (B : A →+ A)
    (hh : hasEndoSquareClass B CKSignature.hyperbolic) :
    ¬ hasEndoSquareClass B CKSignature.elliptic := by
  intro he
  rcases exists_ne (0 : A) with ⟨x, hx⟩
  have h1 : B (B x) = x := hh x
  have hm1 : B (B x) = -x := he x
  have hsum : x + x = 0 := by
    calc
      x + x = (B (B x)) + x := by rw [h1]
      _ = (-x) + x := by rw [hm1]
      _ = 0 := by simp
  have hsmul : (2 : ℤ) • x = 0 := by
    simpa [two_zsmul] using hsum
  have hcase : (2 : ℤ) = 0 ∨ x = 0 :=
    NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero hsmul
  cases hcase with
  | inl h2 =>
      norm_num at h2
  | inr hx0 =>
      exact hx hx0

/--
Closed integer-carrier endpoint (no local assumptions):
on `A = ℤ`, hyperbolic excludes elliptic for Bogoliubov generators.
-/
@[rep_depth thermo]
theorem bogoliubov_hyperbolic_not_elliptic_int
    (B : ℤ →+ ℤ)
    (hh : hasEndoSquareClass B CKSignature.hyperbolic) :
    ¬ hasEndoSquareClass B CKSignature.elliptic := by
  exact bogoliubov_hyperbolic_not_elliptic (A := ℤ) B hh

/--
Real incompatibility lemma on the square-class lane:
on a nontrivial additive carrier, an endomorphism cannot be both
elliptic (`B² = -id`) and parabolic (`B² = 0`).
-/
@[rep_depth thermo]
theorem endo_elliptic_not_parabolic
    [Nontrivial A]
    (B : A →+ A)
    (he : hasEndoSquareClass B CKSignature.elliptic) :
    ¬ hasEndoSquareClass B CKSignature.parabolic := by
  intro hp
  rcases exists_ne (0 : A) with ⟨x, hx⟩
  have hm1 : B (B x) = -x := he x
  have h0 : B (B x) = 0 := hp x
  have hx0 : x = 0 := by
    have : -x = 0 := hm1.symm.trans h0
    exact neg_eq_zero.mp this
  exact hx hx0

/--
Real separation theorem for CK square classes on one endomorphism:
under nontriviality (and `NoZeroSMulDivisors ℤ A` for the hyperbolic/elliptic
lane), the three classes are pairwise incompatible.
-/
@[rep_depth thermo]
theorem endo_square_classes_pairwise_incompatible
    [NoZeroSMulDivisors ℤ A] [Nontrivial A]
    (B : A →+ A) :
    (hasEndoSquareClass B CKSignature.hyperbolic →
      ¬ hasEndoSquareClass B CKSignature.parabolic) ∧
    (hasEndoSquareClass B CKSignature.hyperbolic →
      ¬ hasEndoSquareClass B CKSignature.elliptic) ∧
    (hasEndoSquareClass B CKSignature.elliptic →
      ¬ hasEndoSquareClass B CKSignature.parabolic) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hh
    exact bogoliubov_hyperbolic_not_parabolic (A := A) B hh
  · intro hh
    exact bogoliubov_hyperbolic_not_elliptic (A := A) B hh
  · intro he
    exact endo_elliptic_not_parabolic (A := A) B he

/--
Parabolic exclusion theorem (owner-side):
on a nontrivial additive carrier, a parabolic endomorphism (`B² = 0`) cannot
also be hyperbolic (`B² = id`) nor elliptic (`B² = -id`).
-/
@[rep_depth thermo]
theorem endo_parabolic_excludes_hyperbolic_and_elliptic
    [Nontrivial A]
    (B : A →+ A)
    (hp : hasEndoSquareClass B CKSignature.parabolic) :
    (¬ hasEndoSquareClass B CKSignature.hyperbolic) ∧
    (¬ hasEndoSquareClass B CKSignature.elliptic) := by
  refine ⟨?_, ?_⟩
  · intro hh
    have h1 : ∀ x : A, B (B x) = x := hh
    have h0 : ∀ x : A, B (B x) = 0 := hp
    rcases exists_ne (0 : A) with ⟨x, hx⟩
    exact hx ((h1 x).symm.trans (h0 x))
  · intro he
    exact (endo_elliptic_not_parabolic (A := A) B he) hp

/--
Bundled hyperbolic-sector rigidity:
the Bogoliubov hyperbolic lane excludes parabolic and elliptic collapse.
-/
@[rep_depth thermo]
theorem bogoliubov_hyperbolic_rigidity_bundle
    [NoZeroSMulDivisors ℤ A] [Nontrivial A]
    (B : A →+ A)
    (hh : hasEndoSquareClass B CKSignature.hyperbolic) :
    (¬ hasEndoSquareClass B CKSignature.parabolic) ∧
    (¬ hasEndoSquareClass B CKSignature.elliptic) := by
  refine ⟨?_, ?_⟩
  · exact bogoliubov_hyperbolic_not_parabolic (A := A) B hh
  · exact bogoliubov_hyperbolic_not_elliptic (A := A) B hh

end HyperbolicSectorAPI

section ParabolicSectorAPI

variable {A : Type*} [AddCommGroup A]

/--
Exceptional-point/parabolic sector on the endomorphism lane:
strict nilpotency (`Op² = 0`) is exactly the parabolic square class.
-/
@[rep_depth thermo]
theorem exceptionalPoint_parabolic_sector
    (T : A →+ A)
    (hNil : ∀ x : A, T (T x) = 0) :
    hasEndoSquareClass T CKSignature.parabolic := by
  simpa [hasEndoSquareClass] using hNil

/--
Parabolic Nambu off-diagonal lane from pairwise-zero composites.
This is the doubled EP boundary in block form.
-/
@[rep_depth thermo]
theorem exceptionalPoint_nambu_offdiag_parabolic
    (b c : A →+ A)
    (hbc : ∀ x : A, b (c x) = 0)
    (hcb : ∀ x : A, c (b x) = 0) :
    hasEndoSquareClass (nambuBlockOffDiag b c) CKSignature.parabolic := by
  simpa using nambu_offdiag_has_parabolic_square (A := A) b c hbc hcb

/--
Drazin-index-1 surrogate on the linear operator lane:
strict nilpotency is equivalent to parabolic class.
-/
@[rep_depth thermo]
theorem parabolic_drazinIndexOneSurrogate_iff
    {𝕜 E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (T : E →ₗ[𝕜] E) :
    hasDrazinIndexOneSurrogate T ↔ hasLinearSquareClass T CKSignature.parabolic := by
  simpa using hasDrazinIndexOneSurrogate_iff_parabolic (𝕜 := 𝕜) (E := E) T

end ParabolicSectorAPI

section EllipticSectorAPI

/--
Elliptic sector from Wick rotation on complex scalars:
if `B² = 1` (hyperbolic), then `(I*B)² = -1` (elliptic).
-/
@[rep_depth thermo]
theorem wick_hyperbolic_to_elliptic_sector
    {B : ℂ}
    (hB : B * B = 1) :
    hasCKSignature (Complex.I * B) CKSignature.elliptic := by
  simpa [hasCKSignature] using wick_twist_complex_hyperbolic_to_elliptic (B := B) hB

/--
Wick period-two transport at the signature level:
`wickCKMap (wickCKMap σ) = σ`, i.e. analytic continuation is involutive
on square classes.
-/
@[rep_depth thermo]
theorem wick_signature_period_two_sector
    (σ : CKSignature) :
    wickCKMap (wickCKMap σ) = σ := by
  simpa using wickCKMap_involutive σ

/--
One-step Wick transport exactly matches the signature map.
-/
@[rep_depth thermo]
theorem wick_signature_transport_sector
    {B : ℂ} {σ : CKSignature}
    (hσ : hasCKSignature B σ) :
    hasCKSignature (Complex.I * B) (wickCKMap σ) := by
  simpa using wick_twist_complex_signature_image (B := B) (σ := σ) hσ

/--
Two-step Wick transport returns to the original square class.
-/
@[rep_depth thermo]
theorem wick_signature_return_sector
    {B : ℂ} {σ : CKSignature}
    (hσ : hasCKSignature B σ) :
    hasCKSignature (Complex.I * (Complex.I * B)) σ := by
  simpa using wick_twist_complex_signature_period_two (B := B) (σ := σ) hσ

end EllipticSectorAPI

end InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
