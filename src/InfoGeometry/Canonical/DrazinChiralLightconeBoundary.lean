import Mathlib.LinearAlgebra.QuadraticForm.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.FiniteInvariantTransport

/-!
# InfoGeometry.Canonical.DrazinChiralLightconeBoundary

Algebraic Drazin/lightcone boundary facts.

This file formalizes only the finite algebraic spine of the proposed picture:

* the Drazin complementary projector is an idempotent defect/null-sector
  projector;
* the Drazin power annihilates that defect lane on both sides;
* algebraic null cones are stable under nonzero real rescaling, so nullity
  descends to projective rays;
* chiral left/right Majorana CAR identities are transported by finite-stage
  ring homomorphisms;
* Jordan anticommutator and Lie commutator expressions are transported by
  finite-stage ring homomorphisms.

There is no topological-boundary theorem, no holographic reconstruction theorem,
no analytic completion, and no colimit claim here.
-/

namespace InfoGeometry.Canonical.DrazinChiralLightconeBoundary

open InfoGeometry.Canonical.Drazin

/-! ## Drazin complement as algebraic defect/null-sector projector -/

section DrazinDefect

variable {R : Type*} [Ring R]
variable {a b : R} {k : ℕ}

/-- The Drazin complementary projector is idempotent. -/
theorem drazin_defect_projector_idempotent
    (h : IsDrazinInverse a b k) :
    IsDrazinInverse.complementaryProjection a b *
        IsDrazinInverse.complementaryProjection a b =
      IsDrazinInverse.complementaryProjection a b :=
  IsDrazinInverse.complementaryProjection_is_idempotent h

/-- The regular Drazin projector and the defect projector are orthogonal. -/
theorem drazin_regular_defect_orthogonal
    (h : IsDrazinInverse a b k) :
    IsDrazinInverse.projection a b *
        IsDrazinInverse.complementaryProjection a b = 0 ∧
      IsDrazinInverse.complementaryProjection a b *
        IsDrazinInverse.projection a b = 0 :=
  ⟨IsDrazinInverse.projection_mul_complementaryProjection h,
    IsDrazinInverse.complementaryProjection_mul_projection h⟩

/-- The Drazin regular and defect projectors decompose the identity. -/
theorem drazin_regular_add_defect_eq_one :
    IsDrazinInverse.projection a b +
        IsDrazinInverse.complementaryProjection a b = (1 : R) :=
  IsDrazinInverse.projection_add_complementaryProjection

/--
The Drazin defect lane is annihilated by the Drazin power on both sides.

This is the algebraic finite-stage form of “the complementary Drazin sector is
null/zero-mode for the power `a^k`”.
-/
theorem drazin_power_annihilates_defect_lane
    (h : IsDrazinInverse a b k) :
    a ^ k * IsDrazinInverse.complementaryProjection a b = 0 ∧
      IsDrazinInverse.complementaryProjection a b * a ^ k = 0 :=
  ⟨IsDrazinInverse.power_mul_complementaryProjection_eq_zero h,
    IsDrazinInverse.complementaryProjection_mul_power_eq_zero h⟩

end DrazinDefect

/-! ## Algebraic null cone and projective massless rays -/

section AlgebraicNullCone

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Algebraic null cone of a real quadratic form. -/
def AlgebraicNullCone (Q : QuadraticForm ℝ V) (v : V) : Prop :=
  Q v = 0

/-- Nonzero algebraic null vectors: the finite algebraic proxy for massless rays. -/
def MasslessVector (Q : QuadraticForm ℝ V) (v : V) : Prop :=
  v ≠ 0 ∧ AlgebraicNullCone Q v

/-- Nullity is preserved by real scaling. -/
theorem algebraicNullCone_smul
    (Q : QuadraticForm ℝ V) {v : V}
    (hv : AlgebraicNullCone Q v) (r : ℝ) :
    AlgebraicNullCone Q (r • v) := by
  unfold AlgebraicNullCone at hv ⊢
  rw [Q.map_smul, hv]
  simp

/-- Nonzero null vectors remain nonzero null vectors under nonzero real scaling. -/
theorem masslessVector_smul
    (Q : QuadraticForm ℝ V) {v : V}
    (hv : MasslessVector Q v) {r : ℝ} (hr : r ≠ 0) :
    MasslessVector Q (r • v) := by
  exact ⟨smul_ne_zero hr hv.1, algebraicNullCone_smul Q hv.2 r⟩

/-- Algebraic nullity is the representative-level condition for a projective null ray. -/
theorem algebraicNullCone_projective_representative
    (Q : QuadraticForm ℝ V) {v : V} :
    AlgebraicNullCone Q v ↔ Q v = 0 :=
  Iff.rfl

end AlgebraicNullCone

/-! ## Chiral Majorana / Clifford-Jordan-Lie finite transport -/

section ChiralTransport

variable {A B : Type*} [Ring A] [Ring B]

/-- Fermionic anticommutator expression. -/
def anticommutator (x y : A) : A :=
  x * y + y * x

/-- Associative commutator expression. -/
def commutator (x y : A) : A :=
  x * y - y * x

/--
Transport a chiral left/right Majorana CAR packet by a finite-stage ring
homomorphism.
-/
theorem ringHom_transports_chiral_majorana_CAR
    (f : A →+* B) {ψL ψR hL hR : A}
    (hLL : anticommutator ψL ψL = hL)
    (hRR : anticommutator ψR ψR = hR)
    (hLR : anticommutator ψL ψR = 0) :
    f ψL * f ψL + f ψL * f ψL = f hL ∧
      f ψR * f ψR + f ψR * f ψR = f hR ∧
      f ψL * f ψR + f ψR * f ψL = 0 := by
  exact
    ⟨by
      simpa [anticommutator] using
        InfoGeometry.Canonical.FiniteInvariantTransport.ringHom_preserves_anticommutator f hLL,
     by
      simpa [anticommutator] using
        InfoGeometry.Canonical.FiniteInvariantTransport.ringHom_preserves_anticommutator f hRR,
     by
      simpa [anticommutator] using
        InfoGeometry.Canonical.FiniteInvariantTransport.ringHom_preserves_anticommutator f hLR⟩

/-- Jordan/anticommutator closure is transported by finite-stage ring homomorphisms. -/
theorem ringHom_transports_jordan_closure
    (f : A →+* B) {x y h : A}
    (hxy : anticommutator x y = h) :
    f x * f y + f y * f x = f h := by
  simpa [anticommutator] using
    InfoGeometry.Canonical.FiniteInvariantTransport.ringHom_preserves_anticommutator f hxy

/-- Lie/commutator closure is transported by finite-stage ring homomorphisms. -/
theorem ringHom_transports_lie_closure
    (f : A →+* B) {x y c : A}
    (hxy : commutator x y = c) :
    f x * f y - f y * f x = f c := by
  simpa [commutator] using
    InfoGeometry.Canonical.FiniteInvariantTransport.ringHom_preserves_commutator f hxy

/-- Central-lane commutation is transported on the image of a finite-stage ring homomorphism. -/
theorem ringHom_transports_central_lane_on_image
    (f : A →+* B) {c : A}
    (hc : ∀ x : A, commutator c x = 0)
    (x : A) :
    f c * f x - f x * f c = 0 := by
  simpa using ringHom_transports_lie_closure f (hc x)

end ChiralTransport

end InfoGeometry.Canonical.DrazinChiralLightconeBoundary
