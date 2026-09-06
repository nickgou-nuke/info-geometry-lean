import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ChiralProjectorFromInvolution

/-!
# Joint Witt/circular projectors

This is the operator-algebraic joint spectral layer for the two-sheet packet.
It uses two commuting involutions rather than assuming a commutative ambient
algebra: one involution represents the split/hyperbolic axis and the other the
circular/chiral axis.  The four joint projectors are products of the already
constructively derived half-projectors from `ChiralInvolution`.
-/

noncomputable section

namespace InfoGeometry.Optics.SheetWittCircularBasis

open InfoGeometry.OperatorAlgebra

variable {Op : Type*} [Ring Op] [Module ℝ Op] [Algebra ℝ Op]

def choose (ε : Bool) (p q : Op) : Op :=
  if ε = true then p else q

/-- Two commuting involutions in one operator algebra. -/
structure CommutingInvolutions (Op : Type*) [Ring Op] [Module ℝ Op]
    [Algebra ℝ Op] where
  hyperbolic : Op
  circular : Op
  hyperbolic_sq : hyperbolic * hyperbolic = 1
  circular_sq : circular * circular = 1
  commute : hyperbolic * circular = circular * hyperbolic
  projector_commute :
    ∀ ε σ, choose ε ((1 / 2 : ℝ) • (1 + hyperbolic))
      ((1 / 2 : ℝ) • (1 - hyperbolic)) *
      choose σ ((1 / 2 : ℝ) • (1 + circular))
      ((1 / 2 : ℝ) • (1 - circular)) =
    choose σ ((1 / 2 : ℝ) • (1 + circular))
      ((1 / 2 : ℝ) • (1 - circular)) *
      choose ε ((1 / 2 : ℝ) • (1 + hyperbolic))
      ((1 / 2 : ℝ) • (1 - hyperbolic))

namespace CommutingInvolutions

variable (S : CommutingInvolutions Op)

def hyperbolicInvolution (S : CommutingInvolutions Op) : ChiralInvolution Op where
  chi := S.hyperbolic
  chi_sq := S.hyperbolic_sq

def circularInvolution (S : CommutingInvolutions Op) : ChiralInvolution Op where
  chi := S.circular
  chi_sq := S.circular_sq

/-- Product of the selected hyperbolic and circular half-projectors. -/
def jointProjector (ε σ : Bool) : Op :=
  choose ε (hyperbolicInvolution S).Pleft (hyperbolicInvolution S).Pright *
    choose σ (circularInvolution S).Pleft (circularInvolution S).Pright

private theorem hyperbolic_projector_commutes_circular_projector
    (ε σ : Bool) :
    choose ε (hyperbolicInvolution S).Pleft (hyperbolicInvolution S).Pright *
        choose σ (circularInvolution S).Pleft (circularInvolution S).Pright =
      choose σ (circularInvolution S).Pleft (circularInvolution S).Pright *
        choose ε (hyperbolicInvolution S).Pleft (hyperbolicInvolution S).Pright := by
  exact S.projector_commute ε σ

private theorem product_idem_of_commute
    {p q : Op} (hp : p * p = p) (hq : q * q = q)
    (hpq : p * q = q * p) : (p * q) * (p * q) = p * q := by
  calc
    (p * q) * (p * q) = p * (q * p) * q := by simp [mul_assoc]
    _ = p * (p * q) * q := by rw [hpq]
    _ = (p * p) * (q * q) := by simp [mul_assoc]
    _ = p * q := by rw [hp, hq]
    
@[simp] theorem jointProjector_idem (ε σ : Bool) :
    S.jointProjector ε σ * S.jointProjector ε σ = S.jointProjector ε σ := by
  unfold jointProjector
  apply product_idem_of_commute
  · cases ε
    · simpa only [choose] using (hyperbolicInvolution S).Pright_idem
    · simpa only [choose] using (hyperbolicInvolution S).Pleft_idem
  · cases σ
    · simpa only [choose] using (circularInvolution S).Pright_idem
    · simpa only [choose] using (circularInvolution S).Pleft_idem
  · exact hyperbolic_projector_commutes_circular_projector S ε σ

@[simp] theorem jointProjector_sum :
    S.jointProjector true true + S.jointProjector true false +
        S.jointProjector false true + S.jointProjector false false = 1 := by
  unfold jointProjector
  simp only [choose]
  calc
    (hyperbolicInvolution S).Pleft * (circularInvolution S).Pleft +
        (hyperbolicInvolution S).Pleft * (circularInvolution S).Pright +
        (hyperbolicInvolution S).Pright * (circularInvolution S).Pleft +
        (hyperbolicInvolution S).Pright * (circularInvolution S).Pright =
      ((hyperbolicInvolution S).Pleft + (hyperbolicInvolution S).Pright) *
        ((circularInvolution S).Pleft + (circularInvolution S).Pright) := by
          noncomm_ring
    _ = 1 := by rw [(hyperbolicInvolution S).Pleft_add_Pright,
      (circularInvolution S).Pleft_add_Pright]; simp

end CommutingInvolutions

end InfoGeometry.Optics.SheetWittCircularBasis
