import InfoGeometry.Optics.OperatorValuedConnection

/-!
# Gauge calculus for associative twisted coefficient algebras

Meier--Viana (3.31)--(3.32), with the sign explicitly compared to (4.18).
An existing operator-valued Connection is constructed from actual additive
Leibniz maps. The derivative datum is not a freely chosen curvature field.
This coefficient calculus is not a Dolbeault-complex or action-integral construction.
-/
noncomputable section
namespace InfoGeometry.Twistor.TwistedGauge
open InfoGeometry.Optics.OperatorValuedConnection
variable {A I : Type*} [Ring A]

def connection (d : I → A →+ A) (a : I → A) :
    Connection (Point := Unit) (Tangent := I) (Value := A) where
  form _ i := a i
  derivative _ i j := d i (a j)-d j (a i)
  derivative_swap := by intro p i j; abel
  derivative_same := by intro p i; simp

@[simp] theorem curvature_coeff (d : I → A →+ A) (a : I → A) (i j : I) :
    curvature (connection d a) () i j =
      d i (a j)-d j (a i)+a i*a j-a j*a i := by
  simp [curvature, connection, wedgeSquare]
  abel

/-- The minus convention is equation (3.31). -/
def variation (d : I → A →+ A) (a : I → A) (e : A) (i : I) : A :=
  -d i e+(e*a i-a i*e)

/-- The plus convention is printed in equation (4.18). -/
def plusVariation (d : I → A →+ A) (a : I → A) (e : A) (i : I) : A :=
  d i e+(e*a i-a i*e)

/-- First variation of d a + a wedge a in coefficient directions. -/
def curvatureVariation (d : I → A →+ A) (a v : I → A) (i j : I) : A :=
  d i (v j)-d j (v i)+v i*a j+a i*v j-v j*a i-a j*v i

theorem variation_covariance (d : I → A →+ A)
    (hd : ∀ i x y, d i (x*y)=d i x*y+x*d i y)
    (hc : ∀ i j x, d i (d j x)=d j (d i x))
    (a : I → A) (e : A) (i j : I) :
    curvatureVariation d a (variation d a e) i j =
      e*curvature (connection d a) () i j-curvature (connection d a) () i j*e := by
  simp only [curvatureVariation, variation, map_add, map_sub, map_neg,
    hd, curvature_coeff]
  rw [hc i j e]
  noncomm_ring

/-- Exact residual when the sign of d epsilon is changed but the commutator
and curvature conventions are kept fixed. This is not silently set to zero. -/
theorem plus_variation_residual (d : I → A →+ A)
    (hd : ∀ i x y, d i (x*y)=d i x*y+x*d i y)
    (hc : ∀ i j x, d i (d j x)=d j (d i x))
    (a : I → A) (e : A) (i j : I) :
    curvatureVariation d a (plusVariation d a e) i j -
      (e*curvature (connection d a) () i j-curvature (connection d a) () i j*e) =
      2 * (d i e*a j-a j*d i e-(d j e*a i-a i*d j e)) := by
  simp only [curvatureVariation, plusVariation, map_add, map_sub, hd, curvature_coeff]
  rw [hc i j e]
  noncomm_ring

def covariant (d : I → A →+ A) (a : I → A) (i : I) (x : A) : A :=
  d i x+a i*x-x*a i

/-- Bianchi identity with derivatives, not only the Jacobi identity for constant fields. -/
theorem bianchi (d : I → A →+ A)
    (hd : ∀ i x y, d i (x*y)=d i x*y+x*d i y)
    (hc : ∀ i j x, d i (d j x)=d j (d i x))
    (a : I → A) (i j k : I) :
    covariant d a i (curvature (connection d a) () j k)+
      covariant d a j (curvature (connection d a) () k i)+
      covariant d a k (curvature (connection d a) () i j)=0 := by
  simp only [covariant, curvature_coeff, map_add, map_sub, hd]
  rw [hc i j (a k), hc j k (a i), hc k i (a j)]
  noncomm_ring

/-- Cyclicity is an explicit functional hypothesis; no integration is assumed. -/
theorem cyclic_commutator {M : Type*} [AddCommGroup M]
    (tau : A →+ M) (ht : ∀ x y, tau (x*y)=tau (y*x)) (e x : A) :
    tau (e*x-x*e)=0 := by rw [map_sub, ht e x, sub_self]

/-- The algebraic cancellation used in the local BF variation, conditional on
covariance and cyclic integration/trace, equations (4.19)--(4.21). -/
theorem bf_pairing_variation {M : Type*} [AddCommGroup M]
    (tau : A →+ M) (ht : ∀ x y, tau (x*y)=tau (y*x)) (e b g : A) :
    tau ((e*b-b*e)*g+b*(e*g-g*e))=0 := by
  have h : (e*b-b*e)*g+b*(e*g-g*e)=e*(b*g)-(b*g)*e := by noncomm_ring
  rw [h]
  exact cyclic_commutator tau ht e (b*g)

/-- A central volume coefficient may be moved into the cyclic functional. -/
theorem bf_with_central_volume {M : Type*} [AddCommGroup M]
    (tau : A →+ M) (ht : ∀ x y, tau (x*y)=tau (y*x))
    (volume e b g : A) (hv : volume*e=e*volume) :
    tau (volume*((e*b-b*e)*g+b*(e*g-g*e)))=0 := by
  have h : volume*((e*b-b*e)*g+b*(e*g-g*e)) =
      e*(volume*(b*g))-(volume*(b*g))*e := by
    noncomm_ring [hv]
  rw [h]
  exact cyclic_commutator tau ht e (volume*(b*g))

end InfoGeometry.Twistor.TwistedGauge
