/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveNilpotentFlows
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Algebraic idempotent orbit contracts

A stabilizer quotient, formal first-order directions, supported units, and
transvection recovery. No topology, principal bundle, or exact-order claim.
The conjugation action is installed locally, not as a global instance.
-/
namespace InfoGeometry.Canonical.IdempotentOrbitContracts
variable {A : Type*} [Ring A]

/-- Unit conjugation on the underlying ring. -/
@[instance_reducible] def unitConjugation : MulAction Aˣ A where
  smul g x := (g : A) * x * (↑(g⁻¹) : A)
  one_smul x := by
    change (↑(1 : Aˣ) : A)*x*(↑((1 : Aˣ)⁻¹) : A)=x
    simp
  mul_smul g h x := by
    change (↑(g*h) : A)*x*(↑((g*h)⁻¹) : A)=
      (g : A)*((h : A)*x*(↑(h⁻¹) : A))*(↑(g⁻¹) : A)
    simp [mul_assoc]

attribute [local instance] unitConjugation
local instance conjugationSMul : SMul Aˣ A := unitConjugation.toSMul

/-- Native quotient by the actual stabilizer, rather than a kernel setoid. -/
noncomputable def quotientEquivOrbit (p : A) :
    (Aˣ ⧸ MulAction.stabilizer Aˣ p) ≃ MulAction.orbit Aˣ p :=
  (MulAction.orbitEquivQuotientStabilizer Aˣ p).symm

theorem stabilizer_iff_commute (p : A) (g : Aˣ) :
    g ∈ MulAction.stabilizer Aˣ p ↔ (g : A)*p=p*(g : A) := by
  change (g : A)*p*(↑(g⁻¹) : A)=p ↔ _
  exact GrassmannianBundleCyclotomicOrientability.unitOrbitMap_eq_self_iff p g

/-- The local native action agrees with the existing orbit map. -/
theorem orbit_eq_existing_range (p : A) :
    MulAction.orbit Aˣ p =
      Set.range (GrassmannianBundleCyclotomicOrientability.unitOrbitMap p) := rfl

/-- Linearized idempotency forces the diagonal corner to vanish. -/
theorem tangent_diagonal_zero {p v : A} (hp : p*p=p)
    (hv : p*v+v*p=v) : p*v*p=0 := by
  have h := congrArg (fun x : A => p*x) hv
  have hpp : p*(p*v)=p*v := by rw [← mul_assoc,hp]
  simp only [mul_add,hpp,← mul_assoc] at h
  exact add_left_cancel (show p*v+p*v*p=p*v+0 by simpa using h)

/-- Both directed off-diagonal corners comprise a formal tangent vector. -/
theorem tangent_split {p v : A} (hp : p*p=p) (hv : p*v+v*p=v) :
    v=p*v*(1-p)+(1-p)*v*p := by
  have hz := tangent_diagonal_zero hp hv
  calc
    v = p*v+v*p := hv.symm
    _ = p*v*(1-p)+(1-p)*v*p := by noncomm_ring [hz]

/-- Every formal tangent vector has an explicit infinitesimal conjugation lift. -/
theorem tangent_horizontal_lift {p v : A} (hp : p*p=p)
    (hv : p*v+v*p=v) :
    (v*p-p*v)*p-p*(v*p-p*v)=v := by
  have hz := tangent_diagonal_zero hp hv
  calc
    _ = v*(p*p)+(p*p)*v-2 • (p*v*p) := by simp only [two_nsmul]; noncomm_ring
    _ = v := by rw [hp,hz]; simpa [add_comm] using hv

/-- Two generators have the same variation exactly when their difference
commutes with the reference element. -/
theorem generator_ambiguity (p h k : A) :
    h*p-p*h=k*p-p*k ↔ Commute (h-k) p := by
  change _ ↔ (h-k)*p=p*(h-k)
  have he : (h-k)*p-p*(h-k)=(h*p-p*h)-(k*p-p*k) := by noncomm_ring
  rw [← sub_eq_zero, ← he, sub_eq_zero]

/-- Complete a two-sided unit of an idempotent corner to an ambient unit. -/
def completeCornerUnit (e x y : A) (he : e*e=e)
    (hex : e*x=x) (hxe : x*e=x) (hey : e*y=y) (hye : y*e=y)
    (hxy : x*y=e) (hyx : y*x=e) : Aˣ where
  val := 1-e+x
  inv := 1-e+y
  val_inv := by noncomm_ring [he,hex,hxe,hey,hye,hxy]
  inv_val := by noncomm_ring [he,hex,hxe,hey,hye,hyx]

/-- Recover the active transvection from the fourth- and third-cyclotomic
operators. Only square-zero and the first inner-inverse law are needed. -/
theorem cyclotomic_pair_recovers_transvection {d B : A}
    (hd : d*d=0) (hB : B*B=0) (hr : d*B*d=d) :
    (-(d-B))*(-(B*d)+d-B)=(d*B+B*d)+d := by
  have hbb : B*(B*d)=0 := by rw [← mul_assoc,hB,zero_mul]
  have hdr : d*(B*d)=d := by simpa only [mul_assoc] using hr
  noncomm_ring [hd,hB,hr]
  simp only [hbb,hdr]
  abel

end InfoGeometry.Canonical.IdempotentOrbitContracts
