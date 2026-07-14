import Mathlib.Tactic

/-!
# InfoGeometry.Prequantum.Scaling

Scalarized prequantum scaling laws relating curvature, symplectic scale, and `ℏ`.
-/

namespace Scaling
end Scaling

/-- Minimal prequantum line-bundle data (scalarized): symplectic scale `ω`,
curvature scale `F`, and conversion constant `ℏ` with relation `F = ω / ℏ`. -/
structure PrequantumData where
  omegaScale : ℝ
  curvatureScale : ℝ
  hbar : ℝ
  hbar_ne_zero : hbar ≠ 0
  curvature_relation : curvatureScale = omegaScale / hbar

@[ext] theorem PrequantumData.ext
    {P Q : PrequantumData}
    (hOmega : P.omegaScale = Q.omegaScale)
    (hCurv : P.curvatureScale = Q.curvatureScale)
    (hHbar : P.hbar = Q.hbar) :
    P = Q := by
  cases P
  cases Q
  cases hOmega
  cases hCurv
  cases hHbar
  simp

theorem PrequantumData.curvature_mul_hbar_eq_omega
    (P : PrequantumData) :
    P.curvatureScale * P.hbar = P.omegaScale := by
  rw [P.curvature_relation]
  field_simp [P.hbar_ne_zero]

theorem PrequantumData.omega_eq_hbar_mul_curvature
    (P : PrequantumData) :
    P.omegaScale = P.hbar * P.curvatureScale := by
  have h := P.curvature_mul_hbar_eq_omega
  linarith

/-- Rescaling `ℏ` by `c` rescales curvature by `1/c` at fixed symplectic scale. -/
noncomputable def PrequantumData.rescaleHbar
    (P : PrequantumData) (c : ℝ) (hc : c ≠ 0) : PrequantumData where
  omegaScale := P.omegaScale
  curvatureScale := P.curvatureScale / c
  hbar := c * P.hbar
  hbar_ne_zero := mul_ne_zero hc P.hbar_ne_zero
  curvature_relation := by
    rw [P.curvature_relation]
    field_simp [hc, P.hbar_ne_zero]

theorem PrequantumData.rescaleHbar_curvature
    (P : PrequantumData) (c : ℝ) (hc : c ≠ 0) :
    (P.rescaleHbar c hc).curvatureScale = P.curvatureScale / c := rfl

theorem PrequantumData.rescaleHbar_hbar
    (P : PrequantumData) (c : ℝ) (hc : c ≠ 0) :
    (P.rescaleHbar c hc).hbar = c * P.hbar := rfl

theorem PrequantumData.rescaleHbar_rescaleHbar
    (P : PrequantumData) (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) :
    (P.rescaleHbar c hc).rescaleHbar d hd
      = P.rescaleHbar (d * c) (mul_ne_zero hd hc) := by
  ext <;> simp [PrequantumData.rescaleHbar, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

noncomputable instance : SMul (Units ℝ) PrequantumData :=
  ⟨fun u P => P.rescaleHbar (u : ℝ) (Units.ne_zero u)⟩

@[simp] theorem PrequantumData.smul_omegaScale
    (u : Units ℝ) (P : PrequantumData) :
    (u • P).omegaScale = P.omegaScale := rfl

@[simp] theorem PrequantumData.smul_curvatureScale
    (u : Units ℝ) (P : PrequantumData) :
    (u • P).curvatureScale = P.curvatureScale / (u : ℝ) := rfl

@[simp] theorem PrequantumData.smul_hbar
    (u : Units ℝ) (P : PrequantumData) :
    (u • P).hbar = (u : ℝ) * P.hbar := rfl

noncomputable instance : MulAction (Units ℝ) PrequantumData where
  one_smul := by
    intro P
    apply PrequantumData.ext <;> simp
  mul_smul := by
    intro u v P
    symm
    simpa [mul_assoc] using
      (P.rescaleHbar_rescaleHbar
        (c := (v : ℝ)) (d := (u : ℝ))
        (hc := Units.ne_zero v) (hd := Units.ne_zero u))

namespace PrequantumData

/-- Local gauge group for scalarized prequantum data. -/
abbrev Gauge := Units ℝ

/-- Weight `-1` observable (connection/curvature scale). -/
def connectionScale (P : PrequantumData) : ℝ :=
  P.curvatureScale

@[simp] theorem connectionScale_smul
    (u : Gauge) (P : PrequantumData) :
    connectionScale (u • P) = connectionScale P / (u : ℝ) := by
  rfl

/-- Gauge-invariant scalar `F * ℏ`, equal to `ω`. -/
def covariantScale (P : PrequantumData) : ℝ :=
  P.curvatureScale * P.hbar

@[simp] theorem covariantScale_eq_omega (P : PrequantumData) :
    covariantScale P = P.omegaScale := by
  exact P.curvature_mul_hbar_eq_omega

@[simp] theorem covariantScale_smul
    (u : Gauge) (P : PrequantumData) :
    covariantScale (u • P) = covariantScale P := by
  calc
    covariantScale (u • P) = (u • P).omegaScale := covariantScale_eq_omega (u • P)
    _ = P.omegaScale := by simp
    _ = covariantScale P := (covariantScale_eq_omega P).symm

/-- Gauge-orbit equivalence on scalarized prequantum data. -/
def GaugeEquivalent (P Q : PrequantumData) : Prop :=
  ∃ u : Gauge, u • P = Q

lemma gaugeEquivalent_refl (P : PrequantumData) :
    GaugeEquivalent P P := by
  refine ⟨1, ?_⟩
  simp

lemma gaugeEquivalent_symm {P Q : PrequantumData}
    (h : GaugeEquivalent P Q) :
    GaugeEquivalent Q P := by
  rcases h with ⟨u, rfl⟩
  refine ⟨u⁻¹, ?_⟩
  simp [smul_smul]

lemma gaugeEquivalent_trans {P Q R : PrequantumData}
    (hPQ : GaugeEquivalent P Q)
    (hQR : GaugeEquivalent Q R) :
    GaugeEquivalent P R := by
  rcases hPQ with ⟨u, rfl⟩
  rcases hQR with ⟨v, rfl⟩
  refine ⟨v * u, ?_⟩
  simp [smul_smul]

/-- Setoid of gauge orbits. -/
def gaugeSetoid : Setoid PrequantumData where
  r := GaugeEquivalent
  iseqv := ⟨gaugeEquivalent_refl, gaugeEquivalent_symm, gaugeEquivalent_trans⟩

/-- `covariantScale` descends to the gauge quotient. -/
noncomputable def covariantScaleOnQuotient :
    Quotient gaugeSetoid → ℝ :=
  Quotient.lift
    covariantScale
    (by
      intro P Q hPQ
      rcases hPQ with ⟨u, rfl⟩
      simp)

@[simp] theorem covariantScaleOnQuotient_mk (P : PrequantumData) :
    covariantScaleOnQuotient (Quotient.mk _ P) = covariantScale P := rfl

/-- `omegaScale` also descends (same invariant, different presentation). -/
noncomputable def omegaScaleOnQuotient :
    Quotient gaugeSetoid → ℝ :=
  Quotient.lift
    (fun P => P.omegaScale)
    (by
      intro P Q hPQ
      rcases hPQ with ⟨u, rfl⟩
      simp)

@[simp] theorem omegaScaleOnQuotient_mk (P : PrequantumData) :
    omegaScaleOnQuotient (Quotient.mk _ P) = P.omegaScale := rfl

end PrequantumData


namespace Scaling

/-- Canonical namespaced façade for the scalarized prequantum scaling data. -/
abbrev PrequantumData := _root_.PrequantumData

namespace PrequantumData

@[ext] theorem ext
    {P Q : PrequantumData}
    (hOmega : P.omegaScale = Q.omegaScale)
    (hCurv : P.curvatureScale = Q.curvatureScale)
    (hHbar : P.hbar = Q.hbar) :
    P = Q := by
  simpa using (_root_.PrequantumData.ext hOmega hCurv hHbar)

noncomputable abbrev rescaleHbar
    (P : PrequantumData) (c : ℝ) (hc : c ≠ 0) : PrequantumData :=
  _root_.PrequantumData.rescaleHbar P c hc

abbrev Gauge := _root_.PrequantumData.Gauge

abbrev connectionScale (P : PrequantumData) : ℝ :=
  _root_.PrequantumData.connectionScale P

abbrev covariantScale (P : PrequantumData) : ℝ :=
  _root_.PrequantumData.covariantScale P

abbrev GaugeEquivalent (P Q : PrequantumData) : Prop :=
  _root_.PrequantumData.GaugeEquivalent P Q

noncomputable abbrev covariantScaleOnQuotient :
    Quotient _root_.PrequantumData.gaugeSetoid → ℝ :=
  _root_.PrequantumData.covariantScaleOnQuotient

noncomputable abbrev omegaScaleOnQuotient :
    Quotient _root_.PrequantumData.gaugeSetoid → ℝ :=
  _root_.PrequantumData.omegaScaleOnQuotient

end PrequantumData

end Scaling
