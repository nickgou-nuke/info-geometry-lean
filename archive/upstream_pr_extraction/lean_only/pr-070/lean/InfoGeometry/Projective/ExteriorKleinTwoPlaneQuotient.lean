import InfoGeometry.Projective.ExteriorKleinFrameSurjection

/-!
# The framed exterior cover and the real two-plane carrier

This owner quotients nondegenerate ordered two-frames by equality of their
linear span.  The resulting quotient is equivalent to the native subtype of
two-dimensional real submodules of `Vec4`.

This is the set-level `Gr(2,4)` carrier needed for Plücker descent.  It does
not identify that carrier with Mathlib's scheme-oriented
`Module.Grassmannian`, whose structure records locally free quotient data.
-/

noncomputable section

namespace InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorKleinFrameSurjection

/-- The native set-level carrier of real two-planes in `Vec4`. -/
abbrev RealTwoPlane :=
  {P : Submodule ℝ Vec4 // Module.finrank ℝ P = 2}

/-- Nonvanishing of the top exterior product of a finite basis of a submodule,
after inclusion into the ambient space. -/
theorem exterior_ιMulti_coe_basis_ne_zero
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    {P : Submodule ℝ V} (b : Module.Basis (Fin n) ℝ P) :
    exteriorPower.ιMulti ℝ n (fun i => (b i : V)) ≠ 0 := by
  choose g hg using fun i : Fin n => LinearMap.exists_extend (b.coord i)
  let f : Fin n → Module.Dual ℝ V := g
  have hg_apply (i j : Fin n) :
      g i (b j : V) = (b.coord i) (b j) := by
    exact LinearMap.congr_fun (hg i) (b j)
  have heval :
      (exteriorPower.alternatingMapToDual ℝ V n f)
          (exteriorPower.ιMulti ℝ n (fun i => (b i : V))) = 1 := by
    rw [exteriorPower.alternatingMapToDual_apply_ιMulti]
    rw [show Matrix.of (fun i j => f j (b i : V)) = 1 by
      ext i j
      classical
      by_cases h : i = j <;>
        simp [f, hg_apply, h, Matrix.one_apply]]
    exact Matrix.det_one
  intro hzero
  rw [hzero, map_zero] at heval
  norm_num at heval

/-- The universal exterior product of a finite linearly independent family is
nonzero. -/
theorem exterior_ιMulti_ne_zero_of_linearIndependent
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : Fin n → V) (hv : LinearIndependent ℝ v) :
    exteriorPower.ιMulti ℝ n v ≠ 0 := by
  simpa only [Module.Basis.span_apply] using
    (exterior_ιMulti_coe_basis_ne_zero (Module.Basis.span hv))

/-- A nonzero exterior two-frame is linearly independent. -/
theorem nondegenerateExteriorFrame_linearIndependent
    (uv : NondegenerateExteriorFrame) :
    LinearIndependent ℝ uv.1 := by
  by_contra h
  exact uv.2 ((exteriorPower.ιMulti ℝ 2).map_linearDependent uv.1 h)

/-- The two-plane spanned by a nondegenerate exterior frame. -/
def frameSpan (uv : NondegenerateExteriorFrame) : RealTwoPlane :=
  ⟨Submodule.span ℝ (Set.range uv.1), by
    rw [finrank_span_eq_card
      (nondegenerateExteriorFrame_linearIndependent uv)]
    simp⟩

@[simp] theorem frameSpan_val (uv : NondegenerateExteriorFrame) :
    (frameSpan uv).1 = Submodule.span ℝ (Set.range uv.1) :=
  rfl

/-- Every real two-plane admits a nondegenerate ordered basis frame. -/
theorem frameSpan_surjective : Function.Surjective frameSpan := by
  rintro ⟨P, hP⟩
  let b : Module.Basis (Fin 2) ℝ P :=
    (Module.finBasis ℝ P).reindex (finCongr hP)
  have hwedge :
      exteriorPower.ιMulti ℝ 2 (fun i => (b i : Vec4)) ≠ 0 :=
    exterior_ιMulti_coe_basis_ne_zero b
  refine ⟨⟨fun i => (b i : Vec4), hwedge⟩, ?_⟩
  apply Subtype.ext
  change Submodule.span ℝ (Set.range (P.subtype ∘ b)) = P
  rw [Set.range_comp, Submodule.span_image, b.span_eq,
    Submodule.map_subtype_top]

/-- Change of ordered frame: two frames are equivalent exactly when they span
the same real two-plane. -/
def framePlaneSetoid : Setoid NondegenerateExteriorFrame :=
  Setoid.ker frameSpan

/-- Nondegenerate ordered frames modulo equality of their spanned plane. -/
abbrev FramePlaneQuotient := Quotient framePlaneSetoid

/-- The span map descended to the change-of-frame quotient. -/
def framePlaneQuotientToTwoPlane : FramePlaneQuotient → RealTwoPlane :=
  Quotient.lift frameSpan (fun _ _ h => h)

@[simp] theorem framePlaneQuotientToTwoPlane_mk
    (uv : NondegenerateExteriorFrame) :
    framePlaneQuotientToTwoPlane (Quotient.mk framePlaneSetoid uv) =
      frameSpan uv :=
  rfl

theorem framePlaneQuotientToTwoPlane_injective :
    Function.Injective framePlaneQuotientToTwoPlane := by
  intro q₁ q₂ h
  revert h
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro uv₁ uv₂ h
  exact Quotient.sound h

theorem framePlaneQuotientToTwoPlane_surjective :
    Function.Surjective framePlaneQuotientToTwoPlane := by
  intro P
  obtain ⟨uv, huv⟩ := frameSpan_surjective P
  exact ⟨Quotient.mk framePlaneSetoid uv, huv⟩

/-- Ordered nondegenerate two-frames modulo change of frame are exactly real
two-planes in `Vec4`. -/
noncomputable def framePlaneQuotientEquivTwoPlane :
    FramePlaneQuotient ≃ RealTwoPlane :=
  Equiv.ofBijective framePlaneQuotientToTwoPlane
    ⟨framePlaneQuotientToTwoPlane_injective,
      framePlaneQuotientToTwoPlane_surjective⟩

@[simp] theorem framePlaneQuotientEquivTwoPlane_apply_mk
    (uv : NondegenerateExteriorFrame) :
    framePlaneQuotientEquivTwoPlane
        (Quotient.mk framePlaneSetoid uv) = frameSpan uv :=
  rfl

end InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient
