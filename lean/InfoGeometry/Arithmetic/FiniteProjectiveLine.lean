import Mathlib.LinearAlgebra.Projectivization.Action
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.GroupTheory.QuotientGroup.Basic

noncomputable section

namespace InfoGeometry.Arithmetic.FiniteProjectiveLine

open scoped LinearAlgebra.Projectivization

abbrev Line (F : Type*) [Field F] := ℙ F (Fin 2 → F)

abbrev GL2 (F : Type*) [Field F] :=
  LinearMap.GeneralLinearGroup F (Fin 2 → F)

def translationLinearEquiv [Field F] (b : F) :
    (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) :=
  { toFun := fun v => ![v 0 + b * v 1, v 1]
    invFun := fun v => ![v 0 - b * v 1, v 1]
    left_inv := by
      intro v
      funext i
      fin_cases i <;> simp
    right_inv := by
      intro v
      funext i
      fin_cases i <;> simp
    map_add' := by
      intro v w
      funext i
      fin_cases i <;>
        simp [mul_add, add_assoc, add_left_comm]
    map_smul' := by
      intro c v
      funext i
      fin_cases i
      · simp [smul_eq_mul]
        ring
      · simp }

noncomputable def translationGL2 [Field F] (b : F) : GL2 F :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (translationLinearEquiv b)

def scaleLinearEquiv [Field F] (a : Fˣ) :
    (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) :=
  { toFun := fun v => ![(a : F) * v 0, v 1]
    invFun := fun v => ![((a⁻¹ : Fˣ) : F) * v 0, v 1]
    left_inv := by
      intro v
      funext i
      fin_cases i <;> simp
    right_inv := by
      intro v
      funext i
      fin_cases i <;> simp
    map_add' := by
      intro v w
      funext i
      fin_cases i <;> simp [mul_add]
    map_smul' := by
      intro c v
      funext i
      fin_cases i
      · simp [smul_eq_mul]
        ring
      · simp }

noncomputable def scaleGL2 [Field F] (a : Fˣ) : GL2 F :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (scaleLinearEquiv a)

def swapLinearEquiv [Field F] :
    (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) :=
  { toFun := fun v => ![v 1, v 0]
    invFun := fun v => ![v 1, v 0]
    left_inv := by
      intro v
      funext i
      fin_cases i <;> simp
    right_inv := by
      intro v
      funext i
      fin_cases i <;> simp
    map_add' := by
      intro v w
      funext i
      fin_cases i <;> simp
    map_smul' := by
      intro c v
      funext i
      fin_cases i <;> simp [smul_eq_mul] }

noncomputable def swapGL2 [Field F] : GL2 F :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv swapLinearEquiv

noncomputable def frameCycleGL2 [Field F] : GL2 F :=
  swapGL2 (F := F) * translationGL2 (F := F) 1 *
    scaleGL2 (F := F) (Units.mk0 (-1) (by simp))

noncomputable instance instFintypeLine [Field F] [Fintype F] :
    Fintype (Line F) := Fintype.ofFinite (Line F)

theorem card_line [Field F] [Fintype F] :
    Fintype.card (Line F) = Fintype.card F + 1 := by
  have h := Projectivization.card_of_finrank F (Fin 2 → F)
    (n := 2) (by simp)
  simpa [Line, Nat.card_eq_fintype_card, add_comm] using h

theorem units_smul_eq_self [Field F] (a : Fˣ) (x : Line F) :
    a • x = x := by
  induction x using Projectivization.ind with
  | h v hv =>
    rw [Projectivization.smul_mk]
    have hav : a • v ≠ 0 := by
      exact (smul_ne_zero_iff_ne a).2 hv
    apply (Projectivization.mk_eq_mk_iff' F (a • v) v
      hav hv).2
    exact ⟨(a : F), by simp [Units.smul_def]⟩

theorem gl2_smul_mk [Field F] (g : GL2 F) {v : Fin 2 → F} (hv : v ≠ 0) :
    g • Projectivization.mk F v hv =
      Projectivization.mk F (g • v) ((smul_ne_zero_iff_ne g).2 hv) := by
  exact Projectivization.smul_mk g hv

theorem gl2_smul_eq_iff [Field F] (g : GL2 F)
    (x y : Line F) :
    g • x = y ↔ x = g⁻¹ • y := by
  constructor
  · intro h
    rw [← inv_smul_smul g x, h]
  · intro h
    rw [h, smul_smul, mul_inv_cancel, one_smul]

noncomputable def scalarGL2 [Field F] (a : Fˣ) : GL2 F :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    (LinearEquiv.ofBijective
      (DistribSMul.toLinearMap F (Fin 2 → F) (a : F))
      a.isUnit.smul_bijective)

theorem scalarGL2_smul_eq_self [Field F] (a : Fˣ) (x : Line F) :
    scalarGL2 (F := F) a • x = x := by
  induction x using Projectivization.ind with
  | h v hv =>
      rw [gl2_smul_mk]
      change Projectivization.mk F ((a : F) • v) _ =
        Projectivization.mk F v hv
      exact units_smul_eq_self a (Projectivization.mk F v hv)

noncomputable def scalarGL2Hom [Field F] : Fˣ →* GL2 F where
  toFun := scalarGL2
  map_one' := by
    ext v
    simp [scalarGL2]
  map_mul' a b := by
    ext v
    simp [scalarGL2]
    ring

/- The permutation representation of `GL₂(F)` on the projective line. -/
noncomputable def gl2ActionHom [Field F] : GL2 F →* Equiv.Perm (Line F) :=
  MulAction.toPermHom (GL2 F) (Line F)

theorem scalarGL2Hom_mem_action_kernel [Field F] (a : Fˣ) :
    scalarGL2Hom (F := F) a ∈ (gl2ActionHom (F := F)).ker := by
  rw [MonoidHom.mem_ker]
  ext x
  change scalarGL2 (F := F) a • x = x
  exact scalarGL2_smul_eq_self a x

theorem scalarGL2Hom_range_le_action_kernel [Field F] :
    MonoidHom.range (scalarGL2Hom (F := F)) ≤
      (gl2ActionHom (F := F)).ker := by
  intro g hg
  rcases hg with ⟨a, rfl⟩
  exact scalarGL2Hom_mem_action_kernel a

private lemma action_kernel_fix_mk [Field F] (g : GL2 F)
    (hg : g ∈ (gl2ActionHom (F := F)).ker)
    (v : Fin 2 → F) (hv : v ≠ 0) :
    g • Projectivization.mk F v hv = Projectivization.mk F v hv := by
  have hhom : gl2ActionHom (F := F) g = 1 := hg
  have hpoint := congrArg
    (fun e : Equiv.Perm (Line F) => e (Projectivization.mk F v hv)) hhom
  simpa [gl2ActionHom] using hpoint

theorem action_kernel_le_scalarGL2Hom_range [Field F] :
    (gl2ActionHom (F := F)).ker ≤
      MonoidHom.range (scalarGL2Hom (F := F)) := by
  intro g hg
  let e0 : Fin 2 → F := ![1, 0]
  let e1 : Fin 2 → F := ![0, 1]
  have he0 : e0 ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [e0] at h0
  have he1 : e1 ≠ 0 := by
    intro h
    have h1 := congrFun h 1
    simp [e1] at h1
  have hs : e0 + e1 ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [e0, e1] at h0
  have h0 := (Projectivization.mk_eq_mk_iff' F (g • e0) e0
    ((smul_ne_zero_iff_ne g).2 he0) he0).mp
    (action_kernel_fix_mk g hg e0 he0)
  have h1 := (Projectivization.mk_eq_mk_iff' F (g • e1) e1
    ((smul_ne_zero_iff_ne g).2 he1) he1).mp
    (action_kernel_fix_mk g hg e1 he1)
  have hsum := (Projectivization.mk_eq_mk_iff' F (g • (e0 + e1)) (e0 + e1)
    ((smul_ne_zero_iff_ne g).2 hs) hs).mp
    (action_kernel_fix_mk g hg (e0 + e1) hs)
  rcases h0 with ⟨a, ha⟩
  rcases h1 with ⟨b, hb⟩
  rcases hsum with ⟨c, hc⟩
  have hc' : c • e0 + c • e1 = g • e0 + g • e1 := by
    simpa [smul_add] using hc
  have hge0 : (g • e0) 0 = a := by
    simpa [e0] using (congrFun ha 0).symm
  have hge1 : (g • e1) 0 = 0 := by
    simpa [e1] using (congrFun hb 0).symm
  have hge0' : (g • e0) 1 = 0 := by
    simpa [e0] using (congrFun ha 1).symm
  have hge1' : (g • e1) 1 = b := by
    simpa [e1] using (congrFun hb 1).symm
  have hac : c = a := by
    calc
      c = (g • e0 + g • e1) 0 := by simpa [e0, e1] using congrFun hc' 0
      _ = (g • e0) 0 + (g • e1) 0 := by rfl
      _ = a + 0 := by rw [hge0, hge1]
      _ = a := add_zero _
  have hbc : c = b := by
    calc
      c = (g • e0 + g • e1) 1 := by simpa [e0, e1] using congrFun hc' 1
      _ = (g • e0) 1 + (g • e1) 1 := by rfl
      _ = 0 + b := by rw [hge0', hge1']
      _ = b := zero_add _
  have hab : a = b := hac.symm.trans hbc
  have ha_ne : a ≠ 0 := by
    intro ha0
    have hzero : g • e0 = 0 := by simpa [ha0] using ha.symm
    exact ((smul_ne_zero_iff_ne g).2 he0) hzero
  let au : Fˣ := Units.mk0 a ha_ne
  refine ⟨au, ?_⟩
  apply Units.ext
  apply LinearMap.ext
  intro v
  have hv : v = v 0 • e0 + v 1 • e1 := by
    ext i
    fin_cases i <;> simp [e0, e1]
  rw [hv, map_add, map_smul, map_smul]
  change v 0 • (scalarGL2 (F := F) au).toLinearEquiv e0 +
      v 1 • (scalarGL2 (F := F) au).toLinearEquiv e1 =
      g • (v 0 • e0 + v 1 • e1)
  have hs0 : (scalarGL2 (F := F) au).toLinearEquiv e0 = a • e0 := by
    simp [scalarGL2, au]
  have hs1 : (scalarGL2 (F := F) au).toLinearEquiv e1 = a • e1 := by
    simp [scalarGL2, au]
  rw [hs0, hs1]
  have hgadd : g • (v 0 • e0 + v 1 • e1) =
      v 0 • (g • e0) + v 1 • (g • e1) := by
    change g.toLinearEquiv (v 0 • e0 + v 1 • e1) =
      v 0 • g.toLinearEquiv e0 + v 1 • g.toLinearEquiv e1
    rw [map_add, map_smul, map_smul]
  rw [hgadd]
  rw [show g • e0 = a • e0 from ha.symm,
    show g • e1 = a • e1 from hab ▸ hb.symm]

theorem action_kernel_eq_scalarGL2Hom_range [Field F] :
    (gl2ActionHom (F := F)).ker =
      MonoidHom.range (scalarGL2Hom (F := F)) := by
  apply le_antisymm
  · exact action_kernel_le_scalarGL2Hom_range
  · exact scalarGL2Hom_range_le_action_kernel

/-
The effective projective quotient of `GL₂(F)` on `ℙ¹(F)`.  This is defined by
the kernel of the native projective action.
-/
abbrev PGL2 (F : Type*) [Field F] :=
  GL2 F ⧸ (gl2ActionHom (F := F)).ker

noncomputable def pgl2ActionHom [Field F] :
    PGL2 F →* Equiv.Perm (Line F) :=
  QuotientGroup.lift (gl2ActionHom (F := F)).ker
    (gl2ActionHom (F := F)) le_rfl

@[simp] theorem pgl2ActionHom_mk [Field F] (g : GL2 F) :
    pgl2ActionHom (F := F)
        (QuotientGroup.mk' (gl2ActionHom (F := F)).ker g) =
      gl2ActionHom (F := F) g := by
  rfl

theorem pgl2ActionHom_injective [Field F] :
    Function.Injective (pgl2ActionHom (F := F)) := by
  exact QuotientGroup.kerLift_injective (gl2ActionHom (F := F))

noncomputable instance pgl2MulAction [Field F] : MulAction (PGL2 F) (Line F) :=
  MulAction.compHom (Line F) (pgl2ActionHom (F := F))

noncomputable def affinePoint [Field F] (x : F) : Line F :=
  Projectivization.mk F ![x, 1] (by
    intro h
    have h1 := congrFun h 1
    simp at h1)

noncomputable def infinityPoint [Field F] : Line F :=
  Projectivization.mk F ![1, 0] (by
    intro h
    have h0 := congrFun h 0
    simp at h0)

noncomputable def zeroPoint [Field F] : Line F := affinePoint 0

noncomputable def onePoint [Field F] : Line F := affinePoint 1

theorem gl2_smul_affinePoint [Field F] (g : GL2 F) (x : F)
    (hden : (g • (![x, 1] : Fin 2 → F)) 1 ≠ 0) :
    g • affinePoint x =
      affinePoint ((g • (![x, 1] : Fin 2 → F)) 0 /
        (g • (![x, 1] : Fin 2 → F)) 1) := by
  change g • Projectivization.mk F ![x, 1] _ = _
  rw [gl2_smul_mk]
  apply (Projectivization.mk_eq_mk_iff' F
    (g • (![x, 1] : Fin 2 → F)) ![
      (g • (![x, 1] : Fin 2 → F)) 0 /
        (g • (![x, 1] : Fin 2 → F)) 1, 1]
    ((smul_ne_zero_iff_ne g).2 (by simp)) (by simp)).2
  refine ⟨(g • (![x, 1] : Fin 2 → F)) 1, ?_⟩
  funext i
  fin_cases i
  · change (g • (![x, 1] : Fin 2 → F)) 1 *
      ((g • (![x, 1] : Fin 2 → F)) 0 /
        (g • (![x, 1] : Fin 2 → F)) 1) =
      (g • (![x, 1] : Fin 2 → F)) 0
    field_simp [hden]
  · change (g • (![x, 1] : Fin 2 → F)) 1 * 1 =
      (g • (![x, 1] : Fin 2 → F)) 1
    simp

theorem gl2_smul_affinePoint_of_apply_one_eq_zero [Field F]
    (g : GL2 F) (x : F)
    (hden : (g • (![x, 1] : Fin 2 → F)) 1 = 0) :
    g • affinePoint x = infinityPoint (F := F) := by
  change g • Projectivization.mk F ![x, 1] _ = _
  rw [gl2_smul_mk]
  have hvec : (g • (![x, 1] : Fin 2 → F)) ≠ 0 :=
    (smul_ne_zero_iff_ne g).2 (by simp)
  have hfirst : (g • (![x, 1] : Fin 2 → F)) 0 ≠ 0 := by
    intro hzero
    apply hvec
    funext i
    fin_cases i <;> simp [hzero, hden]
  apply (Projectivization.mk_eq_mk_iff' F
    (g • (![x, 1] : Fin 2 → F)) ![1, 0] hvec (by simp)).2
  refine ⟨(g • (![x, 1] : Fin 2 → F)) 0, ?_⟩
  funext i
  fin_cases i
  · change (g • (![x, 1] : Fin 2 → F)) 0 * 1 =
      (g • (![x, 1] : Fin 2 → F)) 0
    simp
  · change (g • (![x, 1] : Fin 2 → F)) 0 * 0 =
      (g • (![x, 1] : Fin 2 → F)) 1
    simp [hden]

theorem gl2_smul_affinePoint_affine_or_infinity [Field F]
    (g : GL2 F) (x : F) :
    g • affinePoint x =
        affinePoint ((g • (![x, 1] : Fin 2 → F)) 0 /
          (g • (![x, 1] : Fin 2 → F)) 1) ∨
      g • affinePoint x = infinityPoint (F := F) := by
  by_cases hden : (g • (![x, 1] : Fin 2 → F)) 1 = 0
  · exact Or.inr (gl2_smul_affinePoint_of_apply_one_eq_zero g x hden)
  · exact Or.inl (gl2_smul_affinePoint g x hden)

theorem gl2_smul_infinityPoint_of_apply_one_ne_zero [Field F]
    (g : GL2 F)
    (hden : (g • (![1, 0] : Fin 2 → F)) 1 ≠ 0) :
    g • infinityPoint (F := F) =
      affinePoint ((g • (![1, 0] : Fin 2 → F)) 0 /
        (g • (![1, 0] : Fin 2 → F)) 1) := by
  change g • Projectivization.mk F ![1, 0] _ = _
  rw [gl2_smul_mk]
  apply (Projectivization.mk_eq_mk_iff' F
    (g • (![1, 0] : Fin 2 → F)) ![
      (g • (![1, 0] : Fin 2 → F)) 0 /
        (g • (![1, 0] : Fin 2 → F)) 1, 1]
    ((smul_ne_zero_iff_ne g).2 (by simp)) (by simp)).2
  refine ⟨(g • (![1, 0] : Fin 2 → F)) 1, ?_⟩
  funext i
  fin_cases i
  · change (g • (![1, 0] : Fin 2 → F)) 1 *
      ((g • (![1, 0] : Fin 2 → F)) 0 /
        (g • (![1, 0] : Fin 2 → F)) 1) =
      (g • (![1, 0] : Fin 2 → F)) 0
    field_simp [hden]
  · change (g • (![1, 0] : Fin 2 → F)) 1 * 1 =
      (g • (![1, 0] : Fin 2 → F)) 1
    simp

theorem gl2_smul_infinityPoint_of_apply_one_eq_zero [Field F]
    (g : GL2 F)
    (hden : (g • (![1, 0] : Fin 2 → F)) 1 = 0) :
    g • infinityPoint (F := F) = infinityPoint (F := F) := by
  change g • Projectivization.mk F ![1, 0] _ = _
  rw [gl2_smul_mk]
  have hvec : (g • (![1, 0] : Fin 2 → F)) ≠ 0 :=
    (smul_ne_zero_iff_ne g).2 (by simp)
  have hfirst : (g • (![1, 0] : Fin 2 → F)) 0 ≠ 0 := by
    intro hzero
    apply hvec
    funext i
    fin_cases i <;> simp [hzero, hden]
  apply (Projectivization.mk_eq_mk_iff' F
    (g • (![1, 0] : Fin 2 → F)) ![1, 0] hvec (by simp)).2
  refine ⟨(g • (![1, 0] : Fin 2 → F)) 0, ?_⟩
  funext i
  fin_cases i
  · change (g • (![1, 0] : Fin 2 → F)) 0 * 1 =
      (g • (![1, 0] : Fin 2 → F)) 0
    simp
  · change (g • (![1, 0] : Fin 2 → F)) 0 * 0 =
      (g • (![1, 0] : Fin 2 → F)) 1
    simp [hden]

theorem gl2_smul_infinityPoint_affine_or_infinity [Field F]
    (g : GL2 F) :
    g • infinityPoint (F := F) =
        affinePoint ((g • (![1, 0] : Fin 2 → F)) 0 /
          (g • (![1, 0] : Fin 2 → F)) 1) ∨
      g • infinityPoint (F := F) = infinityPoint (F := F) := by
  by_cases hden : (g • (![1, 0] : Fin 2 → F)) 1 = 0
  · exact Or.inr (gl2_smul_infinityPoint_of_apply_one_eq_zero g hden)
  · exact Or.inl (gl2_smul_infinityPoint_of_apply_one_ne_zero g hden)

theorem translationGL2_smul_affinePoint [Field F] (b x : F) :
    translationGL2 (F := F) b • affinePoint x = affinePoint (x + b) := by
  rw [gl2_smul_affinePoint (g := translationGL2 (F := F) b) (x := x)]
  · have h0 : (translationGL2 (F := F) b • (![x, 1] : Fin 2 → F)) 0 =
        x + b := by
      change (translationLinearEquiv b (![x, 1])) 0 = x + b
      simp [translationLinearEquiv]
    have h1 : (translationGL2 (F := F) b • (![x, 1] : Fin 2 → F)) 1 =
        1 := by
      change (translationLinearEquiv b (![x, 1])) 1 = 1
      simp [translationLinearEquiv]
    rw [h0, h1]
    simp
  · have h1 : (translationGL2 (F := F) b • (![x, 1] : Fin 2 → F)) 1 =
        1 := by
      change (translationLinearEquiv b (![x, 1])) 1 = 1
      simp [translationLinearEquiv]
    rw [h1]
    simp

theorem scaleGL2_smul_affinePoint [Field F] (a : Fˣ) (x : F) :
    scaleGL2 (F := F) a • affinePoint x =
      affinePoint ((a : F) * x) := by
  rw [gl2_smul_affinePoint (g := scaleGL2 (F := F) a) (x := x)]
  · have h0 : (scaleGL2 (F := F) a • (![x, 1] : Fin 2 → F)) 0 =
        (a : F) * x := by
      change (scaleLinearEquiv a (![x, 1])) 0 = (a : F) * x
      simp [scaleLinearEquiv]
    have h1 : (scaleGL2 (F := F) a • (![x, 1] : Fin 2 → F)) 1 =
        1 := by
      change (scaleLinearEquiv a (![x, 1])) 1 = 1
      simp [scaleLinearEquiv]
    rw [h0, h1]
    simp
  · have h1 : (scaleGL2 (F := F) a • (![x, 1] : Fin 2 → F)) 1 =
        1 := by
      change (scaleLinearEquiv a (![x, 1])) 1 = 1
      simp [scaleLinearEquiv]
    rw [h1]
    simp

theorem swapGL2_smul_affinePoint_of_ne_zero [Field F] (x : F)
    (hx : x ≠ 0) :
    swapGL2 (F := F) • affinePoint x = affinePoint x⁻¹ := by
  rw [gl2_smul_affinePoint (g := swapGL2 (F := F)) (x := x)]
  · have h0 : (swapGL2 (F := F) • (![x, 1] : Fin 2 → F)) 0 = 1 := by
      change (swapLinearEquiv (![x, 1])) 0 = 1
      simp [swapLinearEquiv]
    have h1 : (swapGL2 (F := F) • (![x, 1] : Fin 2 → F)) 1 = x := by
      change (swapLinearEquiv (![x, 1])) 1 = x
      simp [swapLinearEquiv]
    rw [h0, h1]
    simp
  · change (swapLinearEquiv (![x, 1])) 1 ≠ 0
    simpa [swapLinearEquiv] using hx

theorem swapGL2_smul_affinePoint_zero [Field F] :
    swapGL2 (F := F) • affinePoint (0 : F) = infinityPoint (F := F) := by
  apply gl2_smul_affinePoint_of_apply_one_eq_zero
  change (swapLinearEquiv (![0, 1])) 1 = 0
  simp [swapLinearEquiv]

theorem swapGL2_smul_infinityPoint [Field F] :
    swapGL2 (F := F) • infinityPoint (F := F) = zeroPoint (F := F) := by
  change swapGL2 (F := F) • Projectivization.mk F ![1, 0] _ = _
  rw [gl2_smul_mk]
  apply (Projectivization.mk_eq_mk_iff' F ![0, 1] ![0, 1]
    (by simp) (by simp)).2
  exact ⟨1, by funext i; fin_cases i <;> simp⟩

theorem translationGL2_smul_zeroPoint [Field F] (b : F) :
    translationGL2 (F := F) b • zeroPoint (F := F) = affinePoint b := by
  simpa [zeroPoint] using
    (translationGL2_smul_affinePoint (F := F) b 0)

theorem translationGL2_smul_onePoint [Field F] (b : F) :
    translationGL2 (F := F) b • onePoint (F := F) = affinePoint (1 + b) := by
  simpa [onePoint] using
    (translationGL2_smul_affinePoint (F := F) b 1)

theorem translationGL2_smul_infinityPoint [Field F] (b : F) :
    translationGL2 (F := F) b • infinityPoint (F := F) =
      infinityPoint (F := F) := by
  apply gl2_smul_infinityPoint_of_apply_one_eq_zero
  change (translationLinearEquiv b (![1, 0])) 1 = 0
  simp [translationLinearEquiv]

theorem translationGL2_smul_affinePoint_to_zero [Field F] (x : F) :
    translationGL2 (F := F) (-x) • affinePoint x = zeroPoint (F := F) := by
  simpa [zeroPoint, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (translationGL2_smul_affinePoint (F := F) (-x) x)

theorem translationGL2_smul_affinePoint_to_one [Field F] (x : F) :
    translationGL2 (F := F) (1 - x) • affinePoint x = onePoint (F := F) := by
  simpa [onePoint, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (translationGL2_smul_affinePoint (F := F) (1 - x) x)

theorem affinePoint_to_infinity [Field F] (x : F) :
    swapGL2 (F := F) •
        (translationGL2 (F := F) (-x) • affinePoint x) =
      infinityPoint (F := F) := by
  rw [translationGL2_smul_affinePoint_to_zero]
  exact swapGL2_smul_affinePoint_zero (F := F)

theorem scaleGL2_smul_zeroPoint [Field F] (a : Fˣ) :
    scaleGL2 (F := F) a • zeroPoint (F := F) = zeroPoint (F := F) := by
  simpa [zeroPoint] using
    (scaleGL2_smul_affinePoint (F := F) a 0)

theorem scaleGL2_smul_onePoint [Field F] (a : Fˣ) :
    scaleGL2 (F := F) a • onePoint (F := F) = affinePoint (a : F) := by
  simpa [onePoint] using
    (scaleGL2_smul_affinePoint (F := F) a 1)

theorem scaleGL2_smul_infinityPoint [Field F] (a : Fˣ) :
    scaleGL2 (F := F) a • infinityPoint (F := F) =
      infinityPoint (F := F) := by
  apply gl2_smul_infinityPoint_of_apply_one_eq_zero
  change (scaleLinearEquiv a (![1, 0])) 1 = 0
  simp [scaleLinearEquiv]

theorem gl2_normalize_zero_one_affine [Field F] (t : F)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ∃ g : GL2 F,
      g • zeroPoint (F := F) = zeroPoint (F := F) ∧
      g • onePoint (F := F) = onePoint (F := F) ∧
      g • affinePoint t = infinityPoint (F := F) := by
  have htm1 : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have hunit : (t - 1) / t ≠ 0 := div_ne_zero htm1 ht0
  let a : Fˣ := Units.mk0 ((t - 1) / t) hunit
  let b : Fˣ := Units.mk0 t ht0
  let g : GL2 F :=
    scaleGL2 (F := F) a * swapGL2 (F := F) *
      translationGL2 (F := F) (-(t⁻¹)) * swapGL2 (F := F)
  have hshift : 1 - t⁻¹ ≠ 0 := by
    intro h
    apply ht1
    apply inv_eq_one.mp
    exact (sub_eq_zero.mp h).symm
  refine ⟨g, ?_, ?_, ?_⟩
  · simp only [g, mul_smul]
    rw [show swapGL2 (F := F) • zeroPoint (F := F) =
          infinityPoint (F := F) by
          simpa [zeroPoint] using (swapGL2_smul_affinePoint_zero (F := F)),
      translationGL2_smul_infinityPoint,
      swapGL2_smul_infinityPoint,
      scaleGL2_smul_zeroPoint]
  · simp only [g, mul_smul]
    rw [show swapGL2 (F := F) • onePoint (F := F) =
          affinePoint (1 : F)⁻¹ by
          simpa [onePoint] using
            (swapGL2_smul_affinePoint_of_ne_zero (F := F) 1 one_ne_zero)]
    simp only [inv_one]
    rw [translationGL2_smul_affinePoint]
    have hshift' :
        1 + -(t⁻¹) = 1 - t⁻¹ := by ring
    rw [hshift']
    rw [swapGL2_smul_affinePoint_of_ne_zero _ hshift]
    rw [scaleGL2_smul_affinePoint]
    apply congrArg affinePoint
    simp [a]
    field_simp [ht0, hshift]
  · simp only [g, mul_smul]
    rw [swapGL2_smul_affinePoint_of_ne_zero t ht0]
    rw [translationGL2_smul_affinePoint]
    have hz : t⁻¹ + -(t⁻¹) = 0 := by ring
    rw [hz]
    rw [swapGL2_smul_affinePoint_zero]
    exact scaleGL2_smul_infinityPoint a

theorem gl2_normalize_affine_triple [Field F] (x y z : F)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ g : GL2 F,
      g • affinePoint x = zeroPoint (F := F) ∧
      g • affinePoint y = onePoint (F := F) ∧
      g • affinePoint z = infinityPoint (F := F) := by
  let a : F := y - x
  let b : F := z - x
  have ha : a ≠ 0 := by
    exact sub_ne_zero.mpr hxy.symm
  have hb : b ≠ 0 := by
    exact sub_ne_zero.mpr hxz.symm
  have hab : b ≠ a := by
    dsimp [a, b]
    intro h
    apply hyz
    exact (sub_left_inj.mp h).symm
  let t : F := b / a
  have ht0 : t ≠ 0 := by
    exact div_ne_zero hb ha
  have ht1 : t ≠ 1 := by
    intro ht
    have hba : b = 1 * a := (div_eq_iff ha).mp ht
    exact hab (by simpa using hba)
  have hunit : a ≠ 0 := ha
  let ua : Fˣ := Units.mk0 a hunit
  let h : GL2 F :=
    scaleGL2 (F := F) (ua⁻¹) * translationGL2 (F := F) (-x)
  rcases gl2_normalize_zero_one_affine t ht0 ht1 with
    ⟨k, hk0, hk1, hkt⟩
  refine ⟨k * h, ?_, ?_, ?_⟩
  · have hmap : h • affinePoint x = zeroPoint (F := F) := by
      simp only [h, mul_smul]
      rw [translationGL2_smul_affinePoint]
      have hx : x + -x = (0 : F) := add_neg_cancel x
      rw [hx]
      simpa [zeroPoint] using (scaleGL2_smul_zeroPoint (F := F) (ua⁻¹))
    rw [mul_smul, hmap, hk0]
  · have hmap : h • affinePoint y = onePoint (F := F) := by
      simp only [h, mul_smul]
      rw [translationGL2_smul_affinePoint]
      have hscale : ((ua⁻¹ : Fˣ) : F) * a = 1 := by
        change a⁻¹ * a = 1
        exact inv_mul_cancel₀ ha
      rw [scaleGL2_smul_affinePoint]
      have hyx : y + -x = a := by simp [a, sub_eq_add_neg]
      rw [hyx, hscale]
      rfl
    rw [mul_smul, hmap, hk1]
  · have hmap : h • affinePoint z = affinePoint t := by
      simp only [h, mul_smul]
      rw [translationGL2_smul_affinePoint]
      have hscale : ((ua⁻¹ : Fˣ) : F) * b = t := by
        simp [ua, t, div_eq_mul_inv, mul_comm]
      rw [scaleGL2_smul_affinePoint,
        show z + -x = b by simp [b, sub_eq_add_neg], hscale]
    rw [mul_smul, hmap, hkt]

theorem pgl2_normalize_affine_triple [Field F] (x y z : F)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ g : PGL2 F,
      g • affinePoint x = zeroPoint (F := F) ∧
      g • affinePoint y = onePoint (F := F) ∧
      g • affinePoint z = infinityPoint (F := F) := by
  rcases gl2_normalize_affine_triple x y z hxy hxz hyz with
    ⟨g, hg0, hg1, hginf⟩
  refine ⟨QuotientGroup.mk' (gl2ActionHom (F := F)).ker g, ?_⟩
  constructor
  · simpa [pgl2MulAction, pgl2ActionHom_mk] using hg0
  constructor
  · simpa [pgl2MulAction, pgl2ActionHom_mk] using hg1
  · simpa [pgl2MulAction, pgl2ActionHom_mk] using hginf

theorem gl2_fix_frame_eq_scalar [Field F] (g : GL2 F)
    (hzero : g • zeroPoint (F := F) = zeroPoint (F := F))
    (hone : g • onePoint (F := F) = onePoint (F := F))
    (hinfinity : g • infinityPoint (F := F) = infinityPoint (F := F)) :
    ∃ a : Fˣ, g = scalarGL2 (F := F) a := by
  let u : Fin 2 → F := ![1, 0]
  let v : Fin 2 → F := ![0, 1]
  have hu : u ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [u] at h0
  have hv : v ≠ 0 := by
    intro h
    have h1 := congrFun h 1
    simp [v] at h1
  have huv : u + v ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [u, v] at h0
  have hInf : g • Projectivization.mk F u hu =
      Projectivization.mk F u hu := by
    simpa [u, infinityPoint] using hinfinity
  have hZero : g • Projectivization.mk F v hv =
      Projectivization.mk F v hv := by
    simpa [v, zeroPoint, affinePoint] using hzero
  have hOne : g • Projectivization.mk F (u + v) huv =
      Projectivization.mk F (u + v) huv := by
    simpa [u, v, onePoint, affinePoint] using hone
  have hU := (Projectivization.mk_eq_mk_iff' F (g • u) u
    ((smul_ne_zero_iff_ne g).2 hu) hu).mp hInf
  have hV := (Projectivization.mk_eq_mk_iff' F (g • v) v
    ((smul_ne_zero_iff_ne g).2 hv) hv).mp hZero
  have hUV := (Projectivization.mk_eq_mk_iff' F (g • (u + v)) (u + v)
    ((smul_ne_zero_iff_ne g).2 huv) huv).mp hOne
  rcases hU with ⟨a, ha⟩
  rcases hV with ⟨b, hb⟩
  rcases hUV with ⟨c, hc⟩
  have hc' : c • u + c • v = g • u + g • v := by
    simpa [smul_add] using hc
  have hgu0 : (g • u) 0 = a := by
    simpa [u] using (congrFun ha 0).symm
  have hgv0 : (g • v) 0 = 0 := by
    simpa [v] using (congrFun hb 0).symm
  have hgu1 : (g • u) 1 = 0 := by
    simpa [u] using (congrFun ha 1).symm
  have hgv1 : (g • v) 1 = b := by
    simpa [v] using (congrFun hb 1).symm
  have hac : c = a := by
    calc
      c = (g • u + g • v) 0 := by simpa [u, v] using congrFun hc' 0
      _ = (g • u) 0 + (g • v) 0 := by rfl
      _ = a + 0 := by rw [hgu0, hgv0]
      _ = a := add_zero _
  have hbc : c = b := by
    calc
      c = (g • u + g • v) 1 := by simpa [u, v] using congrFun hc' 1
      _ = (g • u) 1 + (g • v) 1 := by rfl
      _ = 0 + b := by rw [hgu1, hgv1]
      _ = b := zero_add _
  have hab : a = b := hac.symm.trans hbc
  have ha_ne : a ≠ 0 := by
    intro ha0
    have hzero : g • u = 0 := by simpa [ha0] using ha.symm
    exact ((smul_ne_zero_iff_ne g).2 hu) hzero
  let au : Fˣ := Units.mk0 a ha_ne
  refine ⟨au, ?_⟩
  apply Units.ext
  apply LinearMap.ext
  intro w
  have hw : w = w 0 • u + w 1 • v := by
    ext i
    fin_cases i <;> simp [u, v]
  rw [hw, map_add, map_smul, map_smul]
  change w 0 • (g : GL2 F).toLinearEquiv u +
      w 1 • (g : GL2 F).toLinearEquiv v =
    (scalarGL2 (F := F) au).toLinearEquiv (w 0 • u + w 1 • v)
  have hs0 : (scalarGL2 (F := F) au).toLinearEquiv u = a • u := by
    simp [scalarGL2, au]
  have hs1 : (scalarGL2 (F := F) au).toLinearEquiv v = a • v := by
    simp [scalarGL2, au]
  have hgadd : g • (w 0 • u + w 1 • v) =
      w 0 • (g • u) + w 1 • (g • v) := by
    change g.toLinearEquiv (w 0 • u + w 1 • v) =
      w 0 • g.toLinearEquiv u + w 1 • g.toLinearEquiv v
    rw [map_add, map_smul, map_smul]
  calc
    w 0 • (g : GL2 F).toLinearEquiv u +
        w 1 • (g : GL2 F).toLinearEquiv v =
      g • (w 0 • u + w 1 • v) := by
        symm
        exact hgadd
    _ = w 0 • (a • u) + w 1 • (a • v) := by
      rw [hgadd, show g • u = a • u from ha.symm,
        show g • v = a • v from hab ▸ hb.symm]
    _ = (scalarGL2 (F := F) au).toLinearEquiv
        (w 0 • u + w 1 • v) := by
      rw [map_add, map_smul, map_smul, hs0, hs1]

theorem pgl2_fix_frame_eq_one [Field F] (q : PGL2 F)
    (hzero : q • zeroPoint (F := F) = zeroPoint (F := F))
    (hone : q • onePoint (F := F) = onePoint (F := F))
    (hinfinity : q • infinityPoint (F := F) = infinityPoint (F := F)) :
    q = 1 := by
  revert hzero hone hinfinity
  refine QuotientGroup.induction_on q ?_
  intro g hzero hone hinfinity
  have hzero' : gl2ActionHom (F := F) g • zeroPoint (F := F) =
      zeroPoint (F := F) := by
    simpa [pgl2MulAction, pgl2ActionHom_mk] using hzero
  have hone' : gl2ActionHom (F := F) g • onePoint (F := F) =
      onePoint (F := F) := by
    simpa [pgl2MulAction, pgl2ActionHom_mk] using hone
  have hinfinity' : gl2ActionHom (F := F) g • infinityPoint (F := F) =
      infinityPoint (F := F) := by
    simpa [pgl2MulAction, pgl2ActionHom_mk] using hinfinity
  rcases gl2_fix_frame_eq_scalar g hzero' hone' hinfinity' with ⟨a, ha⟩
  rw [ha]
  exact (QuotientGroup.eq_one_iff _).2
    (scalarGL2Hom_mem_action_kernel (F := F) a)
theorem pgl2_normalize_triple_unique [Field F]
    (p₁ p₂ p₃ : Line F) (g h : PGL2 F)
    (hg₁ : g • p₁ = zeroPoint (F := F))
    (hg₂ : g • p₂ = onePoint (F := F))
    (hg₃ : g • p₃ = infinityPoint (F := F))
    (hh₁ : h • p₁ = zeroPoint (F := F))
    (hh₂ : h • p₂ = onePoint (F := F))
    (hh₃ : h • p₃ = infinityPoint (F := F)) :
    g = h := by
  have hinv₀ : h⁻¹ • zeroPoint (F := F) = p₁ := by
    rw [← hh₁]
    exact inv_smul_smul h _
  have hinv₁ : h⁻¹ • onePoint (F := F) = p₂ := by
    rw [← hh₂]
    exact inv_smul_smul h _
  have hinvinf : h⁻¹ • infinityPoint (F := F) = p₃ := by
    rw [← hh₃]
    exact inv_smul_smul h _
  have hfix₀ : (g * h⁻¹) • zeroPoint (F := F) =
      zeroPoint (F := F) := by
    rw [mul_smul, hinv₀, hg₁]
  have hfix₁ : (g * h⁻¹) • onePoint (F := F) =
      onePoint (F := F) := by
    rw [mul_smul, hinv₁, hg₂]
  have hfixinf : (g * h⁻¹) • infinityPoint (F := F) =
      infinityPoint (F := F) := by
    rw [mul_smul, hinvinf, hg₃]
  have hrel : g * h⁻¹ = 1 :=
    pgl2_fix_frame_eq_one (g * h⁻¹) hfix₀ hfix₁ hfixinf
  exact mul_inv_eq_one.mp hrel

@[simp] theorem affinePoint_zero [Field F] :
    affinePoint (0 : F) = Projectivization.mk F ![0, 1] (by
      intro h
      have h1 := congrFun h 1
      simp at h1) := rfl


theorem pgl2_normalize_affine_triple_unique [Field F] (x y z : F)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (g h : PGL2 F)
    (hg0 : g • affinePoint x = zeroPoint (F := F))
    (hg1 : g • affinePoint y = onePoint (F := F))
    (hginf : g • affinePoint z = infinityPoint (F := F))
    (hh0 : h • affinePoint x = zeroPoint (F := F))
    (hh1 : h • affinePoint y = onePoint (F := F))
    (hhinf : h • affinePoint z = infinityPoint (F := F)) :
    g = h := by
  have hinv0 : h⁻¹ • zeroPoint (F := F) = affinePoint x := by
    rw [← hh0]
    exact inv_smul_smul h _
  have hinv1 : h⁻¹ • onePoint (F := F) = affinePoint y := by
    rw [← hh1]
    exact inv_smul_smul h _
  have hinvinf : h⁻¹ • infinityPoint (F := F) = affinePoint z := by
    rw [← hhinf]
    exact inv_smul_smul h _
  have hfix0 : (g * h⁻¹) • zeroPoint (F := F) =
      zeroPoint (F := F) := by
    rw [mul_smul, hinv0, hg0]
  have hfix1 : (g * h⁻¹) • onePoint (F := F) =
      onePoint (F := F) := by
    rw [mul_smul, hinv1, hg1]
  have hfixinf : (g * h⁻¹) • infinityPoint (F := F) =
      infinityPoint (F := F) := by
    rw [mul_smul, hinvinf, hginf]
  have hrel : g * h⁻¹ = 1 :=
    pgl2_fix_frame_eq_one (g * h⁻¹) hfix0 hfix1 hfixinf
  exact mul_inv_eq_one.mp hrel

theorem pgl2_sharply_three_transitive_affine [Field F] (x y z : F)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃! g : PGL2 F,
      g • affinePoint x = zeroPoint (F := F) ∧
      g • affinePoint y = onePoint (F := F) ∧
      g • affinePoint z = infinityPoint (F := F) := by
  rcases pgl2_normalize_affine_triple x y z hxy hxz hyz with
    ⟨g, hg0, hg1, hginf⟩
  refine ⟨g, ⟨hg0, hg1, hginf⟩, ?_⟩
  intro h hh
  exact (pgl2_normalize_affine_triple_unique x y z hxy hxz hyz g h
    hg0 hg1 hginf hh.1 hh.2.1 hh.2.2).symm

set_option linter.unusedSimpArgs false in
theorem pgl2_normalize_affine_pair_infinity [Field F] (x y : F)
    (hxy : x ≠ y) :
    ∃ g : PGL2 F,
      g • affinePoint x = zeroPoint (F := F) ∧
      g • affinePoint y = onePoint (F := F) ∧
      g • infinityPoint (F := F) = infinityPoint (F := F) := by
  have ha : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  let a : Fˣ := Units.mk0 (y - x) ha
  let h : GL2 F :=
    scaleGL2 (F := F) (a⁻¹) * translationGL2 (F := F) (-x)
  refine ⟨QuotientGroup.mk' (gl2ActionHom (F := F)).ker h, ?_⟩
  constructor
  · change h • affinePoint x = zeroPoint (F := F)
    rw [mul_smul, translationGL2_smul_affinePoint_to_zero,
      scaleGL2_smul_zeroPoint]
  constructor
  · change h • affinePoint y = onePoint (F := F)
    rw [mul_smul, translationGL2_smul_affinePoint]
    have hscale : ((a⁻¹ : Fˣ) : F) * (y - x) = 1 := by
      change (y - x)⁻¹ * (y - x) = 1
      exact inv_mul_cancel₀ ha
    rw [scaleGL2_smul_affinePoint,
      show y + -x = y - x by exact (sub_eq_add_neg y x).symm, hscale]
    rfl
  · change h • infinityPoint (F := F) = infinityPoint (F := F)
    rw [mul_smul, translationGL2_smul_infinityPoint,
      scaleGL2_smul_infinityPoint]

theorem swapGL2_smul_onePoint [Field F] :
    swapGL2 (F := F) • onePoint (F := F) = onePoint (F := F) := by
  simpa [onePoint] using
    (swapGL2_smul_affinePoint_of_ne_zero (F := F) 1 one_ne_zero)

theorem frameCycleGL2_smul_zeroPoint [Field F] :
    frameCycleGL2 (F := F) • zeroPoint (F := F) = onePoint (F := F) := by
  simp only [frameCycleGL2, mul_smul]
  rw [scaleGL2_smul_zeroPoint,
    translationGL2_smul_zeroPoint]
  change swapGL2 (F := F) • onePoint (F := F) = onePoint (F := F)
  exact swapGL2_smul_onePoint

theorem frameCycleGL2_smul_onePoint [Field F] :
    frameCycleGL2 (F := F) • onePoint (F := F) =
      infinityPoint (F := F) := by
  simp only [frameCycleGL2, mul_smul]
  rw [scaleGL2_smul_onePoint]
  have hneg : ((Units.mk0 (-1) (by simp) : Fˣ) : F) = -1 := rfl
  rw [hneg, translationGL2_smul_affinePoint]
  have hz : -1 + 1 = (0 : F) := by ring
  rw [hz]
  exact swapGL2_smul_affinePoint_zero (F := F)

theorem frameCycleGL2_smul_infinityPoint [Field F] :
    frameCycleGL2 (F := F) • infinityPoint (F := F) =
      zeroPoint (F := F) := by
  simp only [frameCycleGL2, mul_smul]
  rw [scaleGL2_smul_infinityPoint,
    translationGL2_smul_infinityPoint,
    swapGL2_smul_infinityPoint]

theorem pgl2_normalize_infinity_affine_pair [Field F] (x y : F)
    (hxy : x ≠ y) :
    ∃ g : PGL2 F,
      g • infinityPoint (F := F) = zeroPoint (F := F) ∧
      g • affinePoint x = onePoint (F := F) ∧
      g • affinePoint y = infinityPoint (F := F) := by
  rcases pgl2_normalize_affine_pair_infinity x y hxy with
    ⟨h, hx, hy, hinf⟩
  let c : PGL2 F :=
    QuotientGroup.mk' (gl2ActionHom (F := F)).ker (frameCycleGL2 (F := F))
  have hc0 : c • zeroPoint (F := F) = onePoint (F := F) := by
    simpa [c, pgl2MulAction, pgl2ActionHom_mk] using
      (frameCycleGL2_smul_zeroPoint (F := F))
  have hc1 : c • onePoint (F := F) = infinityPoint (F := F) := by
    simpa [c, pgl2MulAction, pgl2ActionHom_mk] using
      (frameCycleGL2_smul_onePoint (F := F))
  have hcinf : c • infinityPoint (F := F) = zeroPoint (F := F) := by
    simpa [c, pgl2MulAction, pgl2ActionHom_mk] using
      (frameCycleGL2_smul_infinityPoint (F := F))
  refine ⟨c * h, ?_, ?_, ?_⟩
  · rw [mul_smul, hinf, hcinf]
  · rw [mul_smul, hx, hc0]
  · rw [mul_smul, hy, hc1]

theorem pgl2_normalize_affine_infinity_affine [Field F] (x y : F)
    (hxy : x ≠ y) :
    ∃ g : PGL2 F,
      g • affinePoint x = zeroPoint (F := F) ∧
      g • infinityPoint (F := F) = onePoint (F := F) ∧
      g • affinePoint y = infinityPoint (F := F) := by
  rcases pgl2_normalize_affine_pair_infinity x y hxy with
    ⟨h, hx, hy, hinf⟩
  let s : PGL2 F :=
    QuotientGroup.mk' (gl2ActionHom (F := F)).ker (swapGL2 (F := F))
  let c : PGL2 F :=
    QuotientGroup.mk' (gl2ActionHom (F := F)).ker (frameCycleGL2 (F := F))
  have hs0 : s • zeroPoint (F := F) = infinityPoint (F := F) := by
    simpa [s, pgl2MulAction, pgl2ActionHom_mk] using
      (swapGL2_smul_affinePoint_zero (F := F))
  have hs1 : s • onePoint (F := F) = onePoint (F := F) := by
    simpa [s, pgl2MulAction, pgl2ActionHom_mk] using
      (swapGL2_smul_onePoint (F := F))
  have hsi : s • infinityPoint (F := F) = zeroPoint (F := F) := by
    simpa [s, pgl2MulAction, pgl2ActionHom_mk] using
      (swapGL2_smul_infinityPoint (F := F))
  have hc0 : c • zeroPoint (F := F) = onePoint (F := F) := by
    simpa [c, pgl2MulAction, pgl2ActionHom_mk] using
      (frameCycleGL2_smul_zeroPoint (F := F))
  have hc1 : c • onePoint (F := F) = infinityPoint (F := F) := by
    simpa [c, pgl2MulAction, pgl2ActionHom_mk] using
      (frameCycleGL2_smul_onePoint (F := F))
  have hci : c • infinityPoint (F := F) = zeroPoint (F := F) := by
    simpa [c, pgl2MulAction, pgl2ActionHom_mk] using
      (frameCycleGL2_smul_infinityPoint (F := F))
  refine ⟨c * s * h, ?_, ?_, ?_⟩
  · rw [mul_smul, mul_smul, hx, hs0, hci]
  · rw [mul_smul, mul_smul, hinf, hsi, hc0]
  · rw [mul_smul, mul_smul, hy, hs1, hc1]

theorem affinePoint_injective [Field F] : Function.Injective (affinePoint : F → Line F) := by
  intro x y h
  rcases (Projectivization.mk_eq_mk_iff' F ![x, 1] ![y, 1]
    (by simp) (by simp)).mp h with ⟨a, ha⟩
  have ha1 := congrFun ha 1
  have ha0 := congrFun ha 0
  simp at ha1 ha0
  subst a
  simpa using ha0.symm

theorem zeroPoint_ne_onePoint [Field F] : zeroPoint (F := F) ≠ onePoint (F := F) := by
  intro h
  exact (zero_ne_one : (0 : F) ≠ 1) (affinePoint_injective h)

theorem affinePoint_ne_infinityPoint [Field F] (x : F) :
    affinePoint x ≠ infinityPoint (F := F) := by
  intro h
  have h' := (Projectivization.mk_eq_mk_iff' F ![x, 1] ![1, 0]
    (by simp) (by simp)).mp h
  rcases h' with ⟨a, ha⟩
  have h1 := congrFun ha 1
  have h0 := congrFun ha 0
  simp at h1 h0

theorem zeroPoint_ne_infinityPoint [Field F] :
    zeroPoint (F := F) ≠ infinityPoint (F := F) := by
  exact affinePoint_ne_infinityPoint 0

theorem onePoint_ne_infinityPoint [Field F] :
    onePoint (F := F) ≠ infinityPoint (F := F) := by
  exact affinePoint_ne_infinityPoint 1

theorem eq_infinity_or_eq_affine [Field F] (p : Line F) :
    p = infinityPoint (F := F) ∨ ∃ x : F, p = affinePoint x := by
  induction p using Projectivization.ind with
  | h v hv =>
    by_cases hb : v 1 = 0
    · left
      have hv0 : v 0 ≠ 0 := by
        intro h0
        apply hv
        funext i
        fin_cases i <;> simp [h0, hb]
      apply (Projectivization.mk_eq_mk_iff' F v ![1, 0] hv (by simp)).2
      refine ⟨v 0, ?_⟩
      funext i
      fin_cases i <;> simp [hb]
    · right
      refine ⟨v 0 / v 1, ?_⟩
      apply (Projectivization.mk_eq_mk_iff' F v ![v 0 / v 1, 1]
        hv (by simp)).2
      refine ⟨v 1, ?_⟩
      funext i
      fin_cases i
      · change v 1 * (v 0 / v 1) = v 0
        field_simp [hb]
      · simp

noncomputable def affineWithInfinityMap [Field F] : Option F → Line F
  | none => infinityPoint
  | some x => affinePoint x

theorem affineWithInfinityMap_injective [Field F] :
    Function.Injective (affineWithInfinityMap : Option F → Line F) := by
  intro x y h
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some y =>
          exact (affinePoint_ne_infinityPoint y h.symm).elim
  | some x =>
      cases y with
      | none =>
          exact (affinePoint_ne_infinityPoint x h).elim
      | some y =>
          exact congrArg some (affinePoint_injective h)

theorem affineWithInfinityMap_surjective [Field F] :
    Function.Surjective (affineWithInfinityMap : Option F → Line F) := by
  intro p
  rcases eq_infinity_or_eq_affine p with hp | ⟨x, hx⟩
  · exact ⟨none, hp.symm⟩
  · exact ⟨some x, hx.symm⟩

noncomputable def affineWithInfinityEquiv [Field F] :
    Option F ≃ Line F :=
  Equiv.ofBijective affineWithInfinityMap
    ⟨affineWithInfinityMap_injective, affineWithInfinityMap_surjective⟩

theorem canonical_frame_pairwise [Field F] :
    zeroPoint (F := F) ≠ onePoint (F := F) ∧
      zeroPoint (F := F) ≠ infinityPoint (F := F) ∧
      onePoint (F := F) ≠ infinityPoint (F := F) :=
  ⟨zeroPoint_ne_onePoint, zeroPoint_ne_infinityPoint,
    onePoint_ne_infinityPoint⟩

theorem pgl2_normalize_triple [Field F]
    (p₁ p₂ p₃ : Line F)
    (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃) :
    ∃ g : PGL2 F,
      g • p₁ = zeroPoint (F := F) ∧
      g • p₂ = onePoint (F := F) ∧
      g • p₃ = infinityPoint (F := F) := by
  by_cases hp₁ : p₁ = infinityPoint (F := F)
  · have hp₂ : p₂ ≠ infinityPoint (F := F) := by
      intro h
      exact h₁₂ (hp₁.trans h.symm)
    have hp₃ : p₃ ≠ infinityPoint (F := F) := by
      intro h
      exact h₁₃ (hp₁.trans h.symm)
    rcases eq_infinity_or_eq_affine p₂ with hp₂' | ⟨x, hx⟩
    · exact (hp₂ hp₂').elim
    rcases eq_infinity_or_eq_affine p₃ with hp₃' | ⟨y, hy⟩
    · exact (hp₃ hp₃').elim
    subst p₁
    subst p₂
    subst p₃
    have hxy : x ≠ y := by
      intro h
      apply h₂₃
      simp [h]
    exact pgl2_normalize_infinity_affine_pair x y hxy
  · by_cases hp₂ : p₂ = infinityPoint (F := F)
    · have hp₃ : p₃ ≠ infinityPoint (F := F) := by
        intro h
        exact h₂₃ (hp₂.trans h.symm)
      rcases eq_infinity_or_eq_affine p₁ with hp₁' | ⟨x, hx⟩
      · exact (hp₁ hp₁').elim
      rcases eq_infinity_or_eq_affine p₃ with hp₃' | ⟨y, hy⟩
      · exact (hp₃ hp₃').elim
      subst p₁
      subst p₂
      subst p₃
      have hxy : x ≠ y := by
        intro h
        apply h₁₃
        simp [h]
      exact pgl2_normalize_affine_infinity_affine x y hxy
    · by_cases hp₃ : p₃ = infinityPoint (F := F)
      · rcases eq_infinity_or_eq_affine p₁ with hp₁' | ⟨x, hx⟩
        · exact (hp₁ hp₁').elim
        rcases eq_infinity_or_eq_affine p₂ with hp₂' | ⟨y, hy⟩
        · exact (hp₂ hp₂').elim
        subst p₁
        subst p₂
        subst p₃
        have hxy : x ≠ y := by
          intro h
          apply h₁₂
          simp [h]
        exact pgl2_normalize_affine_pair_infinity x y hxy
      · rcases eq_infinity_or_eq_affine p₁ with hp₁' | ⟨x, hx⟩
        · exact (hp₁ hp₁').elim
        rcases eq_infinity_or_eq_affine p₂ with hp₂' | ⟨y, hy⟩
        · exact (hp₂ hp₂').elim
        rcases eq_infinity_or_eq_affine p₃ with hp₃' | ⟨z, hz⟩
        · exact (hp₃ hp₃').elim
        subst p₁
        subst p₂
        subst p₃
        have hxy : x ≠ y := by
          intro h
          apply h₁₂
          simp [h]
        have hxz : x ≠ z := by
          intro h
          apply h₁₃
          simp [h]
        have hyz : y ≠ z := by
          intro h
          apply h₂₃
          simp [h]
        rcases pgl2_sharply_three_transitive_affine x y z hxy hxz hyz with
          ⟨g, hg, _⟩
        exact ⟨g, hg⟩

theorem pgl2_sharply_three_transitive [Field F]
    (p₁ p₂ p₃ : Line F)
    (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃) :
    ∃! g : PGL2 F,
      g • p₁ = zeroPoint (F := F) ∧
      g • p₂ = onePoint (F := F) ∧
      g • p₃ = infinityPoint (F := F) := by
  rcases pgl2_normalize_triple p₁ p₂ p₃ h₁₂ h₁₃ h₂₃ with
    ⟨g, hg₁, hg₂, hg₃⟩
  refine ⟨g, ⟨hg₁, hg₂, hg₃⟩, ?_⟩
  intro h hh
  exact (pgl2_normalize_triple_unique p₁ p₂ p₃ g h
    hg₁ hg₂ hg₃ hh.1 hh.2.1 hh.2.2).symm

theorem gl2Action_transitive [Field F] (p q : Line F) :
    ∃ g : GL2 F, g • p = q := by
  rcases eq_infinity_or_eq_affine p with hp | ⟨x, hp⟩
  · rcases eq_infinity_or_eq_affine q with hq | ⟨y, hq⟩
    · subst p
      subst q
      exact ⟨1, by simp⟩
    · subst p
      subst q
      refine ⟨translationGL2 (F := F) y * swapGL2 (F := F), ?_⟩
      rw [mul_smul, swapGL2_smul_infinityPoint]
      simpa [zeroPoint] using
        (translationGL2_smul_affinePoint (F := F) y 0)
  · rcases eq_infinity_or_eq_affine q with hq | ⟨y, hq⟩
    · subst p
      subst q
      refine ⟨swapGL2 (F := F) * translationGL2 (F := F) (-x), ?_⟩
      rw [mul_smul, translationGL2_smul_affinePoint_to_zero]
      exact swapGL2_smul_affinePoint_zero (F := F)
    · subst p
      subst q
      refine ⟨translationGL2 (F := F) (y - x), ?_⟩
      rw [translationGL2_smul_affinePoint]
      simp [sub_eq_add_neg]

theorem pgl2Action_transitive [Field F] (p q : Line F) :
    ∃ g : PGL2 F, g • p = q := by
  rcases gl2Action_transitive p q with ⟨g, hg⟩
  refine ⟨QuotientGroup.mk' (gl2ActionHom (F := F)).ker g, ?_⟩
  simpa [pgl2MulAction, pgl2ActionHom_mk] using hg

end InfoGeometry.Arithmetic.FiniteProjectiveLine
