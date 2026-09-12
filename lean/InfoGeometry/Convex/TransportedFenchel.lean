import InfoGeometry.Convex.FenchelConjugate

namespace InfoGeometry.Convex

noncomputable section

def dualTransport {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (y : DualSpace F) : DualSpace E :=
  y.comp e.toContinuousLinearMap

def transportedFenchelSetFromDual {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (e : E ≃L[ℝ] F) (y : DualSpace F) : Set ℝ :=
  fenchelSet (fun x => f (e x)) (dualTransport e y)

theorem transportedFenchelSetFromDual_eq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (e : E ≃L[ℝ] F) (y : DualSpace F) :
    transportedFenchelSetFromDual f e y = fenchelSet f y := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨e x, ?_⟩
    change (y.comp e.toContinuousLinearMap) x - f (e x) = y (e x) - f (e x)
    simp
  · rintro ⟨u, rfl⟩
    refine ⟨e.symm u, ?_⟩
    change (y.comp e.toContinuousLinearMap) (e.symm u) - f (e (e.symm u)) = y u - f u
    simp

theorem transportedFenchelConjFromDual_eq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (e : E ≃L[ℝ] F) (y : DualSpace F) :
    sSup (transportedFenchelSetFromDual f e y) = fenchelConj f y := by
  rw [transportedFenchelSetFromDual_eq]
  rfl

theorem transportedFenchelSetFromDual_bddAbove {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (e : E ≃L[ℝ] F) (y : DualSpace F)
    (hb : BddAbove (fenchelSet f y)) :
    BddAbove (transportedFenchelSetFromDual f e y) := by
  rw [transportedFenchelSetFromDual_eq]
  exact hb

theorem transportedFenchelSetFromDual_bddAbove_iff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (e : E ≃L[ℝ] F) (y : DualSpace F) :
    BddAbove (transportedFenchelSetFromDual f e y) ↔ BddAbove (fenchelSet f y) := by
  rw [transportedFenchelSetFromDual_eq]

theorem transportedFenchelSetFromDual_nonempty {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (e : E ≃L[ℝ] F) (y : DualSpace F) :
    (transportedFenchelSetFromDual f e y).Nonempty := by
  rw [transportedFenchelSetFromDual_eq]
  exact fenchelSet_nonempty f y


theorem transportedFenchelConjFromDual_eq_of_isGreatest {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (e : E ≃L[ℝ] F) (y : DualSpace F) (x : E)
    (hG : IsGreatest (fenchelSet f y)
      (dualPair y (e x) - f (e x))) :
    sSup (transportedFenchelSetFromDual f e y) =
      dualPair y (e x) - f (e x) := by
  rw [transportedFenchelSetFromDual_eq]
  exact fenchelConj_eq_of_isGreatest f y (e x) hG

theorem transportedFenchelConjFromDual_eq_iff_isGreatest {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (e : E ≃L[ℝ] F) (y : DualSpace F) (x : E)
    (hb : BddAbove (fenchelSet f y)) :
    sSup (transportedFenchelSetFromDual f e y) =
        dualPair y (e x) - f (e x) ↔
      IsGreatest (fenchelSet f y) (dualPair y (e x) - f (e x)) := by
  rw [transportedFenchelConjFromDual_eq]
  exact fenchelConj_eq_iff_isGreatest f y (e x) hb

theorem transportedFenchelYoungFromDual {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (e : E ≃L[ℝ] F) (y : DualSpace F) (x : E)
    (hb : BddAbove (fenchelSet f y)) :
    dualPair y (e x) ≤ f (e x) + sSup (transportedFenchelSetFromDual f e y) := by
  rw [transportedFenchelSetFromDual_eq]
  exact fenchelYoung f y (e x) hb

theorem transportedFenchelYoungFromDual_eq_of_isGreatest {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (e : E ≃L[ℝ] F) (y : DualSpace F) (x : E)
    (hG : IsGreatest (fenchelSet f y)
      (dualPair y (e x) - f (e x))) :
    dualPair y (e x) = f (e x) + sSup (transportedFenchelSetFromDual f e y) := by
  rw [transportedFenchelSetFromDual_eq]
  exact fenchelYoung_eq_of_conj_eq f y (e x)
    (fenchelConj_eq_of_isGreatest f y (e x) hG)

def transportedFenchelSet {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (e : E ≃L[ℝ] F) (y : DualSpace E) : Set ℝ :=
  fenchelSet (fun x => f (e x)) y

def transportedFenchelConj {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (e : E ≃L[ℝ] F) (y : DualSpace E) : ℝ :=
  sSup (transportedFenchelSet f e y)

theorem transportedFenchelConj_def {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (e : E ≃L[ℝ] F) (y : DualSpace E) :
    transportedFenchelConj f e y =
      sSup (transportedFenchelSet f e y) := rfl

theorem transportedFenchelSet_nonempty {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (e : E ≃L[ℝ] F) (y : DualSpace E) :
    (transportedFenchelSet f e y).Nonempty := by
  unfold transportedFenchelSet
  exact fenchelSet_nonempty (fun x : E => f (e x)) y

theorem transportedFenchelYoung {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (e : E ≃L[ℝ] F) (y : DualSpace E) (x : E)
    (hb : BddAbove (transportedFenchelSet f e y)) :
    dualPair y x ≤ f (e x) + transportedFenchelConj f e y := by
  exact fenchelYoung (fun z : E => f (e z)) y x (by simpa [transportedFenchelSet] using hb)

theorem transportedFenchelConj_eq_of_isGreatest {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (e : E ≃L[ℝ] F) (y : DualSpace E) (x : E)
    (hG : IsGreatest (transportedFenchelSet f e y)
      (dualPair y x - f (e x))) :
    transportedFenchelConj f e y = dualPair y x - f (e x) := by
  exact fenchelConj_eq_of_isGreatest (fun z : E => f (e z)) y x (by simpa [transportedFenchelSet] using hG)

theorem transportedFenchelYoung_eq_of_isGreatest {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (e : E ≃L[ℝ] F) (y : DualSpace E) (x : E)
    (hG : IsGreatest (transportedFenchelSet f e y)
      (dualPair y x - f (e x))) :
    dualPair y x = f (e x) + transportedFenchelConj f e y := by
  exact fenchelYoung_eq_of_conj_eq (fun z : E => f (e z)) y x
    (transportedFenchelConj_eq_of_isGreatest f e y x hG)

end
end InfoGeometry.Convex
