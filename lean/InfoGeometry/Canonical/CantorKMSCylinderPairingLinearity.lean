import InfoGeometry.Canonical.CantorKMSCylinderState

/-!
# Additivity of the finite Cantor GNS pairing

The finite cylinder state already owns the quotient and its pairing.  This
file supplies the missing additive laws directly from the finite-support sum;
it does not introduce a second quotient or a completion.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorKMSCylinderState

theorem cylinderKMSHermitianPairing_add_left
    (f g h : List Bool →₀ ℂ) :
    cylinderKMSHermitianPairing (f + g) h =
      cylinderKMSHermitianPairing f h +
        cylinderKMSHermitianPairing g h := by
  classical
  unfold cylinderKMSHermitianPairing
  let S : Finset (List Bool) := f.support ∪ g.support ∪ h.support
  have hfg : (f + g).support ∪ h.support ⊆ S := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact Finset.mem_union.mpr <| Or.inl <|
        (Finset.mem_union.mp (Finsupp.support_add hu)).elim
          (fun hf => Finset.mem_union.mpr (Or.inl hf))
          (fun hg => Finset.mem_union.mpr (Or.inr hg))
    · exact Finset.mem_union.mpr <| Or.inr hu
  have hf : f.support ∪ h.support ⊆ S := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inl hu
    · exact Finset.mem_union.mpr <| Or.inr hu
  have hg : g.support ∪ h.support ⊆ S := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inr hu
    · exact Finset.mem_union.mpr <| Or.inr hu
  have hsum_fg :
      ((f + g).support ∪ h.support).sum
          (fun u => (cylinderKMSWeight u : ℂ) * star ((f + g) u) * h u) =
        S.sum
          (fun u => (cylinderKMSWeight u : ℂ) * star ((f + g) u) * h u) := by
    apply Finset.sum_subset hfg
    intro u hu hnot
    have hsum : (f + g) u = 0 := by
      by_contra hzero
      apply hnot
      exact Finset.mem_union.mpr (Or.inl (Finsupp.mem_support_iff.mpr hzero))
    simp [hsum]
  have hsum_f :
      (f.support ∪ h.support).sum
          (fun u => (cylinderKMSWeight u : ℂ) * star (f u) * h u) =
        S.sum
          (fun u => (cylinderKMSWeight u : ℂ) * star (f u) * h u) := by
    apply Finset.sum_subset hf
    intro u hu hnot
    have hzero : f u = 0 := by
      by_contra hzero
      apply hnot
      exact Finset.mem_union.mpr (Or.inl (Finsupp.mem_support_iff.mpr hzero))
    simp [hzero]
  have hsum_g :
      (g.support ∪ h.support).sum
          (fun u => (cylinderKMSWeight u : ℂ) * star (g u) * h u) =
        S.sum
          (fun u => (cylinderKMSWeight u : ℂ) * star (g u) * h u) := by
    apply Finset.sum_subset hg
    intro u hu hnot
    have hzero : g u = 0 := by
      by_contra hzero
      apply hnot
      exact Finset.mem_union.mpr (Or.inl (Finsupp.mem_support_iff.mpr hzero))
    simp [hzero]
  rw [hsum_fg, hsum_f, hsum_g, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [Finsupp.add_apply, star_add]
  ring_nf

theorem cylinderKMSHermitianPairing_add_right
    (f g h : List Bool →₀ ℂ) :
    cylinderKMSHermitianPairing f (g + h) =
      cylinderKMSHermitianPairing f g +
        cylinderKMSHermitianPairing f h := by
  calc
    cylinderKMSHermitianPairing f (g + h) =
        star (cylinderKMSHermitianPairing (g + h) f) := by
          rw [cylinderKMSHermitianPairing_conj_symm]
    _ = star (cylinderKMSHermitianPairing g f +
        cylinderKMSHermitianPairing h f) := by
          rw [cylinderKMSHermitianPairing_add_left]
    _ = star (cylinderKMSHermitianPairing g f) +
        star (cylinderKMSHermitianPairing h f) := by
          exact star_add _ _
    _ = cylinderKMSHermitianPairing f g +
        cylinderKMSHermitianPairing f h := by
          rw [cylinderKMSHermitianPairing_conj_symm,
            cylinderKMSHermitianPairing_conj_symm]

theorem cylinderKMSGNSQuotient_one_smul
    (x : cylinderKMSGNSQuotient) :
    (1 : ℂ) • x = x := by
  refine Quotient.inductionOn x ?_
  intro f
  change Quotient.mk' ((1 : ℂ) • f) = Quotient.mk' f
  rw [one_smul]

theorem cylinderKMSGNSHermitianPairing_smul_left
    (c : ℂ) (x y : cylinderKMSGNSQuotient) :
    cylinderKMSGNSHermitianPairing (c • x) y =
      star c * cylinderKMSGNSHermitianPairing x y := by
  by_cases hc : c = 0
  · subst c
    refine Quotient.inductionOn₂ x y ?_
    intro f g
    simp [cylinderKMSGNSHermitianPairing, cylinderKMSHermitianPairing]
  · calc
      cylinderKMSGNSHermitianPairing (c • x) y =
          cylinderKMSGNSHermitianPairing (c • x) (1 • y) := by
            exact congrArg
              (fun z => cylinderKMSGNSHermitianPairing (c • x) z)
              (cylinderKMSGNSQuotient_one_smul y).symm
      _ = star c * 1 * cylinderKMSGNSHermitianPairing x y :=
        cylinderKMSGNSHermitianPairing_smul c 1 hc one_ne_zero x y
      _ = star c * cylinderKMSGNSHermitianPairing x y := by ring

theorem cylinderKMSGNSHermitianPairing_smul_right
    (c : ℂ) (x y : cylinderKMSGNSQuotient) :
    cylinderKMSGNSHermitianPairing x (c • y) =
      c * cylinderKMSGNSHermitianPairing x y := by
  by_cases hc : c = 0
  · subst c
    refine Quotient.inductionOn₂ x y ?_
    intro f g
    simp [cylinderKMSGNSHermitianPairing, cylinderKMSHermitianPairing]
  · calc
      cylinderKMSGNSHermitianPairing x (c • y) =
          cylinderKMSGNSHermitianPairing (1 • x) (c • y) := by
            exact congrArg
              (fun z => cylinderKMSGNSHermitianPairing z (c • y))
              (cylinderKMSGNSQuotient_one_smul x).symm
      _ = star 1 * c * cylinderKMSGNSHermitianPairing x y :=
        cylinderKMSGNSHermitianPairing_smul 1 c one_ne_zero hc x y
      _ = c * cylinderKMSGNSHermitianPairing x y := by simp

theorem cylinderKMSGNSHermitianPairing_left_kernel
    (x : cylinderKMSGNSQuotient) :
    (∀ y, cylinderKMSGNSHermitianPairing x y = 0) ↔ x = 0 := by
  constructor
  · intro h
    exact (cylinderKMSGNSHermitianPairing_self_eq_zero_iff x).mp (h x)
  · intro hx
    subst x
    intro y
    refine Quotient.inductionOn y ?_
    intro f
    change cylinderKMSGNSHermitianPairing
      (Quotient.mk' (0 : List Bool →₀ ℂ))
      (Quotient.mk' f) = 0
    rw [cylinderKMSGNSHermitianPairing_mk]
    simp [cylinderKMSHermitianPairing]

theorem cylinderKMSGNSHermitianPairing_right_kernel
    (x : cylinderKMSGNSQuotient) :
    (∀ y, cylinderKMSGNSHermitianPairing y x = 0) ↔ x = 0 := by
  constructor
  · intro h
    exact (cylinderKMSGNSHermitianPairing_self_eq_zero_iff x).mp (h x)
  · intro hx
    subst x
    intro y
    refine Quotient.inductionOn y ?_
    intro f
    change cylinderKMSGNSHermitianPairing
      (Quotient.mk' f)
      (Quotient.mk' (0 : List Bool →₀ ℂ)) = 0
    rw [cylinderKMSGNSHermitianPairing_mk]
    simp [cylinderKMSHermitianPairing]

end InfoGeometry.Canonical.CantorKMSCylinderState
