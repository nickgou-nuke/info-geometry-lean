module

public import InfoGeometry.Exceptional.CFSGPort.CurtisTitsRankOne

/-!
# Bruhat multiplication on the exceptional rank-one operator subgroup

Local API port of the rank-one identities in CFSG's `PartBRankOne`.
The carrier is the subgroup of root-module endomorphism units.
-/

public section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.OperatorRankOneRels

variable {τ : Tag} {K : Type*} [Field K] {i : Fin τ.rank}
variable (R : OperatorRankOneRels (τ := τ) (K := K) i)

/-- The unit Weyl operator inverts the torus parameter when moved past it. -/
theorem w_one_mul_h (t : Kˣ) : R.w 1 * R.h t = R.h t⁻¹ * R.w 1 := by
  have e := R.h_conj_w t 1
  rw [mul_one, R.w_eq_h_mul (t ^ 2)] at e
  have e2 : R.h t * R.w 1 = R.h (t ^ 2) * R.w 1 * R.h t :=
    mul_inv_eq_iff_eq_mul.mp e
  calc
    R.w 1 * R.h t = (R.h (t ^ 2))⁻¹ * (R.h (t ^ 2) * R.w 1 * R.h t) := by
      group
    _ = (R.h (t ^ 2))⁻¹ * (R.h t * R.w 1) := by rw [← e2]
    _ = R.h ((t ^ 2)⁻¹ * t) * R.w 1 := by
      rw [R.h_inv, R.h_mul]
      group
    _ = R.h t⁻¹ * R.w 1 := by
      congr 2
      group

/-- The corresponding torus-to-Weyl interchange law. -/
theorem h_mul_w_one (t : Kˣ) : R.h t * R.w 1 = R.w 1 * R.h t⁻¹ := by
  rw [R.w_one_mul_h, inv_inv]

/-- Reduction of a nonzero positive-root operator between two Weyl operators
to the long Bruhat cell. -/
theorem w_one_mul_x_mul_w_one (b : Kˣ) :
    R.w 1 * R.x (b : K) * R.w 1 =
      R.x (-((b⁻¹ : Kˣ) : K)) * R.w 1 * R.x (-(b : K)) * R.h (-b) := by
  have e1 : R.y (-(b : K)) =
      R.x (-((b⁻¹ : Kˣ) : K)) * R.w b⁻¹ * R.x (-((b⁻¹ : Kˣ) : K)) := by
    rw [w, inv_inv, R.x_neg]
    group
  have econj : R.w 1 * R.x (b : K) * (R.w 1)⁻¹ = R.y (-(b : K)) := by
    simpa only [neg_neg] using (R.y_eq_conj (-(b : K))).symm
  calc
    _ = (R.w 1 * R.x (b : K) * (R.w 1)⁻¹) * (R.w 1 * R.w 1) := by group
    _ = R.y (-(b : K)) * R.h (-1) := by rw [econj, R.w_one_mul_w_one]
    _ = R.x (-((b⁻¹ : Kˣ) : K)) * (R.h b⁻¹ * R.w 1) *
        R.x (-((b⁻¹ : Kˣ) : K)) * R.h (-1) := by rw [e1, R.w_eq_h_mul]
    _ = R.x (-((b⁻¹ : Kˣ) : K)) * R.w 1 *
        (R.h b * R.x (-((b⁻¹ : Kˣ) : K))) * R.h (-1) := by
      rw [← R.w_one_mul_h]
      group
    _ = R.x (-((b⁻¹ : Kˣ) : K)) * R.w 1 *
        R.x ((b : K) ^ 2 * -((b⁻¹ : Kˣ) : K)) * R.h (b * -1) := by
      rw [R.h_mul_x, R.h_mul]
      group
    _ = _ := by
      rw [mul_neg_one]
      congr 3
      simp [pow_two]

/-- The two Bruhat cells are stable under right multiplication by the unit
Weyl operator. -/
theorem mul_w_mem_bruhat {g : operatorRankOneSubgroup (τ := τ) (K := K) i}
    (hg : g ∈ R.bruhat) : g * R.w 1 ∈ R.bruhat := by
  rcases hg with ⟨a, t, rfl⟩ | ⟨a, b, t, rfl⟩
  · right
    refine ⟨a, 0, t⁻¹, ?_⟩
    rw [R.x_zero, mul_one, mul_assoc, R.h_mul_w_one, ← mul_assoc]
  by_cases hb : b = 0
  · left
    refine ⟨a, -t⁻¹, ?_⟩
    calc
      _ = R.x a * (R.w 1 * R.w 1) * R.h t⁻¹ := by
        rw [hb, R.x_zero, mul_assoc _ (R.h t), R.h_mul_w_one]
        group
      _ = R.x a * R.h (-t⁻¹) := by
        rw [R.w_one_mul_w_one, mul_assoc, ← R.h_mul, neg_one_mul]
  · let u : Kˣ := Units.mk0 b hb
    have hu : (u : K) = b := rfl
    right
    refine ⟨a + -((u⁻¹ : Kˣ) : K), -b, -u * t⁻¹, ?_⟩
    calc
      _ = R.x a * (R.w 1 * R.x (u : K) * R.w 1) * R.h t⁻¹ := by
        rw [hu, mul_assoc _ (R.h t), R.h_mul_w_one]
        group
      _ = R.x a * R.x (-((u⁻¹ : Kˣ) : K)) * R.w 1 * R.x (-(u : K)) *
          (R.h (-u) * R.h t⁻¹) := by
        rw [R.w_one_mul_x_mul_w_one]
        group
      _ = _ := by rw [← R.h_mul, R.x_add, hu]

/-- The same stability holds for the inverse Weyl operator. -/
theorem mul_w_inv_mem_bruhat {g : operatorRankOneSubgroup (τ := τ) (K := K) i}
    (hg : g ∈ R.bruhat) : g * (R.w 1)⁻¹ ∈ R.bruhat := by
  rw [R.w_inv, R.w_eq_h_mul, ← mul_assoc]
  exact R.mul_w_mem_bruhat (R.mul_h_mem_bruhat hg (-1))

/-- Negative-root multiplication preserves the two Bruhat cells. -/
theorem mul_y_mem_bruhat {g : operatorRankOneSubgroup (τ := τ) (K := K) i}
    (hg : g ∈ R.bruhat) (c : K) : g * R.y c ∈ R.bruhat := by
  rw [R.y_eq_conj, ← mul_assoc, ← mul_assoc]
  exact R.mul_w_inv_mem_bruhat (R.mul_x_mem_bruhat (R.mul_w_mem_bruhat hg) _)

/-- Every element of the actual rank-one operator subgroup lies in one of
the two Bruhat cells. This follows from generation by the two root groups. -/
theorem mem_bruhat (g : operatorRankOneSubgroup (τ := τ) (K := K) i) :
    g ∈ R.bruhat := by
  have hgen : operatorRankOneSubgroup (τ := τ) (K := K) i =
      Subgroup.closure (Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i)) := by
    have hx : pinnedX τ K (Pi.single i 1) = xUnit τ K i :=
      funext (pinnedX_single (τ := τ) (R := K) i)
    have hy : pinnedX τ K (-Pi.single i 1) = yUnit τ K i :=
      funext (pinnedX_neg_single (τ := τ) (R := K) i)
    simp only [operatorRankOneSubgroup, rootSubgroup, hx, hy, Subgroup.closure_union]
  have hg : (g : (Module.End K (RootModule τ K))ˣ) ∈
      Subgroup.closure (Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i)) := by
    rw [← hgen]
    exact g.property
  have hcover : ∃ z : operatorRankOneSubgroup (τ := τ) (K := K) i,
      (z : (Module.End K (RootModule τ K))ˣ) = g ∧ z ∈ R.bruhat := by
    refine Subgroup.closure_induction_right
      (p := fun a _ => ∃ z : operatorRankOneSubgroup (τ := τ) (K := K) i,
        (z : (Module.End K (RootModule τ K))ˣ) = a ∧ z ∈ R.bruhat)
      ⟨1, rfl, R.one_mem_bruhat⟩ ?_ ?_ hg
    · rintro a ha z hz ⟨v, hv, hB⟩
      rcases hz with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · refine ⟨v * R.x c, ?_, R.mul_x_mem_bruhat hB c⟩
        change (v : (Module.End K (RootModule τ K))ˣ) * ↑(R.x c) = _
        rw [hv, R.x_val]
      · refine ⟨v * R.y c, ?_, R.mul_y_mem_bruhat hB c⟩
        change (v : (Module.End K (RootModule τ K))ˣ) * ↑(R.y c) = _
        rw [hv, R.y_val]
    · rintro a ha z hz ⟨v, hv, hB⟩
      rcases hz with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · refine ⟨v * R.x (-c), ?_, R.mul_x_mem_bruhat hB (-c)⟩
        rw [R.x_neg]
        change (v : (Module.End K (RootModule τ K))ˣ) * (↑(R.x c))⁻¹ = _
        rw [hv, R.x_val]
      · refine ⟨v * R.y (-c), ?_, R.mul_y_mem_bruhat hB (-c)⟩
        rw [R.y_neg]
        change (v : (Module.End K (RootModule τ K))ˣ) * (↑(R.y c))⁻¹ = _
        rw [hv, R.y_val]
  obtain ⟨z, hz, hB⟩ := hcover
  have heq : z = g := Subtype.ext hz
  exact heq ▸ hB

/-- Move a positive-root factor to the right of the torus. -/
theorem x_mul_h (t : Kˣ) (a : K) :
    R.x a * R.h t = R.h t * R.x (((t⁻¹ : Kˣ) : K) ^ 2 * a) := by
  have e := R.h_mul_x t⁻¹ a
  rw [← R.h_inv] at e
  calc
    _ = R.h t * ((R.h t)⁻¹ * R.x a) * R.h t := by group
    _ = _ := by rw [e]; group

end InfoGeometry.Exceptional.CFSGPort.Chevalley.OperatorRankOneRels

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley

variable {τ : Tag} {K : Type*} [Field K]

/-- Rank-one Bruhat factorization in the factor order of the external
`SteinbergExtras.rankOne_bruhat` field, on the ambient operator-unit group.
All root and torus membership witnesses are constructed locally. -/
theorem operatorRankOne_bruhat (i : Fin τ.rank)
    {g : (Module.End K (RootModule τ K))ˣ}
    (hg : g ∈ operatorRankOneSubgroup (τ := τ) (K := K) i) :
    (∃ h ∈ simpleRootTorusSubgroup (τ := τ) (K := K) i,
      ∃ u ∈ rootSubgroup τ K (Pi.single i 1), g = h * u) ∨
    ∃ u ∈ rootSubgroup τ K (Pi.single i 1),
      ∃ h ∈ simpleRootTorusSubgroup (τ := τ) (K := K) i,
        ∃ v ∈ rootSubgroup τ K (Pi.single i 1),
          g = u * weylElt τ K i 1 * h * v := by
  let R := operatorRankOneRels (τ := τ) (K := K) i
  have hx (c : K) : (R.x c : (Module.End K (RootModule τ K))ˣ) ∈
      rootSubgroup τ K (Pi.single i 1) := by
    rw [R.x_val, ← pinnedX_single]
    exact Subgroup.subset_closure ⟨c, rfl⟩
  have hh (t : Kˣ) : (R.h t : (Module.End K (RootModule τ K))ˣ) ∈
      simpleRootTorusSubgroup (τ := τ) (K := K) i := by
    rw [R.coe_h]
    exact Subgroup.subset_closure ⟨t, rfl⟩
  rcases R.mem_bruhat ⟨g, hg⟩ with ⟨a, t, he⟩ | ⟨a, b, t, he⟩
  · left
    rw [R.x_mul_h] at he
    exact ⟨_, hh t, _, hx _, congrArg Subtype.val he⟩
  · right
    have he' : (⟨g, hg⟩ : operatorRankOneSubgroup (τ := τ) (K := K) i) =
        R.x a * R.w 1 * R.h t * R.x (((t⁻¹ : Kˣ) : K) ^ 2 * b) := by
      rw [he, mul_assoc (R.x a * R.w 1), R.x_mul_h, ← mul_assoc]
    refine ⟨_, hx a, _, hh t, _, hx (((t⁻¹ : Kˣ) : K) ^ 2 * b), ?_⟩
    have hv := congrArg Subtype.val he'
    simpa only [Subgroup.coe_mul, R.coe_w] using hv

/-- The operator rank-one subgroup is contained in the adjoint group. -/
theorem operatorRankOneSubgroup_le_adjointGroup (i : Fin τ.rank) :
    operatorRankOneSubgroup (τ := τ) (K := K) i ≤ adjointGroup τ K :=
  sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)

/-- The rank-one Bruhat factorization transported into the actual adjoint
group, with its root and torus subgroups restricted along the inclusion. -/
theorem adjointGroup_rankOne_bruhat (i : Fin τ.rank) {g : adjointGroup τ K}
    (hg : g ∈ (operatorRankOneSubgroup (τ := τ) (K := K) i).subgroupOf
      (adjointGroup τ K)) :
    (∃ h ∈ (simpleRootTorusSubgroup (τ := τ) (K := K) i).subgroupOf (adjointGroup τ K),
      ∃ u ∈ (rootSubgroup τ K (Pi.single i 1)).subgroupOf (adjointGroup τ K),
        g = h * u) ∨
    ∃ u ∈ (rootSubgroup τ K (Pi.single i 1)).subgroupOf (adjointGroup τ K),
      ∃ h ∈ (simpleRootTorusSubgroup (τ := τ) (K := K) i).subgroupOf (adjointGroup τ K),
        ∃ v ∈ (rootSubgroup τ K (Pi.single i 1)).subgroupOf (adjointGroup τ K),
          g = u * ⟨weylElt τ K i 1, operatorRankOneSubgroup_le_adjointGroup i
            (weylElt_mem_operatorRankOneSubgroup i 1)⟩ * h * v := by
  rcases operatorRankOne_bruhat i (Subgroup.mem_subgroupOf.mp hg) with
    ⟨h, hh, u, hu, he⟩ | ⟨u, hu, h, hh, v, hv, he⟩
  · left
    refine ⟨⟨h, simpleRootTorusSubgroup_le_adjointGroup i hh⟩,
      Subgroup.mem_subgroupOf.mpr hh,
      ⟨u, rootSubgroup_le_adjointGroup _ hu⟩, Subgroup.mem_subgroupOf.mpr hu, ?_⟩
    exact Subtype.ext he
  · right
    refine ⟨⟨u, rootSubgroup_le_adjointGroup _ hu⟩, Subgroup.mem_subgroupOf.mpr hu,
      ⟨h, simpleRootTorusSubgroup_le_adjointGroup i hh⟩, Subgroup.mem_subgroupOf.mpr hh,
      ⟨v, rootSubgroup_le_adjointGroup _ hv⟩, Subgroup.mem_subgroupOf.mpr hv, ?_⟩
    exact Subtype.ext he

end InfoGeometry.Exceptional.CFSGPort.Chevalley
