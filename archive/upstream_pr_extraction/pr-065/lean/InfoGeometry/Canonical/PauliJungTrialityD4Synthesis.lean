import Mathlib
import InfoGeometry.Canonical.SplitOctonionKleinFourTriality

namespace InfoGeometry.Canonical

/-!
# The honest three-colour cycle of the Klein-four grading

The cycle below is the order-three subgroup of the permutation symmetry of
the three nonzero grades.  This file does not call that single cycle `S₃`,
and it does not identify graded planes with Dynkin roots or prove Spin(4,4)
triality.
-/

inductive ColorChannel
  | red
  | green
  | blue
  deriving DecidableEq, Fintype

def trialityPermute : ColorChannel → ColorChannel
  | .red => .green
  | .green => .blue
  | .blue => .red

theorem triality_order_three (c : ColorChannel) :
    trialityPermute (trialityPermute (trialityPermute c)) = c := by
  cases c <;> rfl

def gradeCycle : KleinFour ≃+ KleinFour where
  toFun := fun g => (g.2, g.1 + g.2)
  invFun := fun g => (g.1 + g.2, g.1)
  left_inv := by
    intro g
    rcases g with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> rfl
  right_inv := by
    intro g
    rcases g with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> rfl
  map_add' := by
    intro g h
    rcases g with ⟨a, b⟩
    rcases h with ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> rfl

theorem gradeCycle_order_three (g : KleinFour) :
    gradeCycle (gradeCycle (gradeCycle g)) = g := by
  rcases g with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> rfl

def colorGrade : ColorChannel → KleinFour
  | .red => (1, 0)
  | .green => (0, 1)
  | .blue => (1, 1)

theorem gradeCycle_colorGrade (c : ColorChannel) :
    gradeCycle (colorGrade c) = colorGrade (trialityPermute c) := by
  cases c <;> decide

def trialityCyclePerm : Equiv.Perm ColorChannel where
  toFun := trialityPermute
  invFun := fun c => trialityPermute (trialityPermute c)
  left_inv := by
    intro c
    cases c <;> rfl
  right_inv := by
    intro c
    cases c <;> rfl

def sharedGrade : KleinFour := (0, 0)

def sharedIntegralPlane :
    Submodule ℤ StandardIntegralSplitOctonion :=
  planeComponent sharedGrade

def colorPlane (c : ColorChannel) :
    Submodule ℤ StandardIntegralSplitOctonion :=
  planeComponent (colorGrade c)

theorem gradeCycle_preserves_sharedGrade :
    gradeCycle sharedGrade = sharedGrade := by
  rfl

theorem triality_preserves_sharedIntegralPlane :
    planeComponent (gradeCycle sharedGrade) = sharedIntegralPlane := by
  rfl

theorem triality_cycle_preserves_shared_axis
    {x : StandardIntegralSplitOctonion}
    (hx : x ∈ sharedIntegralPlane) :
    x ∈ planeComponent (gradeCycle sharedGrade) := by
  simpa [sharedIntegralPlane, gradeCycle_preserves_sharedGrade] using hx

/-!
`Equiv.Perm ColorChannel` is the honest combinatorial `S₃` action on the
three outer labels.  At this layer it permutes names of planes; it is not yet
an algebra automorphism of the split-octonion carrier.
-/

abbrev ColorPermutation := Equiv.Perm ColorChannel

def permutedColorPlane
    (p : ColorPermutation) (c : ColorChannel) :
    Submodule ℤ StandardIntegralSplitOctonion :=
  colorPlane (p c)

theorem permutedColorPlane_identity (c : ColorChannel) :
    permutedColorPlane (Equiv.refl ColorChannel) c = colorPlane c := by
  rfl

theorem permutedColorPlane_composition
    (p q : ColorPermutation) (c : ColorChannel) :
    permutedColorPlane (q.trans p) c =
      permutedColorPlane p (q c) := by
  rfl

@[simp] theorem trialityCyclePerm_apply (c : ColorChannel) :
    trialityCyclePerm c = trialityPermute c := rfl

/-!
The following graph is the incidence shadow only: one central vertex and
three outer vertices.  Calling it a Dynkin diagram does not add root data or
a Lie algebra, so those structures are intentionally absent here.
-/

abbrev FourPlaneVertex := ColorChannel ⊕ Unit

def d4StarGraph : SimpleGraph FourPlaneVertex where
  Adj := fun v w =>
    match v, w with
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | _, _ => False
  symm := by
    intro v w
    cases v <;> cases w <;> simp
  loopless := by
    refine Std.Irrefl.mk ?_
    intro v
    cases v <;> simp

theorem d4StarGraph_outer_adj_center (c : ColorChannel) :
    d4StarGraph.Adj (Sum.inl c) (Sum.inr ()) := by
  simp [d4StarGraph]

theorem d4StarGraph_center_adj_outer (c : ColorChannel) :
    d4StarGraph.Adj (Sum.inr ()) (Sum.inl c) := by
  simp [d4StarGraph]

theorem d4StarGraph_outer_adj_iff_center (c : ColorChannel) (v : FourPlaneVertex) :
    d4StarGraph.Adj (Sum.inl c) v ↔ v = Sum.inr () := by
  cases v <;> simp [d4StarGraph]

theorem d4StarGraph_center_adj_iff_outer (v : FourPlaneVertex) :
    d4StarGraph.Adj (Sum.inr ()) v ↔ ∃ c : ColorChannel, v = Sum.inl c := by
  cases v <;> simp [d4StarGraph]


/-- Map nonzero KleinFour grades to a `Fin 3` index representing red, green, blue. -/
def gradeToFin : KleinFour → Option (Fin 3)
  | (0, 0) => none
  | (1, 0) => some 0
  | (0, 1) => some 1
  | (1, 1) => some 2

/-- Map a `Fin 3` index back to the corresponding nonzero KleinFour grade. -/
def finToGrade : Fin 3 → KleinFour
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)

theorem finToGrade_ne_zero (i : Fin 3) : finToGrade i ≠ (0,0) := by
  fin_cases i <;> decide

theorem gradeToFin_finToGrade (i : Fin 3) : gradeToFin (finToGrade i) = some i := by
  fin_cases i <;> rfl

theorem gradeToFin_some_iff {g : KleinFour} {i : Fin 3} : gradeToFin g = some i ↔ g = finToGrade i := by
  rcases g with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> decide

/-- Convert an additive equivalence permutation of `KleinFour` into a permutation on the three nonzero grades. -/

def gradeAutomorphismPerm (σ : KleinFour ≃+ KleinFour) : Equiv.Perm (Fin 3) where
  toFun := fun i =>
    match gradeToFin (σ (finToGrade i)) with
    | some j => j
    | none => i
  invFun := fun j =>
    match gradeToFin (σ.symm (finToGrade j)) with
    | some i => i
    | none => j
  left_inv := by
    intro i
    have h_ne : σ (finToGrade i) ≠ (0,0) := by
      intro h
      have h2 := congrArg σ.symm h
      rw [AddEquiv.symm_apply_apply] at h2
      have h_zero : σ.symm (0,0) = (0,0) := map_zero σ.symm
      rw [h_zero] at h2
      exact finToGrade_ne_zero i h2
    have ⟨j, hj⟩ : ∃ j, gradeToFin (σ (finToGrade i)) = some j := by
      rcases hg : σ (finToGrade i) with ⟨a, b⟩
      fin_cases a <;> fin_cases b
      · rw [hg] at h_ne
        exact False.elim (h_ne rfl)
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
    simp [hj]
    have hg_eq : σ (finToGrade i) = finToGrade j := gradeToFin_some_iff.mp hj
    have hs : σ.symm (finToGrade j) = finToGrade i := by
      rw [← hg_eq, AddEquiv.symm_apply_apply]
    have h_inv : gradeToFin (σ.symm (finToGrade j)) = some i := by
      rw [hs, gradeToFin_finToGrade]
    simp [h_inv]
  right_inv := by
    intro j
    have h_ne : σ.symm (finToGrade j) ≠ (0,0) := by
      intro h
      have h2 := congrArg σ h
      rw [AddEquiv.apply_symm_apply] at h2
      have h_zero : σ (0,0) = (0,0) := map_zero σ
      rw [h_zero] at h2
      exact finToGrade_ne_zero j h2
    have ⟨i, hi⟩ : ∃ i, gradeToFin (σ.symm (finToGrade j)) = some i := by
      rcases hg : σ.symm (finToGrade j) with ⟨a, b⟩
      fin_cases a <;> fin_cases b
      · rw [hg] at h_ne
        exact False.elim (h_ne rfl)
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
    simp [hi]
    have hg_eq : σ.symm (finToGrade j) = finToGrade i := gradeToFin_some_iff.mp hi
    have hs : σ (finToGrade i) = finToGrade j := by
      rw [← hg_eq, AddEquiv.apply_symm_apply]
    have h_inv : gradeToFin (σ (finToGrade i)) = some j := by
      rw [hs, gradeToFin_finToGrade]
    simp [h_inv]

-- The above provides an explicit isomorphism between the additive permutation group on the non‑zero
-- grades of the Klein‑four and the symmetric group `S₃` acting on three elements.

end InfoGeometry.Canonical

