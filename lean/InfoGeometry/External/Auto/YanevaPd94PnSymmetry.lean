import Mathlib

namespace YanevaPd94PnSymmetry

abbrev Q := ℚ

def Tz (N Z : Q) : Q := (N - Z) / 2

def doubledTz (N Z : ℤ) : ℤ := N - Z

def doubledT (T : ℕ) : ℕ := 2 * T

def inIsospinMultiplet (T : ℕ) (twoTz : ℤ) : Prop :=
  |twoTz| ≤ (doubledT T : ℤ)

structure IsospinState where
  T : ℕ
  dim : ℕ
  is_su2_irrep : dim = 2 * T + 1

def isospinIrrepDim (T : ℕ) : ℕ := 2 * T + 1

theorem isospinState_dim_eq_irrepDim (s : IsospinState) :
    s.dim = isospinIrrepDim s.T := by
  exact s.is_su2_irrep

def so3Dim (J : ℕ) : ℕ := 2 * J + 1

def e2Allowed (Ji Jf : ℕ) : Prop := Ji = Jf + 2

theorem e2Allowed_iff (Ji Jf : ℕ) :
    e2Allowed Ji Jf ↔ Ji = Jf + 2 := by
  rfl

def weakCollectivity (b threshold : Q) : Prop := b < threshold

def inClosedInterval (x lo hi : Q) : Prop := lo ≤ x ∧ x ≤ hi

theorem inClosedInterval_refl {x : Q} :
    inClosedInterval x x x := by
  exact ⟨le_rfl, le_rfl⟩

theorem doubledTz_add_swap (N Z : ℤ) :
    doubledTz N Z = -(doubledTz Z N) := by
  simp [doubledTz]

theorem isospinIrrepDim_nonzero (T : ℕ) :
    0 < isospinIrrepDim T := by
  simp [isospinIrrepDim]

end YanevaPd94PnSymmetry
