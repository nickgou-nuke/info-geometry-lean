import Mathlib

/-!
# Dual-flat graphs in a neutral primal/dual carrier

This finite algebraic owner realizes the intrinsic `V ⊕ V*` picture using
`Covector n := (Fin n → ℝ) →ₗ[ℝ] ℝ`.  It proves only the graph identities: a
symmetric generating bilinear form induces its symmetric metric on the graph,
and the graph is isotropic for the canonical skew pairing.
-/

namespace InfoGeometry.Quantum.DualFlatKreinGraph

open scoped InnerProductSpace

abbrev Vector (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Covector (n : ℕ) := Vector n →ₗ[ℝ] ℝ
abbrev Carrier (n : ℕ) := Vector n × Covector n

/- An exchange requires a chosen linear identification of the two
  polarizations.  Keeping that identification explicit avoids silently
  imposing a Euclidean metric on the dual space. -/
def exchange {n : ℕ} (E : Vector n ≃ₗ[ℝ] Covector n) (x : Carrier n) : Carrier n :=
  (E.symm x.2, E x.1)

theorem exchange_sq {n : ℕ} (E : Vector n ≃ₗ[ℝ] Covector n) (x : Carrier n) :
    exchange E (exchange E x) = x := by
  ext <;> simp [exchange]

def SymmetricDuality {n : ℕ} (E : Vector n ≃ₗ[ℝ] Covector n) : Prop :=
  ∀ v w, (E v) w = (E w) v

/-- A positive realization obtained after choosing the primal/dual
  identification.  This is deliberately separate from the neutral pairing. -/
noncomputable def positivePair {n : ℕ} (E : Vector n ≃ₗ[ℝ] Covector n)
    (x y : Carrier n) : ℝ :=
  ⟪x.1, y.1⟫_ℝ + ⟪E.symm x.2, E.symm y.2⟫_ℝ

theorem positivePair_self_nonneg {n : ℕ} (E : Vector n ≃ₗ[ℝ] Covector n)
    (x : Carrier n) : 0 ≤ positivePair E x x := by
  unfold positivePair
  exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg

theorem positivePair_self_pos {n : ℕ} (E : Vector n ≃ₗ[ℝ] Covector n)
    {x : Carrier n} (hx : x ≠ 0) : 0 < positivePair E x x := by
  unfold positivePair
  by_cases hv : x.1 = 0
  · have hα : E.symm x.2 ≠ 0 := by
      intro hα
      apply hx
      apply Prod.ext
      · exact hv
      · apply E.symm.injective
        simpa using hα
    have hsecond : 0 < ⟪E.symm x.2, E.symm x.2⟫_ℝ :=
      real_inner_self_pos.mpr hα
    simpa [hv] using hsecond
  · have hfirst : 0 < ⟪x.1, x.1⟫_ℝ := real_inner_self_pos.mpr hv
    have hsecond : 0 ≤ ⟪E.symm x.2, E.symm x.2⟫_ℝ := real_inner_self_nonneg
    nlinarith

/-- The neutral symmetric pairing between primal and dual coordinates. -/
noncomputable def neutralPair {n : ℕ} (x y : Carrier n) : ℝ :=
  (x.2 y.1 + y.2 x.1) / 2

theorem neutralPair_comm {n : ℕ} (x y : Carrier n) :
    neutralPair x y = neutralPair y x := by
  unfold neutralPair
  ring

/-- The canonical skew pairing on the same primal/dual carrier. -/
def symplecticPair {n : ℕ} (x y : Carrier n) : ℝ :=
  x.2 y.1 - y.2 x.1

theorem symplecticPair_swap {n : ℕ} (x y : Carrier n) :
    symplecticPair y x = -symplecticPair x y := by
  unfold symplecticPair
  ring

/-- The primal/dual grading. -/
def grading {n : ℕ} (x : Carrier n) : Carrier n :=
  (x.1, -x.2)

theorem grading_sq {n : ℕ} (x : Carrier n) : grading (grading x) = x := by
  ext <;> simp [grading]

theorem exchange_preserves_neutralPair {n : ℕ}
    (E : Vector n ≃ₗ[ℝ] Covector n) (hE : SymmetricDuality E)
    (x y : Carrier n) :
    neutralPair (exchange E x) (exchange E y) = neutralPair x y := by
  unfold neutralPair exchange
  rw [hE x.1 (E.symm y.2), hE y.1 (E.symm x.2),
    E.apply_symm_apply, E.apply_symm_apply]
  ring

theorem grading_exchange_anticommute {n : ℕ}
    (E : Vector n ≃ₗ[ℝ] Covector n) (x : Carrier n) :
    grading (exchange E x) = -exchange E (grading x) := by
  ext <;> simp [grading, exchange]

def PositiveFundamentalDuality {n : ℕ}
    (E : Vector n ≃ₗ[ℝ] Covector n) : Prop :=
  SymmetricDuality E ∧
    ∀ x, x ≠ 0 → 0 < neutralPair x (exchange E x)

theorem positiveFundamentalPair_self_pos {n : ℕ}
    (E : Vector n ≃ₗ[ℝ] Covector n)
    (hE : PositiveFundamentalDuality E) {x : Carrier n} (hx : x ≠ 0) :
    0 < neutralPair x (exchange E x) :=
  hE.2 x hx

/-- The two null polarizations of the carrier. -/
def primal {n : ℕ} (v : Vector n) : Carrier n := (v, 0)
def dual {n : ℕ} (α : Covector n) : Carrier n := (0, α)

theorem grading_primal {n : ℕ} (v : Vector n) :
    grading (primal v) = primal v := by
  simp [grading, primal]

theorem grading_dual {n : ℕ} (α : Covector n) :
    grading (dual α) = dual (-α) := by
  rfl

theorem neutralPair_primal_primal {n : ℕ} (v w : Vector n) :
    neutralPair (primal v) (primal w) = 0 := by
  simp [neutralPair, primal]

theorem neutralPair_dual_dual {n : ℕ} (α β : Covector n) :
    neutralPair (dual α) (dual β) = 0 := by
  simp [neutralPair, dual]

theorem neutralPair_primal_dual {n : ℕ} (v : Vector n) (α : Covector n) :
    neutralPair (primal v) (dual α) = α v / 2 := by
  simp [neutralPair, primal, dual]

/-- The graph of a generating bilinear form `B : V × V → ℝ`. -/
def graphLift {n : ℕ} (B : Vector n →ₗ[ℝ] Covector n) (v : Vector n) :
    Carrier n := (v, B v)

def graphMap {n : ℕ} (B : Vector n →ₗ[ℝ] Covector n) :
    Vector n →ₗ[ℝ] Carrier n :=
  { toFun := graphLift B
    map_add' := by
      intro v w
      simp [graphLift, map_add]
    map_smul' := by
      intro c v
      simp [graphLift, map_smul] }

theorem graphMap_apply {n : ℕ} (B : Vector n →ₗ[ℝ] Covector n) (v : Vector n) :
    graphMap B v = graphLift B v := by
  rfl

theorem graphLift_injective {n : ℕ} (B : Vector n →ₗ[ℝ] Covector n) :
    Function.Injective (graphLift B) := by
  intro v w h
  exact congrArg Prod.fst h

theorem graphMap_injective {n : ℕ} (B : Vector n →ₗ[ℝ] Covector n) :
    Function.Injective (graphMap B) := by
  intro v w h
  exact graphLift_injective B (by simpa [graphMap_apply] using h)

def Symmetric {n : ℕ} (B : Vector n →ₗ[ℝ] Covector n) : Prop :=
  ∀ v w, (B v) w = (B w) v

def PositiveDefinite {n : ℕ} (B : Vector n →ₗ[ℝ] Covector n) : Prop :=
  ∀ v, v ≠ 0 → 0 < (B v) v

theorem neutralPair_graphLift {n : ℕ}
    (B : Vector n →ₗ[ℝ] Covector n) (hB : Symmetric B)
    (v w : Vector n) :
    neutralPair (graphLift B v) (graphLift B w) = B v w := by
  change ((B v) w + (B w) v) / 2 = (B v) w
  rw [hB v w]
  ring

theorem neutralPair_graphLift_self_pos {n : ℕ}
    (B : Vector n →ₗ[ℝ] Covector n) (hB : Symmetric B)
    (hpos : PositiveDefinite B) {v : Vector n} (hv : v ≠ 0) :
    0 < neutralPair (graphLift B v) (graphLift B v) := by
  rw [neutralPair_graphLift B hB v v]
  exact hpos v hv

theorem symplecticPair_graphLift {n : ℕ}
    (B : Vector n →ₗ[ℝ] Covector n) (hB : Symmetric B)
    (v w : Vector n) :
    symplecticPair (graphLift B v) (graphLift B w) = 0 := by
  change (B v) w - (B w) v = 0
  exact sub_eq_zero.mpr (hB v w)

end InfoGeometry.Quantum.DualFlatKreinGraph
