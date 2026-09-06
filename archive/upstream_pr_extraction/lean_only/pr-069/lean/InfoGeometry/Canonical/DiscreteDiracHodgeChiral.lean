import Mathlib.Tactic

/-!
# Discrete Dirac-Hodge Chirality

Finite algebraic owner for the total-form Dirac-Hodge pattern
`D = d + δ`, its Laplacian `L = dδ + δd`, and the chirality split.

The nilpotent expansion `D² = dδ + δd`, chirality anticommutation, evenness of
`D²`, and exact/coexact/harmonic predicate readbacks are proved at ring/function
level.

Hodge decomposition, Betti-number identification, and graph/simplicial
realization are intentionally represented only by explicit hypotheses in the
readout theorem below.
-/

namespace InfoGeometry.Canonical.DiscreteDiracHodgeChiral

universe u

/-! ## Ring-level Dirac-Hodge algebra -/

variable {Op : Type u} [Ring Op]

/-- Total-form Dirac-Hodge operator `D = d + δ`. -/
def diracHodge (d cod : Op) : Op :=
  d + cod

/-- Hodge Laplacian algebraic cross term `L = dδ + δd`. -/
def hodgeLaplacian (d cod : Op) : Op :=
  d * cod + cod * d

/-- Nilpotence of both odd parts removes the diagonal terms in `D²`. -/
theorem diracHodge_sq_eq_hodgeLaplacian
    (d cod : Op)
    (hd : d * d = 0)
    (hcod : cod * cod = 0) :
    diracHodge d cod * diracHodge d cod = hodgeLaplacian d cod := by
  unfold diracHodge hodgeLaplacian
  calc
    (d + cod) * (d + cod)
        = d * d + d * cod + (cod * d + cod * cod) := by
          rw [add_mul, mul_add, mul_add]
    _ = 0 + d * cod + (cod * d + 0) := by
          rw [hd, hcod]
    _ = d * cod + cod * d := by
          simp

/-- If both `d` and `δ` anticommute with chirality, then `D = d + δ` does too. -/
theorem diracHodge_anticommutes_chirality
    (d cod gamma : Op)
    (hd : d * gamma = -(gamma * d))
    (hcod : cod * gamma = -(gamma * cod)) :
    diracHodge d cod * gamma = -(gamma * diracHodge d cod) := by
  unfold diracHodge
  calc
    (d + cod) * gamma = d * gamma + cod * gamma := by
      rw [add_mul]
    _ = -(gamma * d) + -(gamma * cod) := by
      rw [hd, hcod]
    _ = -(gamma * (d + cod)) := by
      rw [mul_add]
      abel

/-- Any operator anticommuting with chirality has a chirality-even square. -/
theorem square_commutes_chirality_of_anticommutes
    (D gamma : Op)
    (hD : D * gamma = -(gamma * D)) :
    (D * D) * gamma = gamma * (D * D) := by
  calc
    (D * D) * gamma = D * (D * gamma) := by
      rw [mul_assoc]
    _ = D * (-(gamma * D)) := by
      rw [hD]
    _ = -(D * (gamma * D)) := by
      simp
    _ = -((D * gamma) * D) := by
      rw [mul_assoc]
    _ = -((-(gamma * D)) * D) := by
      rw [hD]
    _ = gamma * (D * D) := by
      simp [mul_assoc]

/-- The Dirac-Hodge Laplacian is chirality-even under the supplied oddness laws. -/
theorem hodgeLaplacian_commutes_chirality
    (d cod gamma : Op)
    (hdNil : d * d = 0)
    (hcodNil : cod * cod = 0)
    (hdOdd : d * gamma = -(gamma * d))
    (hcodOdd : cod * gamma = -(gamma * cod)) :
    hodgeLaplacian d cod * gamma = gamma * hodgeLaplacian d cod := by
  have hDodd :
      diracHodge d cod * gamma = -(gamma * diracHodge d cod) :=
    diracHodge_anticommutes_chirality d cod gamma hdOdd hcodOdd
  have hsq :
      diracHodge d cod * diracHodge d cod = hodgeLaplacian d cod :=
    diracHodge_sq_eq_hodgeLaplacian d cod hdNil hcodNil
  calc
    hodgeLaplacian d cod * gamma
        = (diracHodge d cod * diracHodge d cod) * gamma := by
          rw [hsq]
    _ = gamma * (diracHodge d cod * diracHodge d cod) := by
          exact square_commutes_chirality_of_anticommutes (diracHodge d cod) gamma hDodd
    _ = gamma * hodgeLaplacian d cod := by
          rw [hsq]

/-! ## Exact, coexact, and harmonic predicates on finite total forms -/

section FormPredicates

variable {Form : Type u} [Zero Form]

/-- Exact part: image of the discrete exterior derivative. -/
def IsExact (d : Form → Form) (x : Form) : Prop :=
  ∃ y : Form, d y = x

/-- Coexact part: image of the codifferential. -/
def IsCoexact (cod : Form → Form) (x : Form) : Prop :=
  ∃ y : Form, cod y = x

/-- Harmonic part: kernel of both the exterior derivative and codifferential. -/
def IsHarmonic (d cod : Form → Form) (x : Form) : Prop :=
  d x = 0 ∧ cod x = 0

/-- Harmonic forms are closed. -/
theorem harmonic_closed
    (d cod : Form → Form) (x : Form)
    (hx : IsHarmonic d cod x) :
    d x = 0 :=
  hx.1

/-- Harmonic forms are coclosed. -/
theorem harmonic_coclosed
    (d cod : Form → Form) (x : Form)
    (hx : IsHarmonic d cod x) :
    cod x = 0 :=
  hx.2

/-- Exact forms are closed when `d² = 0`. -/
theorem exact_closed_of_nilpotent
    (d : Form → Form)
    (hd : ∀ x : Form, d (d x) = 0)
    (x : Form)
    (hx : IsExact d x) :
    d x = 0 := by
  rcases hx with ⟨y, rfl⟩
  exact hd y

/-- Coexact forms are coclosed when `δ² = 0`. -/
theorem coexact_coclosed_of_nilpotent
    (cod : Form → Form)
    (hcod : ∀ x : Form, cod (cod x) = 0)
    (x : Form)
    (hx : IsCoexact cod x) :
    cod x = 0 := by
  rcases hx with ⟨y, rfl⟩
  exact hcod y

/--
If a concrete finite Hodge decomposition is supplied, every form has exact,
coexact, and harmonic components.
-/
theorem hodge_decomposition_readout
    (d cod : Form → Form)
    (component : Form → Form → Form → Form)
    (x exact coexact harmonic : Form)
    (hdecomp :
      x = component exact coexact harmonic ∧
        IsExact d exact ∧ IsCoexact cod coexact ∧ IsHarmonic d cod harmonic) :
    x = component exact coexact harmonic ∧
      IsExact d exact ∧ IsCoexact cod coexact ∧ IsHarmonic d cod harmonic :=
  hdecomp

end FormPredicates

end InfoGeometry.Canonical.DiscreteDiracHodgeChiral
