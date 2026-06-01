import InfoGeometry.Clifford.ConformalLift55
import InfoGeometry.Canonical.FibonacciFiveGradeBridge

/-!
# InfoGeometry.Clifford.FibonacciCl55Carrier

Concrete `Cl(5,5)`-anchored finite Fibonacci braid statements, written with
explicit terms and hypotheses rather than carrier packets.  The file records no
concrete braid formula beyond supplied preservation hypotheses and makes no
unsupported identification between the five-grade carrier and Fibonacci theory.
-/

noncomputable section

namespace InfoGeometry.Clifford.FibonacciCl55Carrier

open InfoGeometry.Clifford.ConformalLift55
open InfoGeometry.Canonical.FibonacciFiveGradeBridge
open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Canonical.FibonacciParafermionAtoms

/-- An explicit conformal null-pair hypothesis gives isotropy of the first leg. -/
theorem nullPair_u_square (u v : ConformalLift55.Cl55)
    (h_u : u ^ 2 = 0) (_h_v : v ^ 2 = 0)
    (_h_anticomm : u * v + v * u = 1) :
    u ^ 2 = 0 :=
  h_u

/-- An explicit conformal null-pair hypothesis gives isotropy of the second leg. -/
theorem nullPair_v_square (u v : ConformalLift55.Cl55)
    (_h_u : u ^ 2 = 0) (h_v : v ^ 2 = 0)
    (_h_anticomm : u * v + v * u = 1) :
    v ^ 2 = 0 :=
  h_v

/-- An explicit conformal null-pair hypothesis gives the anticommutator relation. -/
theorem nullPair_anticomm (u v : ConformalLift55.Cl55)
    (_h_u : u ^ 2 = 0) (_h_v : v ^ 2 = 0)
    (h_anticomm : u * v + v * u = 1) :
    u * v + v * u = 1 :=
  h_anticomm

/-- The finite Fibonacci matrix from explicit coefficients is involutive. -/
theorem fusionMatrix_sq (a b : ℝ) (h : IsFibonacciRelation a b) :
    F_matrix a b * F_matrix a b = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  exact InfoGeometry.Canonical.FibonacciFiveGradeBridge.fusionMatrix_sq a b h

/-- The supplied braid action preserves grade. -/
theorem braid_preserves_grade (grade : ConformalLift55.Cl55 → ConformalGrade) (braid : ConformalLift55.Cl55 → ConformalLift55.Cl55)
    (h_grade : ∀ x : ConformalLift55.Cl55, grade (braid x) = grade x) (x : ConformalLift55.Cl55) :
    grade (braid x) = grade x :=
  InfoGeometry.Canonical.FibonacciFiveGradeBridge.braid_preserves_grade grade braid h_grade x

/-- The supplied braid action preserves the computational sector. -/
theorem braid_preserves_computational
    (computationalSet : Set ConformalLift55.Cl55) (braid : ConformalLift55.Cl55 → ConformalLift55.Cl55)
    (h_comp : ∀ x : ConformalLift55.Cl55, x ∈ computationalSet → braid x ∈ computationalSet)
    (x : ConformalLift55.Cl55) (hx : x ∈ computationalSet) :
    braid x ∈ computationalSet :=
  h_comp x hx

/-- The supplied braid action preserves the leakage sector. -/
theorem braid_preserves_leakage
    (leakageSet : Set ConformalLift55.Cl55) (braid : ConformalLift55.Cl55 → ConformalLift55.Cl55)
    (h_leak : ∀ x : ConformalLift55.Cl55, x ∈ leakageSet → braid x ∈ leakageSet)
    (x : ConformalLift55.Cl55) (hx : x ∈ leakageSet) :
    braid x ∈ leakageSet :=
  InfoGeometry.Canonical.FibonacciFiveGradeBridge.braid_preserves_leakage leakageSet braid h_leak hx

/-- The supplied braid action blocks leakage from the computational sector. -/
theorem braid_not_leakage_of_computational
    (computationalSet leakageSet : Set ConformalLift55.Cl55) (braid : ConformalLift55.Cl55 → ConformalLift55.Cl55)
    (h_comp : ∀ x : ConformalLift55.Cl55, x ∈ computationalSet → braid x ∈ computationalSet)
    (h_disjoint : ∀ x : ConformalLift55.Cl55, x ∈ computationalSet → x ∈ leakageSet → False)
    (x : ConformalLift55.Cl55) (hx : x ∈ computationalSet) :
    ¬ braid x ∈ leakageSet :=
  InfoGeometry.Canonical.FibonacciFiveGradeBridge.braid_not_leakage_of_computational
    computationalSet leakageSet braid h_comp h_disjoint hx

/-- The supplied braid action preserves the `+2` source sector. -/
theorem braid_preserves_source (grade : ConformalLift55.Cl55 → ConformalGrade) (braid : ConformalLift55.Cl55 → ConformalLift55.Cl55)
    (h_grade : ∀ x : ConformalLift55.Cl55, grade (braid x) = grade x) (x : ConformalLift55.Cl55)
    (hx : grade x = ConformalGrade.posTwo) :
    grade (braid x) = ConformalGrade.posTwo :=
  InfoGeometry.Canonical.FibonacciFiveGradeBridge.braid_preserves_source grade braid h_grade hx

/-- The supplied braid action preserves the `-2` sink sector. -/
theorem braid_preserves_sink (grade : ConformalLift55.Cl55 → ConformalGrade) (braid : ConformalLift55.Cl55 → ConformalLift55.Cl55)
    (h_grade : ∀ x : ConformalLift55.Cl55, grade (braid x) = grade x) (x : ConformalLift55.Cl55)
    (hx : grade x = ConformalGrade.negTwo) :
    grade (braid x) = ConformalGrade.negTwo :=
  InfoGeometry.Canonical.FibonacciFiveGradeBridge.braid_preserves_sink grade braid h_grade hx

/-- The supplied braid action preserves the outgoing boundary sector. -/
theorem braid_preserves_outgoing (grade : ConformalLift55.Cl55 → ConformalGrade) (braid : ConformalLift55.Cl55 → ConformalLift55.Cl55)
    (h_grade : ∀ x : ConformalLift55.Cl55, grade (braid x) = grade x) (x : ConformalLift55.Cl55)
    (hx : grade x = ConformalGrade.posOne) :
    grade (braid x) = ConformalGrade.posOne :=
  InfoGeometry.Canonical.FibonacciFiveGradeBridge.braid_preserves_outgoing grade braid h_grade hx

/-- The supplied braid action preserves the incoming boundary sector. -/
theorem braid_preserves_incoming (grade : ConformalLift55.Cl55 → ConformalGrade) (braid : ConformalLift55.Cl55 → ConformalLift55.Cl55)
    (h_grade : ∀ x : ConformalLift55.Cl55, grade (braid x) = grade x) (x : ConformalLift55.Cl55)
    (hx : grade x = ConformalGrade.negOne) :
    grade (braid x) = ConformalGrade.negOne :=
  InfoGeometry.Canonical.FibonacciFiveGradeBridge.braid_preserves_incoming grade braid h_grade hx

/-- The supplied braid action preserves the modular center. -/
theorem braid_preserves_center (grade : ConformalLift55.Cl55 → ConformalGrade) (braid : ConformalLift55.Cl55 → ConformalLift55.Cl55)
    (h_grade : ∀ x : ConformalLift55.Cl55, grade (braid x) = grade x) (x : ConformalLift55.Cl55)
    (hx : grade x = ConformalGrade.zero) :
    grade (braid x) = ConformalGrade.zero :=
  InfoGeometry.Canonical.FibonacciFiveGradeBridge.braid_preserves_center grade braid h_grade hx

end InfoGeometry.Clifford.FibonacciCl55Carrier
