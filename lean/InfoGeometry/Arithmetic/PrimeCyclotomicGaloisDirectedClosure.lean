import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeCyclotomicGaloisEvidence
import InfoGeometry.Topology.ChiralDirectedGraphHomotopy

/-!
# Kernel replay of the prime cyclotomic Galois tower certificate

The companion Sage/GAP scripts emit six rows for primes `2,3,5,7,11,13`.
This owner does not trust those computations: primality, cumulative conductors,
divisibility, and Euler-totient degrees are independently recomputed in Lean.

The directed path is a fixed six-vertex certificate for the cumulative conductor
chain `2 -> 6 -> 30 -> 210 -> 2310 -> 30030`.  Calling this `O(1)` means that
for this fixed tower the kernel checks a constant number of symbolic/decidable
obligations; it is not a complexity claim about discovering arbitrary Galois
towers.
-/

namespace InfoGeometry.Arithmetic.PrimeCyclotomicGaloisDirectedClosure

open InfoGeometry.Arithmetic.PrimeCyclotomicGaloisEvidence
open InfoGeometry.Topology

/-- Native prime sequence underlying the external evidence. -/
def primeAt : Fin 6 → ℕ
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 11
  | 5 => 13

/-- Running squarefree conductor sequence. -/
def conductorAt : Fin 6 → ℕ
  | 0 => 2
  | 1 => 6
  | 2 => 30
  | 3 => 210
  | 4 => 2310
  | 5 => 30030

/-- Expected cyclotomic degrees `phi(conductorAt i)`. -/
def degreeAt : Fin 6 → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 8
  | 3 => 48
  | 4 => 480
  | 5 => 5760

/-- The external rows agree exactly with the independently specified native table. -/
theorem casRow_eq_native (i : Fin 6) :
    casRow i = ⟨primeAt i, conductorAt i, degreeAt i⟩ := by
  fin_cases i <;> rfl

/-- Every listed stage prime is genuinely prime. -/
theorem primeAt_isPrime (i : Fin 6) : Nat.Prime (primeAt i) := by
  fin_cases i <;> native_decide

/-- Lean recomputes every reported Euler-totient degree. -/
theorem totient_conductorAt (i : Fin 6) :
    Nat.totient (conductorAt i) = degreeAt i := by
  fin_cases i <;> native_decide

/-- Exact cumulative-prime recursion at the five nonterminal edges. -/
theorem conductor_step_01 : conductorAt 1 = conductorAt 0 * primeAt 1 := by norm_num [conductorAt, primeAt]
theorem conductor_step_12 : conductorAt 2 = conductorAt 1 * primeAt 2 := by norm_num [conductorAt, primeAt]
theorem conductor_step_23 : conductorAt 3 = conductorAt 2 * primeAt 3 := by norm_num [conductorAt, primeAt]
theorem conductor_step_34 : conductorAt 4 = conductorAt 3 * primeAt 4 := by norm_num [conductorAt, primeAt]
theorem conductor_step_45 : conductorAt 5 = conductorAt 4 * primeAt 5 := by norm_num [conductorAt, primeAt]

/-- Consecutive conductors form a genuine divisibility tower. -/
theorem conductor_dvd_01 : conductorAt 0 ∣ conductorAt 1 := by norm_num [conductorAt]
theorem conductor_dvd_12 : conductorAt 1 ∣ conductorAt 2 := by norm_num [conductorAt]
theorem conductor_dvd_23 : conductorAt 2 ∣ conductorAt 3 := by norm_num [conductorAt]
theorem conductor_dvd_34 : conductorAt 3 ∣ conductorAt 4 := by norm_num [conductorAt]
theorem conductor_dvd_45 : conductorAt 4 ∣ conductorAt 5 := by norm_num [conductorAt]

/-- Stage adjacency for the fixed directed tower. -/
def PrimeTowerEdge (i j : Fin 6) : Prop := i.1 + 1 = j.1

instance primeTowerEdgeDecidable (i j : Fin 6) : Decidable (PrimeTowerEdge i j) :=
  by
    dsimp [PrimeTowerEdge]
    infer_instance

/-- A finite directed graph whose unique forward chain is the prime tower. -/
def primeTowerGraph : ChiralDigraph where
  Vertex := Fin 6
  edge := PrimeTowerEdge
  edge_decidable := primeTowerEdgeDecidable
  sector := fun _ => ChiralSector.left
  allowedTransition := fun _ _ => True
  transition_decidable := fun _ _ => inferInstance
  edge_allowed := by
    intro u v huv
    trivial

private theorem edge01 : primeTowerGraph.edge (0 : Fin 6) (1 : Fin 6) := by
  change PrimeTowerEdge 0 1
  native_decide
private theorem edge12 : primeTowerGraph.edge (1 : Fin 6) (2 : Fin 6) := by
  change PrimeTowerEdge 1 2
  native_decide
private theorem edge23 : primeTowerGraph.edge (2 : Fin 6) (3 : Fin 6) := by
  change PrimeTowerEdge 2 3
  native_decide
private theorem edge34 : primeTowerGraph.edge (3 : Fin 6) (4 : Fin 6) := by
  change PrimeTowerEdge 3 4
  native_decide
private theorem edge45 : primeTowerGraph.edge (4 : Fin 6) (5 : Fin 6) := by
  change PrimeTowerEdge 4 5
  native_decide

/-- The fixed directed certificate from the first to the sixth prime stage. -/
def primeTowerPath : DirectedPath primeTowerGraph (0 : Fin 6) (5 : Fin 6) :=
  DirectedPath.cons edge01
    (DirectedPath.cons edge12
      (DirectedPath.cons edge23
        (DirectedPath.cons edge34
          (DirectedPath.cons edge45
            (DirectedPath.refl (G := primeTowerGraph) (5 : Fin 6))))))

@[simp] theorem primeTowerPath_length : primeTowerPath.length = 5 := by
  norm_num [primeTowerPath, DirectedPath.length]

/-- Every edge of the explicit directed certificate is a conductor divisibility step. -/
theorem primeTower_path_divisibility_certificate :
    conductorAt 0 ∣ conductorAt 1 ∧
    conductorAt 1 ∣ conductorAt 2 ∧
    conductorAt 2 ∣ conductorAt 3 ∧
    conductorAt 3 ∣ conductorAt 4 ∧
    conductorAt 4 ∣ conductorAt 5 := by
  exact ⟨conductor_dvd_01, conductor_dvd_12, conductor_dvd_23,
    conductor_dvd_34, conductor_dvd_45⟩

/-- Constant-size kernel replay of the complete six-row CAS certificate. -/
theorem cas_prime_tower_certificate_closed :
    (∀ i : Fin 6, Nat.Prime (casRow i).prime) ∧
    (∀ i : Fin 6, Nat.totient (casRow i).conductor = (casRow i).degree) ∧
    ((casRow 0).conductor ∣ (casRow 1).conductor) ∧
    ((casRow 1).conductor ∣ (casRow 2).conductor) ∧
    ((casRow 2).conductor ∣ (casRow 3).conductor) ∧
    ((casRow 3).conductor ∣ (casRow 4).conductor) ∧
    ((casRow 4).conductor ∣ (casRow 5).conductor) := by
  constructor
  · intro i
    rw [casRow_eq_native]
    exact primeAt_isPrime i
  constructor
  · intro i
    rw [casRow_eq_native]
    exact totient_conductorAt i
  simp only [casRow_0, casRow_1, casRow_2, casRow_3, casRow_4, casRow_5]
  norm_num

end InfoGeometry.Arithmetic.PrimeCyclotomicGaloisDirectedClosure
