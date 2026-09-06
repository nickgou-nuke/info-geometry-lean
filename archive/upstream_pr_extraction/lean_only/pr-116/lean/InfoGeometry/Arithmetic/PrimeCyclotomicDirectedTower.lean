import Mathlib

/-!
# Prime cyclotomic directed tower: native Lean readback of the CAS prime payload

The repository contains external exploratory calculations using the ordered prime list
`2, 3, 5, 7, 11, 13, ...`, notably in:

* `proofs/idele_scaling_group.gap`;
* `proofs/clifford_prime_base.py`;
* `proofs/clifford_colimit.py`.

Those files are evidence/data sources only.  No GAP, Sage, Python, or NumPy assertion is
used as a theorem here.  The first six prime values are imported as data and rechecked by
Lean.  Their cumulative conductors

`1, 2, 6, 30, 210, 2310, 30030`

form a finite directed divisibility spine.  At each conductor we use Mathlib's native
cyclotomic field and native theorem that a cyclotomic extension is Galois (indeed abelian
Galois).

The directed-path layer is intentionally thin: a path from `i` to `j` is just `i ≤ j`.
Hence any two parallel directed paths are propositionally equal, and the endpoint
transport theorem has proof complexity independent of the number of intermediate stages.

This file does **not** identify separately constructed `CyclotomicField` values by a
canonical inclusion map.  It proves the arithmetic directed spine and stagewise Galois
statements needed before that stronger tower-of-embeddings theorem is introduced.
-/

namespace InfoGeometry.Arithmetic.PrimeCyclotomicDirectedTower

/-- The first six prime components appearing in the external CAS experiments. -/
def casPrime (i : Fin 6) : ℕ :=
  ![2, 3, 5, 7, 11, 13] i

/-- Exact readback of the imported six-prime payload. -/
theorem casPrime_values :
    List.ofFn casPrime = [2, 3, 5, 7, 11, 13] := by
  native_decide

/-- Every imported CAS prime is re-certified by Lean. -/
theorem casPrime_prime (i : Fin 6) : Nat.Prime (casPrime i) := by
  fin_cases i <;> native_decide

/-- Cumulative conductors for adjoining the six prime orders successively. -/
def conductor (i : Fin 7) : ℕ :=
  ![1, 2, 6, 30, 210, 2310, 30030] i

/-- Exact readback of all seven conductor stages. -/
theorem conductor_values :
    List.ofFn conductor = [1, 2, 6, 30, 210, 2310, 30030] := by
  native_decide

/-- Every conductor in the finite tower is nonzero. -/
theorem conductor_ne_zero (i : Fin 7) : conductor i ≠ 0 := by
  fin_cases i <;> native_decide

/-- One directed step multiplies the conductor by the corresponding imported prime. -/
theorem conductor_step (i : Fin 6) :
    conductor i.castSucc * casPrime i = conductor i.succ := by
  fin_cases i <;> native_decide

/-- Consequently each conductor divides the next conductor. -/
theorem conductor_step_dvd (i : Fin 6) :
    conductor i.castSucc ∣ conductor i.succ := by
  refine ⟨casPrime i, ?_⟩
  exact (conductor_step i).symm

/-- A directed path in the finite prime tower.  The index category is a thin poset. -/
def DirectedPath (i j : Fin 7) : Prop := i ≤ j

/-- Constant directed path. -/
theorem DirectedPath.refl (i : Fin 7) : DirectedPath i i := le_rfl

/-- Composition of directed paths. -/
theorem DirectedPath.comp {i j k : Fin 7}
    (p : DirectedPath i j) (q : DirectedPath j k) : DirectedPath i k :=
  le_trans p q

/-- Thinness / directed-homotopy principle: parallel paths carry no extra data. -/
theorem directedPath_homotopy {i j : Fin 7}
    (p q : DirectedPath i j) : p = q := by
  exact Subsingleton.elim p q

/-- Endpoint transport on conductors.  The proof consumes only the endpoints/path witness,
not a list of intermediate edges. -/
theorem conductor_dvd_of_directedPath {i j : Fin 7}
    (p : DirectedPath i j) : conductor i ∣ conductor j := by
  fin_cases i <;> fin_cases j <;>
    simp_all [DirectedPath, conductor]

/-- Composition coherence for endpoint transport.  By proof irrelevance, direct transport
and transport through an intermediate stage are the same proof. -/
theorem conductor_transport_comp {i j k : Fin 7}
    (p : DirectedPath i j) (q : DirectedPath j k) :
    conductor_dvd_of_directedPath (DirectedPath.comp p q) =
      dvd_trans (conductor_dvd_of_directedPath p) (conductor_dvd_of_directedPath q) := by
  apply Subsingleton.elim

/-- The terminal conductor is the product of the imported six-prime payload. -/
theorem terminal_conductor_product :
    conductor 6 = ∏ i : Fin 6, casPrime i := by
  native_decide

/-- Numerical terminal readback. -/
theorem terminal_conductor_eq : conductor 6 = 30030 := by
  native_decide

/-- Every imported prime divides the terminal conductor. -/
theorem casPrime_dvd_terminal (i : Fin 6) : casPrime i ∣ conductor 6 := by
  fin_cases i <;> native_decide

/-- The cyclotomic field attached to a stage of the directed conductor spine. -/
abbrev StageField (i : Fin 7) := CyclotomicField (conductor i) ℚ

/-- Every stage is natively Galois over `ℚ`; no CAS theorem enters this proof. -/
noncomputable instance stage_isGalois (i : Fin 7) : IsGalois ℚ (StageField i) :=
  IsCyclotomicExtension.isGalois {conductor i} ℚ (StageField i)

/-- In fact every stage is an abelian Galois extension. -/
theorem stage_isAbelianGalois (i : Fin 7) : IsAbelianGalois ℚ (StageField i) :=
  IsCyclotomicExtension.isAbelianGalois {conductor i} ℚ (StageField i)

/-- O(1)-style endpoint theorem for the full directed arithmetic spine. -/
theorem initial_dvd_terminal : conductor 0 ∣ conductor 6 := by
  norm_num [conductor]

/-- O(1)-style endpoint theorem for the terminal Galois stage. -/
theorem terminal_isGalois : IsGalois ℚ (StageField 6) := by
  infer_instance

/-- The terminal stage is abelian Galois as well. -/
theorem terminal_isAbelianGalois : IsAbelianGalois ℚ (StageField 6) :=
  stage_isAbelianGalois 6

end InfoGeometry.Arithmetic.PrimeCyclotomicDirectedTower
