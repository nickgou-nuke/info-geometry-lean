import Mathlib

/-!
# Three-point non-isotropic configuration: Orlik--Solomon skeleton

For three points in `C^D`, remove the three pairwise quadratic cones
`q(x_i - x_j) = 0`.  This file formalizes the finite Orlik--Solomon skeleton
used by the de Rham/cooperad computation:

* three degree-one formal generators `A12`, `A23`, `A13`;
* one Arnold--Orlik--Solomon relation in quadratic degree;
* degree ranks `1, 3, 2` for the formal three-point model;
* the `12|3` cooperad cocomposition on generators.

-/

noncomputable section

namespace NonIsoConf3OrlikSolomon

/-- Even complex ambient dimension `D = 2k`, with `k > 0`. -/
structure EvenComplexDimension where
  D : ℕ
  k : ℕ
  positive : 0 < k
  even_dim : D = 2 * k

namespace EvenComplexDimension

/-- Formal cohomological degree assigned to the pairwise quadratic-cone class. -/
def generatorDegree (E : EvenComplexDimension) : ℕ := E.D - 1

/-- Formal quadratic degree of products of two generators. -/
def quadraticDegree (E : EvenComplexDimension) : ℕ := 2 * (E.D - 1)

end EvenComplexDimension

/-- Pair labels for three points. -/
inductive PairGen where
  | A12
  | A23
  | A13
  deriving DecidableEq, Repr, Inhabited

open PairGen

/-- Quadratic monomials in the three generators. -/
inductive PairProduct where
  | A12A23
  | A12A13
  | A23A13
  deriving DecidableEq, Repr, Inhabited

open PairProduct

abbrev Rank2Vector := Fin 2 → ℤ

def vadd (u v : Rank2Vector) : Rank2Vector := fun i => u i + v i
def vsub (u v : Rank2Vector) : Rank2Vector := fun i => u i - v i

/-- Normal form for degree-two products after quotienting by
`A12*A23 - A12*A13 + A23*A13 = 0`.

Basis:
* `0 ↦ A12*A23`
* `1 ↦ A12*A13`

The relation rewrites `A23*A13 = -A12*A23 + A12*A13`. -/
def reduceProduct : PairProduct → Rank2Vector
  | A12A23 => fun i => if i = 0 then 1 else 0
  | A12A13 => fun i => if i = 1 then 1 else 0
  | A23A13 => fun i => if i = 0 then -1 else 1

/-- The Arnold--Orlik--Solomon quadratic relation reduces to zero in the
two-dimensional normal form. -/
theorem arnold_orlik_solomon_relation :
    vadd (vsub (reduceProduct A12A23) (reduceProduct A12A13))
      (reduceProduct A23A13) = 0 := by
  funext i
  fin_cases i <;> simp [vadd, vsub, reduceProduct]

/-- Formal cohomology slots for the three-point non-isotropic model. -/
inductive CohomologySlot where
  | degree0
  | degreeGenerator
  | degreeQuadratic
  | other
  deriving DecidableEq, Repr, Inhabited

open CohomologySlot

/-- Formal Betti ranks after imposing the single Arnold--OS relation. -/
def slotRank : CohomologySlot → ℕ
  | degree0 => 1
  | degreeGenerator => 3
  | degreeQuadratic => 2
  | other => 0

theorem cohomology_rank_synthesis :
    slotRank degree0 = 1 ∧
    slotRank degreeGenerator = 3 ∧
    slotRank degreeQuadratic = 2 ∧
    slotRank other = 0 := by
  simp [slotRank]

/-- A minimal tensor target for the `12|3` cooperad cocomposition. -/
structure CooperadTensor where
  macroPart : Option PairGen
  micro : Option PairGen
  deriving Repr

-- Caveat: this Orlik--Solomon skeleton is a finite formal model for
-- generators and a quadratic relation pattern. It is not itself a proof that these
-- are the actual `dlog` classes of the quadratic-cone divisor complement; that
-- identification must come from the Dupont/Gysin/compactification side.
--
/-- Cocomposition for the cluster where points `1,2` collapse relative to `3`.

`micro` records the internal two-point class of the collapsing cluster.
`macroPart` records the class seen between the cluster and the outside point. -/
def delta12 : PairGen → CooperadTensor
  | A12 => { macroPart := none, micro := some A12 }
  | A13 => { macroPart := some A13, micro := none }
  | A23 => { macroPart := some A13, micro := none }

theorem delta12_internal : delta12 A12 = { macroPart := none, micro := some A12 } := rfl
theorem delta12_external_13 : delta12 A13 = { macroPart := some A13, micro := none } := rfl
theorem delta12_external_23 : delta12 A23 = { macroPart := some A13, micro := none } := rfl



/-- Capstone for the formal three-point OS/cooperad skeleton. -/
theorem non_iso_conf3_os_cooperad_synthesis :
    vadd (vsub (reduceProduct A12A23) (reduceProduct A12A13))
      (reduceProduct A23A13) = 0 ∧
    slotRank degree0 = 1 ∧
    slotRank degreeGenerator = 3 ∧
    slotRank degreeQuadratic = 2 ∧
    delta12 A12 = { macroPart := none, micro := some A12 } ∧
    delta12 A13 = { macroPart := some A13, micro := none } := by
  exact ⟨arnold_orlik_solomon_relation,
    rfl, rfl, rfl,
    delta12_internal,
    delta12_external_13⟩

end NonIsoConf3OrlikSolomon

end noncomputable section
