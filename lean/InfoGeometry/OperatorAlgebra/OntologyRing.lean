/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Center
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.CladisticPhylogenesisBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.EpistemicCompilerPeirceBridge
import InfoGeometry.Canonical.OperatorErlangenFixedPoints
import InfoGeometry.Algebraic.OperatorSurgery

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.OperatorErlangenFixedPoints

/-!
# Ontology Ring: Multi-Level Operator Ontology, Taxonomic Subsumption, and Phylogenetic Cladistics

The carrier of the ontology is the non-commutative ring of operators `B`. Scalars are lifted to
operators via the canonical map `n : ℤ ↦ n • 1_B`. Geometric, taxonomic, phylogenetic, and
multi-level ontological structures are recovered directly over `B`:

- **Grassmannian & Clabject Dualism (`M₀ ↔ M₁`)**: An idempotent `P : B` (`P * P = P`) is a
  *clabject* (Atkinson & Kühne; Carvalho, Almeida, Fonseca & Guizzardi MLT): at level `M₁` it is an
  algebraic operator in `B` (an instance of the idempotent law `X² - X = 0`), while toward level `M₀`
  it acts as a taxonomic class whose extension is the fixed-point subspace
  `projectorSubspace P hP = {x : B | P * x = x}`.
- **Taxonomic Subsumption (`is-a`)**: Sub-clade absorption `cladeSubsumes Psub Panc`
  (`Psub * Panc = Psub ∧ Panc * Psub = Psub`) induces set-theoretic subspace inclusion
  `projectorSubspace Psub hSub ⊆ projectorSubspace Panc hAnc` and an orthogonal daughter split via
  `cladeComplement Psub Panc = Panc - Psub`.
- **Phylogenetic Cladistics (`MRCA` & Character Polarity)**: Sister clades `Pl, Pr` (`Pl * Pr = 0`,
  `Pr * Pl = 0`) share the algebraic Most Recent Common Ancestor `cladeJoin Pl Pr = Pl + Pr` while
  the phylogenetic bifurcation operator `cladeFork Pl Pr = Pl - Pr` acts with synapomorphic polarity
  `+1` on `projectorSubspace Pl hL` and `-1` on `projectorSubspace Pr hR`, with square equal to
  `cladeJoin Pl Pr`.
- **Supergrassmannian & Tangent Space**: `ℤ/2`-graded idempotents via `conePlus`/`coneMinus`
  corners; the Grassmannian tangent condition `P * T + T * P = T` is equivalent to `oddGrade P T = T`.
- **Center / Cartan Casimir Observables & Erlangen 2.0**: Central elements `centerB` are fixed
  under inverse conjugation (`u * v = 1 → u * z * v = z`), and ring automorphisms `σ : B ≃+* B`
  simultaneously transport taxonomic subsumption, phylogenetic forks, and Casimir centralizers.
-/

namespace InfoGeometry.OperatorAlgebra.OntologyRing

variable {B : Type*} [Ring B]

-- Part I: Scalar lift and projector subspace

/-- Projector subspace: for an idempotent `P : B` (`P * P = P`), the set
    `{x | P * x = x}` is the subspace selected by the projector `P`.
    A Grassmannian point is precisely such an idempotent projector. -/
def projectorSubspace (P : B) : Set B := {x : B | P * x = x}

theorem projectorSubspace_zero (P : B) : (0 : B) ∈ projectorSubspace P := by
  simp [projectorSubspace]

theorem projectorSubspace_add (P : B) {x y : B}
    (hx : x ∈ projectorSubspace P) (hy : y ∈ projectorSubspace P) :
    x + y ∈ projectorSubspace P := by
  have h₁ : P * x = x := hx
  have h₂ : P * y = y := hy
  change P * (x + y) = x + y
  calc
    P * (x + y) = P * x + P * y := by rw [mul_add]
    _ = x + y := by rw [h₁, h₂]

/-- The fixed-point set of `P` equals the image of left-multiplication by `P`:
    `{x | P * x = x} = {P * y | y : B}`. -/
theorem projectorSubspace_eq_image (P : B) (hP : P * P = P) :
    projectorSubspace P = {x : B | ∃ y : B, x = P * y} := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    have h₁ : P * x = x := hx
    refine ⟨x, ?_⟩
    exact h₁.symm
  · rintro ⟨y, rfl⟩
    change P * (P * y) = P * y
    calc
      P * (P * y) = (P * P) * y := by rw [← mul_assoc]
      _ = P * y := by rw [hP]

/-- **Drazin core/null decomposition as a pair of ontology fixed-point classes.**
For an operator with a Drazin inverse, every element of the same noncommutative
ring has a unique decomposition into a state fixed by the core projector and a
state fixed by the complementary null projector. This connects the Drazin
Fitting split to the ontology's projector-subspace taxonomy. -/
theorem drazin_core_null_unique_projector_decomposition
    {A : B} (S : InfoGeometry.Algebraic.DrazinSurgery A) (x : B) :
    ∃! parts : B × B,
      parts.1 ∈ projectorSubspace S.coreProjector ∧
      parts.2 ∈ projectorSubspace S.nullProjector ∧
      parts.1 + parts.2 = x := by
  let p : B := S.coreProjector
  let q : B := S.nullProjector
  have hp : p * p = p := S.core_idempotent
  have hq : q * q = q := S.null_idempotent
  have hpq : p * q = 0 := S.core_null_orthogonal
  have hqp : q * p = 0 := by
    dsimp [q, InfoGeometry.Algebraic.DrazinSurgery.nullProjector]
    rw [sub_mul, one_mul, S.core_idempotent, sub_self]
  refine ⟨(p * x, q * x), ?_, ?_⟩
  · constructor
    · change p * (p * x) = p * x
      rw [← mul_assoc, hp]
    · constructor
      · change q * (q * x) = q * x
        rw [← mul_assoc, hq]
      · calc
          p * x + q * x = (p + q) * x := by rw [← add_mul]
          _ = 1 * x := by rw [S.partition_of_unity]
          _ = x := one_mul x
  · intro parts hparts
    rcases hparts with ⟨hcore, hnull, hsum⟩
    apply Prod.ext
    · have hcross : p * parts.2 = 0 := by
        calc
          p * parts.2 = p * (q * parts.2) := by rw [hnull]
          _ = (p * q) * parts.2 := by rw [← mul_assoc]
          _ = 0 := by rw [hpq, zero_mul]
      calc
        parts.1 = p * parts.1 := hcore.symm
        _ = p * parts.1 + p * parts.2 := by rw [hcross, add_zero]
        _ = p * (parts.1 + parts.2) := by rw [mul_add]
        _ = p * x := by rw [hsum]
    · have hcross : q * parts.1 = 0 := by
        calc
          q * parts.1 = q * (p * parts.1) := by rw [hcore]
          _ = (q * p) * parts.1 := by rw [← mul_assoc]
          _ = 0 := by rw [hqp, zero_mul]
      calc
        parts.2 = q * parts.2 := hnull.symm
        _ = q * parts.1 + q * parts.2 := by rw [hcross, zero_add]
        _ = q * (parts.1 + parts.2) := by rw [mul_add]
        _ = q * x := by rw [hsum]

-- Part II: Supergrassmannian (ℤ/2-graded idempotents) & Grassmannian Tangent Space

/-- `conePlus` is nilpotent of order 2: `conePlus P A * conePlus P A' = 0`. -/
theorem conePlusNilpotent (P : B) (hP : P * P = P) (A A' : B) :
    conePlus P A * conePlus P A' = 0 := by
  rw [← P_mul_conePlus hP A', ← mul_assoc, conePlus_mul_P hP, zero_mul]

/-- `coneMinus` is nilpotent of order 2: `coneMinus P C * coneMinus P C' = 0`. -/
theorem coneMinusNilpotent (P : B) (hP : P * P = P) (C C' : B) :
    coneMinus P C * coneMinus P C' = 0 := by
  rw [← coneMinus_mul_P hP C, mul_assoc, P_mul_coneMinus hP, mul_zero]

/-- `conePlus` is linear in its argument. -/
theorem conePlusLinear (P A A' : B) :
    conePlus P (A + A') = conePlus P A + conePlus P A' := by
  dsimp [conePlus]
  noncomm_ring

/-- `coneMinus` is linear in its argument. -/
theorem coneMinusLinear (P C C' : B) :
    coneMinus P (C + C') = coneMinus P C + coneMinus P C' := by
  dsimp [coneMinus]
  noncomm_ring

/-- **Grassmannian Tangent Space Additivity**:
If `T₁` and `T₂` satisfy the Jordan Grassmannian tangent equation `P * T + T * P = T`,
then so does their sum `T₁ + T₂`. -/
theorem grassmannian_tangent_add (P T₁ T₂ : B)
    (h₁ : P * T₁ + T₁ * P = T₁) (h₂ : P * T₂ + T₂ * P = T₂) :
    P * (T₁ + T₂) + (T₁ + T₂) * P = T₁ + T₂ := by
  calc
    P * (T₁ + T₂) + (T₁ + T₂) * P = (P * T₁ + T₁ * P) + (P * T₂ + T₂ * P) := by noncomm_ring
    _ = T₁ + T₂ := by rw [h₁, h₂]

/-- **Grassmannian Tangent Space = Odd Peirce Grade**:
For any idempotent `P` (`P * P = P`), an operator `T` satisfies the Grassmannian tangent
condition `P * T + T * P = T` if and only if `T` is purely odd-graded (`oddGrade P T = T`,
equivalently `evenGrade P T = 0`). -/
theorem grassmannian_tangent_iff_oddGrade_fixed {P : B} (hP : P * P = P) (T : B) :
    (P * T + T * P = T) ↔ oddGrade P T = T := by
  constructor
  · intro hT
    have hPT : P * (P * T + T * P) * P = P * T * P := by rw [hT]
    have h2PTP : P * T * P + P * T * P = P * T * P := by
      calc
        P * T * P + P * T * P = (P * P) * T * P + P * T * (P * P) := by rw [hP]
        _ = P * (P * T + T * P) * P := by noncomm_ring
        _ = P * T * P := hPT
    have hPTP : P * T * P = 0 := by
      calc
        P * T * P = (P * T * P + P * T * P) - P * T * P := by abel
        _ = P * T * P - P * T * P := by rw [h2PTP]
        _ = 0 := sub_self (P * T * P)
    calc
      oddGrade P T = P * T * (1 - P) + (1 - P) * T * P := rfl
      _ = (P * T + T * P) - (P * T * P + P * T * P) := by noncomm_ring
      _ = T := by rw [hT, hPTP]; simp
  · intro hOdd
    rw [← hOdd]
    peirce_nf hP

-- Part III: Center / Cartan subalgebra & Conjugation Invariance

/-- The center of the ontology ring `B`: elements that commute with everything.
    These act as Casimir observables on operator modules. -/
def centerB : Set B := {z : B | ∀ (b : B), z * b = b * z}

theorem centerB_one : (1 : B) ∈ centerB := by
  intro b
  simp

theorem centerB_zero : (0 : B) ∈ centerB := by
  intro b
  simp

theorem centerB_add {z w : B} (hz : z ∈ centerB) (hw : w ∈ centerB) :
    z + w ∈ centerB := by
  intro b
  have h₁ : z * b = b * z := hz b
  have h₂ : w * b = b * w := hw b
  calc
    (z + w) * b = z * b + w * b := by rw [add_mul]
    _ = b * z + b * w := by rw [h₁, h₂]
    _ = b * (z + w) := by rw [mul_add]

theorem centerB_mul {z w : B} (hz : z ∈ centerB) (hw : w ∈ centerB) :
    z * w ∈ centerB := by
  intro b
  have h₁ : z * b = b * z := hz b
  have h₂ : w * b = b * w := hw b
  calc
    (z * w) * b = z * (w * b) := by rw [mul_assoc]
    _ = z * (b * w) := by rw [h₂]
    _ = (z * b) * w := by rw [← mul_assoc]
    _ = (b * z) * w := by rw [h₁]
    _ = b * (z * w) := by rw [mul_assoc]

/-- **Casimir Center Conjugation Invariance**:
Every central operator `z ∈ centerB` is fixed under conjugation `u * z * v = z` whenever
`u * v = 1`. -/
theorem central_fixed_under_conjugation {z u v : B} (hz : z ∈ centerB) (huv : u * v = 1) :
    u * z * v = z := by
  have hzu : z * u = u * z := hz u
  calc
    u * z * v = (z * u) * v := by rw [hzu]
    _ = z * (u * v) := by rw [mul_assoc]
    _ = z * 1 := by rw [huv]
    _ = z := mul_one z

-- Part IV: Taxonomic Subsumption (`is-a`) vs. Phylogenetic Cladistics (`MRCA` & `cladeFork`)

/-- **Taxonomic Subsumption implies Fixed-Point Subspace Inclusion (`is-a`)**:
If `Psub` is taxonomically subsumed by `Panc` (`cladeSubsumes Psub Panc`), then every individual
state in `projectorSubspace Psub` belongs to `projectorSubspace Panc`. -/
theorem cladeSubsumes_projectorSubspace_subset {Psub Panc : B}
    (hClade : cladeSubsumes Psub Panc) :
    projectorSubspace Psub ⊆ projectorSubspace Panc := by
  intro x hx
  have hx' : Psub * x = x := hx
  change Panc * x = x
  calc
    Panc * x = Panc * (Psub * x) := by rw [hx']
    _ = (Panc * Psub) * x := by rw [← mul_assoc]
    _ = Psub * x := by rw [hClade.2]
    _ = x := hx'

/-- **Taxonomic Daughter Complement Disjointness**:
The sub-clade `projectorSubspace Psub` and its taxonomic sister complement
`projectorSubspace (cladeComplement Psub Panc)` intersect only at `0`. -/
theorem cladeComplement_projectorSubspace_disjoint {Psub Panc : B}
    (hSub : Psub * Psub = Psub) (hAnc : Panc * Panc = Panc)
    (hClade : cladeSubsumes Psub Panc) {x : B}
    (hxSub : x ∈ projectorSubspace Psub)
    (hxComp : x ∈ projectorSubspace (cladeComplement Psub Panc)) :
    x = 0 := by
  have hxSub' : Psub * x = x := hxSub
  have hxComp' : cladeComplement Psub Panc * x = x := hxComp
  have hOrth : cladeComplement Psub Panc * Psub = 0 :=
    (cladeComplement_peirce_split hSub hAnc hClade).2.2.1
  calc
    x = cladeComplement Psub Panc * x := hxComp'.symm
    _ = cladeComplement Psub Panc * (Psub * x) := by rw [hxSub']
    _ = (cladeComplement Psub Panc * Psub) * x := by rw [← mul_assoc]
    _ = 0 * x := by rw [hOrth]
    _ = 0 := zero_mul x

/-- **Phylogenetic Cladistics Bridge (MRCA Subsumption & Synapomorphic Polarity)**:
For orthogonal sister clades `Pl, Pr` (`Pl² = Pl`, `Pr² = Pr`, `Pl * Pr = 0`, `Pr * Pl = 0`):
1. Both `Pl` and `Pr` are taxonomically subsumed by their algebraic Most Recent Common Ancestor
   `cladeJoin Pl Pr = Pl + Pr` (`cladeSubsumes Pl (cladeJoin Pl Pr)` and
   `cladeSubsumes Pr (cladeJoin Pl Pr)`), so both subspaces lie inside `projectorSubspace (cladeJoin Pl Pr)`,
2. The phylogenetic bifurcation operator `cladeFork Pl Pr = Pl - Pr` acts with synapomorphic
   character polarity `+1` on `projectorSubspace Pl` and `-1` on `projectorSubspace Pr`,
3. Applying the bifurcation operator twice on any state `z : B` projects onto the MRCA subspace
   (`cladeFork Pl Pr * (cladeFork Pl Pr * z) = cladeJoin Pl Pr * z`). -/
theorem cladeFork_character_polarity_and_mrca_inclusion {Pl Pr : B}
    (hL : Pl * Pl = Pl) (hR : Pr * Pr = Pr)
    (hLR : Pl * Pr = 0) (hRL : Pr * Pl = 0) :
    cladeSubsumes Pl (cladeJoin Pl Pr) ∧
    cladeSubsumes Pr (cladeJoin Pl Pr) ∧
    projectorSubspace Pl ⊆ projectorSubspace (cladeJoin Pl Pr) ∧
    projectorSubspace Pr ⊆ projectorSubspace (cladeJoin Pl Pr) ∧
    (∀ x ∈ projectorSubspace Pl, cladeFork Pl Pr * x = x) ∧
    (∀ y ∈ projectorSubspace Pr, cladeFork Pl Pr * y = -y) ∧
    (∀ z : B, cladeFork Pl Pr * (cladeFork Pl Pr * z) = cladeJoin Pl Pr * z) := by
  have hMrca := cladeFork_mrca hL hR hLR hRL
  have hSubL : cladeSubsumes Pl (cladeJoin Pl Pr) := hMrca.2.2.2.1
  have hSubR : cladeSubsumes Pr (cladeJoin Pl Pr) := hMrca.2.2.2.2
  refine ⟨hSubL, hSubR,
    cladeSubsumes_projectorSubspace_subset hSubL,
    cladeSubsumes_projectorSubspace_subset hSubR,
    ?_, ?_, ?_⟩
  · intro x hx
    have hx' : Pl * x = x := hx
    have hPrx : Pr * x = 0 := by
      calc
        Pr * x = Pr * (Pl * x) := by rw [hx']
        _ = (Pr * Pl) * x := by rw [← mul_assoc]
        _ = 0 := by rw [hRL, zero_mul]
    calc
      cladeFork Pl Pr * x = Pl * x - Pr * x := by dsimp [cladeFork]; rw [sub_mul]
      _ = x := by rw [hx', hPrx, sub_zero]
  · intro y hy
    have hy' : Pr * y = y := hy
    have hPly : Pl * y = 0 := by
      calc
        Pl * y = Pl * (Pr * y) := by rw [hy']
        _ = (Pl * Pr) * y := by rw [← mul_assoc]
        _ = 0 := by rw [hLR, zero_mul]
    calc
      cladeFork Pl Pr * y = Pl * y - Pr * y := by dsimp [cladeFork]; rw [sub_mul]
      _ = -y := by rw [hPly, hy', zero_sub]
  · intro z
    calc
      cladeFork Pl Pr * (cladeFork Pl Pr * z) = (cladeFork Pl Pr * cladeFork Pl Pr) * z := by
        rw [← mul_assoc]
      _ = cladeJoin Pl Pr * z := by rw [hMrca.1]

-- Part V: Multi-Level Ontology Stratification (MLT / Clabjects / Powertypes) & Erlangen Transport

/-- **Four-Level Multi-Level Ontology Stratification (`MLT` / Atkinson–Kühne–Guizzardi)**:
- `M0_StateIndividual`: Module / state vectors `x ∈ projectorSubspace P hP` (individuals),
- `M1_ProjectorClabject`: Idempotent operator `P ∈ B` (`P² = P`), simultaneously an instance of
  the idempotent variety and the classifier of `projectorSubspace P hP` (*clabject*),
- `M2_GrassmannianPowertypeOrbit`: Powertype / Grassmannian orbit `{g • P}` of projectors
  classified by rank/trace and connected by phylogenetic mutations `phyloLineage n P A`,
- `M3_ErlangenCasimirMetaLaw`: Higher-order Erlangen polynomial laws `p ∈ Polynomial ℤ` and
  Casimir centralizer invariants governing all powertype orbits. -/
inductive OntologyMetaLevel : Type
  | M0_StateIndividual
  | M1_ProjectorClabject
  | M2_GrassmannianPowertypeOrbit
  | M3_ErlangenCasimirMetaLaw
  deriving DecidableEq, Repr

namespace OntologyMetaLevel

/-- Numerical stratum index of each ontological level (`0 < 1 < 2 < 3`). -/
def rank : OntologyMetaLevel → ℕ
  | .M0_StateIndividual => 0
  | .M1_ProjectorClabject => 1
  | .M2_GrassmannianPowertypeOrbit => 2
  | .M3_ErlangenCasimirMetaLaw => 3

/-- Direct ontological `instantiates` edge between adjacent MLT strata (no level-skipping wormholes). -/
def instantiatesEdge : OntologyMetaLevel → OntologyMetaLevel → Prop
  | .M0_StateIndividual, .M1_ProjectorClabject => True
  | .M1_ProjectorClabject, .M2_GrassmannianPowertypeOrbit => True
  | .M2_GrassmannianPowertypeOrbit, .M3_ErlangenCasimirMetaLaw => True
  | _, _ => False

theorem instantiatesEdge_rank_succ {u v : OntologyMetaLevel} (h : instantiatesEdge u v) :
    u.rank + 1 = v.rank := by
  cases u <;> cases v <;> simp [instantiatesEdge, rank] at h ⊢

theorem instantiatesEdge_lt_rank {u v : OntologyMetaLevel} (h : instantiatesEdge u v) :
    u.rank < v.rank := by
  have h1 := instantiatesEdge_rank_succ h
  omega

theorem transGen_instantiatesEdge_lt_rank {u v : OntologyMetaLevel}
    (h : Relation.TransGen instantiatesEdge u v) :
    u.rank < v.rank := by
  induction h with
  | single h1 => exact instantiatesEdge_lt_rank h1
  | tail _ h2 ih =>
      have h3 := instantiatesEdge_lt_rank h2
      exact Nat.lt_trans ih h3

/-- **MLT Non-Self-Instantiation & Acyclicity Theorem**:
No ontological stratum can instantiate itself in one or more steps
(`¬ Relation.TransGen instantiatesEdge L L`), and every adjacent `instantiatesEdge` increases
stratum rank by `1` (ruling out level-skipping wormholes). -/
theorem instantiatesEdge_acyclic (L : OntologyMetaLevel) :
    ¬ Relation.TransGen instantiatesEdge L L := by
  intro h
  exact Nat.lt_irrefl L.rank (transGen_instantiatesEdge_lt_rank h)

end OntologyMetaLevel

/-- **Erlangen 2.0 Automorphism Transport of Taxonomy, Phylogenesis, and Casimir Center**:
Any ring automorphism `σ : B ≃+* B` preserves:
1. Taxonomic subsumption (`cladeSubsumes Psub Panc ↔ cladeSubsumes (σ Psub) (σ Panc)`),
2. Phylogenetic bifurcation and MRCA join (`σ (cladeFork Pl Pr) = cladeFork (σ Pl) (σ Pr)` and
   `σ (cladeJoin Pl Pr) = cladeJoin (σ Pl) (σ Pr)`),
3. The Casimir center (`z ∈ centerB ↔ σ z ∈ centerB`). -/
theorem erlangen_ringEquiv_preserves_taxonomy_phylogenesis_and_center
    (σ : B ≃+* B) (Psub Panc Pl Pr z : B) :
    (cladeSubsumes Psub Panc ↔ cladeSubsumes (σ Psub) (σ Panc)) ∧
    σ (cladeFork Pl Pr) = cladeFork (σ Pl) (σ Pr) ∧
    σ (cladeJoin Pl Pr) = cladeJoin (σ Pl) (σ Pr) ∧
    (z ∈ centerB ↔ σ z ∈ centerB) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [← map_mul, h1], by rw [← map_mul, h2]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨σ.injective (by rw [map_mul, h1]), σ.injective (by rw [map_mul, h2])⟩
  · simp [cladeFork, map_sub]
  · simp [cladeJoin, map_add]
  · constructor
    · intro hz b
      have hzb := hz (σ.symm b)
      have h1 := congrArg σ hzb
      simpa [map_mul] using h1
    · intro hσz b
      have hzb := hσz (σ b)
      rw [← map_mul, ← map_mul] at hzb
      exact σ.injective hzb

/-- **Master Unification Theorem of the Ontology Ring (`Ontology + Taxonomy + Phylogenesis + MLT + Erlangen 2.0`)**:
Unifies in one kernel-verified statement over `[Ring B]`:
1. **Multi-Level Ontology (`OntologyMetaLevel`)**: Strict 4-stratum chain `M0 → M1 → M2 → M3`
   with `instantiatesEdge_acyclic`,
2. **Taxonomic Subsumption (`is-a`)**: `cladeSubsumes Psub Panc` induces fixed-point subspace
   inclusion `projectorSubspace Psub hSub ⊆ projectorSubspace Panc hAnc`,
3. **Phylogenetic Cladistics (`cladeFork` & `cladeJoin`)**: Sister clades lie in the algebraic MRCA
   subspace `projectorSubspace (cladeJoin Pl Pr)` and are separated by `+1 / -1` polarity of
   `cladeFork Pl Pr`,
4. **Grassmannian Tangent Space & Casimir Center**: `P * T + T * P = T ↔ oddGrade P T = T` and
   `u * v = 1 → z ∈ centerB → u * z * v = z`,
5. **Erlangen 2.0 Automorphism Transport**: Ring automorphisms `σ : B ≃+* B` preserve taxonomic
   subsumption, phylogenetic forks/joins, and the Casimir center. -/
theorem ontology_taxonomy_phylogenesis_multilevel_master_synthesis
    (σ : B ≃+* B)
    {P Psub Panc Pl Pr : B}
    (hP : P * P = P)
    (hClade : cladeSubsumes Psub Panc)
    (hL : Pl * Pl = Pl) (hR : Pr * Pr = Pr)
    (hLR : Pl * Pr = 0) (hRL : Pr * Pl = 0)
    (T : B) {z u v : B} (hz : z ∈ centerB) (huv : u * v = 1) :
    ((∀ L : OntologyMetaLevel, ¬ Relation.TransGen OntologyMetaLevel.instantiatesEdge L L) ∧
     OntologyMetaLevel.instantiatesEdge .M0_StateIndividual .M1_ProjectorClabject ∧
     OntologyMetaLevel.instantiatesEdge .M1_ProjectorClabject .M2_GrassmannianPowertypeOrbit ∧
     OntologyMetaLevel.instantiatesEdge .M2_GrassmannianPowertypeOrbit .M3_ErlangenCasimirMetaLaw) ∧
    (projectorSubspace Psub ⊆ projectorSubspace Panc) ∧
    (projectorSubspace Pl ⊆ projectorSubspace (cladeJoin Pl Pr) ∧
     projectorSubspace Pr ⊆ projectorSubspace (cladeJoin Pl Pr) ∧
     (∀ x ∈ projectorSubspace Pl, cladeFork Pl Pr * x = x) ∧
     (∀ y ∈ projectorSubspace Pr, cladeFork Pl Pr * y = -y)) ∧
    (((P * T + T * P = T) ↔ oddGrade P T = T) ∧
     u * z * v = z) ∧
    ((cladeSubsumes Psub Panc ↔ cladeSubsumes (σ Psub) (σ Panc)) ∧
     σ (cladeFork Pl Pr) = cladeFork (σ Pl) (σ Pr) ∧
     σ (cladeJoin Pl Pr) = cladeJoin (σ Pl) (σ Pr) ∧
     (z ∈ centerB ↔ σ z ∈ centerB)) := by
  have hPhylo := cladeFork_character_polarity_and_mrca_inclusion hL hR hLR hRL
  exact ⟨⟨OntologyMetaLevel.instantiatesEdge_acyclic, trivial, trivial, trivial⟩,
         cladeSubsumes_projectorSubspace_subset hClade,
         ⟨hPhylo.2.2.1, hPhylo.2.2.2.1, hPhylo.2.2.2.2.1, hPhylo.2.2.2.2.2.1⟩,
         ⟨grassmannian_tangent_iff_oddGrade_fixed hP T,
          central_fixed_under_conjugation hz huv⟩,
         erlangen_ringEquiv_preserves_taxonomy_phylogenesis_and_center σ Psub Panc Pl Pr z⟩

end InfoGeometry.OperatorAlgebra.OntologyRing
