import proofs.DupontHypersurfaceOSModel
import proofs.PenroseSpinIncidenceTessellation

/-!
# Dupont/Gysin skeleton for three non-isotropic quadric divisors

After translation, the arity-three non-isotropic configuration space is the
complement of three affine quadric divisors in `C^D × C^D`:

* `QA = q(a)`;
* `QB = q(b)`;
* `QAB = q(a-b)`.

This file formalizes the finite stratum-poset and cooperad bookkeeping for the
arity-three divisor arrangement.  It deliberately stops at finite masks, cover
arrows, toy generators, and degree-shift bookkeeping; the analytic comparison
with de Rham cohomology is not packaged here.
-/

noncomputable section

namespace NonIsoConf3DupontGysinModel

open DupontHypersurfaceOSModel
open PenroseSpinTilingConfig
open PenroseSpinIncidenceTessellation

/-- The three affine quadric divisors after translation. -/
inductive QuadricDivisor where
  | QA
  | QB
  | QAB
  deriving DecidableEq, Fintype, Repr

open QuadricDivisor

/-- A stratum is encoded by the set of divisors on which the point lies. -/
structure StratumMask where
  onQA : Bool
  onQB : Bool
  onQAB : Bool
  deriving DecidableEq, Fintype, Repr

/-- The open stratum. -/
def openMask : StratumMask := ⟨false, false, false⟩

/-- The deepest triple intersection. -/
def tripleMask : StratumMask := ⟨true, true, true⟩

/-- Boolean membership in a divisor. -/
def StratumMask.contains : StratumMask → QuadricDivisor → Bool
  | S, QA => S.onQA
  | S, QB => S.onQB
  | S, QAB => S.onQAB

/-- Insert one divisor into a stratum mask. -/
def StratumMask.insert : StratumMask → QuadricDivisor → StratumMask
  | S, QA => { S with onQA := true }
  | S, QB => { S with onQB := true }
  | S, QAB => { S with onQAB := true }

/-- Expected generic codimension in the resolved normal-crossing model. -/
def StratumMask.codim (S : StratumMask) : ℕ :=
  (if S.onQA then 1 else 0) +
  (if S.onQB then 1 else 0) +
  (if S.onQAB then 1 else 0)

@[simp] theorem openMask_codim : openMask.codim = 0 := rfl
@[simp] theorem tripleMask_codim : tripleMask.codim = 3 := rfl

/-- There are eight Boolean strata for three divisors. -/
theorem stratumMask_card : Fintype.card StratumMask = 8 := by
  let e : StratumMask ≃ Bool × Bool × Bool :=
    { toFun := fun S => (S.onQA, S.onQB, S.onQAB)
      invFun := fun b => ⟨b.1, b.2.1, b.2.2⟩
      left_inv := by
        intro S
        cases S
        rfl
      right_inv := by
        intro b
        cases b with
        | mk a bc =>
          cases bc
          rfl }
  rw [Fintype.card_congr e]
  norm_num [Fintype.card_prod]

/-- A Gysin cover adds exactly one inactive divisor. -/
structure GysinCover where
  source : StratumMask
  divisor : QuadricDivisor
  inactive : source.contains divisor = false

deriving instance Fintype for GysinCover

/-- Target of a cover arrow. -/
def GysinCover.target (e : GysinCover) : StratumMask :=
  e.source.insert e.divisor

/-- There are twelve Hasse cover arrows in the Boolean three-divisor poset. -/
theorem gysinCover_card : Fintype.card GysinCover = 12 := by
  decide

/-- The representative cover from the open stratum to `QA`. -/
def coverOpenQA : GysinCover where
  source := openMask
  divisor := QA
  inactive := rfl

@[simp] theorem coverOpenQA_target :
    coverOpenQA.target = ⟨true, false, false⟩ := rfl

/-- Universe of three quadratic divisors in deterministic order. -/
def divisorUniverse : Finset QuadricDivisor := ({QA, QB, QAB} : Finset QuadricDivisor)

/-- Divisors active on a stratum mask. -/
def StratumMask.activeDivisors (S : StratumMask) : Finset QuadricDivisor :=
  divisorUniverse.filter (fun d : QuadricDivisor => S.contains d)

/-- Divisors inactive on a stratum mask. -/
def StratumMask.inactiveDivisors (S : StratumMask) : Finset QuadricDivisor :=
  divisorUniverse.filter (fun d : QuadricDivisor => ¬ S.contains d)

@[simp] theorem divisorUniverse_card : divisorUniverse.card = 3 := by
  decide

@[simp] theorem activeDivisors_card (S : StratumMask) :
    S.activeDivisors.card = S.codim := by
  cases S with
  | mk onQA onQB onQAB =>
    cases onQA <;> cases onQB <;> cases onQAB <;> decide

@[simp] theorem inactiveDivisors_card (S : StratumMask) :
    S.inactiveDivisors.card = 3 - S.codim := by
  cases S with
  | mk onQA onQB onQAB =>
    cases onQA <;> cases onQB <;> cases onQAB <;> decide

/-- Outgoing Gysin covers from a source stratum (add one inactive divisor). -/
def outgoingCovers (S : StratumMask) : Finset GysinCover :=
  (Finset.univ : Finset GysinCover).filter (·.source = S)

/-- Incoming Gysin covers into a target stratum (delete one active divisor). -/
def incomingCovers (S : StratumMask) : Finset GysinCover :=
  (Finset.univ : Finset GysinCover).filter (·.target = S)

@[simp] theorem outgoingCovers_card (S : StratumMask) :
    (outgoingCovers S).card = 3 - S.codim := by
  cases S with
  | mk onQA onQB onQAB =>
    cases onQA <;> cases onQB <;> cases onQAB <;> decide

@[simp] theorem incomingCovers_card (S : StratumMask) :
    (incomingCovers S).card = S.codim := by
  cases S with
  | mk onQA onQB onQAB =>
    cases onQA <;> cases onQB <;> cases onQAB <;> decide

/-- Inserting one inactive divisor raises codimension by one. -/
theorem stratum_insert_codim (S : StratumMask) (d : QuadricDivisor)
    (h : S.contains d = false) :
    (S.insert d).codim = S.codim + 1 := by
  cases S with
  | mk onQA onQB onQAB =>
    cases onQA <;> cases onQB <;> cases onQAB <;> cases d <;> simp [StratumMask.insert, StratumMask.contains, StratumMask.codim] at h ⊢

/-- Gysin insertion preserves codimension by adding one. -/
theorem gysinCover_target_codim (e : GysinCover) :
    e.target.codim = e.source.codim + 1 := by
  simpa [GysinCover.target] using stratum_insert_codim e.source e.divisor e.inactive

/-- Finite toy basis for a rank-32 Dupont/Gysin presentation: a stratum mask
plus two beta-flux bits.
This is exactly `8 × 2² = 32` generators before imposing further relations.
-/
structure DupontToyGenerator where
  stratum : StratumMask
  beta : Fin 2 → Bool
  deriving DecidableEq, Fintype, Repr

/-- Number of active quadratic generators (`beta` monomial length). -/
def DupontToyGenerator.betaRank (g : DupontToyGenerator) : ℕ :=
  ((Finset.univ : Finset (Fin 2)).filter (g.beta · = true)).card

def DupontToyGenerator.totalDegree (g : DupontToyGenerator) : ℕ :=
  g.stratum.codim + 3 * DupontToyGenerator.betaRank g

@[simp] theorem dupontToyGenerator_card : Fintype.card DupontToyGenerator = 32 := by
  let e : DupontToyGenerator ≃ StratumMask × (Fin 2 → Bool) :=
    { toFun := fun g => (g.stratum, g.beta)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := by
        intro g
        cases g
        rfl
      right_inv := by
        intro p
        cases p
        rfl }
  rw [Fintype.card_congr e, Fintype.card_prod, stratumMask_card]
  norm_num

@[simp] theorem dupontToyGenerator_codim_zero_card :
    Fintype.card { g : DupontToyGenerator // g.stratum.codim = 0 } = 4 := by
  decide

@[simp] theorem dupontToyGenerator_codim_one_card :
    Fintype.card { g : DupontToyGenerator // g.stratum.codim = 1 } = 12 := by
  decide

@[simp] theorem dupontToyGenerator_codim_two_card :
    Fintype.card { g : DupontToyGenerator // g.stratum.codim = 2 } = 12 := by
  decide

@[simp] theorem dupontToyGenerator_codim_three_card :
    Fintype.card { g : DupontToyGenerator // g.stratum.codim = 3 } = 4 := by
  decide

/-- Boolean-cube style boundary for the toy Dupont model: add one inactive divisor. -/
def toyDupontBoundary (g : DupontToyGenerator) : Finset DupontToyGenerator :=
  (g.stratum.inactiveDivisors).image (fun d : QuadricDivisor =>
    ⟨g.stratum.insert d, g.beta⟩)

/-- The toy boundary raises the stratum codimension by exactly one. -/
theorem toyDupontBoundary_codim_shift (g : DupontToyGenerator)
    (g' : DupontToyGenerator) (h : g' ∈ toyDupontBoundary g) :
    g'.stratum.codim = g.stratum.codim + 1 := by
  rcases Finset.mem_image.mp h with ⟨d, hd, hEq⟩
  rcases hEq with rfl
  have hdFalse : g.stratum.contains d = false := by
    simpa [StratumMask.inactiveDivisors] using (Finset.mem_filter.mp hd).2
  simpa using stratum_insert_codim g.stratum d hdFalse

/-- Dupont's differential uses the Gysin shift `n ↦ n+1` at fixed `q`. -/
theorem gysin_cohomological_degree_shift (n q : ℤ) :
    cohomDegree (n + 1) q = cohomDegree n q + 2 :=
  DupontHypersurfaceOSModel.differential_cohomDegree_shift n q

/-- Dupont's Tate twist shifts by one under the Gysin differential. -/
theorem gysin_tate_twist_shift (n q : ℤ) :
    tateTwist (n + 1) q = tateTwist n q + 1 :=
  DupontHypersurfaceOSModel.differential_tateTwist_shift n q

/-- A two-level target for the cooperad map collapsing the cluster `{1,2}`. -/
inductive CollapseSlot where
  | inner
  | outer
  deriving DecidableEq, Fintype, Repr

/-- Collapse of the `K₃` edges along the cluster `{1,2}`.  The edge `12` is
internal; the two edges from the cluster to point `3` become the same outer
edge in the arity-two quotient. -/
def collapse12Edge : Edge3 → CollapseSlot
  | Edge3.e12 => CollapseSlot.inner
  | Edge3.e13 => CollapseSlot.outer
  | Edge3.e23 => CollapseSlot.outer

@[simp] theorem collapse12_internal : collapse12Edge Edge3.e12 = CollapseSlot.inner := rfl
@[simp] theorem collapse12_external13 : collapse12Edge Edge3.e13 = CollapseSlot.outer := rfl
@[simp] theorem collapse12_external23 : collapse12Edge Edge3.e23 = CollapseSlot.outer := rfl

/-- The two external edges become the same arity-two edge under the cluster
collapse. -/
theorem collapse12_external_edges_identified :
    collapse12Edge Edge3.e13 = collapse12Edge Edge3.e23 := rfl

end NonIsoConf3DupontGysinModel

end noncomputable section
