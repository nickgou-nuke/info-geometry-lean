import proofs.GaugeUHFLift
import proofs.HestenesCuntzPhaseSpace

/-!
# Weyl → Gauge → UHF Colimit Weld

The finite Weyl pair `(σ₃, σ₁)` on M₂(ℂ) with `q=-1` is transported via
the gauge representation `gaugeActAt n` to the diagonal UHF algebra `DiagAlg n`
(for stages `n ≥ 1`).  The Weyl relation `P·X = q·X·P` holds at every stage,
and the `gaugeActAt_commutes_diagEmbed_succ` theorem provides the colimit
compatibility: the coordinated gauge action lifts to the full UHF limit algebra.

This welds three layers:
1. Finite Weyl/clock-shift phase cell (HestenesCuntzPhaseSpace)
2. Gauge action on the diagonal UHF limit algebra (GaugeUHFLift)
3. Finite phase-volume data from the transported Weyl cell

Zero sorries.
-/

noncomputable section

namespace WeylGaugeColimitWeld

open GaugeUHFLift
open HestenesCuntzPhaseSpace
open UHFInductiveColimit

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-! ## Gauge action is ℂ-linear in the matrix argument (for n ≥ 1) -/

/-- The gauge action `gaugeActAt (n+1)` is ℂ-linear in the matrix slot.
This holds because the matrix entries are multiplied directly into the linear
combination; for `n=0` the action is trivial `id` and the identity fails. -/
theorem gaugeActAt_succ_smul (n : ℕ) (c : ℂ) (A : M2C) (f : DiagAlg (n+1)) :
    gaugeActAt (n+1) (c • A) f = c • gaugeActAt (n+1) A f := by
  ext w
  dsimp [gaugeActAt]
  by_cases h : w 0
  · simp [h]; ring
  · simp [h]; ring

/-! ## Gauge action as a ℂ-linear endomorphism -/

/-- The gauge action wrapped as a ℂ-linear endomorphism of `DiagAlg (n+1)`.
Additivity and scalar-linearity in `f` come from `gaugeActAt_is_representation`. -/
def gaugeActAtEnd (n : ℕ) (A : M2C) : DiagAlg (n+1) →ₗ[ℂ] DiagAlg (n+1) where
  toFun := gaugeActAt (n+1) A
  map_add' := by
    rcases gaugeActAt_is_representation (n+1) A 1 with ⟨_, _, hadd, _⟩
    simpa using hadd
  map_smul' := by
    rcases gaugeActAt_is_representation (n+1) A 1 with ⟨_, _, _, hsmul⟩
    simpa using hsmul

/-- The gauge representation is multiplicative as linear endomorphisms.
Multiplication in `End` is composition. -/
theorem gaugeActAtEnd_mul (n : ℕ) (A B : M2C) :
    gaugeActAtEnd n (A * B) = gaugeActAtEnd n A * gaugeActAtEnd n B := by
  rcases gaugeActAt_is_representation (n+1) A B with ⟨hmul, _, _, _⟩
  apply LinearMap.ext; intro f
  simpa using hmul f

/-- The gauge representation preserves the identity. -/
theorem gaugeActAtEnd_one (n : ℕ) :
    gaugeActAtEnd n (1 : M2C) = (1 : DiagAlg (n+1) →ₗ[ℂ] DiagAlg (n+1)) := by
  rcases gaugeActAt_is_representation (n+1) 1 1 with ⟨_, hone, _, _⟩
  apply LinearMap.ext; intro f
  simpa using hone f

/-! ## Transport the finite Weyl pair to the diagonal UHF algebra -/

/-- Transport a `FiniteWeylPair` on M₂(ℂ) to the endomorphism algebra of `DiagAlg (n+1)`
via the gauge representation.  The Weyl phase `q` and the root-of-unity condition
`q ^ N = 1` are preserved. -/
def transportWeylPair (n : ℕ) (W : FiniteWeylPair 2 M2C) :
    FiniteWeylPair 2 (DiagAlg (n+1) →ₗ[ℂ] DiagAlg (n+1)) where
  coordinate := gaugeActAtEnd n W.coordinate
  momentum := gaugeActAtEnd n W.momentum
  q := W.q
  q_pow_dim := W.q_pow_dim
  weyl_relation := by
    calc
      gaugeActAtEnd n W.momentum * gaugeActAtEnd n W.coordinate
          = gaugeActAtEnd n (W.momentum * W.coordinate) := by
        rw [gaugeActAtEnd_mul]
      _ = gaugeActAtEnd n (W.q • (W.coordinate * W.momentum)) := by
        rw [W.weyl_relation]
      _ = W.q • gaugeActAtEnd n (W.coordinate * W.momentum) := by
        apply LinearMap.ext; intro f
        dsimp [gaugeActAtEnd]
        exact gaugeActAt_succ_smul n W.q (W.coordinate * W.momentum) f
      _ = W.q • (gaugeActAtEnd n W.coordinate * gaugeActAtEnd n W.momentum) := by
        rw [gaugeActAtEnd_mul]

/-- The `N=2, q=-1` Weyl pair transported to `DiagAlg (n+1)` endomorphisms. -/
def diagTwoCellWeylPair (n : ℕ) :
    FiniteWeylPair 2 (DiagAlg (n+1) →ₗ[ℂ] DiagAlg (n+1)) :=
  transportWeylPair n twoCellWeylPair

/-- The transported two-cell pair has `q = -1` at every stage. -/
theorem diagTwoCellWeylPair_phase (n : ℕ) :
    (diagTwoCellWeylPair n).q = (-1 : ℂ) := rfl

/-- The coordinate--momentum commutator at any stage has factor `1 - q = 2`. -/
theorem diagTwoCellWeylPair_commutator (n : ℕ) :
    (diagTwoCellWeylPair n).coordinate * (diagTwoCellWeylPair n).momentum -
      (diagTwoCellWeylPair n).momentum * (diagTwoCellWeylPair n).coordinate =
        (1 - (diagTwoCellWeylPair n).q : ℂ) •
          ((diagTwoCellWeylPair n).coordinate * (diagTwoCellWeylPair n).momentum) :=
  (diagTwoCellWeylPair n).coordinate_momentum_commutator

/-- The Weyl relation `P·X = -1·X·P` at any stage. -/
theorem diagTwoCellWeylPair_weyl_relation (n : ℕ) :
    (diagTwoCellWeylPair n).momentum * (diagTwoCellWeylPair n).coordinate =
      (-1 : ℂ) • ((diagTwoCellWeylPair n).coordinate * (diagTwoCellWeylPair n).momentum) := by
  calc
    (diagTwoCellWeylPair n).momentum * (diagTwoCellWeylPair n).coordinate
        = (diagTwoCellWeylPair n).q • ((diagTwoCellWeylPair n).coordinate * (diagTwoCellWeylPair n).momentum) :=
      (diagTwoCellWeylPair n).weyl_relation
    _ = (-1 : ℂ) • ((diagTwoCellWeylPair n).coordinate * (diagTwoCellWeylPair n).momentum) := by
      rw [diagTwoCellWeylPair_phase n]

/-! ## Colimit compatibility: the Weyl pair lifts through diagEmbedSucc -/

/-- The gauge action of the coordinate operator commutes with the UHF transition map.
This is a direct application of `gaugeActAt_commutes_diagEmbed_succ`. -/
theorem coordinate_commutes_diagEmbed (n : ℕ) (f : DiagAlg (n+1)) :
    gaugeActAt (n+2) twoCellWeylPair.coordinate (diagEmbedSucc (n+1) f) =
    diagEmbedSucc (n+1) (gaugeActAt (n+1) twoCellWeylPair.coordinate f) :=
  gaugeActAt_commutes_diagEmbed_succ n twoCellWeylPair.coordinate f

/-- The gauge action of the momentum operator commutes with the UHF transition map. -/
theorem momentum_commutes_diagEmbed (n : ℕ) (f : DiagAlg (n+1)) :
    gaugeActAt (n+2) twoCellWeylPair.momentum (diagEmbedSucc (n+1) f) =
    diagEmbedSucc (n+1) (gaugeActAt (n+1) twoCellWeylPair.momentum f) :=
  gaugeActAt_commutes_diagEmbed_succ n twoCellWeylPair.momentum f

/-- Both coordinate and momentum gauge actions lift through the UHF colimit
transition maps. -/
theorem weyl_pair_commutes_diagEmbed (n : ℕ) (f : DiagAlg (n+1)) :
    (gaugeActAt (n+2) twoCellWeylPair.coordinate (diagEmbedSucc (n+1) f) =
     diagEmbedSucc (n+1) (gaugeActAt (n+1) twoCellWeylPair.coordinate f)) ∧
    (gaugeActAt (n+2) twoCellWeylPair.momentum (diagEmbedSucc (n+1) f) =
     diagEmbedSucc (n+1) (gaugeActAt (n+1) twoCellWeylPair.momentum f)) :=
  ⟨coordinate_commutes_diagEmbed n f,
   momentum_commutes_diagEmbed n f⟩

/-! ## Finite phase-volume data -/

/-- Concrete finite equalities for the transported two-cell and the UHF
transition map. -/
structure PhaseVolumeRescaling (n : ℕ) (f : DiagAlg (n+1)) where
  phase_eq : (diagTwoCellWeylPair n).q = (-1 : ℂ)
  weyl_relation :
    (diagTwoCellWeylPair n).momentum * (diagTwoCellWeylPair n).coordinate =
      (-1 : ℂ) • ((diagTwoCellWeylPair n).coordinate * (diagTwoCellWeylPair n).momentum)
  commutator_eq :
    (diagTwoCellWeylPair n).coordinate * (diagTwoCellWeylPair n).momentum -
      (diagTwoCellWeylPair n).momentum * (diagTwoCellWeylPair n).coordinate =
      (1 - (diagTwoCellWeylPair n).q : ℂ) •
        ((diagTwoCellWeylPair n).coordinate * (diagTwoCellWeylPair n).momentum)
  coordinate_transition :
    gaugeActAt (n+2) twoCellWeylPair.coordinate (diagEmbedSucc (n+1) f) =
      diagEmbedSucc (n+1) (gaugeActAt (n+1) twoCellWeylPair.coordinate f)
  momentum_transition :
    gaugeActAt (n+2) twoCellWeylPair.momentum (diagEmbedSucc (n+1) f) =
      diagEmbedSucc (n+1) (gaugeActAt (n+1) twoCellWeylPair.momentum f)

/-- The transported two-cell supplies all finite phase-volume data at each
stage. -/
def phaseVolumeRescaling (n : ℕ) (f : DiagAlg (n+1)) : PhaseVolumeRescaling n f where
  phase_eq := diagTwoCellWeylPair_phase n
  weyl_relation := diagTwoCellWeylPair_weyl_relation n
  commutator_eq := diagTwoCellWeylPair_commutator n
  coordinate_transition := coordinate_commutes_diagEmbed n f
  momentum_transition := momentum_commutes_diagEmbed n f

/-! ## Synthesis -/

/-- The Weyl–Gauge–UHF colimit weld synthesis:
  1. The `q=-1` Weyl pair is transported to every stage `n ≥ 1` of the diagonal UHF algebra.
  2. The Weyl relation `P·X = -1·X·P` holds at every stage.
  3. Both coordinate and momentum gauge actions lift through the UHF transition maps. -/
theorem weyl_gauge_uhf_colimit_synthesis (n : ℕ) (f : DiagAlg (n+1)) :
    (diagTwoCellWeylPair n).q = (-1 : ℂ) ∧
    (diagTwoCellWeylPair n).momentum * (diagTwoCellWeylPair n).coordinate =
      (-1 : ℂ) • ((diagTwoCellWeylPair n).coordinate * (diagTwoCellWeylPair n).momentum) ∧
    (diagTwoCellWeylPair n).coordinate * (diagTwoCellWeylPair n).momentum -
      (diagTwoCellWeylPair n).momentum * (diagTwoCellWeylPair n).coordinate =
      (1 - (diagTwoCellWeylPair n).q : ℂ) •
        ((diagTwoCellWeylPair n).coordinate * (diagTwoCellWeylPair n).momentum) ∧
    gaugeActAt (n+2) twoCellWeylPair.coordinate (diagEmbedSucc (n+1) f) =
      diagEmbedSucc (n+1) (gaugeActAt (n+1) twoCellWeylPair.coordinate f) ∧
    gaugeActAt (n+2) twoCellWeylPair.momentum (diagEmbedSucc (n+1) f) =
      diagEmbedSucc (n+1) (gaugeActAt (n+1) twoCellWeylPair.momentum f) := by
  refine ⟨?phase, ?weyl, ?commutator, ?coordinate, ?momentum⟩
  · exact diagTwoCellWeylPair_phase n
  · exact diagTwoCellWeylPair_weyl_relation n
  · exact diagTwoCellWeylPair_commutator n
  · exact coordinate_commutes_diagEmbed n f
  · exact momentum_commutes_diagEmbed n f

end WeylGaugeColimitWeld

end noncomputable section
