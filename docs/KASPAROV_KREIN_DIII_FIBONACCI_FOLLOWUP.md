# DIII/Fibonacci-MZM Follow-up Roadmap

**Status:** companion roadmap; no new theorem authority  
**Anchor date:** 2026-06-18  
**Scope:** finite DIII/Andreev corridor to Fibonacci/Majorana braid interfaces

This note is the starting packet for the next lane after the
Kasparov-Krein/DIII corridor. It records what is already kernel-checked, what
the next bridge may assume explicitly, and what remains debt. It does not claim
Majorana zero-mode protection, braid density, fast scrambling, a KO-index
theorem, or a physical horizon theorem.

## 1. Stable Lemmas

These declarations are usable citation anchors after their owner modules build.

### DIII/Andreev/Kasparov-Krein Corridor

- `InfoGeometry.Projective.KasparovKreinDIIIBridge.finite_andreev_diii_signature_packet`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.canonical_diii_proxy_sign_readback`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.canonical_diii_proxy_root_readback`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.krein_kasparov_grade_split_from_witness`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.krein_kasparov_mixed_commutator_gZero`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.kasparov_product_cycle_readback`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.klein_bottle_trace_absorption`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.concreteTopologicalSocket2_packet`

### Finite Andreev Horizon Readout

- `InfoGeometry.Projective.AndreevHorizonUnitarity.andreevTwin_sq`
- `InfoGeometry.Projective.AndreevHorizonUnitarity.andreevTwin_normSq`
- `InfoGeometry.Projective.AndreevHorizonUnitarity.andreevTwin_fourth`
- `InfoGeometry.Projective.AndreevHorizonUnitarity.hawking_is_andreev_reflection`
- `InfoGeometry.Projective.AndreevHorizonUnitarity.concreteAndreevHorizonSMatrix_unitarity`
- `InfoGeometry.Projective.AndreevHorizonUnitarity.horizon_information_preservation_from_trace_zero`
- `InfoGeometry.Projective.AndreevHorizonUnitarity.concreteAndreevHorizon_information_preservation`

### Finite Horizon Braiding Interface

- `InfoGeometry.Projective.Scrambling.horizonFibonacciRegister_card`
- `InfoGeometry.Projective.Scrambling.finite_unitary_braiding_packet`

`ModularTimeFlow.conserves_information` is a field, not a derived theorem. A
future owner may try to derive it from a concrete representation; this file must
not treat it as already proved from unitarity alone.

### Fibonacci/Anyon Matrix And Rewrite Owners

- `InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding.eps_fusion_eps`
- `InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding.one_mem_eps_fusion_eps`
- `InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding.eps_mem_eps_fusion_eps`
- `InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding.mem_eps_fusion_eps_iff`
- `InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding.card_fibonacciComputationalSpace`
- `InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding.fibonacciProjectiveGate_braid_rewrite_of_evalPhase`
- `InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding.fibonacciProjectiveGate_commute_rewrite_of_evalPhase`
- `InfoGeometry.Canonical.YangBaxterProof.F_sq`
- `InfoGeometry.Canonical.YangBaxterProof.F_B_F_eq_R`
- `InfoGeometry.Canonical.YangBaxterProof.braid_relation`

### Related Klein Log-Time / Monodromy Anchors

These are stable algebraic/logarithmic readouts that may inform the next lane.
They do not prove that physical time is globally identical to a de Rham
cohomology class.

- `InfoGeometry.Projective.KleinQuadric.Plucker6.coordinatePairing_kleinGradient_eq_polar`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.kleinQ_add_scale`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.kleinBarrierHessian_symm`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.kleinBarrierHessian_radial_left`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.kleinDLogAlong_eq_gradient_pairing_div`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.kleinDLogAlong_self_eq_two`
- `InfoGeometry.Projective.KleinQuadric.Time.tripotent_square_idempotent`
- `InfoGeometry.Projective.KleinQuadric.Time.nullSpaceProjection_idempotent`
- `InfoGeometry.Projective.KleinQuadric.Time.nullSpaceProjection_mul_tripotent_eq_zero`
- `InfoGeometry.Projective.KleinQuadric.Time.timeCohomology_eq_circleIntegral_grothendieck_dlog`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.circleIntegral_one_div`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.deRhamClass_of_winding`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.wilsonPhase_of_winding`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.chiralNullConductor_eq_selfOrthogonal`

## 2. Explicit Assumptions For The Next Bridge

Any new `FibonacciMZMBraidingBridge` or equivalent file should make these
premises explicit as fields or theorem hypotheses.

1. **Braid realization.** A concrete braid-word action on the chosen finite
   horizon carrier, with a stated map from braid words to matrices/operators.

2. **Unitary/conservation certificate.** For every braid operator used as a
   `ModularTimeFlow`, either provide the `conserves_information` field directly
   or prove it in a local owner from the selected matrix representation.

3. **Fibonacci label readout.** A map from the finite DIII/Andreev parity
   packet to Fibonacci charge labels or projective braid phases, with rewrite
   invariance proved from `FiniteFibonacciAnyonBraiding`/`YangBaxterProof`.

4. **Betti-to-register bridge.** If rank-32 data is used, require a verified
   external certificate plus a Lean theorem connecting that certificate to the
   register dimension. Do not infer protected modes from the current
   `candidateLocalBettiData`.

5. **Physical interpretation gate.** Any statement using "MZM", "horizon",
   "fast scrambling", or "black hole" must be an interface theorem over
   explicit mathematical hypotheses, not a closed physical theorem.

6. **Log-time interpretation gate.** Any statement using "time is de Rham
   cohomology", "modular clock", or "Berry holonomy is physical time" must be
   stated as an interface theorem over explicit geometric, analytic, and
   representation hypotheses. The current Klein/logarithmic modules prove local
   algebraic, residue, and monodromy readbacks only.

## 3. Starter Lemma Shapes

These are acceptable next targets because they are assumption-indexed and
reuse existing owners.

### Rewrite-Invariant Fibonacci Phase Readout

```lean
structure FibonacciMZMReadout where
  phase : FibonacciBraidPhase
  readout : Equiv.Perm ℕ -> Gate
  braidPhase_rewrite :
    phase (left ++ [i, i + 1, i] ++ right) =
      phase (left ++ [i + 1, i, i + 1] ++ right)
```

Target theorem:

```lean
theorem fibonacci_mzm_projective_gate_braid_rewrite
    (D : FibonacciMZMReadout) :
    fibonacciProjectiveGate Gate D.phase D.readout
        (left ++ [i, i + 1, i] ++ right) =
      fibonacciProjectiveGate Gate D.phase D.readout
        (left ++ [i + 1, i, i + 1] ++ right) := ...
```

### DIII-Andreev To Finite Braid Packet

```lean
structure DIIIAndreevFibonacciPacket where
  flow : ModularTimeFlow n
  state : HorizonMicrostates n
  andreevState : InfallingParticle
  parityMatchesBraid : Prop
```

Target theorem:

```lean
theorem diii_andreev_fibonacci_packet_readback
    (P : DIIIAndreevFibonacciPacket) :
    IsUnitaryBraiding P.flow /\ InformationIsConserved P.flow P.state := ...
```

The proof should be a readback from `finite_unitary_braiding_packet`; it should
not imply density, universality, or fast scrambling.

### Rank-Gated Register Size

Target theorem:

```lean
theorem verified_rank32_to_register_budget
    (cert : ExternalBettiData)
    (hConsistent : RankDataConsistent cert)
    (hRank : cert.totalRank * spinTilingMultiplicity = 32) :
    Fintype.card (HorizonFibonacciRegister N) = Nat.fib (2 * N + 1) /\ ... := ...
```

The ellipsis must be replaced by a specific arithmetic/register statement, not
a physical mode-protection claim.

## 4. Open Debt

1. **Braid representation construction**
   - Owner candidates: `InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding`,
     `InfoGeometry.Canonical.YangBaxterProof`.
   - Debt: construct the exact finite operator representation used by
     `ModularTimeFlow`, not only a supplied field.

2. **Majorana/Fibonacci identification**
   - Owner candidates: `InfoGeometry.Canonical.FiniteMajoranaBraiding`,
     `InfoGeometry.Canonical.FiniteMajoranaProjectiveBraiding`,
     `InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding`.
   - Debt: prove a real theorem relating the DIII/Andreev parity packet to the
     Fibonacci charge or Majorana braid labels.

3. **Rank-32 certificate closure**
   - Owner candidates: `InfoGeometry.Projective.NonIsoConf3RankIngestion`,
     `proofs/non_iso_conf3_rank32_external_audit.py`.
   - Debt: replace timeout/candidate data with an external verified payload and
     a Lean theorem that consumes only the verified data.

4. **Protected-boundary-mode theorem**
   - Owner candidates: future condensed-matter/topological module.
   - Debt: show protection/gap/localization from explicit spectral or
     K-theoretic hypotheses. Current finite braid lemmas do not prove this.

5. **Fast-scrambling/density theorem**
   - Owner candidates: future analytic/quantum-information module.
   - Debt: prove a quantitative scrambling bound or density/universality result
     from a concrete representation. Current `finite_unitary_braiding_packet`
     is only conservation under a supplied certificate.

6. **Global log-time theorem**
   - Owner candidates: `InfoGeometry.Projective.KleinQuadricTime`,
     `InfoGeometry.Projective.KleinQuadricMonodromy`, future analytic geometry
     module.
   - Debt: prove global complement/cohomology hypotheses, single-valuedness or
     covering-space conventions, and a representation theorem connecting the
     logarithmic de Rham class to modular flow. Current lemmas prove local
     `dQ/Q`, residue, and barrier-Hessian readbacks.

## 5. Minimal Execution Plan

1. Add `lean/InfoGeometry/Projective/FibonacciMZMBraidingBridge.lean`.
2. Define small structures for the readout assumptions above.
3. Prove two readback lemmas:
   - projective gate rewrite invariance from existing Fibonacci owners;
   - DIII/Andreev finite braid packet from `finite_unitary_braiding_packet`.
4. Add a SymPy witness only for finite matrix algebra already mirrored by Lean
   owners; do not use it as proof authority.
5. Run:

```bash
lake env lean lean/InfoGeometry/Projective/FibonacciMZMBraidingBridge.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Projective.FibonacciMZMBraidingBridge
rg "\bsorry\b|admit|axiom|: True := by|theorem .*: True|unsafe" \
  lean/InfoGeometry/Projective/FibonacciMZMBraidingBridge.lean
```

## 6. Gatekeeping Rule

The next lane starts from finite algebra and explicit interfaces. It must not
turn:

- rewrite invariance into physical robustness;
- supplied norm conservation into a scrambling theorem;
- candidate Betti data into protected Majorana modes;
- finite matrix witnesses into global KO/Kasparov theorems.
- logarithmic de Rham monodromy into a closed theorem identifying physical
  time without explicit global geometric and operator-algebraic hypotheses.
