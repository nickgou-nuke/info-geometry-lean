# Bogoliubov–SU(3)–Parafermion–Braid theorem graph

Status: Lean-checked modules are marked ✓. Socket/analytic hypotheses are marked ◇.

## Core q-clock / thermodynamic spine

```text
SupergradedCuntzBdG ✓
  qRapidity
  qRapidity_add
  affineSuperBracket_even_left/right
  grandCanonicalRapidity
  grandCanonicalQ
  unruhTemperature
  bdgMajoranaPlus / bdgMajoranaMinus
        │
        ▼
BogoliubovWeylChemicalPotential ✓
  BogoliubovInertialFrame
  frameWeylLogClock
  frameWeylQ_eq_qRapidity_logClock
  frameWeylLogClock_mu_shift
        │
        ▼
BogoliubovSU3ParafermionWeld ✓
  frameBraidingPhase
  frameBraidingPhase_eq_frameWeylQ
  frameBraidingPhase_mu_shift
```

## SU(3) color proof chain

```text
GellMannSU3 ✓
  gl1 ... gl8
  gl1_comm_gl2 : [λ₁,λ₂] = 2i λ₃
  gl1_comm_gl3 : [λ₁,λ₃] = -2i λ₂
  gl3_comm_gl8
        │
        ▼
BogoliubovSU3ParafermionWeld ✓
  frame_affine_even_even_lie
  frame_affine_gl1_gl2
  frame_affine_gl1_gl3
  frame_affine_gl3_gl8_commutes
        │
        ▼
BogoliubovSU3ParafermionProofChain ✓
  ColorSpinor4 V := (Fin 3 → V) × V
  colorLieAction4
  colorLieAction4_mul
  colorLieAction4_sub
  colorLieAction4_commutator
  colorAction_gl1_gl2_commutator
  colorAction_gl1_gl3_commutator
  frame_colorAction_gl1_gl2
```

Interpretation: the Bogoliubov affine deformation does **not** deform the even/color SU(3) Lie bracket; the q-clock appears in the odd/braiding lane.

## Parafermion/BdG lane

```text
SupergradedCuntzBdG ✓
  bdgMajoranaPlus i
  bdgMajoranaMinus i
  bdgMajoranaPlus_sq_eq_hamiltonianAtom
        │
        ▼
BogoliubovSU3ParafermionProofChain ✓
  ParafermionStage4 := CuntzAlg ℂ (Fin 4)
  bdgMajoranaPlusColorSpinor4
  bdgMajoranaPlusColorSpinor4_color_sq
  bdgMajoranaPlusColorSpinor4_singlet_sq
```

Note: `CuntzAlg ℂ (Fin 4)` is currently a semiring stage, so subtraction/Lie commutator representation is proved for any additive-group/module target `V`; multiplication-square facts are proved directly in the concrete Cuntz stage.

## Braid/Yang–Baxter connections

```text
BraidIdealDescent ✓
  qCrossMap q
  qCrossMap_tmul
  tauL / tauR
  tauLDesc / tauRDesc
        ▲
        │ frame_qCrossMap_tmul
        │
BogoliubovBraidGraphWeld ✓
  qColorBraid4
  qColorSigma0 / qColorSigma1
  qColorBraid4_artin
  frameColorBraid_artin
  frameColorSigma0_mu_shift
  bogoliubov_braid_graph_synthesis
        │
        ├──────────────► B3RepresentationBridge ✓
        │                 s3_rep.artin
        │                 gl8_rep.artin
        │
        ├──────────────► YangBaxterQSwap ✓
        │                 yang_baxter_relation (frameBraidingPhase F)
        │
        └──────────────► B3PresentedGroup / JonesBraidB3 / TLChain ✓
                          TL₃(2) → Jones generators → B₃ → GL₈
```

Explicit new braid action:

```lean
permuteColorSpinor4 π ψ := (fun i => ψ.1 (π i), ψ.2)
qColorBraid4 q π ψ := q • permuteColorSpinor4 π ψ
qColorSigma0 q := qColorBraid4 q (Equiv.swap 0 1)
qColorSigma1 q := qColorBraid4 q (Equiv.swap 1 2)
```

Proved Artin relation:

```lean
qColorSigma0 q (qColorSigma1 q (qColorSigma0 q ψ)) =
qColorSigma1 q (qColorSigma0 q (qColorSigma1 q ψ))
```

Bogoliubov specialization:

```lean
q = frameBraidingPhase F = frameWeylQ F = qRapidity (frameWeylLogClock F)
```

## Phase-space / Weyl / colimit / canonical socket spine

```text
HestenesCuntzPhaseSpace ✓
  FiniteWeylPair
  twoCellWeylPair
  no_finite_m2_canonical_ccr
        │
        ▼
GaugeUHFLift ✓
  gaugeActAt
  diagEmbedSucc compatibility
        │
        ▼
WeylGaugeColimitWeld ✓
  transportWeylPair
  diagTwoCellWeylPair_commutator
  coordinate_commutes_diagEmbed
  momentum_commutes_diagEmbed
        │
        ▼
WeylColimitCanonicalLimit ✓/◇
  finite UHF Weyl backbone ✓
  WeylColimitCanonicalApproximation ◇
        │
        ▼
RescaledPhaseVolumeCanonical ✓/◇
  commA_rescale ✓
  CanonicalRescalingCertificate ◇
  rescaled_canonical_commutator ✓
```

Honesty clause: finite `M₂(ℂ)` gives Weyl `[X,P]=2XP`, not scalar CCR. Exact `[X',P']=iκ1` lives in the calibrated abstract/analytic socket.

## Current checked roots added in this pass

```text
BogoliubovSU3ParafermionWeld ✓
BogoliubovSU3ParafermionProofChain ✓
BogoliubovBraidGraphWeld ✓
```

Targeted build:

```bash
cd proofs
lake build BogoliubovBraidGraphWeld
# Build completed successfully (8056 jobs).
```
