# Klein Log-Time Formalization Roadmap

**Status:** proof-substrate roadmap; no new theorem authority
**Anchor date:** 2026-06-18
**Scope:** logarithmic de Rham winding around Klein/chiral determinant cones

This note grounds the thesis phrase

```text
time as de Rham 1-form cohomology of winding around the cone of the
chiral Klein quadric
```

in the current repository.  The kernel-checked source currently proves local
algebraic, residue, monodromy, barrier-Hessian, nilpotent, and explicit
interface facts.  It does not prove a global theorem identifying physical time
with this class, nor a full Tomita-Takesaki, Berry-holonomy, or motivic
cohomology theorem for the chiral cone.

The referenced local PDF
`/home/goutev/Downloads/collection_for_formalization/thesis.pdf` is Konrad
Voelkel, *Motivic Cell Structures for Projective Spaces over Split
Quaternions* (2016).  Use it as background for motivic cell structures, split
composition algebras, and split quadrics; it is not proof authority for the
log-time bridge unless its lemmas are explicitly formalized.

Relevant PDF anchors for future formalization are:

- Lemma 2.1.11: odd-dimensional split affine quadrics are identified with
  motivic spheres by an affine-bundle argument.
- Theorem 2.1.12: even-dimensional smooth split affine quadrics are weakly
  equivalent to motivic spheres, citing Asok-Doran-Fasel.
- Lemma 4.1.12: `CP1`, `HP1`, and `OP1` are even-dimensional affine split
  quadrics.
- Theorem 4.4.6: split quaternionic `HP1` over a field is a motivic sphere.
- Theorem 4.4.8: split quaternionic `HPn` over a field carries an unstable
  motivic cell structure built inductively from `HP(n-1)`.

## 1. Stable Lemmas

These declarations are usable anchors after their owner modules build.

### Klein Residue And Monodromy

- `InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.circleIntegral_one_div`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.logarithmicPhase`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.universalCoverLog_sheet_increment`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.holonomyPhase_is_root_of_unity`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.deRhamClass_of_winding`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.wilsonPhase_of_winding`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.logDerivative_at`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.negLogDerivative_at`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.chiralNullConductor_eq_selfOrthogonal`

### Grothendieck-dLog Bridge

- `InfoGeometry.Projective.KleinQuadric.DeRhamMotive.chiralDetPotential_eq_zero_iff`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMotive.grothendieck_dlog`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMotive.grothendieckLog_deriv_log`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMotive.grothendieckLog_deriv_neg_log`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMotive.circleIntegral_grothendieck_dlog`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMotive.grothendieckWinding_of_sheet`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMotive.tomita_sheet_transport`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMotive.grothendieckTomitaWilsonBridge`

### Plucker/Klein Gradient And Barrier Hessian

- `InfoGeometry.Projective.KleinQuadric.Plucker6.coordinatePairing_kleinGradient_eq_polar`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.kleinQ_add_scale`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.polar_symm`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.polar_self_eq_two_mul_kleinQ`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.kleinBarrierHessian_symm`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.kleinBarrierHessian_self`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.kleinBarrierHessian_radial_left`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.kleinBarrierHessian_radial_self`

### Tripotent/Nilpotent Projection Layer

- `InfoGeometry.Projective.KleinQuadric.Time.tripotent_fourth_eq_square`
- `InfoGeometry.Projective.KleinQuadric.Time.tripotent_square_idempotent`
- `InfoGeometry.Projective.KleinQuadric.Time.nullSpaceProjection_idempotent`
- `InfoGeometry.Projective.KleinQuadric.Time.nullSpaceProjection_mul_tripotent_eq_zero`
- `InfoGeometry.Projective.KleinQuadric.Time.tripotent_mul_nullSpaceProjection_eq_zero`
- `InfoGeometry.Projective.KleinQuadric.Time.kleinDLogAlong_eq_gradient_pairing_div`
- `InfoGeometry.Projective.KleinQuadric.Time.kleinDLogAlong_self_eq_two`
- `InfoGeometry.Projective.KleinQuadric.Time.logGeneratingPotential_hasDerivAt`
- `InfoGeometry.Projective.KleinQuadric.Time.timeCohomology_eq_two_pi_I`
- `InfoGeometry.Projective.KleinQuadric.Time.timeCohomology_exp_eq_one`
- `InfoGeometry.Projective.KleinQuadric.Time.timeCohomology_eq_circleIntegral_grothendieck_dlog`

### Parabolic Modular Clock Interface

- `InfoGeometry.Projective.ParabolicTimeMonodromy.modularGenerator_nilpotent`
- `InfoGeometry.Projective.ParabolicTimeMonodromy.parabolic_time_clock`
- `InfoGeometry.Projective.ParabolicTimeMonodromy.nullConeFlow_trace`
- `InfoGeometry.Projective.ParabolicTimeMonodromy.nullConeFlow_det`
- `InfoGeometry.Projective.ParabolicTimeMonodromy.nullConeFlow_parabolic`
- `InfoGeometry.Projective.ParabolicTimeMonodromy.parabolic_winding_power_law`
- `InfoGeometry.Projective.ParabolicTimeMonodromy.deRham_winding_phase`

### 3+1 Chiral Cone Readout

- `InfoGeometry.Canonical.TimeAsWindingMonodromy3D.chiralMatrix_det`
- `InfoGeometry.Canonical.TimeAsWindingMonodromy3D.chiralPotential_eq_det`
- `InfoGeometry.Canonical.TimeAsWindingMonodromy3D.boundary_eq_det_zero_iff`
- `InfoGeometry.Canonical.TimeAsWindingMonodromy3D.Splus_sqr_eq_zero`
- `InfoGeometry.Canonical.TimeAsWindingMonodromy3D.Sminus_sqr_eq_zero`
- `InfoGeometry.Canonical.TimeAsWindingMonodromy3D.Splus_det_zero`
- `InfoGeometry.Canonical.TimeAsWindingMonodromy3D.Sminus_det_zero`
- `InfoGeometry.Canonical.TimeAsWindingMonodromy3D.poleWinding_eq_logarithmicPhase`
- `InfoGeometry.Canonical.TimeAsWindingMonodromy3D.poleWinding_index_is_integer`
- `InfoGeometry.Canonical.TimeAsWindingMonodromy3D.rindler_isometry`
- `InfoGeometry.Canonical.TimeAsWindingMonodromy3D.time_tick_is_integer`

## 2. External Witnesses

- `formalizations/chiral_causal_cone_time_witness.py`
  checks the Klein gradient/polar identity, the barrier Hessian contraction
  formula, the radial `d log Q` readout, the tripotent projection identities
  via GAP when available, and optional Sage/galgebra/clifford blocks.

- `formalizations/klein_quadric_monodromy_witness.py`,
  `formalizations/klein_quadric_multibackend_pipeline.py`, and
  `formalizations/klein_quadric_motive_bridge.py`
  are computational companions only.  They do not replace Lean proof.

- `compute_derham.m2` and Track B scripts are heavyweight external attempts
  for the complement/de Rham computation.  A timeout is evidence of
  computational cost, not a failed theorem and not a verified certificate.

## 3. Explicit Assumptions For A Future Bridge

Any file named `KleinLogTimeBridge`, `ModularLogTimeBridge`, or equivalent
should make these premises explicit as fields or theorem hypotheses.

1. **Transverse divisor model.** A map from a neighborhood of the Klein/chiral
   determinant divisor to the local pole model `z = 0`, with stated loop and
   orientation conventions.

2. **Complement cohomology theorem.** A proof that the chosen logarithmic form
   represents the intended generator of the relevant `H^1` of the complement,
   not only the local `dz/z` residue model.

3. **Branch/cover convention.** A selected universal cover or slit-plane
   convention that explains when `Complex.log`, `uLog`, and sheet shifts are
   being used.

4. **Tomita dictionary.** A representation of the operator algebra and a
   stated map from de Rham residue data to the modular derivation
   `X |-> K*X - X*K`.  The current `MonodromyModularDictionary` keeps this as
   an explicit interface.

5. **Self-concordance hypotheses.** A real cone/domain, positivity assumptions,
   and analytic inequalities proving that `-log Q` is a self-concordant barrier
   on that domain.  The current Lean layer proves algebraic Hessian readbacks,
   not the full optimization-theory theorem.

6. **Physical clock interpretation.** A theorem using "time", "Tomita clock",
   "Berry holonomy", or "causal clock" must quantify over the above dictionary
   data.  Local monodromy alone is not a global physical-time theorem.

7. **Motivic cell bridge.** If the Voelkel split-quaternion thesis is used, the
   specific split-quadric/cell-structure lemma must be cited and formalized or
   isolated as an external assumption.

## 4. Starter Lemma Shapes

These targets are acceptable because they are assumption-indexed.

### Local Log-Time Dictionary

```lean
structure KleinLogTimeDictionary (A : Type*) [Ring A] where
  residue : InfoGeometry.Projective.ParabolicTimeMonodromy.DeRhamResidue A
  timeGenerator : A
  residueToDerivation :
    InfoGeometry.Projective.ParabolicTimeMonodromy.DeRhamResidue A -> A -> A
  residue_eq_modularDerivation :
    residueToDerivation residue =
      InfoGeometry.Projective.ParabolicTimeMonodromy.modularDerivation timeGenerator
  timeGenerator_square_zero : timeGenerator * timeGenerator = 0
```

Target theorem:

```lean
theorem klein_log_time_square_zero_readback
    (D : KleinLogTimeDictionary A) :
    Exists (fun K : A => K * K = 0) := ...
```

This should read back from `parabolic_time_clock`; it should not assert a
global Tomita-Takesaki theorem.

### Period Readout From A Certified Loop

```lean
structure CertifiedKleinLoop where
  R : ℝ
  hR : 0 < R
  winding : ℤ
```

Target theorem:

```lean
theorem certified_loop_period_readout
    (L : CertifiedKleinLoop) :
    (L.winding : ℂ) *
        (circleIntegral (fun z => (1 : ℂ) / z) ...)
      =
    InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.logarithmicPhase
      L.winding := ...
```

In practice, reuse `deRhamClass_of_winding` instead of rebuilding integration.

### Barrier-Hessian Directional Readout

Target theorem:

```lean
theorem barrier_hessian_radial_is_dlog
    (P X : Plucker6 ℂ) (hP : kleinQ P ≠ 0) :
    kleinBarrierHessian P P X = kleinDLogAlong P X := ...
```

This should be a short bridge from `kleinBarrierHessian_radial_left`; it is
only a local algebraic identity.

## 5. Open Debt

1. **Full complement cohomology.**
   Prove or certify the actual de Rham cohomology of the Klein/chiral
   determinant complement.  The current circle integral is the local residue
   model.

2. **Closed/not-exact form theorem.**
   Formalize the differential form complex enough to prove that `dQ/Q` is
   closed on the complement and non-exact globally under the chosen hypotheses.

3. **Analytic self-concordance.**
   Prove the real-domain self-concordance inequalities for `-log Q`, including
   the exact cone/domain and positivity assumptions.

4. **Tomita-Takesaki representation theorem.**
   Replace the dictionary field with an operator-algebra theorem connecting the
   modular generator to the residue/logarithmic data.

5. **Berry/Wilson phase semantics.**
   Separate additive monodromy `2*pi*i*n` from multiplicative holonomy
   `exp(2*pi*i*n)=1`, and prove any physical phase interpretation only after
   specifying the representation.

6. **Noncommutative lift.**
   Show how the determinant/Klein form on the selected commutative coordinate
   readout is induced from the full noncommutative chiral algebra, rather than
   replacing the noncommutative problem by coordinates.

7. **Motivic/split-quaternion bridge.**
   Formalize the relevant split-composition-algebra cell-structure facts if
   the local thesis PDF is to support more than vocabulary.

## 6. Minimal Execution Plan

1. Add `lean/InfoGeometry/Projective/KleinLogTimeBridge.lean`.
2. Import only owner files:
   - `InfoGeometry.Projective.KleinQuadricTime`
   - `InfoGeometry.Projective.ModularMonodromyClock`
   - optionally `InfoGeometry.Canonical.TimeAsWindingMonodromy3D`
3. Define explicit dictionary/certification structures.
4. Prove readback lemmas only:
   - barrier radial Hessian equals `kleinDLogAlong`;
   - local winding period equals `2*pi*i`;
   - dictionary implies square-zero parabolic generator.
5. Keep global/physical claims as named assumptions or debt.
6. Verify with:

```bash
lake env lean lean/InfoGeometry/Projective/KleinLogTimeBridge.lean
python3 formalizations/chiral_causal_cone_time_witness.py
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Projective.All
rg "\bsorry\b|admit|axiom|: True := by|theorem .*: True|unsafe" \
  lean/InfoGeometry/Projective/KleinLogTimeBridge.lean
```

## 7. Gatekeeping Rule

The next lane must not turn:

- `circleIntegral_one_div` into a global physical-time theorem;
- `timeCohomology_eq_two_pi_I` into a Tomita-Takesaki theorem;
- `kleinBarrierHessian_radial_left` into full self-concordance;
- `Splus_det_zero`/`Sminus_det_zero` into a theorem about all massless fields;
- `exp(2*pi*i*n)=1` into a statement that no phase information exists;
- computational witness output into Lean proof authority.
