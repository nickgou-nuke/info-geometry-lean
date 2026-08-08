# Categorical Infrastructure Map

This map records theorem-honest status for categorical, braid, quotient, and
non-orientable topology infrastructure in the current `InfoGeometry` proof
spine.

## Braid Ideal Descent & Unified Field Algebras

Files:

- `proofs/BraidIdealDescent.lean`
- `proofs/ArtinCentralizerMonodromy.lean`
- `proofs/ArtinMonodromyPin55.lean`

Mathematical status:

- **VERIFIED INTERFACE / FINITE ANCHORS**
  - `tauL` and `tauR` are concrete tensor-product linear maps built from
    `TensorProduct.assoc`, `TensorProduct.comm`, and `TensorProduct.map`.
  - `IsLeftTauIdeal` and `IsRightTauIdeal` formalize the quadratic
    Borowiec--Marcinek / Medina Sánchez--Dakić descent conditions.
  - `qCrossMap` formalizes the q-scaled swap `C_q(η⊗x)=q • (x⊗η)`.
  - `qCrossMap_tmul` proves its action on pure tensors.
  - `ArtinCentralizerMonodromy` models the finite centralizer shadow `{I,-I}`.
  - `adjacent_artin_monodromy` and `separated_artin_monodromy` prove Artin
    moves preserve the centralizer monodromy.
  - `adjacent_artin_hits_negI` and `separated_artin_hits_I` identify odd/even
    Artin winding with `-I`/`I`.
  - `oddUnitRootOfNegI` and `evenUnitRootOfI` record n-fold root behavior in the
    two-sign centralizer.
  - `fullTwist_central_trivial` proves the positive full twist has trivial
    `{I,-I}` parity monodromy because `n(n-1)` is even.
  - `ArtinMonodromyPin55` gives a matrix-valued bridge into the existing
    spinor monodromy and Clifford(5,5) anomaly anchors.
  - `spinorHalfTwist_twofold_root` proves the spinor half-twist is a two-fold
    root of the centralizer landing at `-I`.
  - `negative_centralizer_root_closes` proves any negative centralizer root
    closes after `2n` windings.
  - `artin_spinor_monodromy` reuses the existing adjacent Artin relation in the
    uniform spinor monodromy channel.
  - `artin_monodromy_pin55_synthesis` packages the spinor braid relation,
    centralizer roots, Clifford(5,5) factor dimension, and anomaly-index zero
    theorem together with the TKK/Pin/O socket fields.

Socket status:

- `YangBaxterIdealDescentSocket` records the hard theorem boundary:
  Yang--Baxter/PBW coherence plus left/right ideal stability imply quotient
  exchange descent.
- `Pin55O55TKKCentralizerSocket` records the geometric theorem boundary:
  the actual TKK closure with Pin(5,5)/O(5,5) action has exactly the two-sign
  centralizer modeled by the finite Artin monodromy anchor.
- `TKKPin55ClosureSocket` records the parallel matrix/spinor theorem boundary:
  TKK closure, `Pin(5,5) → O(5,5)`, split-form preservation, and centralizer
  winding are supplied as explicit socket hypotheses.

The full theorem "Yang--Baxter compatibility implies arbitrary quadratic ideal
stability" is not asserted as proved; it remains explicit socket data.

## Non-Orientable Spacetime & Trifactor Projectors

Files:

- `proofs/SuperBerezinianKlein.lean`
- `proofs/GlideSymmetricInvariant.lean`
- `proofs/CubicJordanPeirceDecomposition.lean`
- `proofs/GohbergKreinIndex.lean`
- `proofs/klein_metriplectic_flow.py`

Mathematical status:

- **FULLY PROVED FINITE ANCHORS**
  - `trifactor_partition_of_unity`
  - `trifactor_plus_minus_orthogonal`
  - `triPlus_idempotent`
  - `triZero_idempotent`
  - `pgGlide_sq`
  - `hamiltonian_preserves_plus_eigenspace`
  - `hamiltonian_preserves_minus_eigenspace`
  - `Pcanonical_is_tripotent`
  - `sample_nonzero`
  - `ccw_liftedQuarterSum`
  - `cw_liftedQuarterSum`
  - `finiteGKIndex_ccwLoop`
  - `finiteGKIndex_cwLoop`
  - `klein_doubled_sheet_index_cancels`

Socket status:

- Full `Pin(5,5)` / `O(5,5)` spinor characteristic-polynomial analysis,
  Painlevé asymptotics, Gohberg--Krein spectral-flow index, and full
  Albert/TKK representation classification remain sockets.

### Painlevé-Like Exceptional Point Stabilization

Files:

- `proofs/visualize_painleve_cutoff.py`
- `proofs/painleve_transition_stabilization.csv`
- `proofs/painleve_transition_stabilization.png`

Mathematical status:

- **NUMERICAL WITNESS, NOT A PROOF**
  - The Python module simulates a finite-dimensional non-Hermitian/Klein-twist
    toy spectral flow near exceptional points.
  - It compares the divergent bosonic barrier `-log |det A|` with a
    Super-Berezinian-style stabilized barrier `-log |SBer|`.
  - Current run:
    - max unregulated barrier: `34.538776`
    - max SBer-style barrier: `6.992944`
  - This supports the cutoff intuition behind the finite Lean anchors in
    `InformationGeometricCutoff.lean` and `SuperBerezinianKlein.lean`.

### Finite Gohberg--Krein / EP Winding Index

Files:

- `proofs/GohbergKreinIndex.lean`

Mathematical status:

- **FULLY PROVED FINITE ANCHORS**
  - `sample_nonzero` proves the four determinant phase samples stay away from
    the exceptional determinant zero.
  - `finiteGKIndex_ccwLoop` proves the counterclockwise EP loop has index `1`.
  - `finiteGKIndex_cwLoop` proves the reversed loop has index `-1`.
  - `klein_doubled_sheet_index_cancels` proves that a Klein-doubled pair of
    oppositely oriented sheets has net index `0`.

Socket status:

- `GohbergKreinAnalyticSocket` records the analytic theorem boundary: a genuine
  Fredholm/non-Hermitian operator family must identify analytic index, spectral
  flow, and determinant winding.
- A rigorous Painlevé III asymptotic theorem, non-Hermitian spectral-flow
  theorem, and full Gohberg--Krein topological index theorem remain sockets.

## Dirac/Krein / Modular-Souriau Bridge

Files:

- `proofs/DiracKreinMetriplectic.lean`
- `proofs/dirac_krein_metriplectic.py`

Mathematical status:

- **FULLY PROVED FINITE ANCHORS**
  - `diracAdjoint2_involutive`
  - `bogoliubov2_det`
  - `bogoliubov2_preserves_krein`
  - `bogoliubovBarrier2_zero`
  - `souriau_rest_norm_pos`

Socket status:

- Tomita--Takesaki modular conjugation, Souriau temperature-vector geometry,
  q-Fock modular pairings, and full metriplectic dynamics are represented as
  explicit sockets.

## Furey Charge Quantization

Files:

- `proofs/FureyCharges.lean`
- `proofs/ColorCARStandardModel.lean`

Mathematical status:

- **Finite algebraic layer proved:** `FureyCharges.fureyNumber_idempotent`
  reuses the existing triple-CAR number projectors from
  `ColorCARStandardModel`.
- **Charge spectrum proved:** `FureyCharges.fureyOccupationCharge_spectrum`
  proves the positive minimal-ideal scalar readout
  `q(w) = #{i | w i = true}/3 ∈ {0, 1/3, 2/3, 1}` by finite Boolean case
  analysis.
- **Theorem-honest boundary:** this layer defines Furey charges in the existing
  CAR vocabulary; it does not claim the full `SU(3)` color derivation,
  conjugate ideal, or complete Standard Model extraction.

## Operator-Algebra Linear Maps

Files:

- `proofs/GoutevTonevPrinciple.lean`
- `proofs/RelativeModularStateDikin.lean`
- `proofs/relative_modular_state_dikin.py`

Mathematical status:

- **Canonical Lean convention proved:** scalar readouts on a complex operator
  algebra are `A →ₗ[ℂ] ℂ`, and complex-linear superoperators are
  `A →ₗ[ℂ] A`.
- **Finite algebraic anchors:** `leftMulLinear`, `rightMulLinear`, and
  `commutatorLinear` prove that left multiplication, right multiplication, and
  the commutator `x ↦ K*x - x*K` are complex-linear maps on the operator
  algebra.
- **Readout rule:** `readout_comp_operator` records that applying a state after
  a superoperator is ordinary `LinearMap.comp`.
- **Important boundary:** `algebra_linear_selfmap_determined_by_one` proves
  that a map `A →ₗ[A] A` is determined by `T 1`, so physical superoperators
  should usually be `ℂ`-linear, not `A`-linear.
- **Relative modular state layer:** `RelativeModularStateDikin.lean` formalizes
  a state socket `ω : A →ₗ[ℂ] ℂ`, identity gauges `ω(OP - 1) = c`, the complex
  operator Bregman remainder `expOp(εK)-1-εK`, and the Taylor/Dikin readout
  `(ε²/2)ω(K²) + ω(R₃)`.
- **Finite witness:** `relative_modular_state_dikin.py` verifies the same
  identities for a concrete `2×2` vector state `ω(A)=⟨e₀,Ae₀⟩`.

Socket status:

- Boundedness, continuity, positivity, C*-state structure, and analytic modular
  dynamics remain extra hypotheses unless separately instantiated with
  `ContinuousLinearMap`, C*-algebra, and state data.
- Full Tomita--Takesaki relative modular theory, normality/ultraweak
  continuity, positive self-adjoint unbounded operators, and logarithm/exponential
  functional calculus remain explicit socket data.

## Cramer-Rao Weyl Phase-Volume Rescaling

Files:

- `proofs/HestenesCuntzPhaseSpace.lean`
- `proofs/BogoliubovWeylChemicalPotential.lean`
- `proofs/RescaledPhaseVolumeCanonical.lean`
- `proofs/weyl_cramer_rao_rescaling.py`

Mathematical status:

- **Finite Weyl layer:** `FiniteWeylPair` records exact finite clock-shift data
  `P X = q X P` and `q^N = 1`; finite raw CCR remains trace-obstructed.
- **Cramer-Rao action bit:** `cramerRaoPhaseAction cr` is the minimal
  phase-volume/action pixel `MinimalPhaseSpaceVolume cr = I^-1`, with positivity
  inherited from `CramerRaoQuantumBound`.
- **Canonical rescaling socket:** `CanonicalRescalingCertificate` proves that a
  calibrated abstract/infinite pair rescales to
  `[X,P] = i * cramerRaoPhaseActionC cr * 1`.
- **Bogoliubov/Weyl gauge:** `framePhaseActionGauge` records the q-clock action
  pixel and its chemical-potential shift law.
- **Finite witness:** `weyl_cramer_rao_rescaling.py` verifies finite
  clock-shift Weyl relations modulo `q^N-1` for `N = 2..7`, the rescaled
  commutator, and the Dikin/Cramer-Rao identity `h_eff * H_Dikin = 1`.

Socket status:

- The Dikin/Hessian/Itakura-Saito parameter-base geometry is represented by
  `OperatorItakuraSaitoDikinBase`; full analytic convexity, self-concordance,
  and infinite CCR realization remain explicit sockets.

## Bogoliubov--SU(3)--Parafermion Weld Graph

Files:

- `proofs/BogoliubovWeylChemicalPotential.lean`
- `proofs/SupergradedCuntzBdG.lean`
- `proofs/GellMannSU3.lean`
- `proofs/ColorCARStandardModel.lean`
- `proofs/BogoliubovSU3ParafermionWeld.lean`
- `proofs/BogoliubovSU3ParafermionProofChain.lean`
- `proofs/WeylSU3ColorSymmetry.lean`
- `proofs/GellMannParafermionSolder.lean`
- `proofs/ParafermionIdentityRealization.lean`
- `proofs/CantorBoundaryCuntzFamily.lean`
- `proofs/CuntzBoundarySolderRealization.lean`
- `proofs/cuntz_boundary_solder_realization.py`
- `proofs/WeylSolderedParafermionSymmetry.lean`
- `proofs/BogoliubovBraidGraphWeld.lean`
- `proofs/SU3LoopBraidCuntzBoundary.lean`
- `proofs/SU3LoopBraidDuality.lean`
- `proofs/HolographicGaugeSymmetryUniqueness.lean`
- `proofs/GravitationalQuantumBraidDuality.lean`
- `proofs/gravitational_quantum_braid_duality.py`
- `proofs/SUNQuantumBraidDuality.lean`
- `proofs/sun_quantum_braid_duality.py`
- `proofs/tools/ExtractGraph.lean`
- `proofs/tools/lean_graph/DumpLeanGraph.lean`
- `proofs/SpectralCPTKleinBottle.lean`
- `proofs/spectral_cpt_klein_bottle.py`

Mathematical status:

- **Bogoliubov q-clock:** `frame_affine_parameter` reuses
  `frameWeylQ_eq_qRapidity_logClock`, so the inertial/chemical-potential frame
  supplies the affine deformation scalar.
- **Even color sector:** `frame_affine_even_even_lie` proves the q-affine
  superbracket is undeformed on even-even matrix inputs.
- **Concrete SU(3) anchors:** `frame_affine_gl1_gl2`,
  `frame_affine_gl1_gl3`, and `frame_affine_gl3_gl8_commutes` reuse the
  Gell-Mann commutator witnesses.
- **BdG parafermion lane:** `bdgParafermionPlus4_sq` packages the four
  `bdgMajoranaPlus` generators and proves their Hamiltonian-atom square.
- **Furey CAR connection:** `ColorParafermionBraidingSocket` now carries a
  `StandardModelColorSocket` and a proof that its generation is the canonical
  `fureyGeneration`, closing the previously missing graph edge to
  `ColorCARStandardModel`.
- **SU(3) action proof-chain:** `su3_color_action_all_commutators` transports
  all 16 finite Gell-Mann commutators to `colorLieAction4`; this discharges the
  socket's `respectsSU3Commutator` field when the field is instantiated with the
  corresponding color-action commutator proposition.
- **Theorem-backed socket:** `theoremBackedColorParafermionBraidingSocket`
  instantiates `ColorParafermionBraidingSocket` with
  `respectsSU3Commutator := ∃ h, h = su3_color_action_all_commutators ψ`, uses
  `frameBraidingPhase_eq_frameWeylQ` for the braiding phase, preserves the
  BdG/Majorana square lane, and ties Furey CAR compatibility to
  `car_submodule_is_left_tau_ideal`.
- **S₃ Weyl symmetry:** `WeylSU3ColorSymmetry.lean` proves that conjugation by
  involutive permutation matrices preserves Lie commutators.  The central
  transport theorem `weylAct_transport` moves any seed identity
  `[A,B] = c • C` through the Weyl action, and
  `weyl_transport_to_colorAction` descends transported identities to
  `colorLieAction4`.
- **Parafermion soldering:** `GellMannParafermionSolder.lean` defines a
  realization socket `ParafermionRealization`, the solder map
  `gellMannParafermionSolder`, and proves that the soldered action respects
  matrix multiplication, commutators, singlet neutrality, and the verified
  SU(3) table on realized parafermion lanes.
- **Realization closure:** `ParafermionIdentityRealization.lean` supplies
  concrete algebraic inhabitants for the realization socket: `idRealization`
  for `CuntzAlg` acting on itself and `cuntzFamilyRealization` from any
  algebraic `CuntzFamilyOn V` evaluated at a seed vector.  It also records the
  `CantorBoundaryCuntzFamily` UHF boundary socket and resolves the local
  `CuntzAlg` typeclass diamond with an explicit `Ring` instance.
- **Cantor-boundary Cuntz family:** `CantorBoundaryCuntzFamily.lean` defines
  the infinite four-symbol boundary, creation/annihilation shift operators
  `cuntzS`/`cuntzT`, proves exact algebraic Cuntz relations
  `TᵢSⱼ = δᵢⱼI` and `Σᵢ SᵢTᵢ = I`, and builds `c4Realization`.
- **Boundary solder route:** `CuntzBoundarySolderRealization.lean` bundles the
  identity route, universal Cuntz-family route, concrete Cantor-boundary route,
  Gell-Mann soldering, SU(3) commutator preservation, and Weyl transport on
  Cantor-boundary realized lanes via
  `cuntz_boundary_solder_realization_synthesis`.
- **Realization-routes capstone:** `GellMannParafermionRealizationRoutesSynthesis.lean`
  provides the front-door theorem
  `gellmann_parafermion_realization_routes_synthesis`, bundling 13 conjuncts:
  identity realization recovers the BdG spinor and soldered `colorLieAction4`,
  universal Cuntz-family lifts preserve the chosen `S`/`T` operators, the
  Cantor-boundary Fock route satisfies the algebraic Cuntz relations and SU(3)
  table, `swap12`/`swap23` Weyl transport acts on soldered Cantor-boundary
  lanes, the concrete `[λ₁,λ₂]=2iλ₃` transport holds, and the Bogoliubov
  chemical-potential braid phase shift is included on the identity route.
- **Soldered Weyl transport:** `WeylSolderedParafermionSymmetry.lean` directly
  welds the S₃ Weyl transport theorem to the Gell-Mann-to-parafermion solder
  map.  `weyl_soldered_parafermion_transport` proves that any transported seed
  commutator acts correctly on soldered parafermion lanes, with `swap12` and
  `swap23` specializations and concrete `[λ₁,λ₂]=2iλ₃` examples.
- **SU(3) braid/loop boundary socket:** `BogoliubovBraidGraphWeld.lean` proves
  the q-scaled color braid action satisfies the Artin `B₃` relation, agrees
  with the existing adjacent-transposition `S₃` braid skeleton, and feeds the
  same Bogoliubov q-clock into the Yang--Baxter q-swap.  `SU3LoopBraidCuntzBoundary.lean`
  adds finite loop-mode lifts of the seed Gell-Mann commutators and bundles the
  checked braid spine while keeping loop-group `L(SU(3))`, DHR braid statistics,
  quantum `SU_q(3)`, and Cuntz--Krieger boundary realization as explicit socket
  fields.
- **Cantor-loop gauge fusion:** `SU3LoopBraidDuality.lean` adds the finite
  `3+1` lane gauge action `cantorLoopGaugeStep4` and proves that q-scaled color
  braids transport local gauge weights by the same color permutation.  Invariant
  local weights commute exactly with the braid, giving a checked finite
  semidirect-product kernel for `Map(Cantor, SU(3)) ⋊ B₃`.
- **Holographic gauge uniqueness socket:** `HolographicGaugeSymmetryUniqueness.lean`
  bundles the finite forcing chain: loop-mode Gell-Mann commutators, q-color
  Artin braids, Yang--Baxter q-swap, `Cl(5,5)` zero split-anomaly index, and
  CPT/Hill--Wheeler averaging onto `Re(s)=1/2`.  The actual uniqueness theorem
  for the completed boundary gauge shadow remains an explicit socket.
- **Gravitational quantum braid capstone:** `GravitationalQuantumBraidDuality.lean`
  bundles the verified q-clock identity `frameWeylQ = qRapidity(frameWeylLogClock)`,
  Unruh scale law `2πT_U=a`, zero-acceleration `T_U=0`, algebraic Cuntz
  relations on `O₄`, and Weyl/Artin braid signatures.  Its SymPy witness checks
  the matching finite matrix and scalar identities.
- **SU(N) generalization:** `SUNQuantumBraidDuality.lean` replaces the fixed
  `3+1` color/singlet lanes by `(Fin N -> V) × V`, proves q-scaled braid
  Artin transport from any supplied permutation Artin relation, proves
  Cantor-local gauge covariance and invariant-weight commutation for every `N`,
  and records a generic algebraic `O_(N+1)` Cuntz-family package.  The SymPy
  witness checks adjacent braid windows, distant commutation, gauge covariance,
  invariant commutation, `|S_N| = N!`, and the q-clock shift for `SU(2)` through
  `SU(7)`.
- **Topological color crystal:** `TopologicalColorCrystalFormal.lean` records
  the theorem-honest Bott/Weyl/Klein/Bloch reinterpretation.  It proves finite
  Bott translations by `2` and `8`, the positive Cartan `(λ₃,λ₈)` Weyl chamber
  membership rule, the integer Brillouin-zone glide fixed-line theorem
  `kleinGlideBZ k = k ↔ k.2 = 0`, the CPT/Hill--Wheeler fixed line
  `(cptHillWheelerAverage s).re = 1/2`, and the Bloch/current mode-addition
  commutator.  `TopologicalColorCrystal.lean` is now a checked wrapper around
  these finite facts, and `topological_color_crystal_formal.py` mirrors them
  symbolically.
- **Spectral CPT Klein bottle:** `SpectralCPTKleinBottle.lean` makes the
  non-orientable correction explicit on finite spectral-cylinder coordinates
  `(σ,t)`.  It proves thermal imaginary-time translations are additive, the CPT
  glide `g(σ,t)=(1-σ,t)` is involutive, `g` commutes with thermal
  periodicity, `g` fixes exactly the core line `σ=1/2`, and conjugating a scale
  translation by `g` inverts it: `g a g⁻¹ = a⁻¹`.  Its synthesis theorem
  bundles that Klein-bottle word with the CPT/Hill--Wheeler critical-line
  projection, the Möbius `J/Γ` commutation atom, the `Pin(5,5)` zero anomaly
  witness, and explicit quotient-topology sockets.  The SymPy witness mirrors
  the same coordinate identities.

Graph status:

- `ExtractGraph.lean` and `DumpLeanGraph.lean` now include the new Weyl,
  modular, gauge, colimit, Bogoliubov, SU(3), and ColorCAR prefixes.
- The rebuilt environment graph has 5002 declarations; the weld/proof-chain has edges into
  `BogoliubovWeylChemicalPotential`, `SupergradedCuntzBdG`, `GellMannSU3`,
  `ColorCARStandardModel`, `AlgebraicCuntzQuotient`, and the explicit
  `BogoliubovSU3ParafermionProofChain`, `WeylSU3ColorSymmetry`,
  `GellMannParafermionSolder`, `ParafermionIdentityRealization`, and
  `CantorBoundaryCuntzFamily`, `CuntzBoundarySolderRealization`, and
  `WeylSolderedParafermionSymmetry`, and
  `GellMannParafermionRealizationRoutesSynthesis`, `BogoliubovBraidGraphWeld`,
  `SU3LoopBraidCuntzBoundary`, `SU3LoopBraidDuality`,
  `HolographicGaugeSymmetryUniqueness`, and
  `GravitationalQuantumBraidDuality`, `SUNQuantumBraidDuality`, and
  `TopologicalColorCrystalFormal`, and `SpectralCPTKleinBottle` witnesses.

Socket status:

- The parafermion realization boundary is closed for the algebraic identity
  and algebraic Cuntz-family lift cases.  The Cantor-boundary shift family is
  now explicit algebraically on functions over infinite four-symbol sequences;
  C⋆/norm completion and Hilbert-space analytic structure remain separate
  socketed/interpretive layers unless instantiated.
- The finite color-braid, Cantor-local gauge covariance, and Yang--Baxter spine
  are checked, along with the finite Unruh/q-clock and algebraic `O₄` Cuntz
  relation anchors.  Full loop-group conformal nets, DHR superselection theory,
  quantum `SU_q(3)`/`SU_q(N)` C*-algebra construction,
  Nagy/Kazhdan--Lusztig equivalences, and Cuntz--Krieger realization are socketed
  analytic/operator-algebraic layers unless separately formalized.
- The Bott-crystal, Weyl-Brillouin, Klein-bottle, and Bloch-wave language is
  checked only at the finite algebraic/glide/loop-mode/spectral-cylinder level
  listed above.  Analytic Bott equivalences, K-theory band classification,
  Bloch spectral theorem, and global Klein-bottle quotient topology remain
  explicit sockets.

## Primon / Riemann Spectral Boundary

Files:

- `proofs/ArithmeticHamiltonianZeta.lean`
- `proofs/PrimonSuperThermodynamics.lean`
- `proofs/RiemannHypothesis.lean`
- `proofs/MajoranaPrimonSpectralBridge.lean`
- `proofs/PrimonHilbertPolyaSeparation.lean`
- `proofs/PrimonBosonFermionDuality.lean`
- `proofs/PrimonCoarseGraining.lean`
- `proofs/PrimonCoarseGrainedHilbertPolyaPotential.lean`
- `proofs/JaynesLDDPGNSColimit.lean`
- `proofs/ContinuumAsColimitCounting.lean`
- `proofs/CurryHowardLambekColimit.lean`

Mathematical status:

- **Primon thermodynamic Hamiltonian:** `ArithmeticHamiltonianZeta.lean`
  proves the finite arithmetic dictionary: basis state `|n⟩` has energy
  `log n`, integer multiplication adds energies, Boltzmann weights
  `exp(-β log n)` agree with Dirichlet weights `n^{-β}`, and finite
  arithmetic traces equal finite zeta traces.  This is the checked
  thermodynamic/Zeta partition route.
- **Cuntz-BdG Majorana atom:** `MajoranaPrimonSpectralBridge.lean` reuses the
  proved `γ₁`-style facts from `SupergradedCuntzBdG`: the Majorana generator is
  self-adjoint and its square is the positive Hamiltonian atom.  This is kept
  separate from the Hilbert--Pólya zero operator.
- **Boson/graded-sector cancellation:** `PrimonSuperThermodynamics.lean`
  proves finite-cutoff identities for prime modes: the bosonic partition is
  the reciprocal of the graded/super partition where nonzero, and the total
  CPT-graded finite observable has unit partition and zero free/internal
  energy and entropy.
- **Hilbert--Pólya socket:** `RiemannHypothesis.lean` defines
  `hilbert_polya_hamiltonian Z` as a schema whose real spectrum parametrizes
  the nontrivial zeros as `1/2 + iγ`, and proves
  `hilbert_polya_hamiltonian_implies_RH`.  The self-adjoint analytic operator
  realizing this schema is not constructed in the finite Lean layer.
- **Separation certificate:** `PrimonHilbertPolyaSeparation.lean` proves that
  finite Primon/Fock heat traces equal finite zeta partial sums, prime-crystal
  potential coefficients are `log p`, an independent HP spectral datum implies
  RH, and reciprocal/graded-sector singularities are denominator-zero facts.
  Its synthesis theorem explicitly routes any bridge through separate
  potential/scattering/reciprocal-sector data instead of identifying spectra.
- **Boson/Möbius finite duality:** `PrimonBosonFermionDuality.lean` proves the
  finite single-prime identity
  `Z_K^boson(p,β) * (1 - p^{-β}) = 1 - p^{-(K+1)β}`, the
  fermion/Möbius product `(1+x)(1-x)=1-x²`, positivity of finite bosonic cuts,
  the Hagedorn `β=0` zero of the Möbius factor, and the CPT fixed-line
  dictionary.
- **Coarse-graining/RG finite layer:** `PrimonCoarseGraining.lean` packages the
  finite truncation error, vacuum cut, RG step adding one occupation mode, and
  Hagedorn boundary.  Asymptotic convergence and Lee--Yang condensation remain
  socketed/interpretive beyond these finite identities.
- **Coarse-grained HP potential socket:** `PrimonCoarseGrainedHilbertPolyaPotential.lean`
  defines finite prime-crystal spikes, smoothed finite potentials
  `Σ log(p) K_β(x-log(p))`, finite RG cuts, and an effective HP potential
  socket.  The theorem proves finite-cut equality to the coarse sum and shows
  that any RH consequence still flows through the separate HP datum and explicit
  thermodynamic/CPT socket witnesses.
- **Jaynes/LDDP/GNS colimit layer:** `JaynesLDDPGNSColimit.lean` proves finite
  Jaynes relative entropy vanishes against the same reference density,
  relative inclusions preserve reference expectations, a GNS-like vacuum
  expectation equals the reference state, and the UHF cylinder relation
  `cylinder (n+1) (diagEmbedSucc n f) = cylinder n f` gives the checked
  one-step `cut = fractal` algebraic rule.
- **Continuum as colimit of counting:** `ContinuumAsColimitCounting.lean`
  makes the finite-counting content explicit for both the binary UHF spine and
  the four-lane Cuntz/Cantor boundary.  It proves `|BitWord n| = 2^n`,
  `|FourWord n| = 4^n`, successor refinement multiplies the count by `2` or
  `4`, the Jaynes/LDDP entropy of the finite counting reference relative to
  itself is zero, binary and four-lane cylinder observables are unchanged by
  successor refinement, and GNS-like expectations are reference-state readouts.
  This is the checked categorical LDDP kernel behind the statement that the
  continuum is accessed as a compatible colimit of finite counts, not as an
  absolute background set.
- **Curry--Howard--Lambek colimit spine:** `CurryHowardLambekColimit.lean`
  records the finite Lean kernel of the logic/type/category dictionary:
  implication elimination as function application, conjunction introduction as
  product pairing, universal elimination as dependent-function specialization,
  and existential introduction as dependent-pair construction.  Its synthesis
  theorem bundles those checked CHL rules with the four-lane `4^n` counting
  law, fourfold successor refinement, Jaynes/LDDP reference entropy zero,
  four-lane `cut = fractal` cylinder compatibility, GNS reference expectation,
  CPT/Hill--Wheeler averaging onto `Re(s)=1/2`, and explicit socket witnesses
  for the larger categorical semantics.
- **CPT critical line:** both `RiemannHypothesis.lean` and
  `MajoranaPrimonSpectralBridge.lean` prove the fixed-line dictionary for the
  spectral involution/critical damping line `Re(s)=1/2`.

Boundary:

- Do not conflate the Primon thermodynamic Hamiltonian with the
  Hilbert--Pólya candidate.  The Primon Hamiltonian supplies the arithmetic
  `log n`/`log p` energies and finite zeta-trace dictionary; the Riemann-zero
  ordinates belong to the auxiliary Hilbert--Pólya spectral schema.
- Lee--Yang condensation, prime-crystal scattering resonances, RG attractors,
  thermodynamic coarse-graining limits, Wu--Sprung/Berry--Keating potential
  identification, GNS Hilbert-space completion, and analytic continuation of
  the reciprocal sector are physical/analytic interpretations unless
  separately formalized as analytic theorems.  Current checked content covers
  the finite algebraic identities, finite counting/reference-state laws,
  compatible cylinder-colimit rules, basic CHL term rules, and socket
  boundaries.  Full locally cartesian closed category semantics, actual
  adjunctions for dependent quantifiers, initial-algebra/final-coalgebra
  semantics, and categorical colimit universal properties remain explicit
  sockets unless separately proved.

## Hill--Wheeler Projection / It From Bit

Files:

- `proofs/HillWheelerProjection.lean`
- `proofs/HillWheelerUniversalProjection.lean`
- `proofs/hill_wheeler_universal_projection.py`
- `proofs/hill_wheeler_projection.py`

Mathematical status:

- **Projection schema:** `HillWheelerProjection.lean` defines generic
  structures for intrinsic symmetry-broken states, symmetry-restoring
  projection operators, and a Hill--Wheeler-style generalized eigenvalue
  package with Hamiltonian kernel, norm/overlap kernel, projected state, and
  physical spectrum fields.
- **CPT projection theorem:** the checked theorems
  `cpt_as_hill_wheeler_projection` and
  `cpt_fixed_locus_is_physical_spectrum` prove that the spectral CPT map is an
  involution and that its fixed locus is exactly `Re(s)=1/2`.
- **Synthesis theorem:** `it_from_bit_synthesis` bundles the two proved CPT
  facts: `cptSpectralMap (cptSpectralMap s) = s` and
  `cptSpectralMap s = s ↔ s.re = 1/2`.
- **Universal finite projection kernel:** `HillWheelerUniversalProjection.lean`
  proves the diagonal `2×2` generalized secular determinant
  `det(H - E N) = (h0 - E*n0)*(h1 - E*n1)`, finite projector idempotence,
  projector partition of identity, CPT averaging onto `Re(s)=1/2`, definitional
  GNS overlap kernels `N_ab = τ(a*b)`, and UHF cylinder compatibility under the
  finite relative inclusion.
- **GNS/colimit analogues:** the file records `GNSAsHillWheeler`,
  `ColimitAsHillWheeler`, and `ItFromBit` structures as theorem-honest
  carriers for the GNS-vacuum, finite-cut/colimit, and Wheeler-principle
  interpretation.
- **SymPy witnesses:** `hill_wheeler_universal_projection.py` mirrors the
  determinant factorization, a non-diagonal `2×2` determinant audit, projector
  algebra, CPT averaging, finite normalized-trace overlap, and finite UHF
  diagonal embedding average.  `hill_wheeler_projection.py` gives a larger
  illustrative symbolic/numeric witness for CPT, generalized eigenvalues,
  finite-stage convergence, and a two-level mirror-system toy model.

Boundary:

- The repo proves the finite diagonal generalized-eigenvalue kernel, projector
  algebra, CPT critical-line projection, reference-state overlap formula, and
  one-step UHF/cylinder colimit compatibility.  It does not yet solve a realistic
  nuclear Hill--Wheeler generalized eigenvalue problem, construct the analytic
  GNS quotient/completion from the Cuntz algebra, or prove that the full direct
  colimit is literally a Hill--Wheeler projector.  Those identifications remain
  structural sockets/interpretive bridges.

## Projective / Twistor Conformal Closure

Files:

- `proofs/SplitOctonionBraidSU3.lean`
- `proofs/Clifford55AnomalyOSP.lean`
- `proofs/ProjectiveAffineConformalClosure55.lean`
- `proofs/TwistorParafermionBoundary.lean`
- `proofs/CP3CantorGeometricObstruction.lean`

Mathematical status:

- **Split-octonion finite core:** `SplitOctonionBraidSU3.lean` checks the
  `S₃` braid relation, an explicit split-signature null vector, a Zorn
  nilpotent square-zero witness, and the zero-pole determinant of the tripotent
  scale.  The stronger SU(3)/Furey/split-octonion interpretation is carried by
  sockets.
- **Cl(5,5) anomaly arithmetic:** `Clifford55AnomalyOSP.lean` proves the
  dimension factorization `cliffordDim 5 5 = cliffordDim 1 1 * cliffordDim 4 4`,
  the scalar split-index identity `anomalyIndex 5 5 = 0`, and finite OSP/tripotent
  atom laws.  Full conformal anomaly cancellation and CPT stabilization are
  socket fields, not analytic anomaly theorems.
- **Projective affine conformal closure:** `ProjectiveAffineConformalClosure55.lean`
  proves the finite `(4,4) -> (5,5)` null-cone embedding, projective rescaling
  preservation, concrete `Q55`-preserving reflections, and the spectral CPT
  fixed-line equivalence `spectralCPT s = s ↔ s.re = 1/2`.  The full
  `O(5,5)`/`Pin(5,5)` conformal action and Cantor/Cuntz boundary identification
  are represented as sockets.
- **Twistor/parafermion boundary:** `TwistorParafermionBoundary.lean` proves the
  Pauli/paravector determinant formula, the null-cone iff determinant-zero
  dictionary, rank-one spinor dyads as null rays, Cuntz twistor orthogonality
  and partition relations, and the finite chiral/twistor decomposition.  The
  Penrose incidence interpretation, `CP³` projectivization, and identification
  of the Cantor boundary with twistor/projective null space remain socketed.
- **`CP³`/Cantor obstruction and corrected bridge:** `CP3CantorGeometricObstruction.lean`
  records that a literal full geometric/topological equivalence
  `CP³ ≅ Cantor` is obstructed by connectedness: a connected projective model
  cannot be equivalent to a disconnected Cantor model under any map preserving
  connectedness.  It then proves the corrected finite bridge: four nonzero
  homogeneous twistor lane basis elements, Cantor head/prepend lane readout,
  and the exact `O₄` Cuntz relations on the four-symbol Cantor boundary.  The
  valid theorem-honest statement is therefore a symbolic Cuntz resolution of
  the four `CP³` homogeneous twistor lanes, not a global geometric
  homeomorphism/isomorphism.

Boundary:

- It is theorem-honest to say the repo now has checked finite anchors for the
  projective conformal closure: split `(4,4)` data, a `(5,5)` null embedding,
  concrete reflection invariance, determinant/null-cone twistor algebra, Cuntz
  lane orthogonality, and the CPT fixed-line dictionary.
- It is not yet a proved theorem that the Cantor boundary is globally the
  projective null cone of `ℝ^(5,5)`, that `Pin(5,5)` acts as a fully constructed
  double-cover symmetry on that boundary, or that the parafermion lanes are
  globally equivalent to `CP³` Penrose twistor space.  In ordinary topology,
  literal `CP³ ≅ Cantor` is now recorded as obstructed, since `CP³` is connected
  while Cantor space is disconnected/totally disconnected.  The checked bridge
  is symbolic/operator-algebraic: Cantor sequences resolve the four projective
  twistor lanes through the Cuntz shift algebra.

## Policy

Finite algebraic/scalar/matrix claims are proved in Lean.  Numerical or symbolic
experiments are witnesses.  Infinite-dimensional analytic, C*-algebraic,
representation-theoretic, and physical interpretation claims are sockets unless
separately proved.
