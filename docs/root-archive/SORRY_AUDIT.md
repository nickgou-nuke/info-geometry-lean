# Sorry Audit Report

- root: `/home/goutev/repos/info-geometry-lean`
- scanned_root: `/home/goutev/repos/info-geometry-lean/lean`
- files_with_sorry: 159
- total_sorry_hits: 383
- broken_paths_skipped: 0

## Files

### lean/DAG/DisconnectedAudit.lean (24)
- L25: `--   3. sorry_incomplete   : proof uses sorry (debt, not fake root)`
- L35: `category       : String  -- "axiom_contaminated" | "disconnected_island" | "sorry_incomplete" | "unknown"`
- L53: `sorryIncomplete    : Nat`
- L95: `/-- Check if a declaration's proof uses sorry. -/`
- L104: `all.any (fun r => r.toString == "sorryAx" || r.toString == "sorry")`
- L107: `/-- Collect axiom/sorry names from a declaration. -/`
- L118: `if r.toString == "sorryAx" then`
- L119: `axioms := axioms.push s!"sorry:{n.toString}"`
- L191: `let mut sorryCount := 0`
- L231: `"sorry_incomplete"`
- L238: `else if category == "sorry_incomplete" then sorryCount := sorryCount + 1`
- L265: `IO.println s!"[DisconnectedAudit]   sorry_incomplete:   {sorryCount}"`
- L283: `sorryIncomplete := sorryCount`
- L320: `("sorryIncomplete", toJson s.sorryIncomplete),`
- L362: `lines := lines.push s!"|   sorry_incomplete | {s.sorryIncomplete} |"`
- L372: `lines := lines.push "These capstones contain declarations that are axioms or opaques, or that reference sorryAx."`
- L379: `let sorryStr := if d.isSorry then "YES" else "no"`
- L382: `lines := lines.push s!"| `{d.repName}` | {d.sccSize} | {d.declCount} | {axStr} | {sorryStr} | {mlStr} | {mods} |"`
- L405: `let sorryStr := if d.isSorry then "YES" else "no"`
- L407: `lines := lines.push s!"| `{d.repName}` | {d.sccSize} | {d.declCount} | {sorryStr} | {mods} |"`
- L411: `let sorryOnes := payload.disconnected.filter (fun d => d.category == "sorry_incomplete")`
- L412: `if sorryOnes.size > 0 then`
- L415: `lines := lines.push "These capstones use `sorry` in their proofs. The statements might be true"`
- L420: `for d in sorryOnes do`

### lean/InfoGeometry/Probability/HomologicalProbability.lean (16)
- L21: `- `theorem ... := by sorry`  — mathematically stated, analytic proof deferred`
- L1577: `Mechanically verified: no `sorry`.`
- L1771: `Mechanically verified: no `sorry`.`
- L1796: `Mechanically verified: no `sorry`.`
- L1941: `Mechanically verified: no `sorry`.`
- L2122: `Mechanically verified: no `sorry`.`
- L2209: `Mechanically verified: no `sorry`.`
- L2312: `Mechanically verified: no `sorry`.`
- L2355: `Mechanically verified: no `sorry`.`
- L2416: `Mechanically verified: no `sorry`.`
- L2476: `Mechanically verified: no `sorry`.`
- L2492: `Mechanically verified: no `sorry`.`
- L2610: `Mechanically verified: no `sorry`.`
- L2663: `Mechanically verified: no `sorry`.`
- L2677: `Mechanically verified: no `sorry`.`
- L2693: `Mechanically verified: no `sorry`.`

### lean/InfoGeometry/Lint/NonTriviality.lean (14)
- L27: `* transitive axiom audit using `Lean.collectAxioms`, with explicit `sorry` treated as honest closure debt when configured;`
- L57: `/-- Permit explicit `sorry` as honest, visible closure debt. -/`
- L158: `[ "_sorry"`
- L174: `, "sorryProof"`
- L226: `(suspiciousConsts := [``sorryAx])`
- L415: `if ax == ``sorryAx then`
- L418: `state := "honest_sorry"`
- L421: `state := "sorryAx"`
- L424: `if state != "sorryAx" then`
- L434: `if hitDependencyFuelLimit && (state == "clean" || state == "honest_sorry") then`
- L442: `if state == "clean" || state == "honest_sorry" then`
- L480: `if contamState == "honest_sorry" then`
- L535: `("contains_sorry", Json.bool metric.containsSorry),`
- L551: `("reason", if role == "closure_debt" then "honest_sorry_permitted" else if !isProp then "def_eq_protection_required" else "")`

### lean/InfoGeometry/Lint/Pauli.lean (13)
- L11: `/-- Option to control the Pauli sorry linter. -/`
- L12: `register_option linter.pauli.sorry : Bool := {`
- L14: `descr := "report declarations in Canonical namespace depending on explicit sorryAx as visible closure debt"`
- L17: `register_option linter.pauli.sorryAsClosureDebt : Bool := {`
- L19: `descr := "treat explicit sorryAx as permitted closure debt instead of a hard warning; disguised substitutes remain lint targets"`
- L31: `descr := "warn about structures with generic Prop _statement/_sorry field pairs"`
- L51: `linter.pauli.sorry.get (← getOptions) ||`
- L92: `if linter.pauli.sorry.get (← getOptions) then`
- L94: `if axioms.contains ``sorryAx then`
- L95: `if linter.pauli.sorryAsClosureDebt.get (← getOptions) then`
- L96: `logInfo m!"[Pauli/Closure Debt] {declName} explicitly depends on `sorryAx`; permitted as honest closure debt, not eligible for contraction/deletion."`
- L98: `logError m!"[Pauli/Axiom-Surface Seal] {declName} depends on `sorryAx`."`
- L100: `logError m!"[Pauli/Axiom-Surface Seal] {declName} depends on nonstandard `admitAx`; use explicit `sorry` instead of a disguised placeholder."`

### lean/InfoGeometry/Quiver/KoroteevZeitlinMirror.lean (12)
- L126: `sorry`
- L213: `sorry`
- L282: `sorry`
- L293: `sorry`
- L328: `sorry`
- L393: `sorry`
- L410: `sorry`
- L417: `sorry`
- L434: `sorry`
- L452: `sorry`
- L497: `sorry`
- L513: `sorry`

### lean/InfoGeometry/Lint/WitnessLint.lean (11)
- L19: `bar_sorry   : bar_statement`
- L23: `and `True.intro` for `bar_sorry`.  The Lean kernel checks structural`
- L38: `3. there exists a field `g` whose name equals `stem ++ "_sorry"` where`
- L42: `or `*_sorry` has type `Prop` regardless of whether a companion field`
- L71: `/-- True if a string ends with `_sorry`. -/`
- L73: `s.endsWith "_sorry"`
- L76: ``foo_statement` → `foo_sorry`. -/`
- L78: `(statementName.dropEnd "_statement".length).toString ++ "_sorry"`
- L88: `/-- Name of the companion `_sorry` field, if present. -/`
- L96: `- whose leaf name ends in `_statement` or `_sorry`, AND`
- L100: ``stem_sorry` among the structure's fields.  Bare witness fields of type `Prop``

### lean/InfoGeometry/Meta/OwnerTarget.lean (11)
- L30: `sorry -- obligation: fill in the proof`
- L39: `(`#audit_owner_targets`, `sorry_analyzer.py`, graph overlay) can enumerate`
- L43: `A `sorry` in an owner-target proof is machine-visible closure debt.`
- L71: `let mut sorry_decls : Array Name := #[]`
- L86: `if axioms.contains ``sorryAx then`
- L87: `sorry_decls := sorry_decls.push thmName`
- L91: `sorry_decls := sorry_decls.push declName`
- L93: `sorry_decls := sorry_decls.push declName`
- L94: `if sorry_decls.isEmpty then`
- L97: `for d in sorry_decls do`
- L99: `logInfo m!"Owner Target Audit: {proved}/{total} proved, {sorry_decls.size} with closure debt."`

### lean/InfoGeometry/Eval/SorryFillerTest.lean (10)
- L6: `This file contains controlled `sorry` placeholders used as evaluation targets`
- L7: `for the GEPA skill evolution loop. Each theorem has a `sorry` that needs to`
- L19: `sorry`
- L23: `sorry`
- L27: `sorry`
- L31: `sorry`
- L35: `sorry`
- L39: `sorry`
- L43: `sorry`
- L50: `sorry`

### lean/InfoGeometry/Canonical/RealRotorGaussHestenesBridge.lean (9)
- L156: `scalar_i_replaced_by_real_rotor_sorry :`
- L158: `contour_residue_replaced_by_real_gauss_stokes_sorry :`
- L160: `complex_analysis_is_optional_shadow_sorry :`
- L170: `G.scalar_i_replaced_by_real_rotor_sorry`
- L177: `G.contour_residue_replaced_by_real_gauss_stokes_sorry`
- L184: `G.complex_analysis_is_optional_shadow_sorry`
- L203: `rotorReadout_preserves_real_lane_sorry :`
- L230: `B.guard.complex_analysis_is_optional_shadow_sorry`
- L237: `B.rotorReadout_preserves_real_lane_sorry`

### lean/InfoGeometry/OperatorAlgebra/ParabolicClockInClifford.lean (9)
- L17: `instance : Ring ParabolicClockAlg := by sorry`
- L18: `instance : Algebra ℝ ParabolicClockAlg := by sorry`
- L21: `def ε : ParabolicClockAlg := by sorry`
- L23: `property ε_sq_zero : ε * ε = 0 := by sorry`
- L27: `def embed_parabolic_to_Cl11 : ParabolicClockAlg →ₐ[ℝ] CliffordAlgebra (splitQuadraticForm 1) := by sorry`
- L29: `property embed_preserves_nilpotent : (embed_parabolic_to_Cl11 ε) * (embed_parabolic_to_Cl11 ε) = 0 := by sorry`
- L35: `def embed_Cl11_to_Clnn {n : ℕ} (hn : 1 ≤ n) : CliffordAlgebra (splitQuadraticForm 1) →ₐ[ℝ] CliffordAlgebra (splitQuadraticForm n) := by sorry`
- L38: `def embed_parabolic_to_Clnn {n : ℕ} (hn : 1 ≤ n) : ParabolicClockAlg →ₐ[ℝ] CliffordAlgebra (splitQuadraticForm n) := by sorry`
- L44: `∃ (x : CliffordAlgebra (splitQuadraticForm 0)), False := by sorry  -- placeholder`

### lean/InfoGeometry/Quiver/FermiGTIsometry.lean (9)
- L99: `sorry  -- Requires complex differential geometry machinery`
- L111: `sorry  -- Requires Lie derivative machinery`
- L157: `sorry`
- L169: `sorry`
- L177: `sorry`
- L205: `sorry  -- Requires representation theory formalization`
- L224: `sorry`
- L241: `sorry`
- L262: `sorry`

### lean/InfoGeometry/Canonical/MajoranaKitaevSpinorBridge.lean (7)
- L18: `It does not depend on the sorry-equivalent modular spinor layer.`
- L119: `let hplus_sorry := (M.chiralityPolarization.plus).ne_bot_iff.mp hplus_ne'`
- L120: `let ψplus := Classical.choose hplus_sorry`
- L121: `let hplus_witness_spec := Classical.choose_spec hplus_sorry`
- L122: `let hminus_sorry := (M.chiralityPolarization.minus).ne_bot_iff.mp hminus_ne'`
- L123: `let ψminus := Classical.choose hminus_sorry`
- L124: `let hminus_witness_spec := Classical.choose_spec hminus_sorry`

### lean/InfoGeometry/Eval/ClosureDebtTest.lean (7)
- L15: `/-! ## Pattern 1: _True : Prop := by sorry -/`
- L19: `sorry`
- L29: `sorry`
- L35: `sorry`
- L41: `sorry`
- L47: `sorry`
- L53: `sorry`

### lean/InfoGeometry/GrandUnification/SpectralThermalNormalization.lean (7)
- L113: `Mechanically verified: no `sorry`.`
- L145: `Mechanically verified: no `sorry`.`
- L157: `Mechanically verified: no `sorry`.`
- L205: `Mechanically verified: no `sorry`.`
- L221: `Mechanically verified: no `sorry`.`
- L232: `Mechanically verified: no `sorry`.`
- L260: `Mechanically verified: no `sorry`.`

### lean/InfoGeometry/Canonical/FluidCore.lean (6)
- L39: `divergence := sorry`
- L40: `gradient := sorry`
- L41: `laplacian := sorry`
- L47: `divergence := sorry`
- L48: `gradient := sorry`
- L49: `laplacian := sorry`

### lean/InfoGeometry/Canonical/O55FiveGradeCapstone.lean (5)
- L19: `The missing actions [D, v₅] and [D, v₄] are marked as open debt (sorry) but`
- L33: `adjoint actions are proved, and uses sorry for the missing adjoint actions.`
- L77: `D * v4 - v4 * D = -v4 := ⟨sorry, sorry⟩`
- L114: `∧ (D * v5 - v5 * D = -v5   -- sorry`
- L115: `∧ D * v4 - v4 * D = -v4)  -- sorry`

### lean/InfoGeometry/Canonical/PrimeLeeYangLargeDeviation.lean (5)
- L23: ``sorry` debt, not as arbitrary `Prop` fields.`
- L204: `sorry`
- L214: `sorry`
- L223: `sorry`
- L233: `sorry`

### lean/InfoGeometry/Canonical/RelativeDeterminantScatteringSocket.lean (5)
- L10: `unsupported claims are exposed as explicit `sorry` debt, not hidden as arbitrary`
- L53: `sorry`
- L58: `sorry`
- L63: `sorry`
- L68: `sorry`

### lean/InfoGeometry/HilbertTensorProduct/Phase2_HS2Ell2.lean (5)
- L70: `sorry`
- L131: `sorry`
- L202: `sorry`
- L221: `sorry`
- L231: `sorry`

### lean/InfoGeometry/Meta/StrictDef.lean (5)
- L18: `, ``Lean.Parser.Term.«sorry»`
- L31: `"strict {declKind} `{declName}` uses forbidden term syntax (`by`, `sorry`, or `unsafe`) in its type."`
- L34: `"strict {declKind} `{declName}` uses forbidden term syntax (`by`, `sorry`, or `unsafe`) in its value."`
- L252: `s!"strict {declKind} `{declName}` elaborated to an expression containing `sorryAx`."`
- L291: `It accepts only ordinary `def` syntax and rejects tactic blocks, `sorry`, and`

### lean/InfoGeometry/Monster/MonsterMoonshineThermal.lean (5)
- L82: `sorry`
- L139: `sorry`
- L143: `sorry`
- L168: `sorry`
- L247: `sorry`

### lean/InfoGeometry/Quiver/TKKHamiltonian.lean (5)
- L140: `sorry  -- Requires spectral theorem for endomorphisms`
- L164: `sorry  -- Requires diagonalization of H_inc.H_TKK_INC`
- L204: `sorry  -- Requires QQ-system relations`
- L249: `sorry  -- Requires explicit construction with A=73 parameters`
- L264: `sorry  -- Requires case-by-case analysis`

### lean/InfoGeometry/Canonical/DrazinCARColimitBridge_proposal.lean (4)
- L14: `abbrev LimitHilbertSpace (P : CPTDirectLimitGNSPacket) : Type := sorry`
- L17: `abbrev LimitDoubledSpace (P : CPTDirectLimitGNSPacket) : Type := sorry`
- L21: `InfoGeometry.Canonical.CertifiedInverseKernel (LimitDoubledSpace P) := sorry`
- L26: `DrazinFredholmProofBundle (limitCertifiedInverseKernel P) cl11 := sorry`

### lean/InfoGeometry/JordanDecomposition.lean (4)
- L13: `3. `jordanBasis`: algorithmic construction (1 sorry — quotient basis picking)`
- L155: `sorry`
- L161: `sorry`
- L165: `sorry`

### lean/InfoGeometry/Meta/HonestyPolicy.lean (4)
- L15: `- if it does not exist yet, expose the gap explicitly as `sorry` or an`
- L43: `/-- Explicit `sorry` is acceptable only as visible debt. -/`
- L47: `/-- Banner text must not claim certified readback when `sorry` remains. -/`
- L59: `"If a Mathlib-rooted derivation chain is missing, expose the gap explicitly as sorry or an explicit zero-datum. Do not hide debt behind fake witnesses, empty shells, or misleading certification banners."`

### lean/InfoGeometry/Meta/SocketTarget.lean (4)
- L12: `normal `sorry` detection because the law itself is a parameter.`
- L27: `parameters that look clean to `sorry_analyzer.py`.`
- L29: `closure debt — the architectural equivalent of a typed `sorry`.`
- L49: `not check for `sorry` — sockets are *expected* to carry opaque laws.`

### lean/InfoGeometry/Optics/JonesCalculusSpinorLorentz.lean (4)
- L69: `sorry  -- Explicit construction via Pauli matrices`
- L107: `sorry  -- Direct computation with complex norms`
- L113: `sorry  -- Explicit 2:1 homomorphism via sigma matrices`
- L128: `sorry  -- Check det = 1 and M*M† = I`

### lean/InfoGeometry/SelfReference/Shadow.lean (4)
- L42: `| sorryDebt`
- L54: `| ShadowKind.sorryDebt => "sorryDebt"`
- L64: `| ShadowKind.sorryDebt => "explicit sorry in proof body"`
- L165: `| ShadowKind.sorryDebt => 2`

### lean/DAG/ExactProoflessnessAudit.lean (3)
- L189: `let mut sorryCount : Nat := 0`
- L217: `| "blocked.localSorry" => sorryCount := sorryCount + 1`
- L242: `directSorry := sorryCount`

### lean/InfoGeometry/Canonical/SpectralSchurDrazinPenroseHierarchy.lean (3)
- L73: `sorry`
- L79: `sorry`
- L305: `sorry`

### lean/InfoGeometry/Canonical/ThermodynamicChiralGraphCalculus.lean (3)
- L373: `gradient_sorry : G.IsGradientFlow gradientPart`
- L374: `cycle_sorry : G.IsCycleFlow cyclePart`
- L386: `refine ⟨(H.gradientPart, H.cyclePart), ⟨H.gradient_sorry, H.cycle_sorry,`

### lean/InfoGeometry/JordanDecomposition/CyclicNilpotent.lean (3)
- L59: `sorry`
- L111: `sorry`
- L146: `sorry`

### lean/InfoGeometry/KTheory/Dadarlat.lean (3)
- L74: `sorry`
- L156: `sorry`
- L186: `sorry`

### lean/InfoGeometry/Physics/InfoGeoFermi.lean (3)
- L39: `fun ψ => ⟨⁅g0, ψ.state_vector⁆, by sorry⟩`
- L46: `fun ψ => ⟨T ψ.state_vector, by sorry⟩`
- L72: `sorry`

### lean/Agent/CompilerBridgeCore.lean (2)
- L682: `s.endsWith "sorryAx" || s.endsWith "admitAx"`
- L705: `s!"Declaration '{declName}' contains `sorry`."`

### lean/InfoGeometry/Canonical/CognitiveShadow.lean (2)
- L48: `triggerTerms := #["sorry", "proof debt", "hole"]`
- L49: `criticKind := "honest_sorry_triage"`

### lean/InfoGeometry/Canonical/GaugeGroups.lean (2)
- L14: `Dead declarations (`SU2N`, `block_embedding_*`) removed — sorry-equivalent`
- L15: `with zero external consumers. See `reports/dag/sorry-equivalence.md`.`

### lean/InfoGeometry/Canonical/LeeYangAsanoDigest.lean (2)
- L909: ``Analysis.AsanoContractionNative` (no `sorry`).`
- L1090: ``sorry`.`

### lean/InfoGeometry/External/Auto/test_wrapper.lean (2)
- L48: `sorry`
- L52: `sorry`

### lean/InfoGeometry/Instanton/HilbertTwoPoints.lean (2)
- L40: `have h : ( (MVPolynomial (Fin 2) ℚ) ⧸ I ) ≃ₗ[ℚ] (Fin 2 → ℚ) := by sorry`
- L41: `sorry`

### lean/InfoGeometry/Meta/Admission.lean (2)
- L141: `mkAdmissionReason syntheticDecl "trust.sorry" "error"`
- L142: `"declaration depends on `sorryAx`."`

### lean/InfoGeometry/Meta/ShadowLedger.lean (2)
- L6: `The shadow ledger tracks every `:= by sorry` declaration in the repository.`
- L30: `Every `:= by sorry` is a seed for the next evolution cycle.`

### lean/InfoGeometry/Meta/Trust.lean (2)
- L13: `/-- First-pass forbidden axioms beyond explicit `sorryAx` detection. -/`
- L96: `hasSorryAx := axioms.contains ``sorryAx`

### lean/InfoGeometry/OperatorAlgebra/ChiralCompass.lean (2)
- L76: `sorry⟩`
- L85: `sorry`

### lean/InfoGeometry/OperatorAlgebra/SplitOctonions/FureyLadderCAR.lean (2)
- L168: `sorry`
- L174: `sorry`

### lean/InfoGeometry/Physics/A39Mirror.lean (2)
- L30: `sorry`
- L44: `sorry`

### lean/InfoGeometry/Quiver/BetheAnsatzXXZ.lean (2)
- L184: `sorry`
- L201: `sorry`

### lean/InfoGeometry/Sandbox/CliffordFunctorSandbox.lean (2)
- L33: `map_id X := sorry`
- L34: `map_comp f g := sorry`

### lean/InfoGeometry/Topology/BottPeriodicCantorEntropyGraph.lean (2)
- L273: `sorry`
- L280: `sorry`

### lean/InfoGeometry/Topology/CantorCliffordFunctor.lean (2)
- L53: `map_id n := sorry`
- L54: `map_comp {l m n} h_lm h_mn := sorry`

### lean/DAG/EckmannHodge.lean (1)
- L12: `All `sorry` debt is closed. Every theorem is a genuine algebraic proof.`

### lean/DAG/FunctionalGaussJordan.lean (1)
- L17: `All proofs are standard linear algebra — no axioms, no sorry debt.`

### lean/DAG/InfoTreeExtract.lean (1)
- L216: `isSorrySourceScan := refs.contains "sorryAx" || refs.contains "sorry"`

### lean/InfoGeometry/Algebra/CuntzFockRepresentation.lean (1)
- L173: `| `BostConnesAnalytic.lean` | 7+1 | Boltzmann limits, partition function (+1 ground state calculus sorry) |`

### lean/InfoGeometry/Algebra/CuntzRecursiveFermionSystem.lean (1)
- L216: `/-! ## Wedge Actions (sorry-free) -/`

### lean/InfoGeometry/Algebra/HypercomplexTriadMatrix.lean (1)
- L18: `No `sorry`.`

### lean/InfoGeometry/Algebra/NilpotentNonunit.lean (1)
- L11: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Algebra/NoFaithfulAssociativeModel.lean (1)
- L17: `No wrappers. No structures. No `sorry`.`

### lean/InfoGeometry/Algebra/Zorn/Concrete.lean (1)
- L9: `No wrappers. No abstract datum. No `sorry`.`

### lean/InfoGeometry/Algebra/Zorn/ConcreteBarrier.lean (1)
- L18: `No `sorry`.`

### lean/InfoGeometry/Algebra/Zorn/ConcreteComposition.lean (1)
- L15: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Analysis/AsanoRuelleBasicBranches.lean (1)
- L16: `No `sorry`.`

### lean/InfoGeometry/Arithmetic/PolyaHilbertDiracHodgeCantorBridge.lean (1)
- L20: `Plus the internal proof: `SouriauDiracHodgeCoupling` (659 lines, 32 thm, 0 sorry).`

### lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean (1)
- L2070: `Kept as a `Prop` (not a `theorem ... := by sorry`) because this module does not`

### lean/InfoGeometry/Arithmetic/SelfConcordantZetaBarrierProofs.lean (1)
- L6: `No sockets. No certificates. No axioms. No `sorry`.`

### lean/InfoGeometry/Arithmetic/ZetaDihedral.lean (1)
- L15: `No sockets. No certificates. No axioms. No `sorry`.`

### lean/InfoGeometry/AsanoRuelle/AsanoRuelleCounterexample.lean (1)
- L12: `No wrappers. No `sorry`.`

### lean/InfoGeometry/AsanoRuelle/MobiusInversion.lean (1)
- L9: `No placeholders. No `sorry`.`

### lean/InfoGeometry/Automorphic/HeckePurification.lean (1)
- L82: ``Prop`/`sorry` placeholder with a concrete theorem-shaped obligation.`

### lean/InfoGeometry/Canonical/AlgebraicDerivations.lean (1)
- L12: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/AsanoRuelleCounterexample.lean (1)
- L15: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/AsanoRuellePoleExclusion.lean (1)
- L9: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/AsanoRuelleTopologicalEndpoint.lean (1)
- L19: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/BayesianConformalCompression.lean (1)
- L16: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/CantorHaarDiracSea.lean (1)
- L18: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/CartanSuperbracketClosure.lean (1)
- L29: `No `sorry`.`

### lean/InfoGeometry/Canonical/ChiralKKTIsolation.lean (1)
- L11: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/CliffordColimitDynamics.lean (1)
- L53: `sorry -- socket_debt_tag: D14_global_bracket`

### lean/InfoGeometry/Canonical/CliffordWaveletAnalyticBridge.lean (1)
- L17: `No `sorry`.`

### lean/InfoGeometry/Canonical/ConformalSubalgebraDebt.lean (1)
- L8: ``sorry` tokens from the conformal subalgebra without introducing new wrappers.`

### lean/InfoGeometry/Canonical/DepthLogScaleInvariant.lean (1)
- L21: `No `sorry`.`

### lean/InfoGeometry/Canonical/DimensionAgnosticModularKLDivergence.lean (1)
- L7: `remaining fully constructive (no `sorry`).`

### lean/InfoGeometry/Canonical/DrazinAnomalousProjector.lean (1)
- L16: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/FenchelExpLogCore.lean (1)
- L14: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/GeneralizedOperatorChiral.lean (1)
- L9: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/GrandCanonicalSouriau.lean (1)
- L18: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/HestenesKreinModularGeometry.lean (1)
- L780: `sorry`

### lean/InfoGeometry/Canonical/KreinMajoranaZeroModeBlock.lean (1)
- L11: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/LeeYangAsanoMobiusNative.lean (1)
- L25: `No `sorry`.`

### lean/InfoGeometry/Canonical/LeeYangAsanoNativeCore.lean (1)
- L17: `No `sorry`.`

### lean/InfoGeometry/Canonical/LieFenchelQuadratic.lean (1)
- L15: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/LieOrbitAdjointInvariants.lean (1)
- L13: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/LieOrbitInfinitesimal.lean (1)
- L13: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/LieOrbitSymmetryChart2x2.lean (1)
- L9: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/ModularLorentzBoost.lean (1)
- L9: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/ModularSL2R.lean (1)
- L11: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/ModularTensorInduction.lean (1)
- L15: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/OperatorPenroseUnification.lean (1)
- L118: `/-- Junction 5: spinor-modular identification without sorry-equivalent layer. -/`

### lean/InfoGeometry/Canonical/PrimeSUSYVacuum.lean (1)
- L226: `sorry`

### lean/InfoGeometry/Canonical/QuaternionCoaxialOrbit.lean (1)
- L10: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/QuaternionicEmergentGravityFoundation.lean (1)
- L138: `sorry`

### lean/InfoGeometry/Canonical/RindlerWeylDecomposition.lean (1)
- L21: `No placeholders. No `sorry`.`

### lean/InfoGeometry/Canonical/SO3RotationFenchelWitness.lean (1)
- L14: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/SouriauInfinitesimalInvariance.lean (1)
- L8: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/SplitCliffordChiralProjection.lean (1)
- L17: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/SplitCliffordFiniteCurrentObstruction.lean (1)
- L21: `No `sorry`.`

### lean/InfoGeometry/Canonical/SplitCliffordJordanWignerTwoModeCurrent.lean (1)
- L13: `No `sorry`.`

### lean/InfoGeometry/Canonical/SplitCliffordSourceSuperVirasoroFiniteWindow.lean (1)
- L382: `for `J = J_sorry A`, `ψ = psi_sorry B`, and `r = 0`,`

### lean/InfoGeometry/Canonical/SplitCliffordTwoModeTrace.lean (1)
- L11: `No placeholders. No `sorry`.`

### lean/InfoGeometry/Canonical/SplitCliffordTwoModeWick.lean (1)
- L16: `No placeholders. No `sorry`.`

### lean/InfoGeometry/Canonical/SplitCliffordVacuumExpectation.lean (1)
- L15: `No placeholders. No `sorry`.`

### lean/InfoGeometry/Canonical/TomitaBregmanDuality.lean (1)
- L20: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/TomitaFisherMetric.lean (1)
- L17: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/TopologicalGroupIsoExpLog.lean (1)
- L13: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Canonical/ZetaBraneCantorDirac.lean (1)
- L101: `sorry`

### lean/InfoGeometry/Clifford/ConformalReflection55.lean (1)
- L36: `These are **native Lean proofs** — no axioms, sorry, or external certificates.`

### lean/InfoGeometry/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean (1)
- L20: `- All proofs are real — no `trivial`, `axiom`, or `sorry` placeholders`

### lean/InfoGeometry/Clifford/Hestenes1975.lean (1)
- L23: `sorry`

### lean/InfoGeometry/External/Auto/test_noncomm.lean (1)
- L10: `sorry`

### lean/InfoGeometry/Geometry/AmplituhedronFacePoset.lean (1)
- L22: `sorry`

### lean/InfoGeometry/Geometry/BerezinianCayleyVolume.lean (1)
- L75: `strings or `sorryAx`; package their projectors and algebraic laws.`

### lean/InfoGeometry/Geometry/PrimaMateriaThermodynamics.lean (1)
- L86: `sorry -- Proved abstractly using the non-empty, zero-dimensional variety boundary`

### lean/InfoGeometry/HilbertTensorProduct.lean (1)
- L27: `lemma hsNorm_sq_eq (A : H₁ →L[ℝ] H₂) : (hsNorm A)^2 = hsInner A A := by sorry`

### lean/InfoGeometry/HilbertTensorProduct/Phase5_SpectralTheorem.lean (1)
- L81: `sorry`

### lean/InfoGeometry/Lint/SurgeryContract.lean (1)
- L31: `| honest_sorry`

### lean/InfoGeometry/Meta/BridgeTarget.lean (1)
- L44: `if axioms.contains ``sorryAx then`

### lean/InfoGeometry/Meta/ClosureAttribute.lean (1)
- L11: `anchored to the DAG, and free of `sorry` or `admit`.`

### lean/InfoGeometry/Meta/ThermodynamicGEORegulation.lean (1)
- L37: `fitness : ℝ          -- between 0 and 1 (1 = compiles, 0 = sorry)`

### lean/InfoGeometry/ModularVolumePotential.lean (1)
- L375: `sorry`

### lean/InfoGeometry/OperatorAlgebra/AffineCl44CardyEntropy.lean (1)
- L131: `sorry`

### lean/InfoGeometry/OperatorAlgebra/AnomalyTubuleStability.lean (1)
- L239: `sorry`

### lean/InfoGeometry/OperatorAlgebra/ChiralTubuleBoundary.lean (1)
- L305: `sorry`

### lean/InfoGeometry/OperatorAlgebra/LightConeAffineCurrentBridge.lean (1)
- L75: `sorry`

### lean/InfoGeometry/OperatorAlgebra/ParabolicClockInCliffordInfinity.lean (1)
- L79: `∃ (x : CliffordAlgebra (splitQuadraticForm 0)), False := by sorry`

### lean/InfoGeometry/OperatorAlgebra/SugawaraVirasoroComm.lean (1)
- L81: `sorry`

### lean/InfoGeometry/Physics/A31Mirror.lean (1)
- L44: `sorry`

### lean/InfoGeometry/Physics/A73Mirror.lean (1)
- L27: `sorry`

### lean/InfoGeometry/Physics/A75Mirror.lean (1)
- L42: `sorry`

### lean/InfoGeometry/Physics/GammasphereZornMap.lean (1)
- L138: `sorry`

### lean/InfoGeometry/Physics/IsospinMirrorDynamics.lean (1)
- L78: `sorry`

### lean/InfoGeometry/Physics/MeanFieldISB.lean (1)
- L31: `sorry`

### lean/InfoGeometry/Projective/BostConnesZetaIdentity.lean (1)
- L31: `sorry`

### lean/InfoGeometry/Projective/KleinCrossRatioInvariant.lean (1)
- L16: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Projective/KleinQuadric.lean (1)
- L23: `No `sorry`.`

### lean/InfoGeometry/Projective/KleinQuadricIncidence.lean (1)
- L16: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Projective/KleinQuadricPlucker.lean (1)
- L16: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Projective/Quadrics/AffineSlices.lean (1)
- L23: `No `sorry`.`

### lean/InfoGeometry/Projective/SplitOctonions.lean (1)
- L16: `No `sorry`, no `True` placeholders, no fake Freudenthal determinant.`

### lean/InfoGeometry/Projective/SplitOctonions/BektasMatrix.lean (1)
- L14: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Projective/SplitOctonions/ProjectivePolarFiber.lean (1)
- L19: `No `sorry`.`

### lean/InfoGeometry/Projective/SplitOctonions/ProjectivePolarFiberTransport.lean (1)
- L22: `No `sorry`.`

### lean/InfoGeometry/Projective/SplitOctonions/ProjectivePolarInvariant.lean (1)
- L21: `No `sorry`.`

### lean/InfoGeometry/Projective/SplitOctonions/SplitOctonionsColorStabilizer.lean (1)
- L14: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Projective/SplitOctonions/SplitOctonionsLegendre.lean (1)
- L21: `No wrappers. No `sorry`.`

### lean/InfoGeometry/Quiver/HbarOper.lean (1)
- L184: `sorry`

### lean/InfoGeometry/SelfReference/ShadowCone.lean (1)
- L20: `| sorryDebt`

### lean/InfoGeometry/Singular/MoorePenrose.lean (1)
- L12: `It follows the Pauli Protocol: zero sorry, bottom-up derivation, and direct conductivity`

### lean/InfoGeometry/TKK/TKKFramework.lean (1)
- L35: `(isospin_operator c ≠ 0) ↔ (∃ i : Fin 4, c i ≠ 0) := sorry`

### lean/test_measure3.lean (1)
- L3: `def test : MeasureTheory.Measure Bool := ⟨fun _ => 0, by sorry⟩`
