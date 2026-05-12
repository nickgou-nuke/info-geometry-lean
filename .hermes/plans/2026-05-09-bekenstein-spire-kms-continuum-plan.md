# Bekenstein Spire KMS Continuum Implementation Plan

> **For Hermes:** Use subagent-driven-development skill to implement this plan task-by-task.

**Goal:** Climb Spire 1: bridge the new discrete thermodynamic graph calculus into the existing KMS/cocycle/Casini-Bekenstein corridor without promoting unowned continuum claims.

**Architecture:** Treat `ThermodynamicChiralGraphCalculus` as the microscopic owner of finite graph entropy, exact coboundary curvature, discrete no-pumping, and finite-path fluctuation readbacks. Add a narrow translator bridge into `KMSCocycleGeneratorBridge`, then expose continuum-facing readbacks in `YangMillsContinuum`, and finally route a proof-carrying endpoint into `CasiniBekensteinBound`. Do not assert graph-to-continuum limits, KMS analyticity, Yang-Mills curvature equations, or physical Bekenstein closure without explicit owner packets.

**Tech Stack:** Lean 4, Mathlib, existing `InfoGeometry.Canonical.*` modules, locked Lake builds via `tools/infra/run_locked_lake_build.py`.

---

## Current evidence

The following modules already compile under the repository build lock:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.KMSCocycleGeneratorBridge \
  InfoGeometry.Canonical.YangMillsContinuum \
  InfoGeometry.Canonical.CasiniBekensteinBound
```

Result observed: build completed successfully for all three targets.

No `canonical_policy_lint.py` theorem-class findings were printed for these three target files in the filtered run.

## Corridor roles

- Owner/microscopic: `lean/InfoGeometry/Canonical/ThermodynamicChiralGraphCalculus.lean`
- Translator/discrete-to-KMS: `lean/InfoGeometry/Canonical/KMSCocycleGeneratorBridge.lean`
- Coherence/continuum-facing modular surface: `lean/InfoGeometry/Canonical/YangMillsContinuum.lean`
- Capstone/physical bound surface: `lean/InfoGeometry/Canonical/CasiniBekensteinBound.lean`
- Aggregator if new file is introduced: `lean/InfoGeometry/Canonical/All.lean`

Transport-critical comments: comments describing exactness, cocycle generator lift, RN barrier, modular Hamiltonian, and Casini identity are part of the semantic corridor and should not be erased casually.

---

## Task 1: Add a microscopic KMS pairing witness packet

**Objective:** Connect exact finite graph curvature/no-pumping evidence to the existing KMS pairing witness surface as a proof-carrying translator packet.

**Files:**
- Modify: `lean/InfoGeometry/Canonical/KMSCocycleGeneratorBridge.lean`
- Import: `InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus`

**Theorem role:** translator bridge, not owner.

**Step 1: Add import**

At the top:

```lean
import InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus
```

**Step 2: Open microscopic namespace locally**

Inside `namespace InfoGeometry.Canonical.KMSCocycleBridge`:

```lean
namespace TCG := InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus
```

**Step 3: Add a conservative packet**

Insert after `KMSPairingWitness`:

```lean
/--
Microscopic graph evidence feeding the KMS cocycle corridor.

This packet does not claim that a finite stochastic graph has a continuum KMS
state.  It records the exact finite evidence that a later owner module may use to
construct the existing `KMSPairingWitness`.
-/
structure MicroscopicKMSPairingEvidence
    {V Edge : Type}
    (G : TCG.DirectedThermoGraph V Edge)
    (C : TCG.Cycle Edge) where
  gaugeClosed : G.GaugeClosedCycle C
  exactLogAffinity : ∃ φ : TCG.DirectedThermoGraph.GaugeTransform V,
    ∀ e ∈ C.edges, G.logAffinity e = G.gaugeCoboundary φ e
```

**Step 4: Add zero-curvature readback**

```lean
/-- Exact microscopic graph evidence has zero additive cycle curvature. -/
theorem microscopic_cycleCurvatureLog_eq_zero
    {V Edge : Type}
    (G : TCG.DirectedThermoGraph V Edge)
    (C : TCG.Cycle Edge)
    (H : MicroscopicKMSPairingEvidence G C) :
    G.cycleCurvatureLog C = 0 := by
  rcases H.exactLogAffinity with ⟨φ, hφ⟩
  exact G.cycleCurvatureLog_eq_zero_of_logAffinity_eq_coboundary φ C H.gaugeClosed hφ
```

**Step 5: Verify**

```bash
lake env lean lean/InfoGeometry/Canonical/KMSCocycleGeneratorBridge.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.KMSCocycleGeneratorBridge
```

Expected: both pass.

---

## Task 2: Add a discrete no-pumping-to-KMS closure readback

**Objective:** Reuse `DrivenThermoGraph.no_pumping_theorem` as a microscopic zero-integrated-curvature certificate, while keeping KMS closure as an explicit owner hypothesis.

**Files:**
- Modify: `lean/InfoGeometry/Canonical/KMSCocycleGeneratorBridge.lean`

**Theorem role:** translator readback.

**Step 1: Add packet**

```lean
/--
Discrete no-pumping evidence for a graph cycle, packaged for downstream KMS
owners.  The field `kmsClosureRoute` is deliberately explicit: this file does
not derive KMS closure from no-pumping alone.
-/
structure NoPumpingKMSClosureEvidence
    {V Edge Time : Type} [Fintype Time]
    (D : TCG.DirectedThermoGraph.DrivenThermoGraph (V := V) (E := Edge) Time)
    (C : TCG.Cycle Edge)
    (KMSClosureTarget : Prop) where
  barrierDriven : D.BarrierDrivenGraph C
  kmsClosureRoute : D.integratedPumpedCurrent C = 0 → KMSClosureTarget
```

**Step 2: Add readback theorem**

```lean
/-- Barrier-only discrete driving discharges the supplied KMS-closure route. -/
theorem kmsClosureTarget_of_noPumpingEvidence
    {V Edge Time : Type} [Fintype Time]
    {D : TCG.DirectedThermoGraph.DrivenThermoGraph (V := V) (E := Edge) Time}
    {C : TCG.Cycle Edge}
    {KMSClosureTarget : Prop}
    (H : NoPumpingKMSClosureEvidence D C KMSClosureTarget) :
    KMSClosureTarget :=
  H.kmsClosureRoute (D.no_pumping_theorem C H.barrierDriven)
```

**Step 3: Verify**

```bash
lake env lean lean/InfoGeometry/Canonical/KMSCocycleGeneratorBridge.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.KMSCocycleGeneratorBridge
```

Expected: both pass.

---

## Task 3: Add continuum-facing modular readback surface

**Objective:** Let `YangMillsContinuum` consume microscopic zero-curvature evidence as an abstract modular-continuum route, without asserting a graph-to-Yang-Mills limit.

**Files:**
- Modify: `lean/InfoGeometry/Canonical/YangMillsContinuum.lean`
- Import if not already transitively enough: `InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus`

**Theorem role:** coherence surface.

**Step 1: Add namespace alias**

Inside `namespace InfoGeometry.Canonical.YangMillsContinuum`:

```lean
namespace TCG := InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus
```

**Step 2: Add bridge packet**

```lean
/--
A conservative bridge from finite graph holonomy cancellation to a continuum
modular statement.  The route is an explicit owner-supplied implication; this
module only transports already-proved microscopic zero curvature.
-/
structure MicroscopicToModularContinuumBridge
    {V Edge : Type}
    (G : TCG.DirectedThermoGraph V Edge)
    (C : TCG.Cycle Edge)
    (continuumClaim : Prop) where
  gaugeClosed : G.GaugeClosedCycle C
  exactLogAffinity : ∃ φ : TCG.DirectedThermoGraph.GaugeTransform V,
    ∀ e ∈ C.edges, G.logAffinity e = G.gaugeCoboundary φ e
  zeroCurvature_to_continuum : G.cycleCurvatureLog C = 0 → continuumClaim
```

**Step 3: Add readback theorem**

```lean
/-- Exact microscopic graph holonomy discharges the supplied continuum route. -/
theorem continuumClaim_of_microscopicBridge
    {V Edge : Type}
    {G : TCG.DirectedThermoGraph V Edge}
    {C : TCG.Cycle Edge}
    {continuumClaim : Prop}
    (H : MicroscopicToModularContinuumBridge G C continuumClaim) :
    continuumClaim := by
  rcases H.exactLogAffinity with ⟨φ, hφ⟩
  exact H.zeroCurvature_to_continuum
    (G.cycleCurvatureLog_eq_zero_of_logAffinity_eq_coboundary φ C H.gaugeClosed hφ)
```

**Step 4: Verify**

```bash
lake env lean lean/InfoGeometry/Canonical/YangMillsContinuum.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.YangMillsContinuum
```

Expected: both pass.

---

## Task 4: Route microscopic bridge to Casini-Bekenstein capstone as an explicit owner packet

**Objective:** Add a capstone wrapper proving the existing `true_bekenstein_bound` from microscopic bridge evidence plus an explicit geometric/relative-entropy owner context.

**Files:**
- Modify: `lean/InfoGeometry/Canonical/CasiniBekensteinBound.lean`
- Import if needed: `InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus`

**Theorem role:** capstone, transport only.

**Step 1: Add namespace alias**

Inside `namespace InfoGeometry.Canonical.CasiniBekenstein`:

```lean
namespace TCG := InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus
```

**Step 2: Add capstone evidence packet**

```lean
/--
Microscopic-to-Casini evidence packet.

The microscopic graph evidence is retained as a transport-critical field, while
the physical Casini-Bekenstein assumptions remain exactly the existing owner
assumptions: relative entropy positivity, Casini identity, and geometric bridge.
-/
structure MicroscopicCasiniBekensteinEvidence
    {V Edge : Type}
    (G : TCG.DirectedThermoGraph V Edge)
    (C : TCG.Cycle Edge)
    [ctx : CasiniBekensteinContext H]
    (ω ω0 : State (AlgebraEnd H))
    (E_op : AlgebraEnd H) (R : ℝ) where
  gaugeClosed : G.GaugeClosedCycle C
  exactLogAffinity : ∃ φ : TCG.DirectedThermoGraph.GaugeTransform V,
    ∀ e ∈ C.edges, G.logAffinity e = G.gaugeCoboundary φ e
  bridge : BekensteinGeometricBridge ω0 E_op R
```

**Step 3: Add capstone theorem**

```lean
/-- Microscopic exact graph evidence plus the existing Casini geometric bridge
recovers the true Bekenstein bound.  The graph evidence is transported but not
mistaken for the physical relative-entropy theorem. -/
@[rep_depth transport, capstone]
theorem true_bekenstein_bound_of_microscopic_exact_graph
    [ctx : CasiniBekensteinContext H]
    {V Edge : Type}
    {G : TCG.DirectedThermoGraph V Edge}
    {C : TCG.Cycle Edge}
    {E_op : AlgebraEnd H} {R : ℝ}
    (ω ω0 : State (AlgebraEnd H))
    (Hmicro : MicroscopicCasiniBekensteinEvidence G C ω ω0 E_op R) :
    ctx.entropy ω - ctx.entropy ω0 ≤ 2 * Real.pi * R * (ω E_op - ω0 E_op) := by
  exact true_bekenstein_bound (ω := ω) (ω0 := ω0) (bridge := Hmicro.bridge)
```

**Step 4: Verify**

```bash
lake env lean lean/InfoGeometry/Canonical/CasiniBekensteinBound.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.CasiniBekensteinBound
```

Expected: both pass.

---

## Task 5: Add a single optional aggregator import only if a new bridge file is split out

**Objective:** Keep imports minimal. If Tasks 1-4 edit existing files only, do not touch `All.lean`. If a new dedicated bridge file is created, add exactly one import.

**Files:**
- Modify only if needed: `lean/InfoGeometry/Canonical/All.lean`

**Step 1: If creating a new file**

Use a name like:

```text
lean/InfoGeometry/Canonical/ThermodynamicGraphKMSBekensteinBridge.lean
```

**Step 2: Add import to `All.lean`**

```lean
import InfoGeometry.Canonical.ThermodynamicGraphKMSBekensteinBridge
```

**Step 3: Verify aggregator**

```bash
lake env lean lean/InfoGeometry/Canonical/All.lean
```

Expected: pass.

---

## Task 6: Run full target gate and policy smoke

**Objective:** Verify the spire corridor is green after all edits.

**Files:**
- No edits.

**Step 1: Run locked build**

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus \
  InfoGeometry.Canonical.KMSCocycleGeneratorBridge \
  InfoGeometry.Canonical.YangMillsContinuum \
  InfoGeometry.Canonical.CasiniBekensteinBound
```

Expected: build completed successfully.

**Step 2: Scan for proof escapes in touched files**

```bash
grep -R "\b\(sorry\|axiom\|admit\)\b" -n \
  lean/InfoGeometry/Canonical/KMSCocycleGeneratorBridge.lean \
  lean/InfoGeometry/Canonical/YangMillsContinuum.lean \
  lean/InfoGeometry/Canonical/CasiniBekensteinBound.lean || true
```

Expected: no proof escape matches. If comments mention these words, reword comments or report as comment-only false positives.

**Step 3: Diff check**

```bash
git diff --check -- \
  lean/InfoGeometry/Canonical/KMSCocycleGeneratorBridge.lean \
  lean/InfoGeometry/Canonical/YangMillsContinuum.lean \
  lean/InfoGeometry/Canonical/CasiniBekensteinBound.lean
```

Expected: no whitespace errors.

**Step 4: Optional policy lint smoke**

```bash
/home/goutev/arango-graph-venv/bin/python tools/infra/canonical_policy_lint.py 2>&1 \
  | grep -E 'KMSCocycleGeneratorBridge|YangMillsContinuum|CasiniBekensteinBound' \
  | sed -n '1,120p'
```

Expected: no new missing theorem-class findings for the touched declarations. If findings appear, use `canonical-policy-lint-theorem-class-burndown` skill surgically on one file at a time.

---

## Non-goals / red lines

Do not assert any of the following without a separate owner proof:

- finite graph no-pumping implies a KMS state;
- finite graph exactness implies continuum Yang-Mills curvature equations;
- microscopic entropy production directly proves physical Bekenstein/Casini bounds;
- Connes cocycle law follows from finite path fluctuation theorem;
- full hydrodynamic/continuum limit exists;
- analytic integration/measure-theory claims absent from the current corridor.

## Commit strategy

Use one small commit after green verification:

```bash
git add \
  lean/InfoGeometry/Canonical/KMSCocycleGeneratorBridge.lean \
  lean/InfoGeometry/Canonical/YangMillsContinuum.lean \
  lean/InfoGeometry/Canonical/CasiniBekensteinBound.lean

git diff --cached --name-status
git commit -m "Bridge thermodynamic graph exactness to Bekenstein corridor"
```

Do not stage unrelated dirty/deleted/untracked files in the current worktree.
