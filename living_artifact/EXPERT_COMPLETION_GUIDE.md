# Expert Completion Guide (Living Artifact)

> **Purpose:** Practical guide for domain experts to ungate hypothesis bundles into fully constructive, kernel-checked native Lean 4 proofs.  
> **Toolchain:** Lean 4 `v4.28.1` + Mathlib 4  
> **Current Codebase State:** 20,855 verified modules, 0 `sorry`, 0 custom axioms.  
> **Target:** Replace gated assumption structures (`Witness`, `Certificate`, `Packet`) with explicit Mathlib constructions and proofs.

---

## 1. Fast-Track Workflow for Domain Experts

1. **Select a Target Gated Structure** from [`SOCKET_DEBT_LEDGER.md`](SOCKET_DEBT_LEDGER.md).
2. **Inspect the Definition** in the owner file (e.g. `lean/InfoGeometry/Automorphic/SiegelResonance.lean`).
3. **Construct Concrete Instances:** Replace the structure requirement in downstream theorems with an explicit instance or direct derivation from Mathlib.
4. **Compile & Verify:**
   ```bash
   lake build InfoGeometry.<TargetModule>
   bash scripts/quality/quality_gate_fast.sh
   ```
5. **Stage & Commit:**
   ```bash
   git add -A
   git commit -m "Ungate <StructureName>: replace assumption bundle with native proof"
   ```

---

## 2. High-Priority Target Templates

### Target 1: `SiegelEisensteinWitness` (Automorphic Forms)
* **File:** [`lean/InfoGeometry/Automorphic/SiegelResonance.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Automorphic/SiegelResonance.lean#L18)
* **Fields to Construct:**
  1. `siegel`: Real analytic Siegel modular form of degree $g$.
  2. `eisenstein`: Degenerate or standard Siegel Eisenstein series section.
  3. `section_property`: Explicit differential relation on the Siegel upper half-plane $\mathbb{H}_g$.
* **Goal:** Supply a concrete Fourier expansion instance `siegelEisensteinInstance` to eliminate the hypothesis requirement across 101 downstream theorems.

---

### Target 2: `HestenesKreinKMSPacket` (Geometric / Krein Algebra)
* **File:** [`lean/InfoGeometry/Krein/HestenesModularKMSBridge.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Krein/HestenesModularKMSBridge.lean)
* **Fields to Construct:**
  1. `phaseAxis`: Bivector generator $I \in \mathrm{Cl}(p, q)$ with $I^2 = -1$.
  2. `rotor`: Unit rotor $R(t) = \exp(-I t / 2)$.
  3. `modularFlow_eq_rotor_conjugation`: Proof that $\sigma_t(x) = R(t) x R(t)^\dagger$.
* **Goal:** Provide explicit matrix/Clifford representations that satisfy the KMS condition directly.

---

### Target 3: `KWPhysicalDualityWitness` (Operator Algebras)
* **File:** [`lean/InfoGeometry/OperatorAlgebra/PhysicalLanglandsHolonomy.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/OperatorAlgebra/PhysicalLanglandsHolonomy.lean)
* **Fields to Construct:**
  1. `wilson_eq_thooft_dual`: Fourier-transform intertwiner between electric Wilson loops and magnetic 't Hooft loops.
  2. `holonomy_inv`: Path transport covariance.
* **Goal:** Construct explicit bounded linear operators on $L^2(G)$ implementing S-duality.

---

### Target 4: `FiveGradeBracketPacket` Suite (Conformal Lie Algebras)
* **Files:**
  * [`lean/InfoGeometry/Canonical/ConformalFiveGradeBracketAPI.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/ConformalFiveGradeBracketAPI.lean#L38)
  * [`lean/InfoGeometry/Canonical/ConformalFiveGradeCurrentPacket.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/ConformalFiveGradeCurrentPacket.lean#L15)
* **Fields to Construct:**
  1. `bracket`: Explicit 5-graded Lie bracket on $\mathfrak{g} = \bigoplus_{k=-2}^2 \mathfrak{g}_k$.
  2. `gradeCompat`: Proof that $[\mathfrak{g}_i, \mathfrak{g}_j] \subseteq \mathfrak{g}_{i+j}$.
* **Goal:** Instantiate with concrete matrix Lie algebra representations on $\mathfrak{so}(5,5)$ and $\mathfrak{e}_8$.

---

### Target 5: `AsanoKleinV4CompactificationCertificate` (Statistical Mechanics)
* **File:** [`lean/InfoGeometry/Canonical/LeeYangAsanoKleinV4Compactification.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/LeeYangAsanoKleinV4Compactification.lean#L76-L136)
* **Fields to Construct:**
  1. `symmetry`: Klein 4-group $V_4$ coordinate permutation invariance.
  2. `endpoint_holds`: Proof that the Asano contraction maps non-vanishing sets $\mathcal{K} \times \mathcal{K} \to \mathcal{K}$.
* **Goal:** Supply explicit polydisc or circular domain definitions for spin-glass polynomials.

---

## 3. Quality & Promotion Standards

All PRs must satisfy the repository quality gates:
1. **0 `sorry` / `admit`** in all modified files.
2. **0 custom axioms** (Kernel `#print axioms` must only report `propext`, `Classical.choice`, `Quot.sound`).
3. **No cache destruction:** Never run `lake clean` or delete `.lake/`.
4. **Canonical Capstone Pairing:** Every new core module must expose a canonical projection capstone under `InfoGeometry/Canonical/`.
5. **Continuous Index Protection:** Always keep modified files staged with `git add -A`.
