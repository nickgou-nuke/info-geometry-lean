# Memo: Sketch of Conformal Group Construction from Chiral Light Cone Operators (Repo-Native)

---

**1. Chiral Operator Cone Closure**
- Defined by `ChiralOperatorCone` and `IsInChiralOperatorCone`.
- Closed under addition, real scaling, and commutators.
- Theorem: `supercharge_mem_chiralOperatorCone` — Drazin supercharge is a canonical chiral element.

**2. KKT Closure Symmetry**
- Structure: `KKTClosureSymmetry`, `kktClosureSymmetrySubgroup` (unitary conjugations preserving KKT generators).
- Operators: QD (supercharge), ZD (central charge), HD (Hamiltonian), GammaS/GammaG (chiral gradings).
- Theorems: Anticommutator/commutator relations, centrality of ZD, closure under conjugation.

**3. Supercharge and Central Charge Operators**
- Definitions: `operatorialCentralChargeOperator`, `cptSuperchargeKineticPart`.
- Theorems: `cptSupercharge_sq_eq_kinetic_plus_centralChargeOperator`, `root_central_supercharge_theorem`.

**4. Dilation Operator**
- Present as `dilationGap` and related theorems.

**5. Modular Hamiltonian and Inversion**
- Modular Hamiltonian: HD, modularSuperchargeOp.
- Inversion: Not directly named, but can be constructed via sign-change or log/exponential maps on the modular Hamiltonian.

---

**Sketch for Conformal Group Construction:**

- **Translations:** Use supercharge operator QD as the generator.
- **Dilations:** Use `dilationGap` operator.
- **Central Charge:** Use ZD or `operatorialCentralChargeOperator`.
- **Modular Hamiltonian:** Use HD.
- **Inversion/Time-Reversal:** Define as sign change or via the exponential/log of the modular Hamiltonian (e.g., inversion = exp(π i HD) or logOp(−HD)).
- **Closure:** All operators act on EndH, with closure under commutators and conjugation by units in `kktClosureSymmetrySubgroup`.

**To realize the full conformal group:**
- Combine these operators in a generated algebra.
- Explicitly define inversion/time-reversal using the modular Hamiltonian.
- Ensure closure under all group operations (commutators, exponentials, conjugations).

---

**Conclusion:**
All algebraic ingredients for the conformal group are present in operator form. The only missing step is to explicitly define inversion/time-reversal using the modular Hamiltonian and verify closure in the generated algebra.
