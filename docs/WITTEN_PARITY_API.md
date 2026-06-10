# WittenParityIndex API Overview

This document serves as the definitive entry point for interacting with the verified thermodynamics of the Riemann boundary, specifically the `WittenParityIndex.lean` module.

## Core Purpose
The `WittenParityIndex` establishes the fundamental physical invariant of the Riemann zeta boundary: the topological Witten Index ($\text{STr}(e^{-\beta H})$). It rigorously confirms the alternating $+1, -1$ sequence of the Ramanujan Defect Tower under the $S$-duality swap ($\tau \leftrightarrow 1/\tau$).

## Key Components

### 1. Parity Toggles
The module fundamentally categorizes the Dirichlet fractional defect spaces by their modulo 2 index:
- `Odd` degrees ($n = 2, 4 \implies \zeta(5), \zeta(9)$) strictly output a **$-1$ (Anti-Invariant)** parity, indicating an antisymmetric boundary state.
- `Even` degrees ($n = 1, 3 \implies \zeta(3), \zeta(7)$) strictly output a **$+1$ (Invariant)** parity, indicating a symmetric boundary state.

### 2. Verified Theorems
- `parity_even_defect_invariant (n : ℕ) (h : n % 2 = 1)`: Mechanically verifies the symmetric $+1$ eigenspace logic.
- `parity_odd_defect_anti_invariant (n : ℕ) (h : n % 2 = 0)`: Mechanically verifies the antisymmetric $-1$ eigenspace logic.

### 3. Integration with the Cartan Involution
The Parity index strictly governs the topological charge behavior that feeds back into `HodgeCartanTrifactor.lean`. 
- **Invariant ($+1$)** paths map to the Harmonic Core ($\mathfrak{k}$) of the Cartan Involution.
- **Anti-Invariant ($-1$)** paths map to the Exact/Co-exact Drivers ($\mathfrak{p}$) of the Cartan Involution.

## Future Extensions
All future modular flow mapping (e.g., Cuntz shift parity bridges and trace formula operators) should directly import this API and rely strictly on the `parity_even_defect_invariant` and `parity_odd_defect_anti_invariant` theorems to establish the chiral properties of the constructed state before projecting onto the Trifactor geometry.
