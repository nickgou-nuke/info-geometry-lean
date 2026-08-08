# Modular/Parabolic-Time Closure: Final Architecture Spec (v1.18.0 target)

This note records the final closure of the `F_Q(C^D,3)` finite-layer pipeline:
**de Rham topological generator at the forbidden cone ↔ Tomita–Takesaki modular derivation ↔ parabolic time clock**.

## Core theorem chain in Lean

### 1) de Rham + TKK seed
- `chemical_potential_tkk_g0_synthesis` (in `ChemicalPotentialTKKGradeZero.lean`)
  - finite cycle entropy cancellation for the triangle
  - `chemicalGenerator ∈ TKKGrade.z0`, grade-preserving action
- `chemical_potential_derham_g0_synthesis` (in `ChemicalPotentialDeRhamG0Bridge.lean`)
  - exactness of `A.lie1 ω`
  - `C.d 0 μ0 = μ`
  - rank-32 and `formalChiralParityIndex = 0`
  - analytic side kept as sockets (`M`, `P`)

### 2) Jacobian / Radon–Nikodym / modular bridge
- `ModularRadonNikodymJacobianBridge.lean`
  - `modular_derivation_preserves_grade`
  - `forbidden_cone_modular_derivation_clocks_parabolic_time`
- `de_rham_alpha_beta_forbidden_cone_clock_synthesis`
  - injects both the de Rham socket data and the forbidden-cone modular clock socket
  - outputs identification witnesses:
    - `K.forbiddenConeDLogQ = ω`
    - `K.deRhamGeneratorAroundForbiddenCone`
    - `K.dlogQEqualsNegativeLogJacobianPotential`
    - `K.dlogQEqualsNegativeLogRNPotential`
    - `K.dlogQGeneratesModularDerivation`
    - `K.modularDerivationClocksParabolicTime`
    - `K.parabolicTimeIsAffineLogClock`
    - `K.quadricConeMonodromyAnalytic`
- `ModularParabolicTimeBridge.lean`
  - final naming layer for downstream imports (`deRham_is_modular_parabolic_time_derivation`).

### 3) Finite algebraic/categorical consistency
- `ModularMonodromy.lean` (modular/parabolic algebraic identities)
- `QuadricConf3BraidingCooperadBridge.lean` (pairwise split API and Vertex3 wiring)
- non-commutative/categorical symmetry sockets: `RindlerKreinMobiusProtectionSocket`, `ForbiddenConeDeRhamModularClockSocket`

## SymPy witnesses (audit layer)
- `proofs/chemical_potential_derham_g0_witness.py`
- `proofs/modular_radon_nikodym_jacobian_bridge.py`
- `proofs/modular_time_derivation_witness.py` *(new)*
  - verifies `ι_{Xmod} (d log Q) = 2` (or `2c` under scale),
    `d(ι_{Xmod}ω)=0`, `L_{Xmod}ω=0`.
- `proofs/modular_parabolic_time_witness.py`
  - verifies affine/parabolic shear additivity and the same finite modular contraction
    identity in block-matrix form.

## Physical reading (compact)
- `ω = d log Q` is the forbidden-cone de Rham generator on configuration space.
- Its contraction with the parabolic modular vector field is constant: this is the local modular tick.
- This constant-clock property packages the Connes–Takesaki modular flow as intrinsic (state-induced) time.
- By theorem-honest transport, parabolic time is identified with the `TKK` grade-zero modular derivation sector.

## Release alignment
This is the end-state to package under release tag:
- **`v1.18.0-modular-parabolic-time`** (new suggested tag)
- Minimal verification command:
  - `cd proofs && lake build ModularRadonNikodymJacobianBridge`

