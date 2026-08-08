
# Symbolic-to-Lean Normalization Targets

Cluster 1: Bregman cohomology volume kernel Q
- Formal objects:
  - Q : ℝ, Q > 0
  - Ω : finite weighted orbit count = metriplectic orbit cardinality
  - d ln Q = dQ / Q as closed 1-form on finite sum space
- Lemmas:
  - closed_1_form : d (d ln Q) = 0
  - Bregman_potential : B(Q) = -ln Q ; grad B = - grad ln Q
  - orbit_volume_ratio : Q = Ω / Ω_ref ; so ln Q = ln Ω - ln Ω_ref
- mathlib hints:
  - use Finset.card, Finset.weightedSum
  - use Module.End for linear d; use LinearMap.commMatrix if needed
  - for closedness, formalize on trivial complex; actual de Rham in full generality needs MeasureTheory / DifferentialForms, but finite-combinatorial analogue is provable.

Cluster 2: Frame bundle Jacobian B and Pauli/chiral basis lifting
- Formal objects:
  - V := M2(R) as frame/matrix algebra; or M2(C) for sl2C
  - σx, σy, σz standard real Pauli matrices
  - B := det ( Jacobian( flow_on_frame_bundle ) )
  - σ+ : cyclic/raising / σ- : cyclic/lowering in real or split-octonion Pauli sector
  - [s+, s-] closure relation in frame basis
- Lemmas:
  - det_flow_monomial : det (Jacobian) is multiplicative under composition
  - basis_rotation_det_sign : rotation by σ± preserves/negates det depending on grading
  - closure_splus_sminus : bracket or product closure in frame basis
- mathlib hints:
  - Matrix.det, Matrix.IsSymmIff, Matrix.IsOrthogonal
  - Matrix.trace, Matrix.norm_sq

Cluster 3: Krein/S+/S-/n+/n-/Cauchy boundary algebra
- Formal objects:
  - K+ : positive definite block; H- : negative block; H0 : neutral/null
  - J : modular conjugation J^2 = -I or J^2=I depending on signature
  - n+, n- : Möbius parity winding numbers on D+/S/S-
  - D+, S, S- : Cauchy/time-orientable / space-like / time-like triplet, twistor infinity bridge
  - TripotentProjector P : P^3=P with det ∈ {0,±1}
- Lemmas:
  - krein_projector_sum : frame = K+ ⊕ H- ⊕ H0
  - det_tripotent_classification : det(Track(P)) ∈ {0, ±1}
  - mobius_parity_index : formal parity = card(+) - card(-) = 0
- mathlib hints:
  - DirectSum decomposition via Submodule.proj if basis known; otherwise finite type inductive encoding now present.
  - Matrix.det, RingHom.det
  - Fintype.card

Hard rules:
- No sorry
- No trivial proofs that just restate definitions unless explicitly marked trivial lawwork
- If an exact continuous differential form is unavailable in mathlib, switch to combinatorial analogue with explicit finite model
- If symbol lacks formalization path, ask in output rather than invent non-existent term
- All outputs must compile under lake build FibAnyonProofs or at least be accepted as new module references.
