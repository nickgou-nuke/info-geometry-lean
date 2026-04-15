# Relative Modular Hamiltonian Lift Theorem Target Map

This chapter turns chapter 82 into an implementation lane with explicit owner targets.

## Status Bands

- `REPO_THEOREM`: proved and present in Lean.
- `ABSTRACT_READY`: theorem-shape present as interface, but still finite/commuting façade.
- `NOT_YET_FORMALIZED`: target for the unbounded/type-III lane.

## I. Owner Order (Δ primary, K derived)

### Claim
Relative modular operator is the owner; Hamiltonian is derived by logarithmic functional calculus.

### Targets
- `REPO_THEOREM` [RelativeModularOperator.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean:168)
  `relativeModularOperator_cocycle`
- `REPO_THEOREM` [RelativeModularOperator.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean:349)
  `relativeModularHamiltonianReadout`
- `REPO_THEOREM` [RelativeModularHamiltonian.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean:41)
  `modularHamiltonianFromDiagonal`
- `REPO_THEOREM` [RelativeModularHamiltonian.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean:58)
  `relativeModularHamiltonianOperator`

## II. Commuting Additive Lift

### Claim
In the finite commuting lane, multiplicative cocycle of `Δ` lifts to additive cocycle of `K = -log Δ`.

### Targets
- `REPO_THEOREM` [RelativeModularHamiltonian.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean:95)
  `relativeModularHamiltonianOperator_cocycle`
- `REPO_THEOREM` [RelativePotentialCore.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativePotentialCore.lean:381)
  `relativeModularPotential_cocycle`
- `ABSTRACT_READY` [MultiplicativeToAdditiveBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/MultiplicativeToAdditiveBridge.lean:92)
  `FunctionalCalculusLinearization`

## III. Shadow/Readout Separation

### Claim
Scalar Hamiltonian is a readout shadow of the operator owner, not the owner itself.

### Targets
- `REPO_THEOREM` [RelativeModularHamiltonian.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean:113)
  `relativeModularHamiltonianExpectation`
- `REPO_THEOREM` [RelativeModularHamiltonian.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean:119)
  `relativeModularHamiltonianExpectation_eq_readout`
- `REPO_THEOREM` [RelativeSurprisalOperatorLift.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean:326)
  `modularHamiltonianReadout`

## IV. Type III / Unbounded Lift (next lane)

### Claim
Support/domain-aware `K := -log Δ` on unbounded positive self-adjoint operators.

### Targets
- `NOT_YET_FORMALIZED`: support-restricted logarithm of relative modular operator (`supp Δ`).
- `NOT_YET_FORMALIZED`: affiliated-operator Hamiltonian package compatible with core/type-III lane.
- `NOT_YET_FORMALIZED`: commuting-sub-lane theorem `log(AB)=log A + log B` with explicit commutation hypotheses.
- `NOT_YET_FORMALIZED`: Connes-cocycle-based bridge surface from operator Radon–Nikodym data to `Δ_{ψ|φ}` owner.

## Immediate Build Targets

- `lake build InfoGeometry.Canonical.RelativeModularOperator`
- `lake build InfoGeometry.Canonical.RelativeModularHamiltonian`
- `lake build InfoGeometry.Canonical.RelativeSurprisalOperatorLift`
- `lake build InfoGeometry.Canonical.All`

If these remain green, the lane is stable at the finite/commuting operator-owner level.
