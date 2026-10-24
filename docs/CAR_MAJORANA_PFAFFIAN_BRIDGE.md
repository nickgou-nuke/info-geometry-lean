# CAR, finite Majorana chains, and coefficient-kernel criteria

## Scope and exact owners

Inspected base: e49fa4c75b05d7ddb6c7da2f1ff798d67370a6ab. No existing owner or dependency pin is changed.

The finite core reuses Quantum.MajoranaPfaffianNaturalClosure (explicit CAR matrices and Majoranas), Canonical.MajoranaPfaffian4 (signed matching polynomial and PROVED square law), and Canonical.ProjectivePfaffianDeterminantCounts (PfaffianKernel carrier). The general CAR hypothesis is exactly the defining equation of the existing IsMajoranaBasis, generalized to an arbitrary finite index type without defining a substitute predicate.

The full-owner adapters import Canonical.SuperchargeCARCCRBridge, Canonical.KitaevChainMajoranaZeroModes, and Canonical.KreinMajoranaZeroModeBlock. These adapters are separate candidates, not part of the verified-core claim.

## Core theorem contract

For a nontrivial real algebra A and finite normalized Majorana family, define G(v)=sum_i v_i gamma_i and K(w)=1/4 sum_ij w_ij gamma_i gamma_j. CAR proves coefficient extraction {gamma_i,G(v)}=2 v_i 1, hence injectivity of G. For real skew w, [K(w),G(v)]=G(w v). Thus the coefficient kernel corresponds exactly to conserved LINEAR Majorana fields, not arbitrary elements of the full commutant.

An existing PfaffianKernel gives pf=0 iff a nonzero coefficient kernel exists. This general result is conditional on its square-law witness; the witness is not a proved universal Pfaffian theorem in that owner. The four-mode instantiation eliminates the witness assumption using MajoranaPfaffian4.pfaffian4 and its actual polynomial square law af-be+cd.

The concrete full complex four-dimensional spin representation uses gamma=(X tensor I,Y tensor I,Z tensor X,Z tensor Y). Cross-site CAR and self-adjointness are proved, not supplied. The parity string is retained. The two-site open sweet-spot generator K=t gamma_1 gamma_2 is identified with the quadratic coefficient matrix w_12=2t,w_21=-2t. Its endpoint coefficient vectors and nonzero endpoint operators give the full concrete CAR -> Majorana -> finite-chain zero-mode -> Pfaffian chain.

K is skew, not a Hermitian Hamiltonian. The physical convention uses iK; the formal statements currently concern K. No bulk Z2 invariant, robustness, gap, infinite-chain limit, or normalized-state energy-kernel claim follows merely from the finite-chain Pfaffian vanishing.

The general finite-bilinear theorem proves conservation at an endpoint excluded from all edge pairs, assuming the coefficient commutes with that endpoint. The integration candidate specializes this to the original kitaevSweetSpotHamiltonian definition for arbitrary chain length.

## Integration blocker: preserve rather than patch the pins

The full source traversal at ddd806f4989fd94e6288b8ba6530f8c17424e35e reached a pre-existing incompatible external dependency. With Lean 4.34.1 and repository-pinned LeanArchitect 54d3fb249685db8e5a564e0b3f331cff77991607, Architect/Command.lean lines 17-18 uses the old exportEntriesFnEx signature and fails before the new bridge modules compile. See workflow 39902328896 and its failed-source artifact.

No dependency source, pin, existing mathematical owner, or blueprint annotation is altered to bypass this error. The finite core is separated from the heavy owner adapters and checked on its own. Successful finite-core CI DOES NOT certify CARMajoranaOwnerAdapters or KreinMajoranaKernelCriterion. Use workflow_dispatch with check_owner_adapters=true to attempt their distinct integration check after the dependency is repaired through the repository's approved process.

The doubled-space candidate records the naming exchange: the real creation operator is the upper matrix unit called annihilationR by the separate matrix owner. The polarized-block candidate retains the existing model equality and square-law witness when upgrading determinant-zero to a nonzero kernel vector. Its chiral projector is not automatically an energy-kernel projector.

## Validation commands

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.MajoranaLinearKernel \
  InfoGeometry.Canonical.CARMajoranaFiniteBridge
```

The scoped checker compiles complete, unchanged source dependencies and audits every new core theorem and definition, rejecting nonfoundational axioms. A successful source-commit-specific workflow and artifact, not this document alone, establish verification. The adapter files are deliberately not exposed through a global umbrella while their integration remains unverified.
