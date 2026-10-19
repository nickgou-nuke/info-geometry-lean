# GTC: Double Real Krein parabolic shear defect

## Carrier and owner

Use the repository's canonical `DoubledSpace E = WithLp 2 (E × E)` with
`[NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]`, its
canonical diagonal Krein form, and the existing KAN shear
`ρclock (componentNReal t)`. Reuse
`ρclock_componentNReal_apply` and `krein_inner_prod_l2`.

## Consumer-minimal theorem

For `x ξ y η : E` and `t : ℝ`, prove the exact defect identity

```lean
KreinSpace.kreinInner (ρclock (componentNReal t) (to_doubled x ξ))
  (ρclock (componentNReal t) (to_doubled y η)) -
  KreinSpace.kreinInner (to_doubled x ξ) (to_doubled y η) =
  t * (inner ℝ x η + inner ℝ ξ y) + t ^ 2 * inner ℝ ξ η
```

This is an unconditional finite-stage identity on the actual repository
carrier. It must not be packaged as an isometry theorem.

## Optional corollary

For any `ξ ≠ 0` and `t ≠ 0`, the shear changes the Krein quadratic value on
`(0, ξ)` by `t² * ‖ξ‖²`, hence is not a Krein isometry. State this only with
the nonzero-vector witness hypotheses.

## Exclusions

This contract does not identify the shear with a Plabic square move, a cluster
mutation, a Clifford rotor exponential, or a unitary/Krein-isometric action.
It does not assert a classification of all isometries.

## Gate plan

Search for duplicate owner results; keep the Lean module focused and small;
run strict OpenGauss screen/refute; obtain independent A-A on the exact staged
diff; inspect compiler processes; run the target build through the shared lock;
run Gate 4/certification and independent QA-A reruns. Preserve all unrelated
staged work.
