# Complement-preserving hyperbolic orbit v2

Preserves all v1 definitions and theorem statements, their arbitrary CommRing
scope, and the existing IsDualSeedPair hypotheses. Frozen v1 is unchanged.

Exact QA repair source: /tmp/qa-a-complement-hyperbolic-csz0z4_l/compile.log.
- Product: distribute outer scalar actions with smul_add before smul_smul;
  the scalar products then exist for the existing commutativity rewrites.
- Plus expansion: normalize neg_smul and outer smul_neg before collapsing
  nested actions. Remove the diagnosed unused mul_neg simp argument.
- Extract six atomic reusable support/complement absorption and annihilation
  lemmas. The product proof now uses these together with native support_sq,
  support_table and transitionVelocity_sq. Each new helper and the product
  proof is below 20 lines; no bundled conclusions or new assumptions.

No budget/linter suppression, builds, tests, or live-owner edits. Source-only
repair requires independent AA and serialized kernel QA. No metric/KMS claim.
The separate elliptic readback candidate is unchanged.
