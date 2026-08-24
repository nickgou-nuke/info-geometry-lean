import InfoGeometry.Algebra.WittProjectiveClosureHonest

/-!
# Honest Witt / projective closure surface

This module replaces the earlier over-claimed `WittProjectiveClosure` surface
with theorem-backed finite facts re-exported from
`InfoGeometry.Algebra.WittProjectiveClosureHonest`.

It does NOT prove any global `O(5,5)` Virasoro anomaly cancellation, any Krein
realization theorem for the full Witt/Virasoro system, or any physical `c = 0`
statement.

It DOES provide the finite honest surface already verified in-repo:
- the anomaly polynomial `m^3 - m` vanishes on `{-1, 0, 1}`;
- the Virasoro cocycle vanishes on projective generators;
- the Witt bracket on `ℓ_{-1}, ℓ_0, ℓ_1` is the usual centerless bracket;
- nonzero projective brackets stay inside the projective index set.
-/

/-!
This historical module is intentionally declaration-free.  The verified owner
is `InfoGeometry.Algebra.WittProjectiveClosureHonest`; importing this path
keeps the umbrella import stable without creating a forwarding API.
-/
