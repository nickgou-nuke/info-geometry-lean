# RotorWeightOrbitBridge candidate contract

Source: RotorWeightOrbitBridge20261024.lean. Intended native owner:
InfoGeometry.Canonical.RotorWeightOrbitBridge. Source only, not compiled.
Implements the approved bounded B/C/D/E integration, not a five-stream packet.

Imports actual Stream5, Stream3, PeirceWeightedTrace and ReflexiveRotorRealTime.
Foreign FiveStreamMasterIntertwiner is neither imported nor modified. No new
structure, carrier, pair equivalence, quarter-turn theorem, or omnibus result.

Readbacks phaseRotor_eq_native and kmsWeight_eq_supportWeight identify existing
expressions definitionally and are consumed below; they do not recreate primitives.

1. movingPolePlus_mem_unitOrbit: Stream5 IsDualSeedPair's four primitive fields
   feed native rotor_inverse and rotor_reverse_inverse. A LOCAL actual A-unit
   witnesses membership in the existing Grassmannian unitOrbitMap range. The
   normalized circle condition is explicit; no replacement orbit is defined.
2. rotor_supportWeight_conjugation: for arbitrary central a,b,c,s,
   R W(a,b) Rreverse = (a*s²+b*c²)•dB + (a*c²+b*s²)•Bd
     + ((a-b)*c*s)•(d+B).
   Derived from native plus/minus conjugation formulas. No circle normalization
   or positivity is assumed for this polynomial identity.
3. kmsWeight_movingPole_joint: for native NCG.TracialFunctional R A and a
   normalized rotor, the simultaneously conjugated Stream3 kmsModularWeight
   paired with Stream5 movingPolePlus has weighted readout v²*tau(dB).
   Uses the native TracialCARDensity.joint_covariance with a local actual unit,
   then support_table and trace linearity for the explicit coefficient.
   It does NOT claim invariance of a moving projector against a fixed density.
4. movingPolePlus_circle_eq_native identifies Stream5's entire sin/cos function
   with the existing ModularFlowGeneratorDerivative.conjugationPath of the
   actual native realRotor, including the correct reverse-time sign.
   hasDerivAt_movingPolePlus_circle consumes that function equality and native
   hasDerivAt_rotorOrbit, giving the actual derivative [d-B,movingPolePlus(t)].
   No supplied derivative, continuity axiom, or new analytic path definition.

Algebraic scope: CommRing R, Ring A, Algebra R A. Pair hypotheses arrive only
through existing IsDualSeedPair; no desired conclusions are supplied as fields.
Analytic scope: NormedRing A, NormedAlgebra real A. No completeness needed.
No positive-state, faithful-density, star-projection, exponential, analytic KMS,
De Bruijn, or classification claim. Parent retains all colimit implementation.

Staged immediately. No builds/tests/live-owner edits or budget changes.
Independent AA and serialized QA are required before promotion. Audit all seven
heads (two algebraic readbacks, orbit membership, weight rotation, joint readout,
path equality, actual derivative). Existing frozen rotor/FreshTail files preserved.
