# Frozen Fock stream realization candidate

Status: authored sandbox only, UNCOMPILED. No builds, tests, live-owner changes,
new dependency pins, global metric instances, or budget increases.
Independent AA and parent-controlled serial QA remain required.

## Files and integration

- FiniteFockCLMReflexivePair20261024.lean: seven lemmas lifting actual native
  coordinate creation/contraction to CLM square-zero and CAR, deriving both
  reflexivity relations, then constructing the two existing Stream5/Stream4
  property interfaces. Neither interface is assumed as a hypothesis.
- FiniteFockRotorShear20261024.lean: ten focused consumer lemmas. Imports the
  first sandbox module as `scratch.FiniteFockCLMReflexivePair20261024`.
  QA must make that module available first. On promotion, parent may choose
  `InfoGeometry.Clifford.FiniteFockCLMReflexivePair` and redirect exactly that
  import; no promotion has been performed by this session.

Both use namespace `InfoGeometry.Clifford.ClNNNeutralChevalleyBridge` and the
native local fockNormedAddCommGroup/fockInnerProductSpace. D denotes the actual
fockIntActionCLM and C the actual fockExtActionCLM. No new operator, flow, spinor,
or master certificate carrier is defined. CAR proves active support = identity.

## Concrete consumer contract

`fock_realRotor_apply`: R(t)x=cos(t)•x+sin(t)•(Dx-Cx).
`fock_movingPolePlus_eq_conjugationPath`: actual equality between Stream5's
moving pole at cos/sin parameters and the existing realRotor conjugation path.
`fock_movingPolePlus_apply`: cos²•D(Cx)+sin²•C(Dx)-cos*sin•(Dx+Cx).
`fock_movingPolePlus_idempotent`: that actual operator squares to itself.
`fock_doubleShear_apply`: x+Dx-Cx-D(Cx), with this order and sign.
`fock_tripleShear_eq_quarterTurn`: existing Stream4 triple shear = R(pi/2).
`fock_quarterTurn_apply`: R(pi/2)x=Dx-Cx.

D*C is coordinate vacancy, not the full multicoordinate vacuum. There is no
claim that the shears are orthogonal, no global five-stream equivalence,
no topological Klein/Nambu/DeBruijn identification, and no external-repo map.
The coordinate binder i:Fin n correctly excludes a coordinate for n=0.

## Existing analytic reuse, deliberately not re-proved

`Canonical.ReflexiveRotorRealTime.hasDerivAt_rotorOrbit`,
`hasDerivAt_plus_zero`, and `hasDerivAt_deriv_plusOrbit` accept precisely the
four primitive relations proved in the interface file. Together with the named
movingPolePlus/conjugationPath equality, they supply the derivative consumer
without another analytic proof. This batch adds no derivative wrappers.

## Frozen SHA256

- `scratch/FiniteFockCLMReflexivePair20261024.lean`: `aba7f434641143a2046d94384e38084f7c84f6604a118b43f63bc028089c6ed4`

- `scratch/FiniteFockRotorShear20261024.lean`: `f7867345acd670fcf5403071d923a9a6bad4f9c76380947c4fa98138a023784b`

## Native dependency identities at authoring

- `lean/InfoGeometry/Clifford/FiniteRealFockNormBounds.lean`: `4a5382ad9dc1f7667f3703babafa498a8099969564e12005562d1631bf806570`

- `lean/InfoGeometry/Clifford/FiniteRealFockAdjoint.lean`: `f83ccc4ca27cfd634bb8d0122f033e13b29ea30729a3cca546b85e6890233b2c`

- `lean/InfoGeometry/Canonical/DeBruijnRotorAlternationCycle.lean`: `cb4512c763d796ca201863f77fcb5e084d256839a8f2a8c5230ea2c679c76df5`

- `lean/InfoGeometry/Canonical/ModularParabolicCyclotomicSynthesis.lean`: `f8225e845698b06c358ba2a3f10697d10a19519a1fe9e9e3d789d68b919aefb8`

- `lean/InfoGeometry/Canonical/ReflexiveRotorRealTime.lean`: `4d02458fbc4ef7a5e5c0963101dbdbcbbee1dbf882ec1c1219652315fb3db885`
