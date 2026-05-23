# Tessellation Incidence Rigidity

This note records the Lean-safe theorem surface for algebraic lightray
transport.

The finite theorem is:

```text
orthogonal idempotent sectors + supported arrow
  => square-zero lightray
  => unipotent unit 1 + N with inverse 1 - N
  => determinant and trace are preserved by unit conjugation
```

In Lean this is owned by:

```text
InfoGeometry.Tessellation.Incidence
InfoGeometry.Tessellation.VolumeTransport
InfoGeometry.Tessellation.WilsonLoop
```

`Incidence` owns the structured sector API: `Diamond`, `IncidentLightray`,
`SupportedLightray`, and the structure-level square-zero theorem.

`VolumeTransport` imports `Incidence` and mathlib matrix determinant/trace
files. It uses the incidence theorem to build unipotent flow units, then uses
mathlib's determinant and trace invariance under matrix unit conjugation.

`WilsonLoop` owns only the minimal supported-holonomy loop API and the
defect/flatness equivalence. It does not introduce path calculus or cyclic
cohomology.

The main public theorem names are:

```lean
IncidentLightray.square_zero_of_orthogonal
SupportedLightray.square_zero
supported_lightray_square_zero
squareZeroUnit
supportedLightrayFlowUnit
lightrayFlowUnit
det_unitConj
trace_unitConj
det_supported_lightray_conj
trace_supported_lightray_conj
det_square_zero_lightray_conj
trace_square_zero_lightray_conj
WilsonLoop.defect
WilsonLoop.Flat
WilsonLoop.defect_eq_zero_iff_flat
```

`VolumeTransport` uses explicit support laws and orthogonality for the
matrix-level theorems. It does not introduce witness-packed theorem sockets,
and it is re-exported through `Tessellation.All`.

This proves a finite noncommutative `H^1` volume/trace rigidity result:

```text
A ↦ G A G⁻¹
```

preserves determinant and trace.

The incidence rigidity theorem proves that a supported arrow between
orthogonal idempotent sectors is automatically square-zero. Its unipotent
transport `G_t = 1 + tN` acts by unit conjugation and therefore preserves
determinant and trace. This gives a finite noncommutative `H^1` volume/trace
rigidity result. It is an algebraic prerequisite for later symplectic-capacity
or Gromov-Witten interpretations, but it is not itself a proof of Gromov
non-squeezing or a construction of `H^3` cyclic invariants.

This is not a proof of Gromov non-squeezing, Gromov--Witten invariants, Hawking
entropy, or cyclic `H^3` gluing.  Those require additional theorem surfaces such
as symplectic forms, capacities, equivariant localization, or cyclic
cohomology.

Trace is treated here only as a linear conjugation invariant. It is not called
entropy in this layer.
