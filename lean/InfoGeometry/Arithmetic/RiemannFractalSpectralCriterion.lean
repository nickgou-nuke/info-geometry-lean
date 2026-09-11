import InfoGeometry.Arithmetic.HerichiLapidusSpectralBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Riemann fractal spectral criterion — retired compatibility module

The former contents of this path packaged arbitrary predicates as a
`FractalSpectralOperatorCertificate` and used a Boolean field as a purported
Cuntz boundary.  Those declarations did not construct a Cuntz algebra, a
spectral operator, a spectrum, or an invertibility theorem, so they are not
part of the native proof surface.

The maintained owner is
`InfoGeometry.Arithmetic.HerichiLapidusSpectralBridge`.  It exposes the actual
finite Dirichlet shift operator, its vertical-line spectral image, the closure
of that image, and the proved implication
`isQuasiInvertible → pointwise nonvanishing`.

This file remains only as an import-compatible retirement marker.  No scalar
or certificate wrapper is reintroduced here.
-/

namespace InfoGeometry.Arithmetic

end InfoGeometry.Arithmetic
