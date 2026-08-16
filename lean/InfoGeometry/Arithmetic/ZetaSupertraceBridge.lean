import InfoGeometry.Canonical.WeylSupertraceOwner
import InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.Bridge
import InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RelativeDeterminant

/-!
# Zeta/supertrace routing marker

The former contents of this module were two conditional hypothesis packets:

* a `Tendsto` witness for finite Euler readouts, and
* a supplied equivalence between a scalar function zero and a linear-kernel
  witness.

Neither packet constructed an Euler-product limit, an analytic continuation,
an operator determinant, or a noncommutative zero-spectrum theorem.  Keeping
those fields under this legacy name made a hypothesis socket look like a
proved supertrace bridge.

The maintained owners are now imported explicitly:

* `Canonical.WeylSupertraceOwner` owns the finite parity/Weyl supertrace and
  its proved inverse-zeta statement on the stated half-plane;
* `MajoranaPolyaHilbertSocket.Bridge` owns the typed Majorana/Pólya--Hilbert
  obligation packet;
* `MajoranaPolyaHilbertSocket.RelativeDeterminant` owns the typed relative
  determinant/scattering target.

No declarations are re-exported here.  In particular, this marker does not
claim a completed noncommutative determinant identity or a zero correspondence.
-/

