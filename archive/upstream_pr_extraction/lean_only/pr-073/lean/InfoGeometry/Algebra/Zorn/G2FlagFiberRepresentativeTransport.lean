import InfoGeometry.Algebra.Zorn.G2Fin189Certificate
import InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative

/-!
# Transport from the canonical `G₂` flag fiber to concrete representatives

The canonical fiber and the exported 189-word representative carrier are
different objects.  This owner supplies their explicit typed transport; it
does not assert the missing factorization or quotient-injectivity theorem.
-/

namespace InfoGeometry.Algebra.Zorn.G2FlagFiberRepresentativeTransport

open InfoGeometry.Algebra.Zorn.G2Fin189Certificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordEvaluator
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def flagFiberIndex (x : FlagFiber) : Fin 189 :=
  flagFiberEquivFin189 x

noncomputable def flagFiberRepresentative (x : FlagFiber) :
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut :=
  flagRepresentative (flagFiberIndex x)

noncomputable def flagFiberQuotientRepresentative
    (x : FlagFiber) : CarrierQuotient :=
  quotientRepresentative (flagFiberIndex x)

@[simp] theorem flagFiberIndex_apply (x : FlagFiber) :
    flagFiberIndex x = flagFiberEquivFin189 x :=
  rfl

@[simp] theorem flagFiberRepresentative_apply (x : FlagFiber) :
    flagFiberRepresentative x = flagRepresentative (flagFiberIndex x) :=
  rfl

@[simp] theorem flagFiberQuotientRepresentative_apply (x : FlagFiber) :
    flagFiberQuotientRepresentative x =
      quotientRepresentative (flagFiberIndex x) :=
  rfl

theorem flagFiberIndex_surjective : Function.Surjective flagFiberIndex :=
  flagFiber_equiv_fin189_surjective

theorem flagFiberIndex_injective : Function.Injective flagFiberIndex :=
  flagFiber_equiv_fin189_injective

theorem flagFiberRepresentative_mem (x : FlagFiber) :
    flagFiberRepresentative x ∈
      flagGeneratedSubgroup :=
  flagRepresentative_mem _

end InfoGeometry.Algebra.Zorn.G2FlagFiberRepresentativeTransport
