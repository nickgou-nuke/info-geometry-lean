import Mathlib.LinearAlgebra.Basis.Defs
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-- Standard basis of the space of finitely supported functions. -/
noncomputable def Finsupp.basisFun (X R : Type*) [Semiring R] : Module.Basis X R (X →₀ R) where
  repr := (LinearEquiv.refl _ _)
