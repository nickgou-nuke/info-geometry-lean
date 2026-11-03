/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.ChernClassInstantonTopologicalBridge
import InfoGeometry.Canonical.MatrixTracedChernWeilBridge
import InfoGeometry.Canonical.TracedChernWeilCohomologyClassBridge
import InfoGeometry.Canonical.MatrixCurvatureWedgeSquareBridge
import InfoGeometry.Canonical.CovariantBianchiMatrixChernWeilBridge
import InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
import InfoGeometry.Canonical.ExteriorGradedDerivationBridge
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Field.Defs

noncomputable section

namespace InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.TracedChernWeilCohomologyClassBridge
open InfoGeometry.Canonical.MatrixCurvatureWedgeSquareBridge
open InfoGeometry.Canonical.CovariantBianchiMatrixChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.ExteriorGradedDerivationBridge
open BigOperators
open Finset

variable {R V : Type*} [Field R] [AddCommGroup V] [Module R V] {n : ℕ}

def curvatureFromConnection
    (d : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    Matrix (Fin n) (Fin n) (ExteriorAlgebra R V) :=
  matrixExteriorDerivative d A + A * A

def chernSimonsDensityForm
    (d : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    ExteriorAlgebra R V :=
  matrixTraceForm (A * matrixExteriorDerivative d A + (2 / 3 : R) • (A * A * A))

def IsHomogeneousExteriorDegree (k : ℕ) (x : ExteriorAlgebra R V) : Prop :=
  x ∈ (Submodule.span R (Set.range (fun (v : Fin k → V) => List.prod (List.ofFn (fun i => ι R (v i))))))

def MatrixIsHomogeneous (k : ℕ) (M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) : Prop :=
  ∀ i j, IsHomogeneousExteriorDegree k (M i j)

end InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
