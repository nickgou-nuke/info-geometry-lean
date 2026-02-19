
-- 1. FOUNDATIONS & ALGEBRA
import InfoGeometry.Architecture.SymmetricSpace
import InfoGeometry.Core.Involution
import InfoGeometry.Core.UnifiedGeometry
import InfoGeometry.Core.SymmetricLie
import InfoGeometry.Core.SymmetricLieGeneric
import InfoGeometry.Analytic.LogSumExp
import InfoGeometry.Analytic.Softmax
import InfoGeometry.Convex.Bregman
import InfoGeometry.Convex.Duality
import InfoGeometry.Convex.FenchelConjugate
import InfoGeometry.Convex.HessianGeometry
import InfoGeometry.Convex.Legendre
import InfoGeometry.Convex.ProjectiveRays
import InfoGeometry.Convex.RadonHelly
import InfoGeometry.Geometry.KreinAsHessian
import InfoGeometry.Geometry.DualFlat
import InfoGeometry.Geometry.LegendreDuality
import InfoGeometry.Information.MultiLogPotential
import InfoGeometry.Potential.LogPotential
import InfoGeometry.KL
import InfoGeometry.MaxEnt.Core
import InfoGeometry.MaxEnt.Finite
import InfoGeometry.MaxEnt.Lagrange
import InfoGeometry.MaxEnt.Optimality
import InfoGeometry.MaxEnt.Jaynes
import InfoGeometry.MaxEnt.JaynesCanonical
import InfoGeometry.MaxEnt.JaynesInfoStatMech
import InfoGeometry.MaxEnt.JaynesRNMaxEnt
import InfoGeometry.SLT.ConditionalExpectation
import InfoGeometry.ExponentialFamily.Finite
import InfoGeometry.ExponentialFamily.Legendre
import InfoGeometry.ExponentialFamily.KLBregman
import InfoGeometry.Clifford.Lift
import InfoGeometry.Clifford.Tower
import InfoGeometry.GrandCanonical.Core
import InfoGeometry.Jordan.Core
import InfoGeometry.Jordan.SPD
import InfoGeometry.Jordan.LogDet
import InfoGeometry.Krein.Modular
import InfoGeometry.Krein.HilbertBridge
import InfoGeometry.Krein.Thermal
import InfoGeometry.Projective.GaugeQuotient
import InfoGeometry.Projective.Null
import InfoGeometry.Projective.PhysicalKinematics
import InfoGeometry.Twistor
import InfoGeometry.Quantum.Fock
import InfoGeometry.Prequantum.Connection
import InfoGeometry.Thermo.Gibbs
import InfoGeometry.Thermo.FromBregman
import InfoGeometry.Thermo.FromLogDet
import InfoGeometry.Basic
import InfoGeometry.Clifford.Cl11
import InfoGeometry.Clifford.Grading
import InfoGeometry.Clifford.Supercharge
import InfoGeometry.Krein.Metric
import InfoGeometry.Krein.Automorphisms
import InfoGeometry.Quantum.Fock          -- The Rosetta Stone (Data = Creation)
import InfoGeometry.SuperUnified          -- The KKT Construction (Clifford = Lie + Jordan)
import InfoGeometry.Projective.Rays
import InfoGeometry.Projective.ProjectiveMap
import InfoGeometry.Prequantum.Connection -- The Weyl Gauge & Berry Curvature
import InfoGeometry.Geometry.DualFlat     -- Pythagorean Theorem for Inference
import InfoGeometry.Convex.Legendre
import InfoGeometry.Convex.HessianGeometry
import InfoGeometry.Thermo.Gibbs
import InfoGeometry.MaxEnt.Core
import InfoGeometry.MaxEnt.Finite
import InfoGeometry.EntropicInference
import InfoGeometry.TransformationGroups

/-!
# InfoGeometry

Core information-geometric constructions.

## Exposed modules

--------------------------------------------------------------------------------
   INFO GEOMETRY: A GRAND UNIFIED FORMALIZATION IN LEAN 4
--------------------------------------------------------------------------------

   Този файл служи като входна точка за цялата библиотека.
   Той обединява трите стълба на теорията:
   1. Алгебра (Clifford/Krein/Fock)
   2. Геометрия (Projective/Bundle/Connection)
   3. Статистика (Hessian/Thermo/MaxEnt)
-/

/-!
# Обобщение на Теорията

Тази библиотека доказва формално, че следните структури са изоморфни:

1. **Статистическо Многообразие** със структура на Hessian (Dual Flat).
2. **Квантово Пространство на Фок** върху Krein пространство с индефинитна метрика.
3. **Келерово Многообразие** с калибровъчна симетрия (Weyl Gauge).

## Ключови Теореми

* `InfoGeometry.Geometry.DualFlat.bayesian_update_pythagorean`:
  Бейсовият ъпдейт е ортогонална проекция.

* `InfoGeometry.Quantum.Fock.creation_annihilation_orthogonal`:
  Данните и Моделът са алгебрично ортогонални (в плоския лимит).

* `InfoGeometry.SuperUnified.bracket_fermion_fermion_is_bosonic`:
  Взаимодействието на статистически ъпдейти (фермиони) генерира времева еволюция (бозон).

* `InfoGeometry.Projective.Connection.curvature_gauge_invariant_linear`:
  Физическата реалност (кривината) не зависи от мащаба на нормализация (калибровката).
-/
