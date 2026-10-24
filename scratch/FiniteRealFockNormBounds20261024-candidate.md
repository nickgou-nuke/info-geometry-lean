# Coordinate Fock norm bounds — implementation candidate

New uncompiled sandbox imports intended native InfoGeometry.Clifford.FiniteRealFockAdjoint
(QA/promotion pending) and Mathlib.Analysis.Normed.Operator.Basic. The accepted
research contract FiniteRealFockNormBounds20261024.md remains unchanged.

fock_coordinate_norm_sq_split derives norm(Cx)^2+norm(Dx)^2=norm(x)^2 from actual
ext_int_anticommutator at Pi.basisFun/LinearMap.proj (unit pairing), the native
coordinate inner-adjoint theorem, real_inner_comm and self-inner norm squares.
No adjoint/CAR/norm assumption or output field is introduced. Each norm bound
uses nonnegativity of the other square and sq_le_sq₀.

fockExtActionCLM / fockIntActionCLM are precisely native extAction/intAction
packaged with mkContinuous at constant 1 using these derived bounds. Application
readbacks are rfl; norm<=1 follows from LinearMap.mkContinuous_norm_le.
The carrier is existing SpinorSpace(Vector n) with the named induced real metric
activated locally only. No global instance, operator replacement, completed
carrier, complexification, arbitrary-mode bound or norm=1 claim.

No build/test/live edit/budget change. All earlier candidates/research preserved.
Parent serial QA must first accept/promote the adjoint dependency and then check
this file. If adjoint diagnostics arrive, its separate repair takes priority.
