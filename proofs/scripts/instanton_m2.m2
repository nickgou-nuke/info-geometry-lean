needsPackage "Dmodules"

W = QQ[x, y, z, t, Dx, Dy, Dz, Dt, WeylAlgebra => {
    x => Dx, y => Dy, z => Dz, t => Dt
}]

-- The anomaly is a source term in the divergence of the axial current
-- D_mu J^mu_5 = 2N_f Q_topological
Q_top = x^2 + y^2 + z^2 + t^2 -- Simplified instanton profile
axial_anomaly_ideal = ideal(Dx^2 + Dy^2 + Dz^2 + Dt^2 - Q_top)

-- Holonomic D-module representing the zero-mode constraint
M = W^1 / axial_anomaly_ideal
holonomicRank M
