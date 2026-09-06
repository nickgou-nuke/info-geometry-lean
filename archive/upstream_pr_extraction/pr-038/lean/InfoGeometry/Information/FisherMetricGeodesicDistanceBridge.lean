import InfoGeometry.SuperMetriplectic.CasimirHessianFisherBridge
import InfoGeometry.Arithmetic.ChiralPrimonGasFisherMatrixNativePSD
import InfoGeometry.Analysis.SouriauThermodynamics

/-!
# Compatibility surface for native Fisher/BKM geometry

The previous implementation was a standalone diagonal two-coordinate metric
and an assumed affine NESS line.  It was not connected to a measure, a state,
or an observable algebra.  Native Fisher positivity is now supplied by the
positive-functional/C*-GNS owner and the Massieu covariance owners.
-/
