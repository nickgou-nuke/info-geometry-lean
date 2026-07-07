import Mathlib
import InfoGeometry.Optics.JonesCalibration
import InfoGeometry.Geometry.OpticalJonesV4

structure JonesOpticalEvent where
  basis : PolarizationBasis
  kind : OpticalSurfaceKind
  coeff0 : ℂ
  coeff1 : ℂ
  tag : V4Tag

