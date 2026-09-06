import InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge
import InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
import InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge

/-!
# Actual entire completed-Xi datum

The abstract `XiFunctionDatum` interface is realized here by the pole-removed
entire representative `entireRiemannXi`.  Both reflection laws are imported
from native arithmetic owners.  This file introduces no Hardy `Z` function,
zero-location theorem, or Riemann-hypothesis claim.
-/

noncomputable section

namespace InfoGeometry.Topology.ActualEntireXiFunctionDatumBridge

open InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge

def actualEntireRiemannXiFunctionDatum :
    XiFunctionDatum entireRiemannXi where
  functional_eq := entireRiemannXi_one_sub
  schwarz_refl := fun s => (entireRiemannXi_conj s).symm

theorem actualEntireRiemannXi_critical_line_is_real (t : ℝ) :
    star (entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ))) =
      entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) := by
  exact xi_critical_line_is_real entireRiemannXi
    actualEntireRiemannXiFunctionDatum t

end InfoGeometry.Topology.ActualEntireXiFunctionDatumBridge
