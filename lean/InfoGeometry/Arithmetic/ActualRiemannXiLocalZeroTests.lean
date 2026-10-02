import InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge
import InfoGeometry.Arithmetic.ZetaSymmetryHeuristicComplement
import InfoGeometry.Arithmetic.RiemannLectureDependencies
import InfoGeometry.Arithmetic.SarnakLocalCertification

namespace InfoGeometry.Arithmetic.ActualRiemannXiLocalZeroTests

open ActualRiemannXiEntireBridge ActualRiemannXiEntireSchwarzBridge
open ZetaSymmetryHeuristicComplement

example {region : Set ℂ} {point : ℂ}
    (invariant : Set.MapsTo (fun value : ℂ => 1 - star value) region region)
    (unique : (region ∩ {value | entireRiemannXi value = 0}).Subsingleton)
    (member : point ∈ region) (zero_at_point : entireRiemannXi point = 0) :
    point.re = 1 / 2 :=
  entireRiemannXi_unique_zero_in_invariant_region_critical
    invariant unique member zero_at_point

example : ∃ function : ℂ → ℂ, ∃ point : ℂ,
    EvenCentered function ∧ ZeroAt function point ∧
      ZeroAt function (-point) ∧ point.re ≠ 0 :=
  even_symmetry_allows_off_axis_zero_pair

#print axioms entireRiemannXi_one_sub_star
#print axioms entireRiemannXi_reflected_zero
#print axioms entireRiemannXi_unique_zero_in_invariant_region_critical
#print axioms even_symmetry_allows_off_axis_zero_pair
#print axioms entire_symmetry_allows_off_line_zero_in_strip
#print axioms RiemannLectureDependencies.arithmetic_branch
#print axioms RiemannLectureDependencies.symmetry_branch
#print axioms RiemannLectureDependencies.local_certificate_branch
#print axioms RiemannLectureDependencies.arithmetic_and_local_certificate_incomparable
#print axioms RiemannLectureDependencies.symmetry_does_not_supply_uniqueness
#print axioms RiemannLectureDependencies.no_cycle
#print axioms SarnakLocalCertification.CertifiedRegion.zero_on_critical_line
#print axioms SarnakLocalCertification.CertifiedRegion.nonzero_off_critical_line
#print axioms SarnakLocalCertification.covered_zeros_on_critical_line
#print axioms SarnakLocalCertification.finite_height_certificate
#print axioms SarnakLocalCertification.global_confinement_of_certificates_at_every_height
#print axioms SarnakLocalCertification.symmetric_functions_need_not_have_critical_zeros

end InfoGeometry.Arithmetic.ActualRiemannXiLocalZeroTests
