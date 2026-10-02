import InfoGeometry.Clifford.SplitCliffordTransformKernel
import InfoGeometry.Algebra.SplitCliffordTransformKernel
import InfoGeometry.OperatorAlgebra.IwasawaKANTransform

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SplitCliffordTransformFunctoriality

open InfoGeometry.Clifford.SplitCliffordTransformKernel
open InfoGeometry.OperatorAlgebra.IwasawaKAN

variable {Source Target : Type*} [Ring Source] [Algebra ℝ Source]
  [Ring Target] [Algebra ℝ Target]

theorem map_peircePlus (representation : Source →ₐ[ℝ] Target)
    (generator : Source) :
    representation (peircePlus generator) = peircePlus (representation generator) := by
  simp [peircePlus]

theorem map_peirceMinus (representation : Source →ₐ[ℝ] Target)
    (generator : Source) :
    representation (peirceMinus generator) = peirceMinus (representation generator) := by
  simp [peirceMinus]

theorem map_hyperbolicKernel (representation : Source →ₐ[ℝ] Target)
    (generator : Source) (parameter : ℝ) :
    representation (hyperbolicKernel generator parameter) =
      hyperbolicKernel (representation generator) parameter := by
  simp [hyperbolicKernel, map_peircePlus, map_peirceMinus]

theorem map_ellipticKernel (representation : Source →ₐ[ℝ] Target)
    (generator : Source) (parameter : ℝ) :
    representation (ellipticKernel generator parameter) =
      ellipticKernel (representation generator) parameter := by
  simp [ellipticKernel]

theorem map_parabolicKernel (representation : Source →ₐ[ℝ] Target)
    (generator : Source) (parameter : ℝ) :
    representation (parabolicKernel generator parameter) =
      parabolicKernel (representation generator) parameter := by
  simp [parabolicKernel]

def representedKAN (representation : Source →ₐ[ℝ] Target)
    (datum : IwasawaKANClifford Source) : IwasawaKANClifford Target where
  B := representation datum.B
  K_op := representation datum.K_op
  hB := by
    rw [← map_mul, datum.hB]
    simp
  hK := by
    rw [← map_mul, datum.hK, map_one]
  anticomm := by
    rw [← map_mul, ← map_mul, ← map_add, datum.anticomm, map_zero]

theorem map_flow_K (representation : Source →ₐ[ℝ] Target)
    (datum : IwasawaKANClifford Source) (parameter : ℝ) :
    representation (datum.flow_K parameter) =
      (representedKAN representation datum).flow_K parameter := by
  simp [IwasawaKANClifford.flow_K, representedKAN]

theorem map_flow_A (representation : Source →ₐ[ℝ] Target)
    (datum : IwasawaKANClifford Source) (parameter : ℝ) :
    representation (datum.flow_A parameter) =
      (representedKAN representation datum).flow_A parameter := by
  simp [IwasawaKANClifford.flow_A, representedKAN]

theorem map_flow_N (representation : Source →ₐ[ℝ] Target)
    (datum : IwasawaKANClifford Source) (parameter : ℝ) :
    representation (datum.flow_N parameter) =
      (representedKAN representation datum).flow_N parameter := by
  simp [IwasawaKANClifford.flow_N, IwasawaKANClifford.N_plus, representedKAN]

theorem map_iwasawa_element (representation : Source →ₐ[ℝ] Target)
    (datum : IwasawaKANClifford Source) (angle rapidity shear : ℝ) :
    representation (datum.iwasawa_element angle rapidity shear) =
      (representedKAN representation datum).iwasawa_element angle rapidity shear := by
  simp only [IwasawaKANClifford.iwasawa_element, map_mul,
    map_flow_K, map_flow_A, map_flow_N]

theorem flow_K_eq_ellipticKernel (datum : IwasawaKANClifford Source)
    (parameter : ℝ) : datum.flow_K parameter = ellipticKernel datum.B parameter := rfl

theorem flow_A_eq_hyperbolicKernel (datum : IwasawaKANClifford Source)
    (parameter : ℝ) : datum.flow_A parameter = hyperbolicKernel datum.K_op parameter := by
  simpa [IwasawaKANClifford.flow_A, hyperbolicKernel, peircePlus, peirceMinus,
    _root_.SplitCliffordTransformKernel.hyperbolicKernel,
    _root_.SplitCliffordTransformKernel.peircePlus,
    _root_.SplitCliffordTransformKernel.peirceMinus, one_div] using
    (_root_.SplitCliffordTransformKernel.hyperbolicKernel_eq_peirce datum.K_op parameter)

theorem flow_N_eq_parabolicKernel (datum : IwasawaKANClifford Source)
    (parameter : ℝ) : datum.flow_N parameter = parabolicKernel datum.N_plus parameter := rfl

end InfoGeometry.OperatorAlgebra.SplitCliffordTransformFunctoriality
