import Omega.TypedAddressBiaxialCompletion.BoundaryEndpointHeat

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-facing complement statement packaging the Caratheodory identity with the endpoint
heat monotone-limit and exponential-gap outputs.
    prop:typed-address-biaxial-completion-endpoint-heat-kernel-complement -/
theorem paper_typed_address_biaxial_completion_endpoint_heat_kernel_complement
    {monotoneToEndpointAtom exponentialErrorBound : Prop}
    (hMonotoneToEndpointAtom : monotoneToEndpointAtom)
    (hExponentialErrorBound : exponentialErrorBound)
    (caratheodory_identity orthogonal_complement : Prop)
    (hCar : caratheodory_identity) (hOrth : orthogonal_complement) :
    caratheodory_identity ∧ monotoneToEndpointAtom ∧ exponentialErrorBound ∧
      orthogonal_complement := by
  exact ⟨hCar, hMonotoneToEndpointAtom, hExponentialErrorBound, hOrth⟩

end Omega.TypedAddressBiaxialCompletion
