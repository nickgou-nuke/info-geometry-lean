

namespace InfoGeometry.Hardware

/-!
# Persistent Tensor Core Accelerated Modular Flow

This module defines the FFI bindings to the NVIDIA Tensor Core backend
with Pinned Memory (Page-Locked) and Persistent CUDA Context (Zero-Overhead).
-/

/-- 
Opaque reference to the C++ TwistorEngine class.
Managed automatically by Lean's reference counter (engine_finalizer).
-/
opaque TwistorEngine : Type

@[extern "cuda_init_twistor_engine"]
opaque initTwistorEngine (N : UInt32) : IO TwistorEngine

@[extern "cuda_execute_twistor_engine"]
opaque executeTwistorEngine (engine : TwistorEngine) (t : Float) (rawPixels : FloatArray) : FloatArray

end InfoGeometry.Hardware
