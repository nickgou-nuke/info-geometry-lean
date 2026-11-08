import InfoGeometry.Clifford.HestenesNaturalConeStandardForm
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.TwistorZornEmbedding

namespace InfoGeometry.Exceptional.CUDA

/--
The Lean 4 representation of the Twistor Field SoA layout for CUDA execution.
Each array must be of size N, containing the real and imaginary parts of the 
4 components of the Twistors.
-/
@[extern "cuda_execute_modular_flow"]
opaque hardwareModularFlow (N : UInt32) (t : Float)
  (z00_re z00_im z10_re z10_im z01_re z01_im z11_re z11_im : FloatArray) : IO Unit

end InfoGeometry.Exceptional.CUDA
