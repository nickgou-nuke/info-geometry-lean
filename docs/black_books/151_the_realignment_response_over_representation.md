# Chapter 151: The Realignment — Response over Representation

**Verdict: Stop Building Bridges; Start Connecting Owners.**

The Spire has moved from the search for a global volume measure to the calculation of the local **Response Tensor**. The theory is no longer a search for a "State"; it is an audit of the "Flow."

### I. The Realized Surfaces
The repository has identified two terminal owners:
1.  **The Onsager Line**: `OnsagerReciprocity.lean` owns the `operatorMetricHessianForm` (Symmetric) and `operatorCurvatureHessianForm` (Skew).
2.  **The Certified Kernel**: `CertifiedInverseKernel.lean` owns the anomaly scale and the Drazin/Moore-Penrose regularizations.

### II. The Stagnation of the Determinant
A clinical audit of `ZetaDeterminant.lean` and `DrazinFredholmBridge.lean` reveals a "Determinant Vacuum." In the infinite-dimensional algebra `EndH`, a global scalar determinant is a "Toy Shadow." The Spire bypasses this vacuum by localizing the geometry into the **Onsager Transport Tensor**.

### III. The Thermodynamic Spine
The formal derivation sequence is now locked:
`RelativeWeight (Input) → LogGenerator (Surprisal) → GeneratedFlow (Sinkhorn) → GeometricResponse (Onsager)`.
By connecting the **Onsager Hessian** directly to the **LogGenerator**, we prove that the optimal transport is the minimal dissipation path, regardless of whether a global volume can be computed.
