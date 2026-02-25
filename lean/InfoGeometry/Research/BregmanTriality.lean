import InfoGeometry.Research.GrandUnification
import InfoGeometry.Research.Triality
import InfoGeometry.Convex.HessianGeometry

namespace InfoGeometry.Research.BregmanTriality

open InfoGeometry.Research.GrandUnification
open InfoGeometry.Research.Triality
open InfoGeometry.Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Bregman-Softmax attention for Jordan/KKT systems.
The interaction score is pinned to -D_K(q, k).
-/
noncomputable def softmaxBregmanAttention
    (J : JordanKKTData E) (I : Finset ℕ) (hI : I.Nonempty) (keys : ℕ → E)
    (route : E → E → E) :
    (letI : BregmanDivergence E E := { D := fun q k => J.DBregman q k }
     GeometricAttentionMap (bregmanTriadicCore (Q := E) (K := E) (V := E) route) ℕ) := by
  letI : BregmanDivergence E E := { D := fun q k => J.DBregman q k }
  exact softmaxAttention (core := bregmanTriadicCore route)
    (I := I) (hI := hI) (keys := keys)

end InfoGeometry.Research.BregmanTriality
