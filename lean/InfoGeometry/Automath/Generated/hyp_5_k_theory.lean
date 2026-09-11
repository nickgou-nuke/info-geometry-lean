import InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace Automath.Generated

open InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses
open InfoGeometry.Algebra.CuntzTensorQuotient
open CuntzFibonacciBraidInclusion
open Matrix

/--
Reduction-Modulo-(n-1) on K_0: Under K_0(M_n(C)) -> K_0(O_n)/(n-1), the embedding phi induces phi_*: Z -> Z/(n-1) given by reduction mod (n-1). For n=2, K_0(O_2)=0 so the embedding is K-theoretically invisible despite being injective and spectrally faithful. Falsified if phi_*([E_11]) != [1_{O_2}] or if induced map differs from reduction mod (n-1).
The embedding phi(E_{11}) = S_1 S_1^* is Murray-von Neumann equivalent to 1_{O_2}, so the generator maps to 0 in K_0(O_2). The embedding is invisible to ordinary K-theory despite being injective and spectrally faithful. Falsified if phi_*([E_11]) != [1_{O_2}] or induced map differs from reduction mod (n-1).
Source: InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.matrixToCuntz
Objects: k-theory, cuntz-algebra, murray-von-neumann, projection, k0-group -/
theorem hyp_5_k_theory :
    cuntzS 2 (0 : Fin 2) * cuntzSdag 2 (0 : Fin 2) = matrixToCuntz 2 !![1, 0; 0, 0] :=
  hypothesis5_rank_one_projection_equivalence

end Automath.Generated
