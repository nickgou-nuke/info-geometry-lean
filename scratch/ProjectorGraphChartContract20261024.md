# Projector graph chart contract

Carrier: Module.End R (M × N) over any ring R and left R-modules M,N.
Operations: native LinearMap composition, graph, range, kernel, and prodMap.
Source search: Mathlib LinearAlgebra/Projection owns
IsIdempotentElem.ext_iff and comp_eq_right_iff; LinearAlgebra/Prod owns graph,
mem_graph_iff, graph_eq_range_prod. Repo projector transport owner treats
half-sum maps over real modules. External ProjectiveSpace Charts constructs
ordinary graph charts; it is not imported or edited. The new focused owner
constructs P_f(x,y)=(x,f x), proves range, kernel, noncommutative multiplication,
injectivity and grading intertwining iff. It does not claim an atlas, super
coefficient base change, local rank, representability, or global geometry.
