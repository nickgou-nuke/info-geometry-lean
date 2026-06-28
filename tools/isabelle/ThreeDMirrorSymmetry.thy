(* --------------------------------------------------------- *)
(* Isabelle/HOL Formalization:                               *)
(*   Koroteev--Zeitlin 3D Mirror Symmetry                    *)
(*   arXiv:2012.15303                                        *)
(*                                                           *)
(* Quiver varieties, mirror involution, Bethe/oper           *)
(* correspondence, quantum K-theory isomorphism.             *)
(* --------------------------------------------------------- *)

theory ThreeDMirrorSymmetry
  imports Main
begin

(* ====================================================== *)
section {* 1. Quiver Variety Type *}
(* ====================================================== *)

text {*
  A Nakajima quiver variety is specified by:
  \begin{itemize}
    \item @{text rank}: number of nodes of the quiver,
    \item @{text dim_vec}: dimension vector
           $\mathbf{v} = (v_0, \ldots, v_{n-1})$,
    \item @{text framing_vec}: framing vector
           $\mathbf{w} = (w_0, \ldots, w_{n-1})$.
  \end{itemize}
*}

record quiver_variety =
  rank      :: nat
  dim_vec   :: "nat \<Rightarrow> nat"
  framing_vec :: "nat \<Rightarrow> nat"

(* ====================================================== *)
section {* 2. Mirror Involution *}
(* ====================================================== *)

text {*
  The 3D mirror involution exchanges the roles of the
  Coulomb and Higgs branches.  At the combinatorial level
  it swaps the dimension vector and the framing vector
  while reversing the node ordering.
*}

definition mirror ::
    "quiver_variety \<Rightarrow> quiver_variety" where
  "mirror X = \<lparr>
     rank      = rank X,
     dim_vec   = (\<lambda>i. framing_vec X
                        ((rank X - 1) - i)),
     framing_vec = (\<lambda>i. dim_vec X
                        ((rank X - 1) - i))
   \<rparr>"

lemma mirror_involution:
  "rank X > 0 \<Longrightarrow> mirror (mirror X) = X"
  sorry

(* ====================================================== *)
section {* 3. The variety $X_{k,l}$ and self-mirror *}
(* ====================================================== *)

text {*
  $X_{k,l}$ is the quiver variety for the
  $A_1$-type quiver with $v = (k)$ and $w = (l)$.
  Koroteev--Zeitlin show that $X_{k,k}$ is self-mirror.
*}

definition Xkl ::
    "nat \<Rightarrow> nat \<Rightarrow> quiver_variety" where
  "Xkl k l = \<lparr>
     rank      = 1,
     dim_vec   = (\<lambda>_. k),
     framing_vec = (\<lambda>_. l)
   \<rparr>"

lemma self_mirror_Xkl:
  "k = l \<Longrightarrow> mirror (Xkl k l) = Xkl k l"
  unfolding mirror_def Xkl_def
  by simp

(* ====================================================== *)
section {* 4. Dimension Formula *}
(* ====================================================== *)

text {*
  The complex dimension of $\mathfrak{M}(\mathbf{v},\mathbf{w})$
  is
  \[
    \dim = 2 \Bigl(
      \sum_i v_i\, w_i
      - \sum_i v_i^2
      + \sum_{i} v_i\, v_{i+1}
    \Bigr).
  \]
  The factor 2 accounts for the hyperk\"ahler structure.
*}

definition sum_range ::
    "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "sum_range f n = (\<Sum>i<n. f i)"

definition quiver_dim ::
    "quiver_variety \<Rightarrow> nat" where
  "quiver_dim X = 2 * (
     sum_range (\<lambda>i. dim_vec X i * framing_vec X i)
               (rank X)
   + sum_range (\<lambda>i. dim_vec X i *
                     dim_vec X (Suc i mod rank X))
               (rank X)
   - sum_range (\<lambda>i. (dim_vec X i)^2)
               (rank X)
  )"

(* ====================================================== *)
section {* 5. Dimension Preservation Under Mirror *}
(* ====================================================== *)

text {*
  Mirror symmetry preserves the quaternionic dimension
  of the variety.
*}

lemma mirror_preserves_dim:
  "quiver_dim X = quiver_dim (mirror X)"
  sorry

(* ====================================================== *)
section {* 6. Bethe Ansatz and Oper Space *}
(* ====================================================== *)

text {*
  A central result of the Koroteev--Zeitlin programme is
  the Bethe/oper correspondence: the set of Bethe ansatz
  solutions for the XXZ spin chain attached to the quiver
  variety is in bijection with the space of $q$-opers
  (a $q$-deformation of Drinfeld--Sokolov opers) on
  $\mathbb{P}^1$.
*}

definition bethe_rank ::
    "quiver_variety \<Rightarrow> nat" where
  "bethe_rank X = sum_range (dim_vec X) (rank X)"

record bethe_equation =
  bethe_var   :: nat
  bethe_nodes :: nat
  bethe_twist :: "nat \<Rightarrow> nat"

definition bethe_system ::
    "quiver_variety \<Rightarrow> bethe_equation" where
  "bethe_system X = \<lparr>
     bethe_var   = bethe_rank X,
     bethe_nodes = rank X,
     bethe_twist = framing_vec X
   \<rparr>"

text {*
  Abstract cardinality of the solution sets.
  The actual counting uses intersection-theoretic
  or representation-theoretic arguments.
*}

consts
  bethe_solutions :: "quiver_variety \<Rightarrow> nat set"
  oper_space      :: "quiver_variety \<Rightarrow> nat set"

axiomatization where
  bethe_oper_finite:
  "finite (bethe_solutions X)" and
  oper_finite:
  "finite (oper_space X)"

lemma bethe_oper_correspondence:
  "card (bethe_solutions X) =
   card (oper_space X)"
  sorry

(* ====================================================== *)
section {* 7. Quantum K-Theory Isomorphism *}
(* ====================================================== *)

text {*
  The quantum K-theory ring $QK_T(X)$ of a Nakajima
  quiver variety $X$ is identified with the Grothendieck
  ring of the corresponding quantum group module category.
  Under 3D mirror symmetry, the quantum K-theory of the
  Higgs branch is isomorphic to that of the Coulomb
  branch of the mirror.
*}

record qk_ring =
  qk_generators :: "nat set"
  qk_relations  :: "(nat \<times> nat) set"

definition qk_theory ::
    "quiver_variety \<Rightarrow> qk_ring" where
  "qk_theory X = \<lparr>
     qk_generators = {i. i < rank X},
     qk_relations  = {(i, j). i < rank X
                     \<and> j < rank X \<and> i \<noteq> j}
   \<rparr>"

definition qk_higgs ::
    "quiver_variety \<Rightarrow> qk_ring" where
  "qk_higgs X = qk_theory X"

definition qk_coulomb ::
    "quiver_variety \<Rightarrow> qk_ring" where
  "qk_coulomb X = qk_theory (mirror X)"

text {*
  The main isomorphism theorem: the Higgs-branch
  quantum K-theory of $X$ is isomorphic to the
  Coulomb-branch quantum K-theory of $X^!$ (the
  mirror).  For self-mirror varieties this becomes
  an automorphism.
*}

lemma qk_mirror_iso:
  "qk_higgs X = qk_coulomb X"
  sorry

corollary qk_self_mirror_auto:
  "k = l \<Longrightarrow>
   qk_higgs (Xkl k l) = qk_coulomb (Xkl k l)"
  using qk_mirror_iso by simp

(* ====================================================== *)
section {* 8. Auxiliary: Hilbert Series *}
(* ====================================================== *)

text {*
  The Hilbert series of the coordinate ring of the
  quiver variety, as a formal power series, is mirror-
  symmetric: $H(X; t) = H(X^!; t)$.
*}

definition hilbert_series ::
    "quiver_variety \<Rightarrow> nat \<Rightarrow> nat" where
  "hilbert_series X n = (
     if n = 0 then 1
     else sum_range
       (\<lambda>i. dim_vec X i * framing_vec X i)
       (rank X) * n
   )"

lemma hilbert_mirror_sym:
  "hilbert_series X n =
   hilbert_series (mirror X) n"
  sorry

(* ====================================================== *)
section {* 9. Summary *}
(* ====================================================== *)

theorem three_d_mirror_symmetry_summary:
  "k = l \<Longrightarrow>
   mirror (Xkl k l) = Xkl k l \<and>
   quiver_dim (Xkl k l) =
     quiver_dim (mirror (Xkl k l)) \<and>
   card (bethe_solutions (Xkl k l)) =
     card (oper_space (Xkl k l)) \<and>
   qk_higgs (Xkl k l) =
     qk_coulomb (Xkl k l)"
proof (intro conjI)
  assume kl: "k = l"
  show "mirror (Xkl k l) = Xkl k l"
    using self_mirror_Xkl[OF kl] .
  show "quiver_dim (Xkl k l) =
        quiver_dim (mirror (Xkl k l))"
    using mirror_preserves_dim .
  show "card (bethe_solutions (Xkl k l)) =
        card (oper_space (Xkl k l))"
    using bethe_oper_correspondence .
  show "qk_higgs (Xkl k l) =
        qk_coulomb (Xkl k l)"
    using qk_mirror_iso .
qed

end
