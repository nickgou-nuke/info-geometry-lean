# arXiv:2511.22303v2 — theorem-safe relevance note

Paper:
- Thijs Douwes and Marcus Stålhammar
- "Twisted (co)homology of non-orientable Weyl semimetals"
- arXiv:2511.22303v2 [cond-mat.mes-hall]

Why it matters here
- This is direct condensed-matter evidence that non-orientable Brillouin zones, including Klein-bottle-like momentum-space topology induced by glide symmetry, are real research objects rather than metaphor.
- It supports using careful Klein-bottle / glide / Bloch / boundary language around the repo’s finite crystal and inductive-colimit lanes.
- It does not, by itself, prove the stronger holography/LLM identifications in this repository.

Exact extracted support from the paper text
1. Abstract:
   - "When the Brillouin zone is non-orientable, this constraint is replaced by a Z2 charge cancellation..."
   - "A detailed discussion is provided on a specific Klein bottle-like topology induced by a momentum-space glide symmetry..."
   - "...including a full review of the insulating and semimetallic invariants of the system and a classification of the surface states on the non-orientable boundary."
   - "Beyond this, we provide a complete survey of all possible non-orientable Brillouin zones and their associated invariants..."

2. Main body:
   - "Under the correct boundary identifications, this fundamental domain takes on the topology of the non-orientable Klein bottle K^2."
   - "This glide symmetry acts analogously to the one above, yielding a Klein bottle topology in the first two coordinates; with the addition of the periodic kz direction, the final topology of the Brillouin zone becomes K^2 x S^1."
   - Section heading / content explicitly treats `K^2 surface states`.

Safe manuscript paragraph
Recent condensed-matter work gives direct precedent for the non-orientable momentum-space lane used here. Douwes and Stålhammar study Weyl semimetals on non-orientable Brillouin zones and show that the usual orientable chirality-cancellation constraint is replaced by a twisted `Z2` charge-cancellation law. They further analyze a Klein-bottle-like Brillouin-zone topology induced by glide symmetry and classify the associated surface states on the non-orientable boundary. This supports treating Klein-bottle/glide/Bloch language as physically serious background for the repository’s crystal and boundary packets, while remaining distinct from the stronger theorem claims specific to the present Lean formalization.

BibTeX
```bibtex
@article{DouwesStalhammar2025_251122303v2,
  title = {Twisted (co)homology of non-orientable Weyl semimetals},
  author = {Thijs Douwes and Marcus Stålhammar},
  year = {2025},
  eprint = {2511.22303v2},
  archivePrefix = {arXiv},
  primaryClass = {cond-mat.mes-hall},
  url = {https://arxiv.org/abs/2511.22303v2}
}
```

Best repo-level use
- cite it in prose for physical motivation of non-orientable/Klein-bottle Brillouin-zone language;
- do not cite it as authority for repo-native Lean proof closure;
- pair it with the repo’s own finite crystal / inductive-colimit owner files when discussing the finite-to-infinite transition.
