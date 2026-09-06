import InfoGeometry.Projective.NaturalEmbedding

namespace InfoGeometry.Canonical.NaturalEmbeddingCapstone

open InfoGeometry.Projective.NaturalEmbedding

theorem capstone_natural_embedding_synthesis (n : ℕ) (p : ℝ) (hp : p ≠ 0) :
    (naturalEmbed n p).1 / (naturalEmbed n p).2 = (n : ℝ) :=
  grand_natural_embedding_synthesis n p hp

end InfoGeometry.Canonical.NaturalEmbeddingCapstone
