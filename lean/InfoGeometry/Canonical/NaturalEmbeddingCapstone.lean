import InfoGeometry.Projective.NaturalEmbedding
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.NaturalEmbeddingCapstone

open InfoGeometry.Projective.NaturalEmbedding

theorem capstone_natural_embedding_synthesis (n : ℕ) (p : ℝ) (hp : p ≠ 0) :
    (naturalEmbed n p).1 / (naturalEmbed n p).2 = (n : ℝ) := by
  exact natural_embed_ratio n p hp

end InfoGeometry.Canonical.NaturalEmbeddingCapstone
