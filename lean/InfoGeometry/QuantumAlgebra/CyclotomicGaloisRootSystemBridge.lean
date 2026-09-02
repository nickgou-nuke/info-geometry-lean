import InfoGeometry.QuantumAlgebra.RankTwoCyclotomicArtinBridge

/-! Galois transport for the cyclotomic root-system layer.  The action is
coefficient transport; it is not identified with the Weyl or Artin action. -/
namespace InfoGeometry.QuantumAlgebra.CyclotomicGaloisRootSystemBridge

open InfoGeometry.QuantumAlgebra.RankTwoCyclotomicArtinBridge

variable {R : Type*} [CommRing R]

theorem galois_preserves_cyclotomic10 (σ : R →+* R) (ζ : R)
    (hζ : cyclotomic10 ζ = 0) : cyclotomic10 (σ ζ) = 0 := by
  dsimp [cyclotomic10] at hζ ⊢
  simpa [map_add, map_sub, map_pow] using congrArg σ hζ

theorem galois_preserves_cyclotomic12 (σ : R →+* R) (ζ : R)
    (hζ : cyclotomic12 ζ = 0) : cyclotomic12 (σ ζ) = 0 := by
  dsimp [cyclotomic12] at hζ ⊢
  simpa [map_add, map_sub, map_pow] using congrArg σ hζ

theorem galois_preserves_quantum_dimension_five
    (σ : R →+* R) (d : R) (h : d ^ 2 = d + 1) :
    (σ d) ^ 2 = σ d + 1 := by
  simpa [map_add, map_pow] using congrArg σ h

theorem galois_preserves_quantum_dimension_six
    (σ : R →+* R) (d : R) (h : d ^ 2 = 3) :
    (σ d) ^ 2 = 3 := by
  have hh := congrArg σ h
  simpa only [map_pow, map_ofNat] using hh

theorem galois_preserves_matrix_nilpotency
    (σ : R →+* R) (M : Matrix (Fin 2) (Fin 2) R) (h : M ^ 2 = 0) :
    (matrixGaloisMap σ M) ^ 2 = 0 := by
  rw [← matrixGaloisMap_pow, h]
  ext i j
  simp [matrixGaloisMap]

end InfoGeometry.QuantumAlgebra.CyclotomicGaloisRootSystemBridge
