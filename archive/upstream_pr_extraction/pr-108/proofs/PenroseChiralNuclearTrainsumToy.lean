import proofs.QuaternionQuanticsBackendDigest

/-!
# Penrose/chiral many-body nuclear trainsum toy

Theorem-honest finite digest for the external script
`proofs/penrose_chiral_nuclear_trainsum.py`.

The script uses the locally installed `trainsum` package to build a small
spin-1/2 many-body Hamiltonian on an eight-site Fibonacci/Penrose-inspired chord
graph, checks dense Hermiticity and a parity/chiral selection rule, diagonalizes
the finite Hamiltonian, and stores the ground-state vector as a quantics tensor
train.

Lean records only the finite bookkeeping:

* eight sites;
* Hilbert dimension `2^8 = 256`;
* the Fibonacci word used by the graph has length eight;
* the deterministic chord graph has sixteen undirected edges;
* the clique/plaquette list has eight oriented chiral triangles.
-/

namespace PenroseChiralNuclearTrainsumToy

/-- Number of spin-1/2 sites in the first toy model. -/
def toySiteCount : ℕ := 8

/-- Dense Hilbert dimension of eight spin-1/2 sites. -/
def toyHilbertDim : ℕ := 2 ^ toySiteCount

/-- Fibonacci/Sturmian word used to decide Penrose-like chords. -/
def fibonacciWord8 : List ℕ := [0, 1, 0, 1, 1, 0, 1, 0]

/-- Undirected Penrose/Fibonacci chord graph used by the numerical toy. -/
def penroseChordEdges8 : List (ℕ × ℕ) :=
  [(0,1), (0,3), (0,5), (0,6), (0,7),
   (1,2), (1,3), (2,3), (2,5), (2,7),
   (3,4), (3,5), (4,5), (4,6), (5,6), (6,7)]

/-- Oriented chiral triangles/cliques used by the numerical toy. -/
def chiralTriangles8 : List (ℕ × ℕ × ℕ) :=
  [(0,1,3), (0,3,5), (0,5,6), (0,6,7),
   (1,2,3), (2,3,5), (3,4,5), (4,5,6)]

@[simp] theorem toy_site_count_eq : toySiteCount = 8 := rfl

@[simp] theorem toy_hilbert_dim_eq : toyHilbertDim = 256 := rfl

@[simp] theorem fibonacci_word8_length : fibonacciWord8.length = 8 := rfl

@[simp] theorem penrose_chord_edges8_length : penroseChordEdges8.length = 16 := rfl

@[simp] theorem chiral_triangles8_length : chiralTriangles8.length = 8 := rfl

/-- Dense parity sector size for eight spin-1/2 sites. -/
def paritySectorDim8 : ℕ := toyHilbertDim / 2

@[simp] theorem parity_sector_dim8_eq : paritySectorDim8 = 128 := rfl

/-- Local operator labels used by the toy Hamiltonian. -/
inductive LocalPauli where
  | X | Y | Z
  deriving DecidableEq, Repr

/-- Term families in the toy Hamiltonian. -/
inductive PenroseChiralNuclearTerm where
  | onsiteZ
  | exchangeXX
  | exchangeYY
  | anisotropyZZ
  | chiralZXY
  | chiralZYX
  deriving DecidableEq, Repr

/-- Six finite term families are represented in the external model. -/
def termFamilies : List PenroseChiralNuclearTerm :=
  [.onsiteZ, .exchangeXX, .exchangeYY, .anisotropyZZ, .chiralZXY, .chiralZYX]

@[simp] theorem term_families_length : termFamilies.length = 6 := rfl

/-- Capstone: finite graph/Hilbert-space bookkeeping compiles. -/
theorem penrose_chiral_nuclear_trainsum_toy_synthesis :
    toySiteCount = 8 ∧
    toyHilbertDim = 256 ∧
    fibonacciWord8.length = 8 ∧
    penroseChordEdges8.length = 16 ∧
    chiralTriangles8.length = 8 ∧
    paritySectorDim8 = 128 ∧
    termFamilies.length = 6 ∧
    QuaternionQuanticsBackendDigest.quanticsFullDimension 2 8 = 256 := by
  exact ⟨toy_site_count_eq,
    toy_hilbert_dim_eq,
    fibonacci_word8_length,
    penrose_chord_edges8_length,
    chiral_triangles8_length,
    parity_sector_dim8_eq,
    term_families_length,
    rfl⟩

end PenroseChiralNuclearTrainsumToy
