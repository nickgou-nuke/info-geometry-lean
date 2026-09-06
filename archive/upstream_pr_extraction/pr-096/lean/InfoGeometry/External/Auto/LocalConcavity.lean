structure Point where
  x : Int
  y : Int

/-- The determinant of the 3x3 orientation matrix for points in R^2 (using Int for simplicity). --/
def orientation_det (p q r : Point) : Int :=
  (q.x - p.x) * (r.y - p.y) - (q.y - p.y) * (r.x - p.x)

/-- Collinearity defined based on the determinant being exactly zero. --/
def is_collinear (p q r : Point) : Prop :=
  orientation_det p q r = 0

/-- Convexity (counter-clockwise orientation) based on a positive determinant. --/
def is_convex (p q r : Point) : Prop :=
  orientation_det p q r > 0

/-- Concavity (clockwise orientation) based on a negative determinant. --/
def is_concave (p q r : Point) : Prop :=
  orientation_det p q r < 0
