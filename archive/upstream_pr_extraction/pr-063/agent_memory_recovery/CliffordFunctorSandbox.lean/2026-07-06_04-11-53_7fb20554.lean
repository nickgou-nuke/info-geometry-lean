  map {n m} h := AlgCat.ofHom (CliffordAlgebra.map (iso n m (leOfHom h)))
  map_id X := by
    ext x
    simp [iso_id]
  map_comp {l m n} f g := by
    ext x
    simp
    have h_comp : iso l n (leOfHom (f ≫ g)) = (iso m n (leOfHom g)).comp (iso l m (leOfHom f)) :=