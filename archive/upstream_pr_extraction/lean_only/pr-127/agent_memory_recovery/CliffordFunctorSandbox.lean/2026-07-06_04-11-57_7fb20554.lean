  map_comp {l m n} f g := by
    ext x
    simp
    have h_comp : iso l n (leOfHom (f ≫ g)) = (iso m n (leOfHom g)).comp (iso l m (leOfHom f)) :=
      (iso_comp l m n (leOfHom f) (leOfHom g)).symm
    have h_eq : (iso l n (leOfHom (f ≫ g))) x = (iso m n (leOfHom g)) ((iso l m (leOfHom f)) x) := by
      rw [h_comp]
      rfl
    rw [h_eq]
