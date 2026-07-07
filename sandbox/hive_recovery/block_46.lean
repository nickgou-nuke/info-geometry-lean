structure SuperKahlerData (M : Type*) where
  parity : M → ZMod 2
  J : M → M
  g : M → M → K
  omega : M → M → K
  J_sq : ∀ x, J (J x) = -x
  omega_eq_g_J : ∀ x y, omega x y = g (J x) y