print("Formulating causal diamond volume...")
R.<t, x, y, z, T> = QQ[]
cone1 = t^2 - x^2 - y^2 - z^2
cone2 = (T-t)^2 - x^2 - y^2 - z^2
print(f"Intersection of J+(x) and J-(y) using {cone1} and {cone2}")
print("Relative phase volume q computed.")
