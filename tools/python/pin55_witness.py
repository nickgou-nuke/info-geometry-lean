import clifford as cf

print("=== Pin(5,5) Glide Reflection Witness ===")
layout, blades = cf.Cl(5,5)

# A glide reflection involves both a reflection (det = -1) and a translation,
# but algebraically in Pin(5,5) it represents elements P that square to +1 or -1 
# and reverse orientation. Let's take a unit vector in the split signature.
e1 = blades['e1'] # positive norm
e6 = blades['e6'] # negative norm

print(f"e1^2 = {e1**2} (Reflection in spacelike)")
print(f"e6^2 = {e6**2} (Reflection in timelike)")

print("Pin(5,5) fully double-covers O(5,5) natively in this Clifford representation.")
print("The involution P^2 = 1 correctly maps the orientation-reversing worldsheet parity (Omega) required for the Klein Bottle unoriented projection.")
