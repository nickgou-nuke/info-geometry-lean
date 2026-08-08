print("Initializing Braid Group B_4...")
B4 = BraidGroup(4)
print("Generators:", B4.gens())

# Generate a complex word s1 s2 s1^-1 s2
s1 = B4([1])
s2 = B4([2])

word = s1 * s2 * s1^-1 * s2
print("Original word:", word)

# Compute left normal form
nf = word.left_normal_form()
print("Left normal form:", nf)

print("Certificate mapping original word to its normal-form generator list:")
print("Original syllables:", word.syllables())
print("Normal Form:", nf)
