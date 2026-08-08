import clifford as cf

layout, blades = cf.Cl(5, 5)
locals().update(blades)

e = [blades[f'e{i}'] for i in range(1, 11)]

# a_i and a_i_dagger
a = [0.5 * (e[i] + e[i+5]) for i in range(5)]
a_dag = [0.5 * (e[i] - e[i+5]) for i in range(5)]

D = sum([a[i] * a_dag[i] for i in range(5)]) / 5.0
D_dag = sum([a_dag[i] * a[i] for i in range(5)]) / 5.0

print("D + D_dag = ", D + D_dag)

