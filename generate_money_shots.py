import numpy as np
import matplotlib.pyplot as plt
from ModularAsymmetricPipeline import ModularAsymmetricCMOSPipeline

def generate_plots():
    # Locked optimal parameters
    pipeline = ModularAsymmetricCMOSPipeline(
        a=1.0, b=0.0, domain_floor=84.95,
        mu_admission=18.76, epsilon_admission=3.23,
        tau_cosmic=25.38, epsilon_cosmic=3.0,
        tau_dropout=62.57, epsilon_dropout=3.0,
        k_l_admission=0.0, k_l_cosmic=0.0, k_l_dropout=0.0, k_track=0.0
    )
    
    bg = 100.0
    
    # 1. Phase Space Partition Plot
    x_vals = np.linspace(0, 200, 400)
    l_vals = np.linspace(-20, 20, 400)
    X_grid, L_grid = np.meshgrid(x_vals, l_vals)
    
    BG_grid = np.full_like(X_grid, bg)
    TRK_grid = np.zeros_like(X_grid)
    
    res = pipeline.process_frame(X_grid, BG_grid, L_grid, TRK_grid)
    
    state_grid = res['state']
    
    plt.figure(figsize=(10, 8))
    # 0=BACKGROUND, 1=COSMIC, 2=DROPOUT, 3=DOMAIN_FAULT, 4=UNKNOWN
    colors = ['#2ca02c', '#d62728', '#1f77b4', '#7f7f7f', '#ff7f0e']
    from matplotlib.colors import ListedColormap
    cmap = ListedColormap(colors)
    
    plt.pcolormesh(X_grid, L_grid, state_grid, cmap=cmap, shading='auto', vmin=0, vmax=4)
    plt.colorbar(ticks=[0, 1, 2, 3, 4], label='State (0:Bg, 1:CR, 2:Drop, 3:DomainFault, 4:Unk)')
    plt.axvline(bg, color='k', linestyle='--', alpha=0.5, label='Background')
    plt.axhline(0, color='k', linestyle='--', alpha=0.5)
    plt.xlabel('Raw Pixel Value (X)')
    plt.ylabel('Spatial Laplacian (L)')
    plt.title('Phase Space Topological Partition (Branch Energy)')
    plt.legend()
    plt.savefig('phase_space_partition.png', dpi=300, bbox_inches='tight')
    plt.close()
    
    # 2. Gibbs-Fermi Admission Curve
    x_1d = np.linspace(85, 130, 500)
    l_1d = np.zeros_like(x_1d)
    bg_1d = np.full_like(x_1d, bg)
    trk_1d = np.zeros_like(x_1d)
    
    res_1d = pipeline.process_frame(x_1d, bg_1d, l_1d, trk_1d)
    r_adm = res_1d['responsibility']
    
    plt.figure(figsize=(8, 5))
    plt.plot(x_1d, r_adm, color='#9467bd', linewidth=2.5, label='Gibbs-Fermi Admission $r_{adm}$')
    plt.axvline(bg, color='k', linestyle='--', alpha=0.5, label='Background (X=100)')
    plt.xlabel('Pixel Value (X)')
    plt.ylabel('Admission Responsibility $r_{adm}$')
    plt.title('Gibbs-Fermi Admission Soft Roll-off')
    plt.grid(True, alpha=0.3)
    plt.legend()
    plt.savefig('gibbs_fermi_admission.png', dpi=300, bbox_inches='tight')
    plt.close()

if __name__ == "__main__":
    generate_plots()
    print("Money shots generated: phase_space_partition.png and gibbs_fermi_admission.png")
