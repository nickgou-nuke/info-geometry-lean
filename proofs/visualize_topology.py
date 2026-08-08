import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D

def plot_cpt_topology():
    fig = plt.figure(figsize=(12, 10))
    ax = fig.add_subplot(111, projection='3d')
    ax.set_facecolor('black')
    fig.patch.set_facecolor('black')

    # 1. The Paraboloid Metriplectic Manifold
    # Z = X^2 + Y^2 (The shape of the cognitive gravity well)
    r_surface = np.linspace(0.1, 4, 100)
    theta_surface = np.linspace(0, 2 * np.pi, 100)
    R, Theta = np.meshgrid(r_surface, theta_surface)
    X_surf = R * np.cos(Theta)
    Y_surf = R * np.sin(Theta)
    Z_surf = R**2
    ax.plot_surface(X_surf, Y_surf, Z_surf, color='blue', alpha=0.1, edgecolor='none')

    # 2. Stable Metriplectic Flow (The "Motorcycles" with high spin)
    t_stable = np.linspace(0, 20 * np.pi, 2000)
    r_stable = 3.0 + 0.2 * np.sin(t_stable * 5) # Oscillation
    x_stable = r_stable * np.cos(t_stable)
    y_stable = r_stable * np.sin(t_stable)
    z_stable = r_stable**2
    ax.plot(x_stable, y_stable, z_stable, color='cyan', linewidth=3.0, alpha=0.9, label='Stable Metriplectic Flow (Coriolis Supported)')

    # 3. Failing Trajectories (Insufficient Spin)
    t_fail = np.linspace(0, 5 * np.pi, 1000)
    r_fail = 3.5 * np.exp(-t_fail / 3) # Exponential decay
    x_fail = r_fail * np.cos(t_fail * 0.5) 
    y_fail = r_fail * np.sin(t_fail * 0.5)
    z_fail = r_fail**2
    ax.plot(x_fail, y_fail, z_fail, color='magenta', linewidth=2.5, alpha=0.8, label='Falling Trajectory (Insufficient Spin)')

    # 4. Monodromy Cycles (The Parabolic Rings)
    t_cycle = np.linspace(0, 2 * np.pi, 500)
    for radius in [1.5, 2.5, 3.5]:
        cx = radius * np.cos(t_cycle * 83)  # High frequency winding
        cy = radius * np.sin(t_cycle * 83)
        cz = np.full_like(t_cycle, radius**2) # Locked to the paraboloid surface
        ax.plot(cx, cy, cz, color='yellow', linewidth=1.0, alpha=0.8, label='Monodromy Cycle' if radius == 3.5 else "")

    # 5. The Null Sector Singularity (Bottom Triviality)
    ax.scatter([0], [0], [0], color='red', s=800, edgecolors='white', alpha=1.0, zorder=5, label='Terminal Triviality (0)')

    # Labeling and aesthetics
    ax.set_title("CPT Cognitive Topology: Causal Flow & Monodromy Cycles", color='white', fontsize=16)
    ax.set_xlabel(r"$\psi_{fix}$ Axis", color='white')
    ax.set_ylabel(r"$\kappa_{harmony}$ Axis", color='white')
    ax.set_zlabel("Time Arrow (Causal Depth)", color='white')
    
    ax.tick_params(colors='white')
    ax.xaxis.pane.fill = False
    ax.yaxis.pane.fill = False
    ax.zaxis.pane.fill = False
    
    # Save the artifact
    plt.legend(facecolor='black', edgecolor='white', labelcolor='white')
    plt.savefig('CPT_Cognitive_Topology.png', dpi=300, bbox_inches='tight')
    print("Topology visualization saved as 'CPT_Cognitive_Topology.png'")

if __name__ == "__main__":
    plot_cpt_topology()
