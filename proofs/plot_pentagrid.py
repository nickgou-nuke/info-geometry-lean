import os
from pathlib import Path

import numpy as np
import matplotlib.pyplot as plt

def main():
    # Setup the plot
    fig, ax = plt.subplots(figsize=(10, 10))
    ax.set_aspect('equal')
    ax.axis('off')
    
    # Grid limits
    L = 5
    
    # 5 directions for the golden angles
    angles = np.array([j * 2 * np.pi / 5 for j in range(5)])
    
    # Unit vectors
    v = np.column_stack((np.cos(angles), np.sin(angles)))
    
    # Phase shifts to ensure no 3 lines intersect at the exact same point
    # (Forces the local intersections to be generic 2-crossings, resolving Yang-Baxter)
    gamma = np.array([0.2, 0.1, 0.4, 0.3, 0.5])
    
    # Plot families of lines
    colors = ['#FF3366', '#33CCFF', '#FF9933', '#33FF99', '#CC33FF']
    
    # x dot v_j = k + gamma_j
    # => x * cos(th) + y * sin(th) = k + gamma_j
    # => y = (k + gamma_j - x * cos(th)) / sin(th)  [if sin(th) != 0]
    
    x_range = np.linspace(-L, L, 400)
    
    for j in range(5):
        th = angles[j]
        cos_th = np.cos(th)
        sin_th = np.sin(th)
        
        # Draw 20 lines per family
        for k in range(-10, 11):
            c = k + gamma[j]
            
            if abs(sin_th) > 1e-5:
                y_range = (c - x_range * cos_th) / sin_th
                
                # Filter points within bounds to avoid plotting long lines out of frame
                valid = (y_range >= -L) & (y_range <= L)
                if np.any(valid):
                    ax.plot(x_range[valid], y_range[valid], color=colors[j], alpha=0.7, lw=1.5)
            else:
                # Vertical line
                x_val = c / cos_th
                if -L <= x_val <= L:
                    ax.plot([x_val, x_val], [-L, L], color=colors[j], alpha=0.7, lw=1.5)

    # Descriptive title: this is a visualization of a de Bruijn-style line grid,
    # not a proof of Yang-Baxter integrability or a Penrose-limit theorem.
    plt.title("De Bruijn-style Pentagrid Visualization\n"
              "generic two-line intersections after phase shifts",
              fontsize=14, pad=20, color='white')
    
    # Dark theme for contrast
    fig.patch.set_facecolor('#111111')
    ax.set_facecolor('#111111')

    # Save to the artifacts directory
    save_path = Path(__file__).with_name("pentagrid_ybe.png")
    os.makedirs(save_path.parent, exist_ok=True)
    plt.savefig(save_path, bbox_inches='tight', facecolor=fig.get_facecolor(), dpi=300)
    save_path = str(save_path)
    print(f"Pentagrid generated successfully at: {save_path}")

if __name__ == "__main__":
    main()
