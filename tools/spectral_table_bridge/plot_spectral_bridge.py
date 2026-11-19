#!/usr/bin/env python3
"""Export a two-panel scientific figure from the reconciled interior analysis."""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import TwoSlopeNorm
import numpy as np
from fixtures import DEFAULT_OUTPUT_DIR


def plot(source,output):
    data=json.loads(source.read_text())
    selected=data["decimal_subsets"]["all5"]["interior7"]["interaction"]
    positions=np.arange(2,9)
    h=np.array(selected["common_fit"]["residual_log"],dtype=float)
    relative=100*np.expm1(h)
    interaction=100*np.array(selected["interaction"],dtype=float)
    if interaction.shape!=(7,5) or h.shape!=(7,):
        raise ValueError("expected the seven-cartridge, five-channel interior")
    if data["decimal_subsets"]["all5"]["channels"]!=["77","242","295","352","609"]:
        raise ValueError("unexpected channel order")
    output.mkdir(parents=True,exist_ok=True)
    plt.rcParams.update({
        "font.family":"DejaVu Sans",
        "font.size":10.5,
        "axes.titlesize":13,
        "axes.labelsize":11,
        "xtick.labelsize":10.5,
        "ytick.labelsize":10.5,
        "pdf.fonttype":42,
        "ps.fonttype":42,
        "axes.spines.top":False,
        "axes.spines.right":False,
        "savefig.facecolor":"white",
    })
    fig=plt.figure(figsize=(12,5.8),facecolor="white")
    grid=fig.add_gridspec(1,3,width_ratios=[1.03,1.2,.055],
                         left=.075,right=.94,bottom=.20,top=.79,wspace=.34)
    ax=fig.add_subplot(grid[0,0])
    heat=fig.add_subplot(grid[0,1])
    cax=fig.add_subplot(grid[0,2])
    blue="#24658A"
    ax.bar(positions,relative,width=.62,color=blue,edgecolor="white",linewidth=.7,zorder=3)
    ax.axhline(0,color="#45525B",linewidth=.9,zorder=2)
    ax.set_xlim(1.45,8.55)
    ax.set_ylim(-8,8)
    ax.set_xticks(positions)
    ax.set_yticks([-8,-4,0,4,8])
    ax.set_xlabel("Cartridge")
    ax.set_ylabel(r"Relative residual, $100(e^{h}-1)$ (%)")
    ax.set_title("(a) Common spatial residual",loc="left",pad=15,fontweight="bold")
    ax.grid(axis="y",color="#DDE3E6",linewidth=.7,zorder=0)
    for x,y in zip(positions,relative):
        ax.text(x,y+(.27 if y>=0 else -.27),f"{y:+.2f}",ha="center",
                va="bottom" if y>=0 else "top",fontsize=9.5,color="#24343E")
    ax.text(.02,.04,r"$\mu = "+f"{selected['common_fit']['mu']:.6f}"+r"$ per cartridge",
            transform=ax.transAxes,va="bottom",fontsize=10,color="#41515B")

    limit=math.ceil(float(np.max(np.abs(interaction))))
    if limit<=0:limit=1
    norm=TwoSlopeNorm(vmin=-limit,vcenter=0,vmax=limit)
    image=heat.imshow(interaction,cmap="RdBu_r",norm=norm,
                      interpolation="nearest",aspect="auto")
    heat.set_title("(b) Spectral interaction",loc="left",pad=15,fontweight="bold")
    heat.set_xticks(np.arange(5),["77 ROI","242","295","352","609"])
    heat.set_yticks(np.arange(7),positions)
    heat.set_xlabel("Channel (keV)")
    heat.set_ylabel("Cartridge")
    heat.set_xticks(np.arange(-.5,5,1),minor=True)
    heat.set_yticks(np.arange(-.5,7,1),minor=True)
    heat.grid(which="minor",color="white",linewidth=1)
    heat.tick_params(which="minor",bottom=False,left=False)
    for spine in heat.spines.values():spine.set_visible(False)
    for i in range(7):
        for j in range(5):
            value=interaction[i,j]
            heat.text(j,i,f"{value:+.2f}",ha="center",va="center",fontsize=9.4,
                      color="white" if abs(value)>.63*limit else "#142D3A")
    cbar=fig.colorbar(image,cax=cax,ticks=[-limit,-limit/2,0,limit/2,limit])
    cbar.set_label(r"$100E$ (log units)",labelpad=10)
    cbar.outline.set_visible(False)
    cbar.ax.tick_params(length=3)
    fig.text(.075,.97,"Separate spatial and spectral diagnostics",
             ha="left",va="top",fontsize=17,fontweight="bold",color="#173747")
    fig.text(.075,.91,
             "Decimal net peak areas  •  Interior cartridges 2–8  •  Five included channels",
             ha="left",va="top",fontsize=11,color="#51636D")
    fig.text(.075,.105,
             "Common profile: equal-weight affine fit to mean log intensity.  "
             "Interaction: double-centered log rates.",
             ha="left",va="top",fontsize=10,color="#41515B")
    fig.text(.075,.062,
             "The nominal 77-keV ROI is unresolved.  Residuals are descriptive; "
             "measurement-error bars are not available.",
             ha="left",va="top",fontsize=9.5,color="#51636D")
    png=output/"spectral_bridge_diagnostics.png"
    pdf=output/"spectral_bridge_diagnostics.pdf"
    fig.savefig(png,dpi=220)
    fig.savefig(pdf)
    plt.close(fig)
    caption=(
        "Interior spatial and spectral diagnostics for the five-channel decimal-area table. "
        "(a) Relative residual 100(exp(h_i)-1) from an equal-weight affine fit of the mean "
        "log corrected intensity across the five channels at cartridges 2–8. The fitted "
        f"attenuation coefficient is {selected['common_fit']['mu']:.9f} per cartridge. "
        "(b) 100 times the double-centered log intensity E, computed on the same seven "
        "samples and five channels; the diverging color scale is symmetric about zero. "
        "The largest absolute interaction is at cartridge 8 in the 242-keV channel. "
        "Rates use the source point decay correction N/live*exp(lambda*elapsed). The "
        "nominal 77-keV ROI remains unresolved, and no photon yield is assigned to it. "
        "The diagnostics are descriptive and do not identify a physical cause; supplied "
        "data do not include measurement-error bars."
    )
    (output/"spectral_bridge_caption.txt").write_text(caption+"\n")
    metadata={"status":"created","input_sha256":hashlib.sha256(source.read_bytes()).hexdigest(),
              "source":"decimal_subsets.all5.interior7.interaction",
              "panel_a_values_percent":relative.tolist(),
              "panel_b_values_100E":interaction.tolist(),
              "color_scale_symmetric_limits_100E":[-limit,limit],
              "matplotlib_version":matplotlib.__version__,
              "numpy_version":np.__version__,
              "png_dimensions_pixels":[2640,1276],
              "files":[png.name,pdf.name,"spectral_bridge_caption.txt"]}
    (output/"figure_metadata.json").write_text(json.dumps(metadata,indent=2)+"\n")
    print(json.dumps(metadata,indent=2))


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input",type=Path,default=None,
                   help="Override the numerical audit JSON; normally read from --output-dir/results.")
    p.add_argument("--output-dir",type=Path,default=DEFAULT_OUTPUT_DIR)
    args=p.parse_args()
    source=args.input or args.output_dir/"results"/"spectral_domains_audit.json"
    plot(source,args.output_dir/"figures")
