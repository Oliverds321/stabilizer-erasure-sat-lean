"""Schematic of the reduction (Figure 1 of the manuscript)."""
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

FIG = Path(__file__).resolve().parent.parent.parent / "paper" / "quantum-erasure-reliability" / "figures"
FIG.mkdir(exist_ok=True)
plt.rcParams.update({"font.size": 8, "pdf.fonttype": 42, "mathtext.fontset": "cm"})

fig, ax = plt.subplots(figsize=(7.0, 2.35))
ax.set_xlim(0, 100)
ax.set_ylim(0, 34)
ax.axis("off")


def box(x, y, w, h, text, face="#eef3f8", edge="#1b6ca8"):
    ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0.25,rounding_size=0.9",
                                fc=face, ec=edge, lw=0.8))
    ax.text(x + w / 2, y + h / 2, text, ha="center", va="center", linespacing=1.35)


def arrow(x0, y0, x1, y1):
    ax.add_patch(FancyArrowPatch((x0, y0), (x1, y1), arrowstyle="-|>", mutation_scale=7,
                                 lw=0.7, color="0.25", shrinkA=0, shrinkB=0))


box(0.5, 12, 13, 10, "sparse check\nmatrix $H$\n$O(n)$ nonzeros", face="#f6f6f6", edge="0.35")
box(18.5, 19.5, 21, 11, "$\\mathsf{Good}(E,z)$:  $\\exists u$\n$(z+uH)|_E=0$\ncount $A_j=\\sum_{|E|=j}Z\\,2^{-d_E}$")
box(18.5, 3.5, 21, 11, "$\\mathsf{Bad}(E,z)$:  $\\exists x\\in N_E$\n$\\langle x,z\\rangle_s=1$\ncount $B_j=\\binom{n}{j}Z-A_j$")
box(44.5, 9.5, 19.5, 15, "projected counting\nlinear-size hash\n$+$ SAT decisions\non $O(n)$ variables\n$\\widehat A_j,\\ \\widehat B_j$",
    face="#fbefe9", edge="#c8553d")
box(69, 19.5, 13.5, 11, "normalize\n$g_j=\\dfrac{\\widehat A_j}{\\widehat A_j+\\widehat B_j}$")
box(69, 3.5, 13.5, 11, "anchored\nantitone repair\n$1=\\widehat f_0\\geq\\cdots\\geq\\widehat f_n$")
box(87, 9.5, 12.5, 15, "$\\widehat F(p)$,  $\\widehat I(p)$\nrelative error $\\varepsilon$\nin both tails,\nevery $p\\in[0,1]$",
    face="#eaf4ec", edge="#3c8d5a")

arrow(13.9, 19, 18.1, 24)
arrow(13.9, 15, 18.1, 10)
arrow(39.9, 24, 44.1, 19.5)
arrow(39.9, 10, 44.1, 14.5)
arrow(64.4, 19.5, 68.6, 24)
arrow(75.75, 19.1, 75.75, 15.0)
arrow(82.9, 9, 86.6, 14.5)
ax.text(29, 1.1, "for every layer $j=0,\\ldots,n$:  two 3-CNFs, $O(n)$ variables each",
        ha="center", va="center", fontsize=6.6, color="0.3")
fig.subplots_adjust(left=0.005, right=0.995, top=0.99, bottom=0.01)
fig.savefig(FIG / "pipeline.pdf")
fig.savefig(FIG / "pipeline.png", dpi=170)
print("wrote pipeline.pdf")
