from __future__ import annotations

import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIG_DIR = ROOT / "figures"
CACHE_DIR = ROOT / ".cache"
MPL_DIR = ROOT / ".mpl-cache"

os.environ.setdefault("XDG_CACHE_HOME", str(CACHE_DIR))
os.environ.setdefault("MPLCONFIGDIR", str(MPL_DIR))

CACHE_DIR.mkdir(parents=True, exist_ok=True)
MPL_DIR.mkdir(parents=True, exist_ok=True)

import matplotlib

matplotlib.use("Agg")

import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch, Rectangle


def setup_matplotlib() -> None:
    plt.rcParams.update(
        {
            "font.family": "DejaVu Serif",
            "font.size": 10,
            "axes.linewidth": 0.8,
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
        }
    )


def add_box(ax, xy, width, height, title, lines, facecolor, edgecolor="#2f3e46"):
    x, y = xy
    patch = FancyBboxPatch(
        (x, y),
        width,
        height,
        boxstyle="round,pad=0.02,rounding_size=0.03",
        linewidth=1.2,
        facecolor=facecolor,
        edgecolor=edgecolor,
    )
    ax.add_patch(patch)
    ax.text(x + width / 2, y + height * 0.72, title, ha="center", va="center", fontsize=11, fontweight="bold")
    ax.text(x + width / 2, y + height * 0.38, "\n".join(lines), ha="center", va="center", fontsize=9)
    return patch


def add_arrow(ax, start, end, text=None, color="#1d3557"):
    arrow = FancyArrowPatch(start, end, arrowstyle="-|>", mutation_scale=14, linewidth=1.2, color=color)
    ax.add_patch(arrow)
    if text:
        mx = (start[0] + end[0]) / 2
        my = (start[1] + end[1]) / 2 + 0.05
        ax.text(mx, my, text, ha="center", va="bottom", fontsize=9, color=color)


def save(fig, name):
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    fig.savefig(FIG_DIR / name, bbox_inches="tight")
    plt.close(fig)


def draw_hnf_pipeline():
    fig, ax = plt.subplots(figsize=(13, 4.8))
    ax.set_xlim(0, 13)
    ax.set_ylim(0, 4.8)
    ax.axis("off")

    colors = {
        "input": "#f3efe0",
        "stage1": "#dcecf9",
        "stage2": "#e8f3e8",
        "stage3": "#f8e5d6",
        "output": "#ece7f2",
    }

    add_box(ax, (0.3, 1.1), 1.7, 2.2, "Input $A$", ["Public matrix", "reindexed to Fin"], colors["input"])
    add_box(ax, (2.4, 1.1), 2.2, 2.2, "clearFirstColumn", ["swap first nonzero row", "lifted Bezout steps", "normalize pivot"], colors["stage1"])
    add_box(ax, (5.1, 1.1), 2.1, 2.2, "recurse lowerRight", ["solve smaller HNF", "obtain $U_{lr}$"], colors["stage2"])
    add_box(ax, (7.6, 1.1), 1.8, 2.2, "diagLift", ["embed $U_{lr}$", "top row fixed"], colors["stage2"])
    add_box(ax, (9.8, 1.1), 2.1, 2.2, "reduceTopRow", ["replace top entries", "by canonical remainders"], colors["stage3"])
    add_box(ax, (12.1, 1.1), 0.7, 2.2, "$H$", ["HNF"], colors["output"])

    for start, end in [
        ((2.0, 2.2), (2.4, 2.2)),
        ((4.6, 2.2), (5.1, 2.2)),
        ((7.2, 2.2), (7.6, 2.2)),
        ((9.4, 2.2), (9.8, 2.2)),
        ((11.9, 2.2), (12.1, 2.2)),
    ]:
        add_arrow(ax, start, end, text="$U \\cdot A = B$")

    ax.text(3.5, 4.2, "Stage 1", ha="center", va="center", fontsize=11, fontweight="bold", color="#1d3557")
    ax.text(6.5, 4.2, "Stage 2", ha="center", va="center", fontsize=11, fontweight="bold", color="#1d3557")
    ax.text(10.8, 4.2, "Stage 3", ha="center", va="center", fontsize=11, fontweight="bold", color="#1d3557")
    ax.text(6.5, 0.45, "Global invariant at every node: unimodular left certificate $U$ with $U \\cdot A = B$.", ha="center", va="center", fontsize=10)

    save(fig, "hnf_pipeline.pdf")


def draw_certificate_block_lifts():
    fig, ax = plt.subplots(figsize=(11.5, 5.7))
    ax.set_xlim(0, 11.5)
    ax.set_ylim(0, 5.7)
    ax.axis("off")

    ax.text(5.75, 5.35, "Block lifts used by the proof-facing certificate layer", ha="center", va="center", fontsize=13, fontweight="bold")
    ax.text(5.75, 4.95, "Both gadgets are composed as matrices inside LeftTransform.trans.", ha="center", va="center", fontsize=10)

    # Left panel: diagLiftMatrix
    ax.text(2.75, 4.35, r"$\mathrm{diagLiftMatrix}(U)$", ha="center", va="center", fontsize=12)
    x0, y0, w, h = 0.8, 1.4, 3.9, 2.3
    ax.add_patch(Rectangle((x0, y0), w, h, fill=False, linewidth=1.2, edgecolor="#2f3e46"))
    ax.plot([x0 + 0.9, x0 + 0.9], [y0, y0 + h], color="#2f3e46", linewidth=1.0)
    ax.plot([x0, x0 + w], [y0 + 0.55, y0 + 0.55], color="#2f3e46", linewidth=1.0)
    ax.text(x0 + 0.45, y0 + 1.65, "1", ha="center", va="center", fontsize=12)
    ax.text(x0 + 2.4, y0 + 1.65, "0", ha="center", va="center", fontsize=12)
    ax.text(x0 + 0.45, y0 + 0.27, "0", ha="center", va="center", fontsize=12)
    ax.text(x0 + 2.4, y0 + 0.27, "$U$", ha="center", va="center", fontsize=12)
    ax.text(2.75, 0.95, "Keeps the top row fixed and replaces", ha="center", va="center", fontsize=10)
    ax.text(2.75, 0.62, "the lower-right block by $U \\cdot \\mathrm{lowerRight}(A)$.", ha="center", va="center", fontsize=10)

    # Right panel: topBezoutMatrix
    ax.text(8.75, 4.35, r"$\mathrm{topBezoutMatrix}(a,b)$", ha="center", va="center", fontsize=12)
    x1, y1, w1, h1 = 6.8, 1.4, 3.9, 2.3
    ax.add_patch(Rectangle((x1, y1), w1, h1, fill=False, linewidth=1.2, edgecolor="#2f3e46"))
    ax.plot([x1 + 1.0, x1 + 1.0], [y1, y1 + h1], color="#2f3e46", linewidth=1.0)
    ax.plot([x1, x1 + w1], [y1 + 0.8, y1 + 0.8], color="#2f3e46", linewidth=1.0)
    ax.text(x1 + 0.5, y1 + 1.55, "$B(a,b)$", ha="center", va="center", fontsize=12)
    ax.text(x1 + 2.45, y1 + 1.55, "0", ha="center", va="center", fontsize=12)
    ax.text(x1 + 0.5, y1 + 0.38, "0", ha="center", va="center", fontsize=12)
    ax.text(x1 + 2.45, y1 + 0.38, "$I$", ha="center", va="center", fontsize=12)
    ax.text(8.75, 0.95, "Acts only on the first two rows,", ha="center", va="center", fontsize=10)
    ax.text(8.75, 0.62, "sending $(a,b)$ to $(\\gcd(a,b),0)$ with determinant $1$.", ha="center", va="center", fontsize=10)

    add_arrow(ax, (4.95, 2.55), (6.55, 2.55), text="compose by matrix multiplication")
    ax.text(5.75, 2.03, "Explicit field: $\\mathrm{Unimodular}(U)$", ha="center", va="center", fontsize=10, color="#1d3557")
    ax.text(5.75, 1.66, "This is what lets uniqueness use $U^{-1}$ directly.", ha="center", va="center", fontsize=10, color="#1d3557")

    save(fig, "certificate_block_lifts.pdf")


def draw_uniqueness_graph():
    fig, ax = plt.subplots(figsize=(9.5, 8.6))
    ax.set_xlim(0, 9.5)
    ax.set_ylim(0, 8.6)
    ax.axis("off")

    colors = {
        "start": "#f3efe0",
        "mid": "#dcecf9",
        "pivot": "#f8e5d6",
        "finish": "#e8f3e8",
    }

    add_box(ax, (2.7, 7.4), 4.1, 0.8, "Input assumptions", ["unimodular $U$", "$U \\cdot H_1 = H_2$", "$H_1, H_2$ are HNF"], colors["start"])
    add_box(ax, (0.5, 5.9), 3.2, 0.9, "lower-left block of $U$ is zero", ["from first-column equations"], colors["mid"])
    add_box(ax, (5.8, 5.9), 3.2, 0.9, "lower-left block of $U^{-1}$ is zero", ["same argument on $U^{-1} H_2 = H_1$"], colors["mid"])
    add_box(ax, (0.5, 4.2), 3.2, 0.9, "$\\mathrm{lowerRight}(U)$ unimodular", ["restrict the inverse"], colors["mid"])
    add_box(ax, (5.8, 4.2), 3.2, 0.9, "$U_{0,0}$ is a unit", ["read $(0,0)$ of $U U^{-1}=I$"], colors["pivot"])
    add_box(ax, (2.7, 2.6), 4.1, 0.9, "$\\mathrm{lowerRight}(H_1)=\\mathrm{lowerRight}(H_2)$", ["induction hypothesis"], colors["mid"])
    add_box(ax, (0.8, 1.1), 3.0, 0.9, "pivot equality", ["normalized associates imply", "$(H_1)_{0,0}=(H_2)_{0,0}$"], colors["pivot"])
    add_box(ax, (5.6, 1.1), 3.0, 0.9, "top row equality", ["CanonicalMod closes the", "minimal active-row argument"], colors["pivot"])
    add_box(ax, (3.1, 0.1), 3.3, 0.7, "$H_1 = H_2$", ["uniqueness"], colors["finish"])

    arrows = [
        ((4.75, 7.4), (2.1, 6.8)),
        ((4.75, 7.4), (7.4, 6.8)),
        ((2.1, 5.9), (2.1, 5.1)),
        ((7.4, 5.9), (7.4, 5.1)),
        ((2.1, 4.2), (4.75, 3.5)),
        ((7.4, 4.2), (2.3, 2.0)),
        ((4.75, 3.5), (2.3, 2.0)),
        ((4.75, 3.5), (7.1, 2.0)),
        ((2.3, 1.1), (4.75, 0.8)),
        ((7.1, 1.1), (4.75, 0.8)),
    ]
    for start, end in arrows:
        add_arrow(ax, start, end)

    save(fig, "uniqueness_locking_graph.pdf")


def main():
    setup_matplotlib()
    draw_hnf_pipeline()
    draw_certificate_block_lifts()
    draw_uniqueness_graph()


if __name__ == "__main__":
    main()
