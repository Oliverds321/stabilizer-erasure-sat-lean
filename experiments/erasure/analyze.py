"""Turn the result files into the tables and figures of the computed section.

usage: python analyze.py            (reads results/, writes results/summary.json,
                                     results/tables.tex and ../../paper/.../figures/*.pdf)
"""
import json
from fractions import Fraction
from math import comb, log10
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

import qec_codes
from curves import bernstein, exact_tables, repair
from hybrid import combine

HERE = Path(__file__).resolve().parent
RES = HERE / "results"
FIG = HERE.parent.parent / "paper" / "quantum-erasure-reliability" / "figures"
FIG.mkdir(exist_ok=True)

P_GRID = [10.0 ** e for e in np.linspace(-14, np.log10(0.999), 400)]
plt.rcParams.update({"font.size": 9, "axes.linewidth": 0.6, "lines.linewidth": 1.2,
                     "legend.frameon": False, "figure.dpi": 150, "pdf.fonttype": 42})
COLORS = ["#1b6ca8", "#c8553d", "#3c8d5a", "#8a5fb5", "#d49a1c", "#4d4d4d", "#c2528b", "#2aa198"]


def exact_cached(key):
    path = RES / f"exact_{key}.json"
    if path.exists():
        data = json.loads(path.read_text())
        return [Fraction(x) for x in data["f"]], [Fraction(x) for x in data["u"]]
    code = qec_codes.get(key)
    if code.n > 26:
        return None
    f, _, u, _ = exact_tables(code)
    path.write_text(json.dumps({"code": code.name, "n": code.n, "k": code.k,
                                "f": [str(x) for x in f], "u": [str(x) for x in u]}))
    return f, u


def tail_errors(f_hat, f_true):
    """Worst relative errors of both curves over the p grid, and of both coefficient tables."""
    b_hat, b_true = [1 - x for x in f_hat], [1 - float(x) for x in f_true]
    f_true = [float(x) for x in f_true]
    fid, inf = [], []
    for p in P_GRID:
        ft, it = bernstein(f_true, p), bernstein(b_true, p)
        fid.append(abs(bernstein(f_hat, p) - ft) / ft)
        inf.append(abs(bernstein(b_hat, p) - it) / it if it > 0 else 0.0)
    coef_f = max(abs(a - t) / t for a, t in zip(f_hat, f_true))
    coef_b = max((abs(a - t) / t if t > 0 else abs(a)) for a, t in zip(b_hat, b_true))
    return fid, inf, coef_f, coef_b


def formula_size(key, reduced):
    """Largest certificate formula over the two kinds, at the middle layer."""
    from certificates import layer_formula
    code = qec_codes.get(key)
    sizes = [layer_formula(code, code.n // 2, kind, reduced=reduced)[0] for kind in ("good", "bad")]
    return max(f.nvars for f in sizes), max(len(f.clauses) for f in sizes)


def paper_runs():
    rows, curves = [], {}
    for path in sorted(RES.glob("paper_*.json"), key=lambda q: json.loads(q.read_text())["n"]):
        r = json.loads(path.read_text())
        exact = exact_cached(r["key"])
        if exact is None:
            continue
        fid, inf, cf, cb = tail_errors(r["f_hat"], exact[0])
        rows.append({"code": r["code"], "key": r["key"], "n": r["n"], "k": r["k"],
                     "projection": 3 * r["n"] if not r["reduced"] else r["n"] + 2 * r["k"],
                     "reduced": r["reduced"], "eps": r["eps"],
                     "vars": formula_size(r["key"], r["reduced"])[0],
                     "clauses": formula_size(r["key"], r["reduced"])[1],
                     "log2_max_count": max(len(bin(int(x))) - 2 for x in r["good"] + r["bad"]),
                     "max_fid_err": max(fid), "max_inf_err": max(inf),
                     "coef_f_err": cf, "coef_b_err": cb,
                     "cpu_seconds": sum(r["layer_seconds"]), "wall_seconds": r["wall_seconds"]})
        curves[r["key"]] = (r, fid, inf)
    return rows, curves


def figure_validation(curves):
    fig, axes = plt.subplots(1, 2, figsize=(7.0, 2.7), sharey=True)
    for idx, (key, (r, fid, inf)) in enumerate(curves.items()):
        c = COLORS[idx % len(COLORS)]
        exact = max(inf) == 0 and max(fid) == 0
        label = r["code"] + (" (exact)" if exact else "")
        axes[0].plot(P_GRID, [max(x, 1e-17) for x in inf], color=c)
        axes[1].plot(P_GRID, [max(x, 1e-17) for x in fid], color=c, label=label)
    eps = next(iter(curves.values()))[0]["eps"]
    for ax, title in zip(axes, (r"infidelity tail  $|\widehat I-I_H|/I_H$",
                                r"fidelity tail  $|\widehat F-F_H|/F_H$")):
        ax.axhline(eps, color="k", lw=0.6, ls="--")
        ax.set_xscale("log"); ax.set_yscale("log")
        ax.set_ylim(1e-5, 1.0)
        ax.set_xlabel("erasure probability $p$")
        ax.set_title(title, fontsize=9)
    axes[0].set_ylabel("relative error")
    axes[0].text(2e-14, eps * 1.15, rf"guarantee $\varepsilon={eps}$", fontsize=7)
    axes[1].legend(fontsize=6.2, loc="center left", ncol=1)
    fig.tight_layout()
    fig.savefig(FIG / "validation.pdf")
    plt.close(fig)


def hybrid_runs():
    out = {}
    for path in sorted(RES.glob("hybrid_*.json"), key=lambda q: json.loads(q.read_text())["n"]):
        r = json.loads(path.read_text())
        est = combine(r)
        n, k = r["n"], r["k"]
        est["f_hat"] = repair(est["f"], 1.0, 4.0 ** (-k))
        out[r["key"]] = (r, est)
    return out


def hybrid_rows(hyb):
    rows = []
    for key, (r, est) in hyb.items():
        n, k, d = r["n"], r["k"], r["distance"]
        inner = range(d, n + 1)
        rel_b = max(est["rel_b"][j] for j in inner)
        rel_f = max(est["rel_f"])
        exact = exact_cached(key)
        row = {"code": r["code"], "key": key, "n": n, "k": k, "d": d,
               "minimal": r["minimal_by_size"], "complete": r["complete_level"],
               "terms": sum(r["minimal_by_size"].values()),
               "max_rel_se_b": rel_b, "max_rel_se_f": rel_f,
               "sat_seconds": r["sat_seconds"], "wall_seconds": r["wall_seconds"],
               "samples_total": sum(row["mc"]["samples"] for row in r["layers"]),
               "leading": est["b"][d] * comb(n, d)}
        f_hat = est["f_hat"]
        b_hat = [1 - x for x in f_hat]
        lo, hi = 1e-6, 1.0  # p_half: I(p) = 1/2, by bisection (I is nondecreasing)
        for _ in range(60):
            mid = (lo + hi) / 2
            if bernstein(b_hat, mid) < 0.5:
                lo = mid
            else:
                hi = mid
        row["p_half"] = (lo + hi) / 2 if b_hat[-1] >= 0.5 else None
        row["I_at"] = {str(p): bernstein(b_hat, p) for p in (1e-4, 1e-3, 1e-2, 0.05, 0.1, 0.2)}
        if exact is not None:
            fid, inf, cf, cb = tail_errors(f_hat, exact[0])
            row.update({"max_fid_err": max(fid), "max_inf_err": max(inf),
                        "coef_f_err": cf, "coef_b_err": cb})
        rows.append(row)
    return rows


def figure_curves(hyb, keys):
    fig, axes = plt.subplots(1, 3, figsize=(7.0, 2.55))
    ps = np.logspace(-4, -0.0005, 400)
    shown = [k for k in keys if k in hyb]
    for idx, key in enumerate(shown):
        r, est = hyb[key]
        n, d = r["n"], r["distance"]
        b = [1 - x for x in est["f_hat"]]
        c = COLORS[idx % len(COLORS)]
        curve = [bernstein(b, p) for p in ps]
        lead = b[d] * comb(n, d)
        label = r["code"].replace("rotated ", "")
        axes[0].plot(ps, curve, color=c)
        axes[1].plot(ps, [v / (lead * p ** d) for v, p in zip(curve, ps)], color=c)
        js = np.arange(d, n + 1)
        axes[2].plot(js / n, [est["b"][j] for j in js], color=c, lw=0.8, label=label)
        w = r["complete_level"]
        axes[2].plot([j / n for j in js if j <= w], [est["b"][j] for j in js if j <= w],
                     "o", ms=2.2, color=c)
    ax = axes[0]
    ax.axhspan(1e-40, 1e-8, color="0.9", lw=0)
    ax.text(1.3e-4, 3e-9, "fewer than ten failures\nin $10^9$ direct samples", fontsize=6,
            va="top")
    ax.set_xscale("log"); ax.set_yscale("log")
    ax.set_ylim(1e-40, 3); ax.set_xlim(1e-4, 1)
    ax.set_yticks([1e-40, 1e-32, 1e-24, 1e-16, 1e-8, 1])
    ax.set_xlabel("erasure probability $p$")
    ax.set_ylabel("logical error rate $I_H(p)$")
    ax.set_title("(a) logical error rate", fontsize=8.5)
    ax = axes[1]
    ax.axhline(1.0, color="k", lw=0.5, ls="--")
    ax.set_xscale("log"); ax.set_yscale("log")
    ax.set_xlim(1e-4, 1); ax.set_ylim(3e-2, 30)
    ax.set_xlabel("erasure probability $p$")
    ax.set_ylabel("$I_H(p)$ / leading term")
    ax.set_title(r"(b) accuracy of $c\,p^d$", fontsize=8.5)
    ax = axes[2]
    ax.set_yscale("log"); ax.set_xlim(0, 0.62)
    ax.legend(fontsize=5.6, loc="lower right", handlelength=1.2)
    ax.set_xlabel("erased fraction $j/n$")
    ax.set_ylabel("coefficient $1-f_j$")
    ax.set_title("(c) coefficients", fontsize=8.5)
    fig.tight_layout(w_pad=0.6)
    fig.savefig(FIG / "curves.pdf")
    plt.close(fig)


def sci(x, digits=2):
    """LaTeX scientific notation."""
    if x == 0:
        return "0"
    e = int(np.floor(np.log10(abs(x))))
    m = x / 10 ** e
    if -3 <= e < 3:
        return f"{x:.{max(digits - e, 0)}f}" if e < 0 else f"{x:.{digits}f}"
    return rf"{m:.{digits - 1}f}\times10^{{{e}}}"


def clock(seconds):
    if seconds < 90:
        return f"{seconds:.0f}" + r"\,s"
    if seconds < 5400:
        return f"{seconds / 60:.0f}" + r"\,min"
    return f"{seconds / 3600:.1f}" + r"\,h"


def write_tables(paper_rows, rows):
    lines = [r"\begin{tabular}{@{}lrrrrrrrr@{}}", r"\toprule",
             r"Code & $n$ & proj. & vars & clauses & $\log_2$ count & "
             r"err.\ $I$ & err.\ $F$ & time\\", r"\midrule"]
    for r in paper_rows:
        name = r["code"].replace("[[", "$[[").replace("]]", "]]$")
        err = lambda x: "exact" if x == 0 else f"${sci(x)}$"
        lines.append(f"{name} & {r['n']} & {r['projection']} & {r['vars']} & {r['clauses']} & "
                     f"{r['log2_max_count']} & {err(r['max_inf_err'])} & {err(r['max_fid_err'])} & "
                     f"{clock(r['cpu_seconds'])}\\\\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (FIG / "table_paper.tex").write_text("\n".join(lines) + "\n")
    lines = [r"\setlength{\tabcolsep}{4pt}",
             r"\begin{tabular}{@{}lp{0.26\textwidth}rrrrrr@{}}", r"\toprule",
             r"Code & minimal uncorrectable sets, size:\,count & $w$ & "
             r"s.e. & $I_H(10^{-3})$ & $I_H(10^{-2})$ & $I_H(0.1)$ & $p_{1/2}$\\", r"\midrule"]
    for r in rows:
        name = r["code"].replace("[[", "$[[").replace("]]", "]]$").replace("rotated ", "")
        # only levels proved complete; a last, interrupted level is not reported
        mins = ", ".join(a + r":\," + str(b)
                         for a, b in sorted(r["minimal"].items(), key=lambda t: int(t[0]))
                         if int(a) <= r["complete"])
        se = max(r["max_rel_se_b"], r["max_rel_se_f"])
        half = f"{r['p_half']:.3f}" if r["p_half"] else "--"
        pct = f"{100 * se:.2f}" if 100 * se < 0.095 else f"{100 * se:.1f}"
        lines.append(f"{name} & {mins} & {r['complete']} & {pct}" + r"\% & "
                     f"${sci(r['I_at']['0.001'])}$ & ${sci(r['I_at']['0.01'])}$ & "
                     f"${sci(r['I_at']['0.1'])}$ & {half}" + r"\\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (FIG / "table_hybrid.tex").write_text("\n".join(lines) + "\n")


def main():
    paper_rows, curves = paper_runs()
    if curves:
        figure_validation(curves)
    hyb = hybrid_runs()
    rows = hybrid_rows(hyb)
    figure_curves(hyb, [k for k in ("surface7", "toric5", "bb72", "toric6", "surface9", "bb90",
                                    "toric8") if k in hyb])
    write_tables(paper_rows, rows)
    (RES / "summary.json").write_text(json.dumps({"paper": paper_rows, "hybrid": rows}, indent=1))
    for row in paper_rows:
        print(f"paper  {row['code']:28s} proj={row['projection']:3d} vars={row['vars']:5d} "
              f"log2count<={row['log2_max_count']:3d} errF={row['max_fid_err']:.3g} "
              f"errI={row['max_inf_err']:.3g} cpu={row['cpu_seconds']:.0f}s")
    for row in rows:
        extra = (f" errF={row['max_fid_err']:.3g} errI={row['max_inf_err']:.3g}"
                 if "max_inf_err" in row else "")
        print(f"hybrid {row['code']:28s} d={row['d']} complete={row['complete']} terms={row['terms']} "
              f"relSE(b)={row['max_rel_se_b']:.3g} relSE(f)={row['max_rel_se_f']:.3g} "
              f"p_half={row['p_half']} wall={row['wall_seconds']:.0f}s{extra}")


if __name__ == "__main__":
    main()
