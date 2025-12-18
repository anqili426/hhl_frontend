#!/usr/bin/env python3
# Usage:
#   python3 analyze_eval.py --input src/test/evaluation/output_all_*.csv --outdir src/test/evaluation/plots

import argparse
import glob
import os
import re
from pathlib import Path
from typing import List

import numpy as np
import pandas as pd

import matplotlib
matplotlib.use("Agg")  # headless
import matplotlib.pyplot as plt


# ----------------------------
# Helpers
# ----------------------------
NUM_COLS = [
    "Runtime total (s)",
    "Runtime Characterizer avg (s)",
    "Runtime WP avg (s)",
    "Runtime SMT encoding avg (s)",
    "Runtime SMT solving avg (s)",
    "Actual LOC",
    "Spec LOC",
    "Proof LOC",
    "Number of triples",
    "Havoc statements"
]

ID_COLS = ["Test case name", "Suite", "Option", "Engine", "SMT mode"]

# Benchmarks to exclude from the whole evaluation (all stats + plots + CSV outputs)
EXCLUDE_FROM_EVAL = {
    "src/test/evaluation/exists/orhle/sandbox.hhl",
    "src/test/evaluation/exists-forall/orhle/gni/nondet_leak.hhl",
    "src/test/evaluation/forall-exists/hypa/counter_diff.hhl",
    "src/test/evaluation/forall-exists/hypa/counter_sum.hhl",
    "src/test/evaluation/forall/pcsat/half_square_ni.hhl",
    "src/test/evaluation/forall-exists/orhle/delimited-release/parity_fun.hhl",
}

# Benchmarks to exclude only from stage breakdown / pies
EXCLUDE_FOR_STAGE_PLOTS = EXCLUDE_FROM_EVAL | {
    "src/test/evaluation/forall/descartes/solution_true.hhl",
    "src/test/evaluation/exists/descartes/datapoint_false_exists.hhl",
}


def mode_label(row: pd.Series) -> str:
    eng = str(row["Engine"]).strip()
    smt = str(row["SMT mode"]).strip()
    if eng == "semantic":
        return "semantic"
    return f"syntactic-{smt}"


def safe_to_numeric(s: pd.Series) -> pd.Series:
    s = s.replace({"---": np.nan, "NaN": np.nan, "nan": np.nan, "": np.nan})
    return pd.to_numeric(s, errors="coerce")


def ensure_outdir(outdir: str) -> Path:
    p = Path(outdir)
    p.mkdir(parents=True, exist_ok=True)
    return p


def read_inputs(patterns: List[str]) -> pd.DataFrame:
    files: List[str] = []
    for pat in patterns:
        files.extend(glob.glob(pat))
    files = sorted(set(files))
    if not files:
        raise SystemExit(f"No input files matched: {patterns}")

    dfs = []
    for fp in files:
        df = pd.read_csv(fp)
        df["__file"] = os.path.basename(fp)
        m = re.search(r"(\d+)", os.path.basename(fp))
        df["rep"] = int(m.group(1)) if m else -1
        dfs.append(df)

    out = pd.concat(dfs, ignore_index=True)

    for c in NUM_COLS:
        if c not in out.columns:
            out[c] = np.nan

    for c in NUM_COLS:
        out[c] = safe_to_numeric(out[c])

    out["Mode"] = out.apply(mode_label, axis=1)

    out["Option"] = out["Option"].fillna("").astype(str)
    out.loc[out["Option"].str.strip() == "", "Option"] = "(default)"

    out["SMT mode"] = out["SMT mode"].fillna("---").astype(str)

    out["Test case name"] = out["Test case name"].fillna("").astype(str).str.strip()

    if "Test result" in out.columns:
        out["Test result"] = out["Test result"].fillna("").astype(str)
    else:
        out["Test result"] = ""

    return out


def agg_over_reps(df: pd.DataFrame) -> pd.DataFrame:
    group_keys = ["Test case name", "Suite", "Option", "Engine", "SMT mode", "Mode"]

    def pass_all(x: pd.Series) -> str:
        xs = x.astype(str).str.lower()
        if (xs == "failed").any():
            return "Failed"
        if (xs == "passed").all():
            return "Passed"
        return "Mixed"

    agg_dict = {c: "mean" for c in NUM_COLS}
    agg_dict["Test result"] = pass_all

    return df.groupby(group_keys, dropna=False).agg(agg_dict).reset_index()


def _geo_mean(x: np.ndarray) -> float:
    x = x[np.isfinite(x)]
    x = x[x > 0]
    if x.size == 0:
        return float("nan")
    return float(np.exp(np.mean(np.log(x))))


def sem_vs_synboth_table(df_agg: pd.DataFrame) -> pd.DataFrame:
    need = {"semantic", "syntactic-both"}
    if not need.issubset(set(df_agg["Mode"].unique())):
        return pd.DataFrame()

    sem = df_agg[df_agg["Mode"] == "semantic"][[
        "Test case name", "Suite", "Option", "Runtime total (s)", "Test result",
        "Actual LOC", "Spec LOC", "Proof LOC"
    ]].rename(columns={
        "Runtime total (s)": "rt_sem",
        "Test result": "res_sem",
    })

    syn = df_agg[df_agg["Mode"] == "syntactic-both"][[
        "Test case name", "Runtime total (s)", "Test result"
    ]].rename(columns={
        "Runtime total (s)": "rt_syn",
        "Test result": "res_syn",
    })

    m = sem.merge(syn, on="Test case name", how="inner")
    m = m.dropna(subset=["rt_sem", "rt_syn"])
    m = m[(m["rt_sem"] > 0) & (m["rt_syn"] > 0)]
    m["speedup"] = m["rt_sem"] / m["rt_syn"]        # >1 => syntactic-both faster
    m["log2_speedup"] = np.log2(m["speedup"].to_numpy(dtype=float))
    return m


def print_stats(df_agg: pd.DataFrame, outdir: Path) -> None:
    modes = sorted(df_agg["Mode"].unique())
    print("\n=== Summary by mode (averaged over repetitions per test) ===")
    rows = []
    for m in modes:
        sub = df_agg[df_agg["Mode"] == m]
        passed = (sub["Test result"] == "Passed").sum()
        failed = (sub["Test result"] == "Failed").sum()
        mixed = (sub["Test result"] == "Mixed").sum()
        n = len(sub)

        rt = sub["Runtime total (s)"].dropna()
        rows.append({
            "Mode": m,
            "#tests": n,
            "Passed": passed,
            "Failed": failed,
            "Mixed": mixed,
            "PassRate(%)": (passed / n * 100.0) if n else np.nan,
            "TotalRuntimeSum(s)": rt.sum(),
            "MeanRuntime(s)": rt.mean(),
            "StdRuntime(s)": rt.std(ddof=1),
            "MedianRuntime(s)": rt.median(),
            "P95Runtime(s)": rt.quantile(0.95) if len(rt) else np.nan,
        })

    tab = pd.DataFrame(rows).sort_values("Mode")
    with pd.option_context("display.max_columns", None, "display.width", 220):
        print(tab.to_string(index=False))

    m = sem_vs_synboth_table(df_agg)
    if not m.empty:
        su = m["speedup"].to_numpy(dtype=float)

        eps = 0.05  # same tolerance you used before
        faster = int(np.sum(su > 1.0 + eps))
        equal  = int(np.sum((su >= 1.0 - eps) & (su <= 1.0 + eps)))
        slower = int(np.sum(su < 1.0 - eps))
        ncomp  = int(len(su))

        print(f"\nSyntactic-both faster in {faster}/{ncomp} tests ({(faster/ncomp*100.0):.1f}%). "
              f"≈equal in {equal}/{ncomp} ({(equal/ncomp*100.0):.1f}%), "
              f"slower in {slower}/{ncomp} ({(slower/ncomp*100.0):.1f}%). "
              f"(ε={eps:.2f})")

        geo = _geo_mean(su)

        print("\n=== semantic vs syntactic-both speedups (per test, averaged over reps) ===")
        print(f"Compared tests: {len(m)}")
        print(
            f"speedup = semantic/syntactic-both: "
            f"mean={np.nanmean(su):.3f}, median={np.nanmedian(su):.3f}, geo-mean={geo:.3f}, "
            f"p95={np.nanquantile(su, 0.95):.3f}"
        )

        # Save a small summary CSV next to plots
        summary = pd.DataFrame([{
            "comparison": "semantic_vs_syntactic-both",
            "n": int(np.sum(np.isfinite(su) & (su > 0))),
            "arith_mean": float(np.nanmean(su)),
            "median": float(np.nanmedian(su)),
            "geo_mean": float(geo),
            "p95": float(np.nanquantile(su[np.isfinite(su)], 0.95)) if np.isfinite(su).any() else float("nan"),
        }])
        summary.to_csv(outdir / "speedup_summary_sem_vs_synboth.csv", index=False)


# ----------------------------
# Plotting utilities
# ----------------------------
def savefig(path: Path) -> None:
    plt.tight_layout()
    plt.savefig(path, dpi=200)
    plt.close()


def plot_total_runtime_bar(df_agg: pd.DataFrame, outdir: Path) -> None:
    modes = sorted(df_agg["Mode"].unique())
    totals = [df_agg[df_agg["Mode"] == m]["Runtime total (s)"].sum() for m in modes]

    plt.figure(figsize=(10, 4.5))
    plt.bar(modes, totals)
    plt.ylabel("Sum of per-test runtimes (s)")
    plt.title("Total runtime (sum over tests) by mode (avg over repetitions per test)")
    plt.xticks(rotation=25, ha="right")
    savefig(outdir / "total_runtime_sum_by_mode.png")


def plot_runtime_box(df_agg: pd.DataFrame, outdir: Path) -> None:
    modes = sorted(df_agg["Mode"].unique())
    data = [df_agg[df_agg["Mode"] == m]["Runtime total (s)"].dropna().values for m in modes]

    plt.figure(figsize=(10, 4.5))
    plt.boxplot(data, labels=modes, showfliers=False)
    plt.ylabel("Per-test runtime (s)")
    plt.title("Runtime distribution by mode (per test, avg over repetitions)")
    plt.xticks(rotation=25, ha="right")
    savefig(outdir / "runtime_boxplot_by_mode.png")


def plot_passrate_bar(df_agg: pd.DataFrame, outdir: Path) -> None:
    modes = sorted(df_agg["Mode"].unique())
    passrates = []
    for m in modes:
        sub = df_agg[df_agg["Mode"] == m]
        passrates.append((sub["Test result"] == "Passed").mean() * 100.0 if len(sub) else np.nan)

    plt.figure(figsize=(10, 4.5))
    plt.bar(modes, passrates)
    plt.ylim(0, 100)
    plt.ylabel("Pass rate (%)")
    plt.title("Pass rate by mode (Passed iff all reps passed)")
    plt.xticks(rotation=25, ha="right")
    savefig(outdir / "passrate_by_mode.png")


def plot_semantic_vs_syntactic_both_scatter(df_agg: pd.DataFrame, outdir: Path) -> None:
    m = sem_vs_synboth_table(df_agg)
    if m.empty:
        return

    # --- LaTeX-friendly typography (no LaTeX install required) ---
    plt.rcParams.update({
        "font.family": "serif",
        "font.serif": ["CMU Serif", "Computer Modern Roman", "DejaVu Serif"],
        "mathtext.fontset": "cm",
        "font.size": 11,
        "axes.labelsize": 11,
        "xtick.labelsize": 10,
        "ytick.labelsize": 10,
        "legend.fontsize": 10,
    })

    x = m["rt_sem"].to_numpy(dtype=float)
    y = m["rt_syn"].to_numpy(dtype=float)

    # --- Linear scatter (no title) ---
    plt.figure(figsize=(4.6, 4.6))
    plt.scatter(x, y, s=18, color="#b9ceeb")
    mx = max(np.max(x), np.max(y)) if len(x) else 1.0
    plt.plot([0, mx], [0, mx], linewidth=1.0, linestyle="--")  # y=x
    plt.xlabel("semantic runtime (s)")
    plt.ylabel("syntactic-both runtime (s)")
    savefig(outdir / "scatter_semantic_vs_syntactic_both.png")

    # --- Log-log scatter (no title) ---
    plt.figure(figsize=(4.6, 4.6))
    plt.scatter(x, y, s=18, color="#b9ceeb")
    plt.xscale("log")
    plt.yscale("log")

    # Diagonal reference line in log space
    pos_x = x[x > 0]
    pos_y = y[y > 0]
    if pos_x.size and pos_y.size:
        lo = min(pos_x.min(), pos_y.min())
        hi = max(pos_x.max(), pos_y.max())
    else:
        lo, hi = 1e-4, 1.0

    plt.plot([lo, hi], [lo, hi], linewidth=1.0, linestyle="--")
    plt.xlabel("semantic runtime (s)")
    plt.ylabel("syntactic-both runtime (s)")
    savefig(outdir / "scatter_semantic_vs_syntactic_both_loglog.png")


def plot_speedup_histogram(df_agg: pd.DataFrame, outdir: Path) -> None:
    m = sem_vs_synboth_table(df_agg)
    if m.empty:
        return

    # LaTeX-friendly typography
    plt.rcParams.update({
        "font.family": "serif",
        "font.serif": ["CMU Serif", "Computer Modern Roman", "DejaVu Serif"],
        "mathtext.fontset": "cm",
        "font.size": 11,
        "axes.labelsize": 11,
        "xtick.labelsize": 10,
        "ytick.labelsize": 10,
    })

    ls = m["log2_speedup"].to_numpy(dtype=float)
    ls = ls[np.isfinite(ls)]
    if ls.size == 0:
        return

    med = float(np.median(ls))

    import matplotlib.ticker as mticker

    plt.figure(figsize=(3.4, 4.8))  # portrait
    plt.hist(ls, bins=40, orientation="horizontal", color="#b9ceeb")

    # parity line (0 = equal)
    plt.axhline(0.0, linestyle="--", linewidth=1.0)

    # median line (orange, as requested)
    plt.axhline(med, color="orange", linewidth=1.0)

    plt.xlabel("#tests")
    plt.ylabel("Speedup (semantic / syntactic-both)")

    # --- show ticks as actual speedup factors (2^y) instead of log2 values ---
    ax = plt.gca()

    lo = int(np.floor(ls.min()))
    hi = int(np.ceil(ls.max()))
    span = hi - lo
    step = 1 if span <= 12 else (2 if span <= 24 else 4)

    ticks = np.arange(lo, hi + 1, step)
    ax.set_yticks(ticks)

    def pow2_label(y, _pos=None) -> str:
        # y is log2(speedup); label as actual speedup factor
        if abs(y) < 1e-12:
            return "1"
        if float(y).is_integer():
            y = int(y)
            if y > 0:
                return str(2 ** y)          # e.g., 6 -> 64
            else:
                return f"1/{2 ** (-y)}"     # e.g., -6 -> 1/64
        return f"{2.0 ** float(y):.2g}"

    ax.yaxis.set_major_formatter(mticker.FuncFormatter(pow2_label))

    # no title
    savefig(outdir / "speedup_hist_sem_over_synboth.png")


def plot_stage_breakdown(stage_df: pd.DataFrame, outdir: Path) -> None:
    if stage_df.empty:
        return

    plt.rcParams.update({
        "font.family": "serif",
        "font.serif": ["CMU Serif", "Computer Modern Roman", "DejaVu Serif"],
        "mathtext.fontset": "cm",
        "font.size": 11,
        "axes.labelsize": 11,
        "xtick.labelsize": 10,
        "ytick.labelsize": 10,
        "legend.fontsize": 10,
    })

    stage_order = ["Characterizer", "WP", "SMT encoding", "SMT solving"]
    modes = sorted(stage_df["Mode"].unique())
    x = np.arange(len(modes))

    plt.figure(figsize=(6.8, 4.0))
    bottoms = np.zeros(len(modes))

    for stage in stage_order:
        vals = []
        for m in modes:
            row = stage_df[(stage_df["Mode"] == m) & (stage_df["Stage"] == stage)]
            if row.empty:
                v = 0.0
            else:
                v = float(row["share_of_stage_sum"].iloc[0])
                if not np.isfinite(v):
                    v = 0.0
                v *= 100.0
            vals.append(v)

        vals = np.array(vals, dtype=float)
        plt.bar(x, vals, bottom=bottoms, label=stage)
        bottoms += vals

    plt.xticks(x, modes, rotation=25, ha="right")
    plt.ylabel("Share of stage time (%)")
    plt.legend()
    plt.title("Stage breakdown per syntactic mode")
    savefig(outdir / "stage_breakdown_syntactic_modes.png")



def plot_stage_pies(stage_df: pd.DataFrame, outdir: Path) -> None:
    """
    Two big pies (z3, cvc5-proc) stacked tightly, with a dedicated legend row below.
    """
    if stage_df.empty:
        return

    plt.rcParams.update({
        "font.family": "serif",
        "font.serif": ["CMU Serif", "Computer Modern Roman", "DejaVu Serif"],
        "mathtext.fontset": "cm",
        "font.size": 10,
        "axes.titlesize": 11,
        "legend.fontsize": 9,
    })

    stage_order = ["Characterizer", "WP", "SMT encoding", "SMT solving"]

    all_modes = list(stage_df["Mode"].unique())
    modes = [m for m in ("syntactic-z3", "syntactic-cvc5-proc") if m in all_modes]
    if not modes:
        return

    mode_title = {"syntactic-z3": "z3", "syntactic-cvc5-proc": "cvc5-proc"}
    stage_colors = ["#F8CBAD", "#C5E0B4", "#FDEBAA", "#B2C7E6"]

    n = len(modes)

    # Big pies, tight spacing; legend gets its own (short) row.
    fig_h = 2.4 * n + 0.65
    fig = plt.figure(figsize=(3, fig_h))
    gs = fig.add_gridspec(
        nrows=n + 1,
        ncols=1,
        height_ratios=[1.2] * n + [0.16],  # last row reserved for legend
        hspace=0.5,                       # <-- THIS controls the gap between pies
    )

    axes = [fig.add_subplot(gs[i, 0]) for i in range(n)]
    leg_ax = fig.add_subplot(gs[n, 0])
    leg_ax.axis("off")

    def autopct_func(pct: float) -> str:
        return f"{pct:.1f}%" if pct >= 3.0 else ""

    legend_handles = None
    legend_labels = None

    for ax, mode in zip(axes, modes):
        sub = stage_df[stage_df["Mode"] == mode]
        if sub.empty:
            continue

        sub = sub.set_index("Stage").reindex(stage_order).reset_index()

        sizes = (sub["share_of_stage_sum"].to_numpy(dtype=float) * 100.0)
        sizes = np.nan_to_num(sizes, nan=0.0, posinf=0.0, neginf=0.0)
        sizes = np.clip(sizes, 0.0, None)
        if float(sizes.sum()) <= 0.0:
            continue

        labels = sub["Stage"].tolist()

        wedges, _texts, _autotexts = ax.pie(
            sizes,
            labels=None,
            autopct=autopct_func,
            startangle=90,
            colors=stage_colors[:len(labels)],
            textprops={"fontsize": 9},
            radius=1.4,      # <-- BIG pies
            pctdistance=0.7,
        )
        ax.set_title(mode_title.get(mode, mode), pad=10)
        ax.set_aspect("equal")

        if legend_handles is None:
            legend_handles = wedges
            legend_labels = labels

    if legend_handles is not None and legend_labels is not None:
        leg = leg_ax.legend(
            legend_handles,
            legend_labels,
            loc="center",
            ncol=2,
            frameon=True,
            framealpha=1.0,
            handlelength=1.0,
            handletextpad=0.5,
            columnspacing=1.0,
            labelspacing=0.35,
        )
        leg._legend_box.align = "left"

    outdir.mkdir(parents=True, exist_ok=True)
    savefig(outdir / "stage_pies_syntactic_z3_cvc5proc.png")


def plot_runtime_by_suite(df_agg: pd.DataFrame, outdir: Path) -> None:
    focus = df_agg[df_agg["Mode"].isin(["semantic", "syntactic-both"])].copy()
    if focus.empty:
        return

    suites = sorted(focus["Suite"].unique())
    modes = ["semantic", "syntactic-both"]

    mat = np.zeros((len(suites), len(modes)), dtype=float)
    for i, s in enumerate(suites):
        for j, m in enumerate(modes):
            mat[i, j] = focus[(focus["Suite"] == s) & (focus["Mode"] == m)]["Runtime total (s)"].sum()

    plt.figure(figsize=(11, 4.8))
    x = np.arange(len(suites))
    width = 0.35
    plt.bar(x - width / 2, mat[:, 0], width, label="semantic")
    plt.bar(x + width / 2, mat[:, 1], width, label="syntactic-both")
    plt.xticks(x, suites, rotation=25, ha="right")
    plt.ylabel("Sum runtime in suite (s)")
    plt.title("Semantic vs Syntactic-both: total runtime per suite")
    plt.legend()
    savefig(outdir / "semantic_vs_synboth_runtime_by_suite.png")


# ----------------------------
# Better speedup visualizations (semantic vs syntactic-both)
# ----------------------------
def plot_speedup_ecdf(df_agg: pd.DataFrame, outdir: Path) -> None:
    m = sem_vs_synboth_table(df_agg)
    if m.empty:
        return

    su = np.sort(m["speedup"].to_numpy(dtype=float))
    y = np.arange(1, len(su) + 1) / len(su)

    plt.figure(figsize=(7.5, 4.8))
    plt.step(su, y, where="post")
    plt.axvline(1.0, linestyle="--")
    plt.xscale("log")
    plt.xlabel("Speedup (semantic / syntactic-both) [log scale]")
    plt.ylabel("Fraction of tests ≤ x")
    plt.title("ECDF of speedup (semantic vs syntactic-both)")
    savefig(outdir / "speedup_ecdf_sem_vs_synboth.png")


def plot_speedup_survival(df_agg: pd.DataFrame, outdir: Path) -> None:
    m = sem_vs_synboth_table(df_agg)
    if m.empty:
        return

    su = np.sort(m["speedup"].to_numpy(dtype=float))
    y = 1.0 - (np.arange(1, len(su) + 1) / len(su))

    plt.figure(figsize=(7.5, 4.8))
    plt.step(su, y, where="post")
    plt.axvline(1.0, linestyle="--")
    plt.xscale("log")
    plt.xlabel("Speedup (semantic / syntactic-both) [log scale]")
    plt.ylabel("Fraction of tests ≥ x")
    plt.title("Survival curve of speedup (fraction at least x× faster)")
    savefig(outdir / "speedup_survival_sem_vs_synboth.png")


def plot_speedup_rank(df_agg: pd.DataFrame, outdir: Path) -> None:
    m = sem_vs_synboth_table(df_agg)
    if m.empty:
        return

    su = np.sort(m["speedup"].to_numpy(dtype=float))[::-1]
    x = np.arange(1, len(su) + 1)

    plt.figure(figsize=(8.5, 4.8))
    plt.plot(x, su)
    plt.axhline(1.0, linestyle="--")
    plt.yscale("log")
    plt.xlabel("Test rank (sorted by speedup)")
    plt.ylabel("Speedup (semantic / syntactic-both) [log scale]")
    plt.title("Speedup rank plot (semantic vs syntactic-both)")
    savefig(outdir / "speedup_rank_sem_vs_synboth.png")


def plot_speedup_vs_runtime(df_agg: pd.DataFrame, outdir: Path) -> None:
    m = sem_vs_synboth_table(df_agg)
    if m.empty:
        return

    x = m["rt_sem"].to_numpy(dtype=float)
    y = m["log2_speedup"].to_numpy(dtype=float)

    plt.figure(figsize=(7.5, 5.2))
    plt.scatter(x, y, s=18)
    plt.axhline(0.0, linestyle="--")
    plt.xscale("log")
    plt.xlabel("Semantic runtime per test (s) [log scale]")
    plt.ylabel("log2(speedup) = log2(semantic / syntactic-both)")
    plt.title("Speedup vs baseline runtime (semantic vs syntactic-both)")
    savefig(outdir / "speedup_vs_semantic_runtime.png")


def plot_logspeedup_box(df_agg: pd.DataFrame, outdir: Path) -> None:
    m = sem_vs_synboth_table(df_agg)
    if m.empty:
        return

    # --- LaTeX-friendly typography (works without having LaTeX installed) ---
    plt.rcParams.update({
        "font.family": "serif",
        "font.serif": ["CMU Serif", "Computer Modern Roman", "DejaVu Serif"],
        "mathtext.fontset": "cm",
        "font.size": 11,
        "axes.labelsize": 11,
        "xtick.labelsize": 10,
        "ytick.labelsize": 10,
    })

    ls = m["log2_speedup"].to_numpy(dtype=float)

    plt.figure(figsize=(2.6, 4.2))  # narrower portrait
    plt.boxplot(ls, vert=True, showfliers=False, widths=0.32)

    plt.axhline(0.0, linestyle="--")

    ax = plt.gca()
    ax.set_ylabel("log2(speedup)")

    # remove x-axis completely
    ax.set_xticks([])
    ax.set_xlabel("")
    ax.tick_params(axis="x", which="both", bottom=False, top=False, labelbottom=False)

    # only west (left) spine
    for spine in ["top", "right", "bottom"]:
        ax.spines[spine].set_visible(False)
    ax.spines["left"].set_visible(True)

    savefig(outdir / "logspeedup_box_sem_vs_synboth.png")

def plot_speedup_cake(df_agg: pd.DataFrame, outdir: Path, eps: float = 0.05) -> None:
    """
    Compact pie chart with ONLY:
      - syntactic-both faster
      - syntactic-both not faster (includes equal + slower)

    - No title
    - Legend in a small boxed corner
    - Slice labels show: "xx.x% (N)"
    """
    m = sem_vs_synboth_table(df_agg)
    if m.empty:
        return

    su = m["speedup"].to_numpy(dtype=float)
    faster = int(np.sum(su > 1.0 + eps))
    not_faster = int(len(su) - faster)

    sizes = [faster, not_faster]
    names = ["syntactic faster", "syntactic not faster"]

    # Ensure counts printed in the same order as wedges (exact, not rounded)
    counts_iter = iter(sizes)
    def autopct(_pct: float) -> str:
        n = next(counts_iter)
        total = faster + not_faster
        pct = (100.0 * n / total) if total > 0 else 0.0
        return f"{pct:.1f}% ({n})"

    plt.figure(figsize=(4.2, 4.2))
    wedges, _texts, _autotexts = plt.pie(
        sizes,
        labels=None,           # no labels on slices; we use legend instead
        autopct=autopct,       # percentage with absolute count in brackets
        startangle=90,
    )

    # Small boxed legend in the corner (inside axes)
    plt.legend(
        wedges,
        names,
        loc="upper right",
        bbox_to_anchor=(0.98, 0.98),
        frameon=True,
        framealpha=1.0,
        fontsize="small",
        borderaxespad=0.0,
        handlelength=1.0,
        handletextpad=0.5,
        labelspacing=0.3,
    )

    savefig(outdir / "speedup_cake_sem_vs_synboth.png")

# ----------------------------
# Wide CSV with all modes side-by-side (+ speedups)
# ----------------------------
def write_wide_per_test_csv(df_agg: pd.DataFrame, outdir: Path) -> None:
    base_cols = ["Test case name", "Suite", "Option", "Actual LOC", "Spec LOC", "Proof LOC", "Havoc statements"]
    base = (
        df_agg.sort_values(["Test case name", "Mode"])
        .groupby("Test case name", as_index=False)
        .first()[base_cols]
    )

    metric_cols = [
        "Runtime total (s)",
        "Runtime Characterizer avg (s)",
        "Runtime WP avg (s)",
        "Runtime SMT encoding avg (s)",
        "Runtime SMT solving avg (s)",
        "Number of triples",
        "Test result",
    ]

    tmp = df_agg[["Test case name", "Mode"] + metric_cols].copy()
    wide = tmp.pivot(index="Test case name", columns="Mode", values=metric_cols)
    wide.columns = [f"{metric}__{mode}" for metric, mode in wide.columns]
    wide = wide.reset_index()

    out = base.merge(wide, on="Test case name", how="left")

    rt_sem = "Runtime total (s)__semantic"

    def add_speedup(mode: str) -> None:
        rt_syn = f"Runtime total (s)__{mode}"
        if rt_sem in out.columns and rt_syn in out.columns:
            out[f"Speedup semantic/{mode} (total)"] = out[rt_sem] / out[rt_syn]
            out[f"Speedup {mode}/semantic (total)"] = out[rt_syn] / out[rt_sem]

    for m in ["syntactic-both", "syntactic-z3", "syntactic-cvc5-proc"]:
        add_speedup(m)

    preferred_order = ["semantic", "syntactic-both", "syntactic-z3", "syntactic-cvc5-proc"]

    def sort_key(c: str):
        if c in base_cols:
            return (0, 0, c)
        if c.startswith("Speedup "):
            return (2, 0, c)
        for mi, m in enumerate(metric_cols, start=1):
            prefix = f"{m}__"
            if c.startswith(prefix):
                mode = c[len(prefix):]
                mo = preferred_order.index(mode) if mode in preferred_order else 999
                return (1, mi * 1000 + mo, c)
        return (3, 999999, c)

    out = out[sorted(out.columns, key=sort_key)]

    out_path = outdir / "per_test_wide_all_modes.csv"
    out.to_csv(out_path, index=False)
    print(f"Wrote wide per-test CSV to: {out_path}")

def list_slower_tests(df_agg: pd.DataFrame, outdir: Path, eps: float = 0.0, top: int = 50) -> None:
    """
    Print and export test cases where syntactic-both is slower than semantic.

    Condition:
      speedup = rt_sem / rt_syn < 1 - eps
    eps=0.05 would treat [0.95, 1.05] as roughly equal.
    """
    m = sem_vs_synboth_table(df_agg)
    if m.empty:
        print("No semantic vs syntactic-both data available.")
        return

    slower = m[m["speedup"] < 1.0 - eps].copy()
    if slower.empty:
        print(f"No tests where syntactic-both is slower (eps={eps:.2f}).")
        return

    # Sort by worst regression first (smallest speedup means largest slowdown)
    slower = slower.sort_values("speedup", ascending=True)

    print(f"\n=== Tests where syntactic-both is slower than semantic (eps={eps:.2f}) ===")
    print(f"{len(slower)}/{len(m)} tests ({len(slower)/len(m)*100.0:.1f}%)\n")

    for _, r in slower.head(top).iterrows():
        name = r["Test case name"]
        rt_sem = float(r["rt_sem"])
        rt_syn = float(r["rt_syn"])
        speedup = float(r["speedup"])          # < 1 => slower
        slowdown = 1.0 / speedup               # > 1 => syntactic slower by this factor
        print(f"{name}")
        print(f"  semantic={rt_sem:.4f}s, syntactic-both={rt_syn:.4f}s, "
              f"speedup={speedup:.3f}, slowdown={slowdown:.3f}x")

    # Write full list to CSV for convenience
    out_path = outdir / "syntactic_both_slower_tests.csv"
    slower_out = slower[[
        "Test case name", "Suite", "Option",
        "rt_sem", "rt_syn", "speedup", "log2_speedup",
        "res_sem", "res_syn",
        "Actual LOC", "Spec LOC", "Proof LOC",
    ]].copy()
    slower_out["slowdown_syn_over_sem"] = 1.0 / slower_out["speedup"]
    slower_out.to_csv(out_path, index=False)

def compute_stage_stats(df_agg: pd.DataFrame, outdir: Path) -> pd.DataFrame:
    """
    Aggregate stage runtimes per syntactic SMT mode.

    For each Mode (syntactic-z3, syntactic-cvc5-proc), and each stage:
      - mean_stage_time  (mean over tests)
      - median_stage_time
      - sum_stage_time   (sum over tests)
      - share_of_stage_sum       (stage_sum / sum of all stage_sums in that mode)
      - share_of_total_runtime   (stage_sum / total Runtime total (s) in that mode)

    Benchmarks listed in EXCLUDE_FOR_STAGE_PLOTS are ignored.
    """
    stage_cols = [
        "Runtime Characterizer avg (s)",
        "Runtime WP avg (s)",
        "Runtime SMT encoding avg (s)",
        "Runtime SMT solving avg (s)",
    ]

    # only syntactic modes
    sub = df_agg[df_agg["Mode"].str.startswith("syntactic-")].copy()

    # exclude specific benchmarks for fairness in stage breakdown
    if "Test case name" in sub.columns:
        sub = sub[~sub["Test case name"].isin(EXCLUDE_FOR_STAGE_PLOTS)].copy()

    if sub.empty:
        print("No syntactic stage timing data found after exclusions.")
        return pd.DataFrame()

    rows = []
    for mode in sorted(sub["Mode"].unique()):
        if mode not in ("syntactic-z3", "syntactic-cvc5-proc"):
            continue

        sm = sub[sub["Mode"] == mode]
        if sm.empty:
            continue

        total_runtime = float(np.nansum(sm["Runtime total (s)"].to_numpy(dtype=float)))

        stage_sums = {}
        for col in stage_cols:
            vals = sm[col].to_numpy(dtype=float)
            vals = vals[np.isfinite(vals)]
            stage_sums[col] = float(np.nansum(vals))

        total_stage_sum = float(sum(stage_sums.values())) if stage_sums else float("nan")

        for col in stage_cols:
            vals = sm[col].to_numpy(dtype=float)
            vals = vals[np.isfinite(vals)]
            if vals.size == 0:
                mean_stage = float("nan")
                median_stage = float("nan")
            else:
                mean_stage = float(np.mean(vals))
                median_stage = float(np.median(vals))

            stage_sum = stage_sums[col]
            share_stage_sum = (
                stage_sum / total_stage_sum
                if np.isfinite(total_stage_sum) and total_stage_sum > 0.0
                else float("nan")
            )
            share_total_runtime = (
                stage_sum / total_runtime
                if np.isfinite(total_runtime) and total_runtime > 0.0
                else float("nan")
            )

            rows.append({
                "Mode": mode,
                "Stage": col.replace("Runtime ", "").replace(" avg (s)", ""),
                "mean_stage_time": mean_stage,
                "median_stage_time": median_stage,
                "sum_stage_time": stage_sum,
                "share_of_stage_sum": share_stage_sum,
                "share_of_total_runtime": share_total_runtime,
                "num_tests": len(sm),
            })

    stage_df = pd.DataFrame(rows)

    out_path = outdir / "stage_breakdown_stats.csv"
    stage_df.to_csv(out_path, index=False)
    print(f"Wrote stage breakdown stats to: {out_path}")
    return stage_df


def print_stage_stats(stage_df: pd.DataFrame) -> None:
    """
    Pretty console summary of stage shares per mode.
    Uses share_of_stage_sum (sum over tests per stage / sum over all stages).
    """
    if stage_df.empty:
        return

    print("\n=== Stage time shares per syntactic mode (based on sum over tests) ===")
    pivot = stage_df.pivot(index="Stage", columns="Mode", values="share_of_stage_sum") * 100.0
    with pd.option_context("display.max_columns", None, "display.width", 220):
        # 3 decimals after comma
        print(pivot.round(3).to_string())

def compute_run_stability(df: pd.DataFrame, outdir: Path) -> pd.DataFrame:
    """
    For each (test case, mode), compute statistics over repetitions:
      - n_runs
      - mean, std, min, max of Runtime total (s)
      - coefficient of variation (cv = std / mean)

    Returns a DataFrame with one row per (test, mode).
    Also writes it to per_test_mode_run_stability.csv.
    """
    group_keys = ["Test case name", "Suite", "Option", "Engine", "SMT mode", "Mode"]

    g = (
        df.groupby(group_keys)["Runtime total (s)"]
          .agg(n_runs="count", mean="mean", std="std", min="min", max="max")
          .reset_index()
    )

    # Coefficient of variation: std / mean
    g["cv"] = g["std"] / g["mean"]

    out_path = outdir / "per_test_mode_run_stability.csv"
    g.to_csv(out_path, index=False)
    print(f"Wrote per-test run stability stats to: {out_path}")

    return g


def print_run_stability_summary(stab: pd.DataFrame) -> None:
    """
    Print per-mode stability statistics based on the per-test/per-mode
    run statistics produced by compute_run_stability().
    Focuses on Runtime total (s).
    """
    print("\n=== Runtime stability across repetitions (per mode) ===")
    modes = sorted(stab["Mode"].unique())

    rows = []
    for m in modes:
        sub = stab[stab["Mode"] == m]

        # Only tests with at least 2 runs can have a real std/cv
        multi = sub[sub["n_runs"] >= 2].copy()
        cvs = multi["cv"].to_numpy(dtype=float)
        cvs = cvs[np.isfinite(cvs)]

        if cvs.size == 0:
            rows.append({
                "Mode": m,
                "#tests(≥2 runs)": 0,
                "median_cv": np.nan,
                "mean_cv": np.nan,
                "p95_cv": np.nan,
                "frac_cv≤0.05": np.nan,
                "frac_cv≤0.10": np.nan,
            })
            continue

        rows.append({
            "Mode": m,
            "#tests(≥2 runs)": len(cvs),
            "median_cv": float(np.median(cvs)),
            "mean_cv": float(np.mean(cvs)),
            "p95_cv": float(np.quantile(cvs, 0.95)),
            "frac_cv≤0.05": float(np.mean(cvs <= 0.05)),
            "frac_cv≤0.10": float(np.mean(cvs <= 0.10)),
        })

    tab = pd.DataFrame(rows).sort_values("Mode")
    with pd.option_context("display.max_columns", None, "display.width", 220):
        print(tab.to_string(index=False))


# ----------------------------
# Main
# ----------------------------
def main() -> None:
    ap = argparse.ArgumentParser(description="Analyze HHLVerifier evaluation CSVs and generate stats/plots.")
    ap.add_argument(
        "--input",
        nargs="+",
        default=["src/test/evaluation/output_all_*.csv"],
        help="Glob(s) for CSV input files, e.g. src/test/evaluation/output_all_*.csv",
    )
    ap.add_argument("--outdir", default="src/test/evaluation/plots", help="Output directory for plots + aggregated CSVs")
    args = ap.parse_args()

    outdir = ensure_outdir(args.outdir)

    df = read_inputs(args.input)
    df = df[~df["Test case name"].isin(EXCLUDE_FROM_EVAL)].copy()

    stab = compute_run_stability(df, outdir)
    print_run_stability_summary(stab)

    df_agg = agg_over_reps(df)

    stage_df = compute_stage_stats(df_agg, outdir)
    print_stage_stats(stage_df)

    list_slower_tests(df_agg, outdir, eps=0.05, top=9999)

    df.to_csv(outdir / "raw_concat.csv", index=False)
    df_agg.to_csv(outdir / "avg_over_reps_per_test.csv", index=False)

    write_wide_per_test_csv(df_agg, outdir)

    print_stats(df_agg, outdir)

    # Existing plots
    plot_total_runtime_bar(df_agg, outdir)
    plot_runtime_box(df_agg, outdir)
    plot_passrate_bar(df_agg, outdir)
    plot_semantic_vs_syntactic_both_scatter(df_agg, outdir)
    plot_speedup_histogram(df_agg, outdir)
    plot_stage_breakdown(stage_df, outdir)
    plot_stage_pies(stage_df, outdir)
    plot_runtime_by_suite(df_agg, outdir)

    # Better speedup plots (semantic vs syntactic-both)
    plot_speedup_ecdf(df_agg, outdir)
    plot_speedup_survival(df_agg, outdir)
    plot_speedup_rank(df_agg, outdir)
    plot_speedup_vs_runtime(df_agg, outdir)
    plot_logspeedup_box(df_agg, outdir)
    plot_speedup_cake(df_agg, outdir)

    print(f"\nWrote plots + aggregated CSVs to: {outdir.resolve()}")
    print("Key outputs:")
    print(f"  - {outdir / 'avg_over_reps_per_test.csv'}")
    print(f"  - {outdir / 'per_test_wide_all_modes.csv'}")
    print(f"  - {outdir / 'speedup_summary_sem_vs_synboth.csv'}")
    print(f"  - {outdir / 'speedup_ecdf_sem_vs_synboth.png'}")
    print(f"  - {outdir / 'speedup_vs_semantic_runtime.png'}")


if __name__ == "__main__":
    main()
