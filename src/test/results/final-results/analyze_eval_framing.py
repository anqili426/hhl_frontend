#!/usr/bin/env python3
"""
Compare syntactic-both runtimes with framing ENABLED (from output_all_*.csv)
vs framing DISABLED (from 5x output*.csv of the reduced format).

Usage:
  python3 analyze_eval_framing.py \
    --with "src/test/evaluation/output_all_*.csv" \
    --without "src/test/evaluation/output*.csv" \
    --outdir "src/test/evaluation/plots_framing_cmp"

Notes:
- Compares ONLY syntactic-both.
- Averages over repetitions per test in both datasets.
- Merges on "Test case name" intersection.
"""

import argparse
import glob
import os
import re
from pathlib import Path
from typing import List

import numpy as np
import pandas as pd

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


# ----------------------------
# Exclusions (same as your eval script)
# ----------------------------
EXCLUDE_FROM_EVAL = {
    "src/test/evaluation/exists/orhle/sandbox.hhl",
    "src/test/evaluation/exists-forall/orhle/gni/nondet_leak.hhl",
    "src/test/evaluation/forall-exists/hypa/counter_diff.hhl",
    "src/test/evaluation/forall-exists/hypa/counter_sum.hhl",
    "src/test/evaluation/forall/pcsat/half_square_ni.hhl",
}

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
]

# ----------------------------
# Helpers
# ----------------------------
def ensure_outdir(outdir: str) -> Path:
    p = Path(outdir)
    p.mkdir(parents=True, exist_ok=True)
    return p

def safe_to_numeric(s: pd.Series) -> pd.Series:
    s = s.replace({"---": np.nan, "NaN": np.nan, "nan": np.nan, "": np.nan})
    return pd.to_numeric(s, errors="coerce")

def expand_globs(patterns: List[str]) -> List[str]:
    files: List[str] = []
    for pat in patterns:
        files.extend(glob.glob(pat))
    files = sorted(set(files))
    if not files:
        raise SystemExit(f"No input files matched: {patterns}")
    return files

def rep_from_filename(fp: str) -> int:
    m = re.search(r"(\d+)", os.path.basename(fp))
    return int(m.group(1)) if m else -1

def pass_all(x: pd.Series) -> str:
    xs = x.fillna("").astype(str).str.lower()
    if (xs == "failed").any():
        return "Failed"
    if (xs == "passed").all():
        return "Passed"
    return "Mixed"

def savefig(path: Path) -> None:
    plt.tight_layout()
    plt.savefig(path, dpi=200)
    plt.close()


# ----------------------------
# Reading "with framing" (output_all_*.csv)
# ----------------------------
def read_with_framing(patterns: List[str]) -> pd.DataFrame:
    files = expand_globs(patterns)

    dfs = []
    for fp in files:
        df = pd.read_csv(fp)
        df["__file"] = os.path.basename(fp)
        df["rep"] = rep_from_filename(fp)
        dfs.append(df)

    out = pd.concat(dfs, ignore_index=True)

    # normalize required columns
    out["Test case name"] = out["Test case name"].fillna("").astype(str).str.strip()
    out = out[~out["Test case name"].isin(EXCLUDE_FROM_EVAL)].copy()

    # fill missing numeric cols with NaN
    for c in NUM_COLS:
        if c not in out.columns:
            out[c] = np.nan
        out[c] = safe_to_numeric(out[c])

    # normalize key columns present in output_all_*.csv
    out["Engine"] = out.get("Engine", "").fillna("").astype(str).str.strip()
    out["SMT mode"] = out.get("SMT mode", "").fillna("").astype(str).str.strip()
    out["Option"] = out.get("Option", "(default)").fillna("").astype(str).str.strip()
    out.loc[out["Option"] == "", "Option"] = "(default)"

    if "Test result" not in out.columns:
        out["Test result"] = ""
    else:
        out["Test result"] = out["Test result"].fillna("").astype(str)

    # keep ONLY syntactic-both (framing enabled baseline)
    # (syntactic engine + SMT mode "both")
    out = out[(out["Engine"] == "syntactic") & (out["SMT mode"] == "both")].copy()
    out["config"] = "with_framing"
    return out


# ----------------------------
# Reading "without framing" (5x output*.csv reduced format)
# ----------------------------
def read_without_framing(patterns: List[str]) -> pd.DataFrame:
    files = expand_globs(patterns)

    dfs = []
    for fp in files:
        df = pd.read_csv(fp)
        df["__file"] = os.path.basename(fp)
        df["rep"] = rep_from_filename(fp)
        dfs.append(df)

    out = pd.concat(dfs, ignore_index=True)

    out["Test case name"] = out["Test case name"].fillna("").astype(str).str.strip()
    out = out[~out["Test case name"].isin(EXCLUDE_FROM_EVAL)].copy()

    # The reduced CSV uses "SMT mode" as e.g. "both" already. Ensure it's string.
    out["SMT mode"] = out.get("SMT mode", "both").fillna("both").astype(str).str.strip()

    # numeric parsing
    for c in NUM_COLS:
        if c not in out.columns:
            out[c] = np.nan
        out[c] = safe_to_numeric(out[c])

    if "Test result" not in out.columns:
        out["Test result"] = ""
    else:
        out["Test result"] = out["Test result"].fillna("").astype(str)

    # keep ONLY syntactic-both rows (SMT mode == both)
    out = out[out["SMT mode"] == "both"].copy()
    out["config"] = "without_framing"
    return out


# ----------------------------
# Aggregate over repetitions per test
# ----------------------------
def agg_over_reps(df: pd.DataFrame) -> pd.DataFrame:
    group_keys = ["Test case name", "config"]
    agg_dict = {c: "mean" for c in NUM_COLS}
    agg_dict["Test result"] = pass_all
    return df.groupby(group_keys, dropna=False).agg(agg_dict).reset_index()


# ----------------------------
# Plots
# ----------------------------
def plot_scatter(with_df: pd.DataFrame, outdir: Path) -> None:
    x = with_df["rt_with"].to_numpy(dtype=float)
    y = with_df["rt_without"].to_numpy(dtype=float)

    plt.rcParams.update({
        "font.family": "serif",
        "font.serif": ["CMU Serif", "Computer Modern Roman", "DejaVu Serif"],
        "mathtext.fontset": "cm",
        "font.size": 11,
        "axes.labelsize": 11,
        "xtick.labelsize": 10,
        "ytick.labelsize": 10,
    })

    # linear
    plt.figure(figsize=(4.8, 4.8))
    plt.scatter(x, y, s=18)
    mx = max(np.max(x), np.max(y)) if len(x) else 1.0
    plt.plot([0, mx], [0, mx], linewidth=1.0, linestyle="--")
    plt.xlabel("with framing runtime (s)")
    plt.ylabel("without framing runtime (s)")
    savefig(outdir / "scatter_with_vs_without_framing.png")

    # log-log
    plt.figure(figsize=(4.8, 4.8))
    plt.scatter(x, y, s=18)
    plt.xscale("log")
    plt.yscale("log")

    pos_x = x[x > 0]
    pos_y = y[y > 0]
    lo = min(pos_x.min(), pos_y.min()) if pos_x.size and pos_y.size else 1e-4
    hi = max(pos_x.max(), pos_y.max()) if pos_x.size and pos_y.size else 1.0

    plt.plot([lo, hi], [lo, hi], linewidth=1.0, linestyle="--")
    plt.xlabel("with framing runtime (s)")
    plt.ylabel("without framing runtime (s)")
    savefig(outdir / "scatter_with_vs_without_framing_loglog.png")


def plot_speedup_histogram(merged: pd.DataFrame, outdir: Path) -> None:
    """
    Histogram in log2-space, but y-axis shows actual factors (1/64, ..., 1, 2, ..., 64).
    speedup := (without_framing / with_framing)
      > 1 => framing helps (with framing faster)
    """
    su = merged["speedup_without_over_with"].to_numpy(dtype=float)
    su = su[np.isfinite(su) & (su > 0)]
    if su.size == 0:
        return

    ls = np.log2(su)
    med = float(np.median(ls))

    import matplotlib.ticker as mticker

    plt.rcParams.update({
        "font.family": "serif",
        "font.serif": ["CMU Serif", "Computer Modern Roman", "DejaVu Serif"],
        "mathtext.fontset": "cm",
        "font.size": 11,
        "axes.labelsize": 11,
        "xtick.labelsize": 10,
        "ytick.labelsize": 10,
    })

    plt.figure(figsize=(3.4, 4.8))
    plt.hist(ls, bins=40, orientation="horizontal")

    plt.axhline(0.0, linestyle="--", linewidth=1.0)     # parity
    plt.axhline(med, color="orange", linewidth=1.0)     # median

    plt.xlabel("#tests")
    plt.ylabel("Speedup factor (without / with)")

    ax = plt.gca()
    lo = int(np.floor(ls.min()))
    hi = int(np.ceil(ls.max()))
    span = hi - lo
    step = 1 if span <= 12 else (2 if span <= 24 else 4)
    ticks = np.arange(lo, hi + 1, step)
    ax.set_yticks(ticks)

    def pow2_label(y, _pos=None) -> str:
        if abs(y) < 1e-12:
            return "1"
        if float(y).is_integer():
            y = int(y)
            if y > 0:
                return str(2 ** y)
            else:
                return f"1/{2 ** (-y)}"
        return f"{2.0 ** float(y):.2g}"

    ax.yaxis.set_major_formatter(mticker.FuncFormatter(pow2_label))
    savefig(outdir / "speedup_hist_without_over_with.png")

def print_overview_tables(agg_with: pd.DataFrame, agg_wo: pd.DataFrame, merged: pd.DataFrame, eps: float) -> None:
    """
    Prints:
      (A) Per-config overview table (with vs without framing)
      (B) Speedup overview (without/with)
    All runtimes are per-test means (already averaged over repetitions).
    """

    def summarize(agg: pd.DataFrame, label: str) -> dict:
        rt = agg["Runtime total (s)"].dropna()
        n = int(len(agg))
        passed = int((agg["Test result"] == "Passed").sum())
        failed = int((agg["Test result"] == "Failed").sum())
        mixed  = int((agg["Test result"] == "Mixed").sum())

        return {
            "Config": label,
            "#tests": n,
            "Passed": passed,
            "Failed": failed,
            "Mixed": mixed,
            "PassRate(%)": (passed / n * 100.0) if n else np.nan,
            "TotalRuntimeSum(s)": float(rt.sum()) if len(rt) else np.nan,
            "MeanRuntime(s)": float(rt.mean()) if len(rt) else np.nan,
            "StdRuntime(s)": float(rt.std(ddof=1)) if len(rt) > 1 else np.nan,
            "MedianRuntime(s)": float(rt.median()) if len(rt) else np.nan,
            "P95Runtime(s)": float(rt.quantile(0.95)) if len(rt) else np.nan,
        }

    # agg_* are already per-test (avg over reps) for each config
    row_with = summarize(agg_with, "with_framing")
    row_wo   = summarize(agg_wo,   "without_framing")

    tab = pd.DataFrame([row_with, row_wo])

    print("\n=== Overview (syntactic-both, per test avg over reps) ===")
    with pd.option_context("display.max_columns", None, "display.width", 220):
        print(tab.to_string(index=False))

    # Speedup overview on intersection only
    if merged is None or merged.empty:
        print("\n=== Speedup overview (without / with) ===")
        print("No comparable tests after intersection / filtering.")
        return

    su = merged["speedup_without_over_with"].to_numpy(dtype=float)
    su = su[np.isfinite(su) & (su > 0)]
    if su.size == 0:
        print("\n=== Speedup overview (without / with) ===")
        print("No finite positive speedups available.")
        return

    helps = int(np.sum(su > 1.0 + eps))          # with faster => framing helps
    hurts = int(np.sum(su < 1.0 - eps))          # without faster => framing hurts
    equal = int(su.size - helps - hurts)

    geo = float(np.exp(np.mean(np.log(su)))) if su.size else float("nan")

    speed_tab = pd.DataFrame([{
        "Compared tests": int(su.size),
        "Framing helps": helps,
        "≈equal": equal,
        "Framing hurts": hurts,
        "mean": float(np.mean(su)),
        "median": float(np.median(su)),
        "geo-mean": geo,
        "p95": float(np.quantile(su, 0.95)),
        "eps": float(eps),
    }])

    print("\n=== Speedup overview (speedup = without / with) ===")
    with pd.option_context("display.max_columns", None, "display.width", 220):
        print(speed_tab.to_string(index=False))


# ----------------------------
# Main comparison
# ----------------------------
def main() -> None:
    ap = argparse.ArgumentParser(description="Compare syntactic-both with vs without framing.")
    ap.add_argument(
        "--with",
        dest="with_globs",
        nargs="+",
        default=["src/test/evaluation/output_all_*.csv"],
        help="Glob(s) for 'with framing' CSVs (output_all_*.csv).",
    )
    ap.add_argument(
        "--without",
        dest="without_globs",
        nargs="+",
        required=True,
        help="Glob(s) for 'without framing' CSVs (5x output*.csv of reduced format).",
    )
    ap.add_argument("--outdir", default="src/test/evaluation/plots_framing_cmp")
    ap.add_argument("--eps", type=float, default=0.05, help="Tolerance for faster/slower classification.")
    args = ap.parse_args()

    outdir = ensure_outdir(args.outdir)

    df_with = read_with_framing(args.with_globs)
    df_wo   = read_without_framing(args.without_globs)

    agg_with = agg_over_reps(df_with)
    agg_wo = agg_over_reps(df_wo)

    with_rt = agg_with.rename(columns={
        "Runtime total (s)": "rt_with",
        "Test result": "res_with",
    })[["Test case name", "rt_with", "res_with"]]

    wo_rt = agg_wo.rename(columns={
        "Runtime total (s)": "rt_without",
        "Test result": "res_without",
    })[["Test case name", "rt_without", "res_without"]]

    merged = with_rt.merge(wo_rt, on="Test case name", how="inner")
    merged = merged.dropna(subset=["rt_with", "rt_without"])
    merged = merged[(merged["rt_with"] > 0) & (merged["rt_without"] > 0)].copy()

    merged["speedup_without_over_with"] = merged["rt_without"] / merged["rt_with"]
    merged["log2_speedup"] = np.log2(merged["speedup_without_over_with"].to_numpy(dtype=float))

    print_overview_tables(
        agg_with=agg_with,
        agg_wo=agg_wo,
        merged=merged,
        eps=float(args.eps),
    )

    # summary
    su = merged["speedup_without_over_with"].to_numpy(dtype=float)
    eps = float(args.eps)
    helps = int(np.sum(su > 1.0 + eps))                 # without/with > 1 => with framing faster
    hurts = int(np.sum(su < 1.0 - eps))                 # without/with < 1 => without framing faster
    equal = int(len(su) - helps - hurts)

    print("\n=== syntactic-both: with framing vs without framing (per test, avg over reps) ===")
    print(f"Compared tests (intersection): {len(merged)}")
    if len(merged) > 0:
        print(
            f"Framing helps (with faster): {helps}/{len(merged)} ({helps/len(merged)*100:.1f}%), "
            f"≈equal: {equal}/{len(merged)} ({equal/len(merged)*100:.1f}%), "
            f"framing hurts (without faster): {hurts}/{len(merged)} ({hurts/len(merged)*100:.1f}%). "
            f"(ε={eps:.2f})"
        )
        print(
            f"speedup = (without / with): "
            f"mean={np.nanmean(su):.3f}, median={np.nanmedian(su):.3f}, "
            f"p95={np.nanquantile(su, 0.95):.3f}"
        )

    # write CSV
    out_csv = outdir / "per_test_with_vs_without_framing.csv"
    merged.sort_values("speedup_without_over_with", ascending=False).to_csv(out_csv, index=False)
    print(f"\nWrote per-test comparison CSV to: {out_csv}")

    # plots
    plot_scatter(merged, outdir)
    plot_speedup_histogram(merged, outdir)

    print(f"\nWrote plots to: {outdir.resolve()}")
    print("Key outputs:")
    print(f"  - {out_csv}")
    print(f"  - {outdir / 'scatter_with_vs_without_framing.png'}")
    print(f"  - {outdir / 'scatter_with_vs_without_framing_loglog.png'}")
    print(f"  - {outdir / 'speedup_hist_without_over_with.png'}")


if __name__ == "__main__":
    main()
