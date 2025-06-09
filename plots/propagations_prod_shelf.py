import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
import re

# Read CSV
df = pd.read_csv("results/results_prod_shelf.csv")

# Filter for optimal solutions
df_opt = df.copy()

# Clean file names (remove path and extension)
df_opt["data_file"] = df_opt["data_file"].apply(lambda x: x.split("/")[-1].split(".")[0])

# Filter only relevant configurations
df_filtered = df_opt[df_opt["configuration"].str.startswith("Huub_vsids")]

# Pivot the table
pivot_df = df_filtered.pivot(index="data_file", columns="configuration", values="failures")

# Sort by part2 of the filename
pivot_df = pivot_df.reset_index()
pivot_df[["part1", "part2"]] = pivot_df["data_file"].str.extract(r'ps-(\d{2})-(\d{2})').astype('Int64')
pivot_df = pivot_df.sort_values("part2").drop(columns=["part1", "part2"])
pivot_df = pivot_df.set_index("data_file")

# Rename configuration columns for LaTeX clarity
short_cols = {
    "Huub_vsids_no_gen_bounds": "Combined",
    "Huub_vsids_m+o": "M+O",
    "Huub_vsids_m+s": "M+S",
    "Huub_vsids_s+o": "S+O",
    "Huub_vsids_basic": "Basic",
    "Huub_vsids_decomp": "Decomposition",
}
pivot_df = pivot_df.rename(columns=short_cols)

# Reorder columns based on short_cols order
ordered_cols = list(short_cols.values())
pivot_df = pivot_df[[col for col in ordered_cols if col in pivot_df.columns]]

# Escape underscores for LaTeX
pivot_df.columns = [col.replace("_", r"\_") for col in pivot_df.columns]

# Convert to LaTeX with \small and \resizebox
latex_body = pivot_df.to_latex(
    index=True,
    na_rep="--",
    float_format="%.0f",
    column_format='l' + 'r' * len(pivot_df.columns),
    header=True
)

# Wrap the LaTeX in a table environment
latex_table = r"""
\begin{table}[ht]
\centering
\small
\resizebox{\textwidth}{!}{%
""" + latex_body + r"""}
\caption{Number of failures for Products and Shelves (VSIDS)}
\label{tab:container_objectives}
\end{table}
"""

print(latex_table)

