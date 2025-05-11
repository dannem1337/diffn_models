import pandas as pd
import re
import matplotlib
import matplotlib.pyplot as plt
import numpy as np


import pandas as pd

# Read CSV
# Read CSV
df = pd.read_csv("results_optimized_new/results_container.csv")

# Filter for optimal solutions
df_opt = df[df["status"] == "SATISFIED"].copy()

# Clean file names
df_opt.loc[:, "data_file"] = df_opt["data_file"].apply(lambda x: x.split("/")[-1].split(".")[0])

# Filter only relevant configurations
df_filtered = df_opt[
    df_opt["configuration"].str.startswith("Huub_free") |
    df_opt["configuration"].str.contains(r"(chuffed|gecode|cp[-_]?sat)", flags=re.IGNORECASE, regex=True)
]
# Pivot the table
pivot_df = df_filtered.pivot(index="data_file", columns="configuration", values="objective")

# Sort by numeric part of filename
pivot_df = pivot_df.reset_index()
pivot_df["file_num"] = pivot_df["data_file"].str.extract(r'cl(\d+)').astype(int)
pivot_df = pivot_df.sort_values("file_num").drop(columns="file_num")
pivot_df = pivot_df.set_index("data_file")

# Optional: shorten column names
short_cols = {
    "Huub_free_basic": "basic",
    "Huub_free_decomp": "decomp",
    "Huub_free_diffn": "diffn",
    "Huub_free_m+o": "m+o",
    "Huub_free_m+s": "m+s",
    "Huub_free_no_gen_bounds": "no_bounds",
    "Huub_free_s+o": "s+o"
}
pivot_df = pivot_df.rename(columns=short_cols)

# Escape underscores in headers for LaTeX
pivot_df.columns = [col.replace("_", r"\_") for col in pivot_df.columns]

# Convert to LaTeX with \small and \resizebox
latex_body = pivot_df.to_latex(
    index=True,
    na_rep="--",
    float_format="%.0f",
    column_format='l' + 'r' * len(pivot_df.columns),
    header=True
)

# Wrap the output in a resizebox and small text
latex_table = r"""
\begin{table}[ht]
\centering
\small
\resizebox{\textwidth}{!}{%
""" + latex_body + r"""}
\caption{Objective values per configuration for Container Loading (Free)}
\label{tab:container_objectives}
\end{table}
"""

print(latex_table)


# Filter for optimal solutions
df_opt = df[df["status"] == "SATISFIED"]

# Clean file names
df_opt["data_file"] = df_opt["data_file"].apply(lambda x: x.split("/")[-1].split(".")[0])

# Filter only relevant configurations

# Filter only relevant configurations
df_filtered = df_opt[
    df_opt["configuration"].str.startswith("Huub_vsids") |
    df_opt["configuration"].str.contains(r"(chuffed|gecode|cp[-_]?sat)", flags=re.IGNORECASE, regex=True)
]


# Pivot the table
pivot_df = df_filtered.pivot(index="data_file", columns="configuration", values="objective")




# Sort by numeric part of filename
pivot_df = pivot_df.reset_index()
pivot_df["file_num"] = pivot_df["data_file"].str.extract(r'cl(\d+)').astype(int)
pivot_df = pivot_df.sort_values("file_num").drop(columns="file_num")
pivot_df = pivot_df.set_index("data_file")

# Optional: shorten column names
short_cols = {
    "Huub_free_basic": "basic",
    "Huub_free_decomp": "decomp",
    "Huub_free_diffn": "diffn",
    "Huub_free_m+o": "m+o",
    "Huub_free_m+s": "m+s",
    "Huub_free_no_gen_bounds": "no_bounds",
    "Huub_free_s+o": "s+o"
}
pivot_df = pivot_df.rename(columns=short_cols)

# Escape underscores in headers for LaTeX
pivot_df.columns = [col.replace("_", r"\_") for col in pivot_df.columns]

# Convert to LaTeX with \small and \resizebox
latex_body = pivot_df.to_latex(
    index=True,
    na_rep="--",
    float_format="%.0f",
    column_format='l' + 'r' * len(pivot_df.columns),
    header=True
)

# Wrap the output in a resizebox and small text
latex_table = r"""
\begin{table}[ht]
\centering
\small
\resizebox{\textwidth}{!}{%
""" + latex_body + r"""}
\caption{Objective values per configuration for Container Loading (Free)}
\label{tab:container_objectives}
\end{table}
"""

print(latex_table)

