import pandas as pd
import matplotlib
import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator
import numpy as np


matplotlib.use('pgf')
# Provided CSV data
# data = "results_optimized/results_rect_free.csv"
data = "results/results_rect.csv"

# Read CSV into DataFrame
df = pd.read_csv(data)


# Filter for only rows with OPTIMAL_SOLUTION
# df_opt = df[(df["status"] == "OPTIMAL_SOLUTION")]
df_opt = df[(df["status"] == "SATISFIED") | (df["status"] == "ALL_SOLUTIONS")]
# df_opt = df[(df["status"] == "OPTIMAL_SOLUTION") | (df["status"] == "SATISFIED")]

# Create cactus plot comparing configurations
plt.figure(figsize=(10, 6))

name_mapping = {
    "Huub_user_no_gen_bounds": "Combined",
    "Huub_user_m+o": "M+O",
    "Huub_user_m+s": "M+S",
    "Huub_user_s+o": "S+O",
    "Huub_user_basic": "Basic",
    "Huub_user_decomp": "Decomposition",
    "chuffed": "Chuffed",
    "gecode": "Gecode",
    "cp-sat": "CP-SAT"
}

color_mapping = {
    "Huub_user_no_gen_bounds": "#2ca02c",   # green
    "Huub_user_m+o": "#bcbd22",             # yellow-green
    "Huub_user_m+s": "#17becf",             # teal
    "Huub_user_s+o": "#e377c2",             # pink (replaces gray)
    "Huub_user_basic": "#9467bd",           # purple
    "Huub_user_decomp": "#8c564b",          # brown

    "Huub_free_no_gen_bounds": "#2ca02c",   # green
    "Huub_free_m+o": "#bcbd22",             # yellow-green
    "Huub_free_m+s": "#17becf",             # teal
    "Huub_free_s+o": "#e377c2",             # pink (replaces gray)
    "Huub_free_basic": "#9467bd",           # purple
    "Huub_free_decomp": "#8c564b",          # brown

    "Huub_vsids_no_gen_bounds": "#2ca02c",   # green
    "Huub_vsids_m+o": "#bcbd22",             # yellow-green
    "Huub_vsids_m+s": "#17becf",             # teal
    "Huub_vsids_s+o": "#e377c2",             # pink (replaces gray)
    "Huub_vsids_basic": "#9467bd",           # purple
    "Huub_vsids_decomp": "#8c564b",          # brown

    "chuffed": "#d62728",                    # red
    "gecode":  "#1f77b4",                    # blue
    "cp-sat":  "#ff7f0e"                     # orange
}

# Define the plotting order
custom_order = list(name_mapping.keys())

# Filter and plot
df_filtered = df_opt[df_opt["configuration"].isin(custom_order)]

for config in custom_order:
    group = df_filtered[df_filtered["configuration"] == config]
    if not group.empty:
        times = np.sort(group["solveTime"].astype(float))
        y_vals = np.arange(1, len(times) + 1)

        # Build real data with markers
        real_times = times
        real_y = y_vals

        # Start at time 0, y = 0
        extension_start_x = [0, real_times[0]]
        extension_start_y = [0, real_y[0]]

        # End at time 1200, y = last value (if needed)
        extension_end_x = [real_times[-1], 1200]
        extension_end_y = [real_y[-1], real_y[-1]]

        # Plot extension at start (no marker)
        plt.plot(
            extension_start_x,
            extension_start_y,
            drawstyle='steps-post',
            color=color_mapping[config],
            linewidth=1.5,
            linestyle='-',
            marker=None
        )

        # Now plot the real data (with markers)
        line = plt.plot(
            real_times,
            real_y,
            drawstyle='steps-post',
            color=color_mapping[config],
            label=name_mapping[config],
            marker='x',
            markersize=5,
            linewidth=1.5,
        )[0]

        # Use same color as real data for extension end
        plt.plot(
            extension_end_x,
            extension_end_y,
            drawstyle='steps-post',
            color=color_mapping[config],
            linewidth=1.5,
            linestyle='-',
            marker=None
        )

plt.xscale('log')  # <-- log scale on x-axis
plt.xlabel("Time (seconds)", fontsize=14)
plt.ylabel("Solved instances", fontsize=14)
plt.title("Rectangle Packing (User Search)", fontsize=14)
plt.legend(title="Configuration")
plt.gca().yaxis.set_major_locator(MaxNLocator(integer=True))  # Force integer ticks
plt.grid(True)
plt.tight_layout()
plt.xlim(right=1200)
plt.savefig("images/cactus_rect_user_optimized_all.pgf")
