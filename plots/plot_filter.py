import pandas as pd
import matplotlib
import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator
import numpy as np

# matplotlib.use('pgf')

# matplotlib.use('pgf')
# Provided CSV data
# data = "results_filter.csv"
# data = "results_optimized/results_filter_free.csv"
data = "results_optimized_new/results_filter.csv"

# Read CSV into DataFrame
df = pd.read_csv(data)


# Filter for only rows with OPTIMAL_SOLUTION
df_opt = df[(df["status"] == "OPTIMAL_SOLUTION")]
# df_opt = df[(df["status"] == "SATISFIED") | (df["status"] == "ALL_SOLUTIONS")]
# df_opt = df[(df["status"] == "OPTIMAL_SOLUTION") | (df["status"] == "SATISFIED")]

# Create cactus plot comparing configurations
plt.figure(figsize=(10, 6))

for config, group in df_opt[df_opt["configuration"].str.match(r"Huub_user.*|chuffed|gecode|cp-sat")].groupby("configuration"):
    times = np.sort(group["time"].astype(float))
    y_vals = np.arange(1, len(times) + 1)
    # plt.step(times, y_vals, where='post', marker='x', label=config)
    plt.plot(times, y_vals, marker='x', linestyle='-', label=config)

plt.xlabel("Time (seconds)")
plt.ylabel("Solved instances")
plt.title("Filters (User Search)")
plt.legend(title="Configuration")
plt.gca().yaxis.set_major_locator(MaxNLocator(integer=True))  # Force integer ticks
plt.grid(True)
plt.tight_layout()
#plt.savefig("cactus_filter.pgf", format='pgf')
plt.savefig("images/cactus_filter_user_optimized.png")

# matplotlib.use('pgf')

# matplotlib.use('pgf')
# Provided CSV data
# data = "results_filter.csv"
# data = "results_optimized/results_filter_free.csv"

# Read CSV into DataFrame
df = pd.read_csv(data)


# Filter for only rows with OPTIMAL_SOLUTION
df_opt = df[(df["status"] == "OPTIMAL_SOLUTION")]
# df_opt = df[(df["status"] == "SATISFIED") | (df["status"] == "ALL_SOLUTIONS")]
# df_opt = df[(df["status"] == "OPTIMAL_SOLUTION") | (df["status"] == "SATISFIED")]

# Create cactus plot comparing configurations
plt.figure(figsize=(10, 6))

for config, group in df_opt[df_opt["configuration"].str.match(r"Huub_free.*|chuffed|gecode|cp-sat")].groupby("configuration"):
    times = np.sort(group["time"].astype(float))
    y_vals = np.arange(1, len(times) + 1)
    # plt.step(times, y_vals, where='post', marker='x', label=config)
    plt.plot(times, y_vals, marker='x', linestyle='-', label=config)

plt.xlabel("Time (seconds)")
plt.ylabel("Solved instances")
plt.title("Filters (Free Search)")
plt.legend(title="Configuration")
plt.gca().yaxis.set_major_locator(MaxNLocator(integer=True))  # Force integer ticks
plt.grid(True)
plt.tight_layout()
#plt.savefig("cactus_filter.pgf", format='pgf')
plt.savefig("images/cactus_filter_free_optimized.png")

# Read CSV into DataFrame
df = pd.read_csv(data)


# Filter for only rows with OPTIMAL_SOLUTION
df_opt = df[(df["status"] == "OPTIMAL_SOLUTION")]
# df_opt = df[(df["status"] == "SATISFIED") | (df["status"] == "ALL_SOLUTIONS")]
# df_opt = df[(df["status"] == "OPTIMAL_SOLUTION") | (df["status"] == "SATISFIED")]

# Create cactus plot comparing configurations
plt.figure(figsize=(10, 6))

for config, group in df_opt[df_opt["configuration"].str.match(r"Huub_vsids.*|chuffed|gecode|cp-sat")].groupby("configuration"):
    times = np.sort(group["time"].astype(float))
    y_vals = np.arange(1, len(times) + 1)
    # plt.step(times, y_vals, where='post', marker='x', label=config)
    plt.plot(times, y_vals, marker='x', linestyle='-', label=config)

plt.xlabel("Time (seconds)")
plt.ylabel("Solved instances")
plt.title("Filters (Free Search)")
plt.legend(title="Configuration")
plt.gca().yaxis.set_major_locator(MaxNLocator(integer=True))  # Force integer ticks
plt.grid(True)
plt.tight_layout()
#plt.savefig("cactus_filter.pgf", format='pgf')
plt.savefig("images/cactus_filter_vsids_optimized.png")
