import pandas as pd
import matplotlib.pyplot as plt

# Load CSV files
normal_df = pd.read_csv("result_container.csv")
basic_df = pd.read_csv("result_container_basic.csv")
merge_df = pd.read_csv("result_container_merge.csv")
seperate_df = pd.read_csv("result_container_seperate+merge.csv")

normal_df = normal_df[normal_df["configuration"] == "Huub_vsids"].copy()
basic_df = basic_df[basic_df["configuration"] == "Huub_vsids"].copy()
merge_df = merge_df[merge_df["configuration"] == "Huub_vsids"].copy()
seperate_df = seperate_df[seperate_df["configuration"] == "Huub_vsids"].copy()

# Add a prefix to configuration names to distinguish them
basic_df["configuration"] = "basic_" + basic_df["configuration"].astype(str)
merge_df["configuration"] = "merge_" + merge_df["configuration"].astype(str)
seperate_df["configuration"] = "seperate_" + seperate_df["configuration"].astype(str)

# Combine the dataframes
combined_df = pd.concat([normal_df, basic_df, merge_df, seperate_df])

# Clean the data_file column to just the filename (e.g., 'cl01')
combined_df["data_file"] = combined_df["data_file"].apply(
    lambda x: x.split("/")[-1].split(".")[0]
)

# Sort by the numeric part of the data_file name
combined_df["file_num"] = combined_df["data_file"].str.extract(r'cl(\d+)').astype(int)
combined_df = combined_df.sort_values("file_num")
combined_df = combined_df.drop(columns="file_num")

# Create the plot
plt.figure(figsize=(12, 6))

# Loop through each unique configuration and plot
for config in combined_df["configuration"].unique():
    df_subset = combined_df[combined_df["configuration"] == config]
    plt.plot(df_subset["data_file"], df_subset["objective"], marker='o', label=config)

# Formatting
plt.xlabel("Data File")
plt.ylabel("Objective")
plt.title("Objective Value per Data File per Configuration")
plt.xticks(rotation=45)
plt.legend()
plt.tight_layout()
plt.grid(True)

# Show the plot
plt.savefig("vsids_plot.png", dpi=300)
