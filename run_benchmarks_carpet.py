# 1. Create an instance list: mzn-bench collect-instances minizinc-benchmarks > instances.csv
# 2. Run the script: python3 run_benchmark.py
# 3. Collect the statistics: mzn-bench collect-statistics results result.csv
# 4. Summarize and report status: mzn-bench report-status --avg solveTime result.csv
from datetime import timedelta
import pathlib
import minizinc
from mzn_bench import Configuration, schedule

schedule(
    instances= pathlib.Path("./huub_no_gen_bounds/instances_carpet.csv"),
    output_dir=pathlib.Path("./results_carpet_new"),
    timeout=timedelta(minutes=20),
    configurations=[
        # Configuration(name="Huub_free_decomp_new", solver=minizinc.Solver.load(pathlib.Path('./share/minizinc/solvers/huub_decomp_new.msc')), free_search=True ),
        # Configuration(name="Huub_user_decomp_new", solver=minizinc.Solver.load(pathlib.Path('./share/minizinc/solvers/huub_decomp_new.msc')) ),
        # Configuration(name="Huub_free_no_gen_bounds", solver=minizinc.Solver.load(pathlib.Path('./share/minizinc/solvers/huub_no_gen_bounds.msc')), free_search=True ),
        Configuration(name="Huub_user_m+s", solver=minizinc.Solver.load(pathlib.Path('./huub_m+s/share/minizinc/solvers/huub.msc')) ),
        Configuration(name="Huub_user_m+o", solver=minizinc.Solver.load(pathlib.Path('./huub_m+o/share/minizinc/solvers/huub.msc')) ),
        Configuration(name="Huub_user_s+o", solver=minizinc.Solver.load(pathlib.Path('./huub_s+o/share/minizinc/solvers/huub.msc')) ),
        Configuration(name="Huub_user_basic", solver=minizinc.Solver.load(pathlib.Path('./huub_basic/share/minizinc/solvers/huub.msc')) ),
        Configuration(name="Huub_user_no_gen_bounds", solver=minizinc.Solver.load(pathlib.Path('./huub_no_gen_bounds/share/minizinc/solvers/huub.msc')) ),
        # Configuration(name="Huub_user_diffn", solver=minizinc.Solver.load(pathlib.Path('./huub_diffn/share/minizinc/solvers/huub.msc')) ),
        # Configuration(name="Huub_user_decomp", solver=minizinc.Solver.load(pathlib.Path('./huub_decomp/share/minizinc/solvers/huub.msc')) ),
    ],
    nodelist=["critical001"],
    #partition=["comp"],
    cpus_per_task=1,
    memory=16000
)

