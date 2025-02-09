# 1. Create an instance list: mzn-bench collect-instances minizinc-benchmarks > instances.csv
# 2. Run the script: python3 run_benchmark.py 
# 3. Collect the statistics: mzn-bench collect-statistics results result.csv 
# 4. Summarize and report status: mzn-bench report-status --avg solveTime result.csv 
from datetime import timedelta
import pathlib 
import minizinc
from mzn_bench import Configuration, schedule

schedule(
    instances= pathlib.Path("./instances.csv"), 
    output_dir=pathlib.Path("./results/"), 
    timeout=timedelta(minutes=20),
    configurations=[
        # Configuration(name="Huub_vsids", solver=minizinc.Solver.load(pathlib.Path("./share/minizinc/solvers/huub.msc")), other_flags={"--vsids-only": True} ),
        # Configuration(name="Huub_free", solver=minizinc.Solver.lookup("huub"), free_search=True ),
        Configuration(name="chuffed", solver=minizinc.Solver.lookup("chuffed")),
        Configuration(name="Huub_user", solver=minizinc.Solver.load(pathlib.Path('./share/minizinc/solvers/huub.msc')) ),
        Configuration(name="gecode", solver=minizinc.Solver.lookup("gecode")),
    ],
    nodelist=["critical001"],
    #partition=["comp"],
    cpus_per_task=1, 
    memory=16000
)

