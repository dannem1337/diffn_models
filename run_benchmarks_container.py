# 1. Create an instance list: mzn-bench collect-instances minizinc-benchmarks > instances.csv
# 2. Run the script: python3 run_benchmark.py
# 3. Collect the statistics: mzn-bench collect-statistics results result.csv
# 4. Summarize and report status: mzn-bench report-status --avg solveTime result.csv
from datetime import timedelta
import pathlib
import minizinc
from mzn_bench import Configuration, schedule

schedule(
    instances= pathlib.Path("./huub_no_gen_bounds/instances_container.csv"),
    output_dir=pathlib.Path("./results_optimized_new/results_container"),
    timeout=timedelta(minutes=20),
    configurations=[
        Configuration(name="Huub_vsids_basic", solver=minizinc.Solver.load(pathlib.Path('./huub_basic/share/minizinc/solvers/huub.msc')), other_flags={"--vsids-only": True, "--restart": True}),
        Configuration(name="Huub_free_basic", solver=minizinc.Solver.load(pathlib.Path('./huub_basic/share/minizinc/solvers/huub.msc')), free_search=True ),
        Configuration(name="Huub_vsids_no_gen_bounds", solver=minizinc.Solver.load(pathlib.Path('./huub_no_gen_bounds/share/minizinc/solvers/huub.msc')), other_flags={"--vsids-only": True, "--restart": True}),
        Configuration(name="Huub_free_no_gen_bounds", solver=minizinc.Solver.load(pathlib.Path('./share/minizinc/solvers/huub_no_gen_bounds.msc')), free_search=True ),
        Configuration(name="Huub_vsids_m+s", solver=minizinc.Solver.load(pathlib.Path('./huub_m+s/share/minizinc/solvers/huub.msc')), other_flags={"--vsids-only": True, "--restart": True}),
        Configuration(name="Huub_free_m+s", solver=minizinc.Solver.load(pathlib.Path('./huub_m+s/share/minizinc/solvers/huub.msc')), free_search=True ),
        Configuration(name="Huub_vsids_m+o", solver=minizinc.Solver.load(pathlib.Path('./huub_m+o/share/minizinc/solvers/huub.msc')), other_flags={"--vsids-only": True, "--restart": True}),
        Configuration(name="Huub_free_m+o", solver=minizinc.Solver.load(pathlib.Path('./huub_m+o/share/minizinc/solvers/huub.msc')), free_search=True ),
        Configuration(name="Huub_vsids_s+o", solver=minizinc.Solver.load(pathlib.Path('./huub_s+o/share/minizinc/solvers/huub.msc')), other_flags={"--vsids-only": True, "--restart": True}),
        Configuration(name="Huub_free_s+o", solver=minizinc.Solver.load(pathlib.Path('./huub_s+o/share/minizinc/solvers/huub.msc')), free_search=True ),
        Configuration(name="Huub_vsids_basic", solver=minizinc.Solver.load(pathlib.Path('./huub_basic/share/minizinc/solvers/huub.msc')), other_flags={"--vsids-only": True, "--restart": True}),
        Configuration(name="Huub_free_basic", solver=minizinc.Solver.load(pathlib.Path('./huub_basic/share/minizinc/solvers/huub.msc')), free_search=True),
        Configuration(name="Huub_vsids_decomp", solver=minizinc.Solver.load(pathlib.Path('./huub_decomp/share/minizinc/solvers/huub.msc')), other_flags={"--vsids-only": True, "--restart": True} ),
        Configuration(name="Huub_free_decomp", solver=minizinc.Solver.load(pathlib.Path('./huub_decomp/share/minizinc/solvers/huub.msc')), free_search=True ),
    ],
    nodelist=["critical001"],
    #partition=["comp"],
    cpus_per_task=1,
    memory=16000
)

