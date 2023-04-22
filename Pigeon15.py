""""
    Beware: need to change 'latin-1' by 'utf-8' in z3core.py !!!!!!!!!!!!!!!!!
"""

from latest.idp_engine import IDP, Theory, execute
from latest.perfplot import bench
from utils import (get_content, TIME_OUT)

def run(n):
    f = f"./theories/Pigeon15/monotype.idp"
    source = get_content(f)
    kb = IDP.from_str(source.replace("$n$", str(n)))
    kb.execute()

out = bench(
    setup=lambda n: n,
    kernels=[
        lambda p: run(p)
    ],
    labels=["m"],
    n_range=[n+1 for n in range(30, 201, 10)],
    xlabel="Estimate of domain size",
    # More optional arguments with their default values:
    # logx="auto",  # set to True or False to force scaling
    #logy=False,
    equality_check=None, #np.allclose,  # set to None to disable "correctness" assertion
    show_progress=True,
    # target_time_per_measurement=1.0,
    max_time=TIME_OUT,  # maximum time per measurement
    # time_unit="s",  # set to one of ("auto", "s", "ms", "us", or "ns") to force plot units
    # relative_to=1,  # plot the timings relative to one of the measurements
    # flops=lambda n: 3*n,  # FLOPS plots
    # title="Pigeonhole"
)
out.show()
out.save("Pigeon.pgf", transparent=True, bbox_inches="tight")

Done = True