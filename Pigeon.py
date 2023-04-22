""""
    Beware: need to change 'latin-1' by 'utf-8' in z3core.py !!!!!!!!!!!!!!!!!
"""

from latest.perfplot import bench
from utils import (problem,
        monotype1, monotype2, type1, type2,
        l_monotype1, l_monotype2, l_type1, l_type2, TIME_OUT)


f = f"./theories/Pigeon/concrete.idp"
out = bench(
    setup=lambda n: problem(f, n),
    kernels=[
        lambda p: monotype1(f, p, False),
        lambda p: monotype2(f, p, False),
        lambda p: type1(f, p, False),
        lambda p: type2(f, p, False),
        lambda p: l_monotype1(f, p, False),
        lambda p: l_monotype2(f, p, False),
        lambda p: l_type1(f, p, False),
        lambda p: l_type2(f, p, False),
    ],
    labels=["m1", "m2", "t1", "t2",
            "lm1", "lm2", "lt1", "lt2"],
    n_range=[n+1 for n in range(20)],
    xlabel="Pigeons",
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
    title="Pigeonhole"
)
out.show()
out.save("Pigeon.pgf", transparent=True, bbox_inches="tight")

Done = True