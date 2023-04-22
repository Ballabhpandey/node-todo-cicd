
import glob
import re
from subprocess import check_output
from timeit import timeit

from utils import (problem, get_content, run,
        monotype1, monotype2, type1, type2,
        l_monotype1, l_monotype2, l_type1, l_type2, TIME_OUT)


out = ""
for f in sorted(glob.glob(f"./theories/*/concrete.idp")):
    if ("Pigeon" not in f
    and "CADE" not in f
    and 'BAPA' not in f):
        print(f)
        kernels=[
            lambda : l_monotype1(f, problem(f, "")),
            lambda : l_monotype2(f, problem(f, "")),
            lambda : l_type1(f, problem(f, "")),
            lambda : l_type2(f, problem(f, "")),
            lambda : "~",
            lambda : monotype1(f, problem(f, "")),
            lambda : monotype2(f, problem(f, "")),
            lambda : type1(f, problem(f, "")),
            lambda : type2(f, problem(f, "")),
            lambda : "~",
        ]
        times = []
        for k in kernels:
            time = f"{k()}"
            print(time)
            times.append(time)

        minT = min(float(t) if "T" not in t and "~" not in t else 99999 for t in times)

        out += (f'\{f[11:-13].replace("_", "")} & '
                + " & ".join(t if "T" in t or "~" in t or float(t) != minT else f"\\textbf{{{minT}}}" for t in times)
                # + f" & {expansion}"
                +" \\\\ \n")
        print(out)

Done = True