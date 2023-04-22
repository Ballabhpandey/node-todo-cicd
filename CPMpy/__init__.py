import cpmpy
from cpmpy.solvers import CPM_minizinc
from cpmpy.tools import mus
import time

from .racks import RacksExample
from .racks_lifted import LiftedRacksExample
from .racks_model import RackConfiguration


start_time = time.time()

A = 0
B = 0
C = 2
D = 0


### lifted

n, Done = 1, False
while not Done and time.time() - start_time < 120:

    lr: LiftedRacksExample = LiftedRacksExample(n,100)
    lr.model += lr.OBJECTCOUNT[RackConfiguration.ELEMENTA] == A
    lr.model += lr.OBJECTCOUNT[RackConfiguration.ELEMENTB] == B
    lr.model += lr.OBJECTCOUNT[RackConfiguration.ELEMENTC] == C
    lr.model += lr.OBJECTCOUNT[RackConfiguration.ELEMENTD] == D
    solver = lr
    # slower: solver: CPM_minizinc = cpmpy.SolverLookup.get("minizinc", lr.model)
    if solver.solve():
        configuration = lr.build_from_solution()
        print(configuration.info())
        Done = True
    else:
        print("unsatisfiable")
        # print(mus(lr.model.constraints))
        n += 1

lifted = round(time.time()-start_time, 3)
lifted_n = n
print(f"\n> Executed in {lifted} ({lifted_n}) sec")

### concrete

start_time = time.time()
n, Done = 1, False
while not Done and time.time() - start_time < 120:

    print(n)
    lr: RacksExample = RacksExample(n)
    lr.model += lr.OBJECTCOUNT[RackConfiguration.ELEMENTA] == A
    lr.model += lr.OBJECTCOUNT[RackConfiguration.ELEMENTB] == B
    lr.model += lr.OBJECTCOUNT[RackConfiguration.ELEMENTC] == C
    lr.model += lr.OBJECTCOUNT[RackConfiguration.ELEMENTD] == D
    solver = lr
    # slower: solver: CPM_minizinc = cpmpy.SolverLookup.get("minizinc", lr.model)
    if solver.solve():
        configuration = lr.build_from_solution()
        print(configuration.info())
        Done = True
    else:
        n += 1

concrete = round(time.time()-start_time, 3)



print(f"\n> Executed in {lifted} ({lifted_n}) and {concrete} ({n}) sec")

Done = True