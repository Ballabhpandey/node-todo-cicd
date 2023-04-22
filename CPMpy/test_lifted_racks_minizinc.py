from racks_lifted import LiftedRacksExample
from racks_model import RackConfiguration
import cpmpy
from cpmpy.solvers import CPM_minizinc

def test_lifted_racks_one_rack_single_mult1():
    """ tests the lifted problem with the racks example and prints the generated minizinc code"""

    lr = LiftedRacksExample(10,1)
    lr.model += lr.OBJECTTYPE[1] == RackConfiguration.RACKSINGLE
    lr.model += lr.OBJECTTYPE[2] == RackConfiguration.FRAME
    lr.model += lr.OBJECTTYPE[3] == RackConfiguration.FRAME
    lr.model += lr.OBJECTTYPE[4] == RackConfiguration.FRAME
    lr.model += lr.OBJECTTYPE[5] == RackConfiguration.FRAME
    lr.model += lr.OBJECTTYPE[6] == RackConfiguration.ELEMENTA
    lr.model += lr.OBJECTTYPE[7] == RackConfiguration.MODULEI
    lr.model += lr.OBJECTTYPE[8] == RackConfiguration.UNUSED
    lr.model += lr.OBJECTTYPE[9] == RackConfiguration.UNUSED
    lr.model += lr.OBJECTTYPE[10] == RackConfiguration.UNUSED
    #lr.model.solve(solver="minizinc")
    solver: CPM_minizinc = cpmpy.SolverLookup.get("minizinc", lr.model)
    print(solver.mzn_model._code_fragments)
    ret = solver.solve(time_limit=60)
    assert ret == True 
    configuration = lr.build_from_solution()
    print(configuration.info())
    assert len(configuration.get_violated_constraints())==0

