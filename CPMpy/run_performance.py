from random import seed, randint
from datetime import datetime
from racks_lifted import LiftedRacksExample
from racks import RacksExample
from racks_model import RackConfiguration

def generate_element_testcase(nrofobjects: int):
    """ generate random element testcase """    
    remaining = nrofobjects
    nrofelementsA = randint(0,remaining)
    remaining = remaining - nrofelementsA
    nrofelementsB = randint(0,remaining)
    remaining = remaining - nrofelementsB
    nrofelementsC = randint(0,remaining)
    remaining = remaining - nrofelementsC
    nrofelementsD = remaining
    return (nrofelementsA,nrofelementsB,nrofelementsC,nrofelementsD)

def run_lifted(A,B,C,D,nrofliftedobjects,mult,time_limit):
    """ run lifted example """
    lr: LiftedRacksExample = LiftedRacksExample(nrofliftedobjects,mult)
    lr.model += lr.OBJECTCOUNT[RackConfiguration.ELEMENTA] == A
    lr.model += lr.OBJECTCOUNT[RackConfiguration.ELEMENTB] == B
    lr.model += lr.OBJECTCOUNT[RackConfiguration.ELEMENTC] == C
    lr.model += lr.OBJECTCOUNT[RackConfiguration.ELEMENTD] == D
    estimated_frames = 4 + (A + B*3 + C*3 + D*4) // 5
    lr.model += (lr.OBJECTCOUNT[RackConfiguration.FRAME] <= estimated_frames)
    if lr.model.solve(time_limit=time_limit):     
        status = lr.model.status()
        lifted_result = True
        lifted_time = status.runtime
        configuration = lr.build_from_solution()
        print(configuration.info())
        cvs = configuration.get_violated_constraints()
        testcase_ok = True
        if len(cvs)>0:
            print(cvs)
            testcase_ok = False
        return (lifted_result,lifted_time,testcase_ok)    
    else:
        return (False,time_limit,True)

def run_nonlifted(A,B,C,D,nrofobjects,time_limit):
    """ run nonlifted example """

    r: RacksExample = RacksExample(nrofobjects)
    r.model += r.OBJECTCOUNT[RackConfiguration.ELEMENTA] == A
    r.model += r.OBJECTCOUNT[RackConfiguration.ELEMENTB] == B
    r.model += r.OBJECTCOUNT[RackConfiguration.ELEMENTC] == C
    r.model += r.OBJECTCOUNT[RackConfiguration.ELEMENTD] == D
    estimated_frames = 4 + (A + B*3 + C*3 + D*4) // 5
    r.model += (r.OBJECTCOUNT[RackConfiguration.FRAME] <= estimated_frames)
    if r.model.solve(time_limit=time_limit):
        status = r.model.status()
        nonlifted_result = True
        nonlifted_time = status.runtime
        configuration = r.build_from_solution()
        print(configuration.info())
        cvs = configuration.get_violated_constraints()
        testcase_ok = True
        if len(cvs)>0:
            print(cvs)
            testcase_ok = False
        return (nonlifted_result,nonlifted_time,testcase_ok)
    else:
        return (False,time_limit,True)

def test_performance_increasing_elements(start,stop,step,time_limit,seed_value=23):
    """ test lifted and non-lifted approach with increasing number of elements 
        for the non-lifted approach the domain size is estimated
        for the lifted it is fixed
    """    
    date = datetime.today()
    seed(seed_value)
    all_testcases_ok = True
    results = []
    
    for nrofelements in range(start,stop+1,step):
        for j in range(2):
            (A,B,C,D) = generate_element_testcase(nrofelements)
            (lifted_result,lifted_time,testcase_ok) = run_lifted(A,B,C,D,12,100,time_limit)
            # for more complicated examples 2x nr of classes
            #(lifted_result,lifted_time,testcase_ok) = run_lifted(A,B,C,D,25,100,time_limit)
            all_testcases_ok &= testcase_ok
            # estimated nrofobjects
            nrofelements = A + B + C + D
            nrofmodules = A + 3*B + 3*C + 4*D
            nrofframes = 8 + nrofmodules // 5
            nrofracks = 1 + nrofframes // 4
            nrofobjects = nrofelements + nrofmodules + nrofframes + nrofracks
            (nonlifted_result,nonlifted_time,testcase_ok) = run_nonlifted(A,B,C,D,nrofobjects,time_limit)
            all_testcases_ok &= testcase_ok
            result = (nrofelements,A,B,C,D,lifted_result,lifted_time,nonlifted_result,nonlifted_time)
            print(result)
            results.append(result)

    date_string = f"{date.year}{date.month:02d}{date.day:02d}{date.second:02d}"
    with open(f"performance_elements_{date_string}_{time_limit}_{seed_value}.csv","w",encoding="utf-8") as test_performance_csv:
        for result in results:
            line = ",".join(map(str,result)) + "\n"
            test_performance_csv.write(line)

    print(f"all testcases ok: {all_testcases_ok}")
    
if __name__=="__main__":
    test_performance_increasing_elements(1,10,1,60)


