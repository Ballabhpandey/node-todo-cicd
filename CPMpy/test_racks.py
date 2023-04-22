from racks import RacksExample
from racks_model import RackConfiguration

def test_lifted_racks_one_rack_single():

    lr = RacksExample(10)
    lr.model += lr.OBJECTTYPE[1] == RackConfiguration.RACKSINGLE
    lr.model += lr.OBJECTTYPE[2] == RackConfiguration.FRAME
    lr.model += lr.OBJECTTYPE[3] == RackConfiguration.FRAME
    lr.model += lr.OBJECTTYPE[4] == RackConfiguration.FRAME
    lr.model += lr.OBJECTTYPE[5] == RackConfiguration.FRAME
    lr.model += lr.OBJECTTYPE[6] == RackConfiguration.ELEMENTA
    lr.model += lr.OBJECTTYPE[7] == RackConfiguration.MODULEI
    lr.model += lr.OBJECTTYPE[8] == RackConfiguration.UNUSED
    lr.model += lr.OBJECTTYPE[9] == RackConfiguration.UNUSED
    lr.model += lr.OBJECTTYPE[10] ==RackConfiguration.UNUSED
    #test_lifted_racks_one_rack_singlr.solve1()