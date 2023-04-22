"""
    "lifted" rack example (cpmpy) encoded with Pierre Carbonnelles method
    work in progress
    @author gottfried schenner
"""

import cpmpy
from cpmpy.tools import mus
try:
    from .racks_model import RackConfiguration
except:
    from racks_model import RackConfiguration

class LiftedRacksExample:
    """ lifted version of rack example """

    timelimit = 60

    # max number of lifted objects
    N : int = None
    MAX_MULT = None
    NROFOBJECTS = None
    model = None

    # Rack <-> Frame
    RACK_OF = None
    RACK_FRAME_COUNT = None
    ASSIGNED_TO_RACK = None

    # Frame <-> Module
    FRAME_OF = None
    FRAME_MODULE_COUNT = None
    ASSIGNED_TO_FRAME = None

    # Element <-> Module
    ELEMENT_OF = None
    ELEMENT_MODULE_COUNT = None
    ASSIGNED_TO_ELEMENT = None
    ISAMODULEITOIV = None

    # Special constraints II<->V
    FRAME_MODULEII_COUNT = None
    MODULEII_ASSIGNED_TO_FRAME = None

    FRAME_MODULEV_COUNT = None
    MODULEV_ASSIGNED_TO_FRAME = None

    def __init__(self,maxnrofobjects,maxmult):
        """ initialize model with the given parameters """
        self.model = cpmpy.Model()
        self.N = maxnrofobjects
        self.MAX_MULT = maxmult
        self.build_model()

    def isaRack(self,otype):
        """ is a rack """
        return (otype == RackConfiguration.RACKSINGLE) | (otype == RackConfiguration.RACKDOUBLE)

    def isaModule(self,otype):
        """ is a module """
        return (otype==RackConfiguration.MODULEI) | (otype==RackConfiguration.MODULEII) | (otype==RackConfiguration.MODULEIII) | (otype==RackConfiguration.MODULEIV) | (otype==RackConfiguration.MODULEV)

    def isaModuleItoIV(self,otype):
        """ is a module """
        return (otype==RackConfiguration.MODULEI) | (otype==RackConfiguration.MODULEII) | (otype==RackConfiguration.MODULEIII) | (otype==RackConfiguration.MODULEIV)

    def isaModuleV(self,otype):
        """ is a module """
        return (otype==RackConfiguration.MODULEV)

    def isaElement(self,otype):
        """ is a element """
        return otype==RackConfiguration.ELEMENTA | otype==RackConfiguration.ELEMENTB | otype==RackConfiguration.ELEMENTC | otype==RackConfiguration.ELEMENTD

    def build_model(self):

        self.MAXOBJ = self.N + 1
        MAXTYPES = RackConfiguration.NROFTYPES + 1

        self.NROFOBJECTS = cpmpy.intvar(0,self.N)

        self.OBJECTTYPE = cpmpy.intvar(0,RackConfiguration.NROFTYPES,shape=self.MAXOBJ, name="objecttype")
        self.model += self.OBJECTTYPE[0] == 0

        # nr of objects for every type
        self.OBJECTCOUNT = cpmpy.intvar(0,self.N*self.MAX_MULT,shape=MAXTYPES, name="objectcount")
        self.model += self.OBJECTCOUNT[0] == 0

        self.MULT = cpmpy.intvar(0,self.MAX_MULT,shape=self.MAXOBJ,name="mult")
        self.model += self.MULT[0] == 0

        # objecttype
        for i in range(1,self.MAXOBJ):
            cond = (i <= self.NROFOBJECTS)
            expr = ((self.OBJECTTYPE[i]!=RackConfiguration.UNUSED) & (self.MULT[i]>0))
            self.model += cond.implies(expr)
            cond = (i > self.NROFOBJECTS)
            expr = ((self.OBJECTTYPE[i]==RackConfiguration.UNUSED) & (self.MULT[i]==0))
            self.model += cond.implies(expr)

        # objectcount
        for i in range(1,MAXTYPES):
            count = cpmpy.intvar(0,self.N*self.MAX_MULT,shape=self.MAXOBJ)
            self.model += count[0] == 0
            for j in range(1,self.MAXOBJ):
                cond = self.OBJECTTYPE[j] == i
                self.model += (cond).implies(count[j] == self.MULT[j])
                cond = self.OBJECTTYPE[j] != i
                self.model += (cond).implies(count[j] == 0)
            self.model += self.OBJECTCOUNT[i] == sum(count)


        self.define_rack_frame_association()
        self.define_frame_module_association()
        self.define_element_module_association()

        self.constraint_moduleII_requires_moduleV()

    def define_rack_frame_association(self):
        """ RACK <-> FRAME """

        self.RACK_OF = cpmpy.intvar(0,self.N,shape=self.MAXOBJ, name="rackof")
        self.model += self.RACK_OF[0] == 0

        self.RACK_FRAME_COUNT = cpmpy.intvar(0,self.N*self.MAX_MULT,shape=self.MAXOBJ, name="framecount")
        self.model += self.RACK_FRAME_COUNT[0] == 0

        # FRAME <-> RACK
        for i in range(1,self.MAXOBJ):
            self.model += (self.OBJECTTYPE[i] == RackConfiguration.FRAME).implies(self.RACK_OF[i] > 0)
            self.model += (self.OBJECTTYPE[i] != RackConfiguration.FRAME).implies(self.RACK_OF[i] == 0)

        self.ASSIGNED_TO_RACK = {}
        for i in range(1,self.MAXOBJ):
            self.ASSIGNED_TO_RACK[i] = cpmpy.intvar(0,self.N*self.MAX_MULT,self.MAXOBJ)
            self.model += self.ASSIGNED_TO_RACK[i][0] == 0
            for j in range(1,self.MAXOBJ):
                cond = (self.RACK_OF[j]==i)
                self.model += (cond).implies(self.ASSIGNED_TO_RACK[i][j] == self.MULT[j])
                # MULT[j] must be N * MULT[i]
                #self.model += (cond).implies(self.MULT[i]*cpmpy.intvar(1,self.N*self.MAX_MULT) == self.MULT[j])
                cond = (self.RACK_OF[j]!=i)
                self.model += (cond).implies(self.ASSIGNED_TO_RACK[i][j] == 0)
            self.model += self.RACK_FRAME_COUNT[i]==sum(self.ASSIGNED_TO_RACK[i])

        # type
        for i in range(1,self.MAXOBJ):
            self.model += (self.RACK_OF[i]>0).implies(self.isaRack(self.OBJECTTYPE[self.RACK_OF[i]]))

        # cardinality restrictions for frames
        for i in range(1,self.MAXOBJ):
            self.model += (self.OBJECTTYPE[i]==RackConfiguration.RACKSINGLE).implies(4*self.MULT[i] == self.RACK_FRAME_COUNT[i])

        for i in range(1,self.MAXOBJ):
            self.model += (self.OBJECTTYPE[i]==RackConfiguration.RACKDOUBLE).implies(8*self.MULT[i] == self.RACK_FRAME_COUNT[i])

    def define_frame_module_association(self):
        """ FRAME <-> MODULE """

        self.FRAME_OF = cpmpy.intvar(0,self.N,shape=self.MAXOBJ, name="frameof")
        self.model += self.FRAME_OF[0] == 0

        self.FRAME_MODULE_COUNT = cpmpy.intvar(0,self.N*self.MAX_MULT,shape=self.MAXOBJ, name="framemodulecount")
        self.model += self.FRAME_MODULE_COUNT[0] == 0

        for i in range(1,self.MAXOBJ):
            cond = self.isaModule(self.OBJECTTYPE[i])
            self.model += cond.implies(self.FRAME_OF[i] > 0)
            self.model += (~cond).implies(self.FRAME_OF[i] == 0)

        self.ASSIGNED_TO_FRAME = {}
        for i in range(1,self.MAXOBJ):
            self.ASSIGNED_TO_FRAME[i] = cpmpy.intvar(0,self.N*self.MAX_MULT,self.MAXOBJ)
            self.model += self.ASSIGNED_TO_FRAME[i][0] == 0
            for j in range(1,self.MAXOBJ):
                cond = (self.FRAME_OF[j]==i)
                self.model += (cond).implies(self.ASSIGNED_TO_FRAME[i][j] == self.MULT[j])
                # MULT[j] must be N * MULT[i]
                self.model += (cond).implies(self.MULT[i]*cpmpy.intvar(1,self.N*self.MAX_MULT) == self.MULT[j])
                cond = (self.FRAME_OF[j]!=i)
                self.model += (cond).implies(self.ASSIGNED_TO_FRAME[i][j] == 0)
            self.model += self.FRAME_MODULE_COUNT[i]==sum(self.ASSIGNED_TO_FRAME[i])

        # type
        for i in range(1,self.MAXOBJ):
            self.model += (self.FRAME_OF[i]>0).implies(self.OBJECTTYPE[self.FRAME_OF[i]]==RackConfiguration.FRAME)

        for i in range(1,self.MAXOBJ):
            self.model += (self.OBJECTTYPE[i]==RackConfiguration.FRAME).implies(5*self.MULT[i] >= self.FRAME_MODULE_COUNT[i])

    def define_element_module_association(self):
        """ element <-> MODULE """

        self.ELEMENT_OF = cpmpy.intvar(0,self.N,shape=self.MAXOBJ, name="elementof")
        self.model += self.ELEMENT_OF[0] == 0

        self.ELEMENT_MODULE_COUNT = cpmpy.intvar(0,self.N*self.MAX_MULT,shape=self.MAXOBJ, name="elementmodulecount")
        self.model += self.ELEMENT_MODULE_COUNT[0] == 0

        self.ISAMODULEITOIV = cpmpy.boolvar(self.MAXOBJ)
        for i in range(1,self.MAXOBJ):
            self.model += self.ISAMODULEITOIV[i] == self.isaModuleItoIV(self.OBJECTTYPE[i])
            cond = self.ISAMODULEITOIV[i]
            self.model += cond.implies(self.ELEMENT_OF[i] > 0)
            self.model += (~cond).implies(self.ELEMENT_OF[i] == 0)

        self.ASSIGNED_TO_ELEMENT = {}
        cond = {}
        for i in range(1,self.MAXOBJ):
            self.ASSIGNED_TO_ELEMENT[i] = cpmpy.intvar(0,self.N*self.MAX_MULT,self.MAXOBJ)
            self.model += self.ASSIGNED_TO_ELEMENT[i][0] == 0
            for j in range(1,self.MAXOBJ):
                cond = (self.ELEMENT_OF[j]==i)
                self.model += (cond).implies(self.ASSIGNED_TO_ELEMENT[i][j] == self.MULT[j])
                # MULT[j] must be N * MULT[i]
                self.model += (cond).implies(self.MULT[i]*cpmpy.intvar(1,self.N*self.MAX_MULT) == self.MULT[j])
                cond = (self.ELEMENT_OF[j]!=i)
                self.model += (cond).implies(self.ASSIGNED_TO_ELEMENT[i][j] == 0)
            self.model += self.ELEMENT_MODULE_COUNT[i]==sum(self.ASSIGNED_TO_ELEMENT[i])

        self.element_module_type_constraints()
        self.element_modules_cardinality_constraints()

    def element_module_type_constraints(self):
        # type
        for i in range(1,self.MAXOBJ):
            self.model += (self.OBJECTTYPE[i]==RackConfiguration.MODULEI).implies(self.OBJECTTYPE[self.ELEMENT_OF[i]]==RackConfiguration.ELEMENTA)
            self.model += (self.OBJECTTYPE[i]==RackConfiguration.MODULEII).implies(self.OBJECTTYPE[self.ELEMENT_OF[i]]==RackConfiguration.ELEMENTB)
            self.model += (self.OBJECTTYPE[i]==RackConfiguration.MODULEIII).implies(self.OBJECTTYPE[self.ELEMENT_OF[i]]==RackConfiguration.ELEMENTC)
            self.model += (self.OBJECTTYPE[i]==RackConfiguration.MODULEIV).implies(self.OBJECTTYPE[self.ELEMENT_OF[i]]==RackConfiguration.ELEMENTD)

    def element_modules_cardinality_constraints(self):
        # cardinality restrictions
        for i in range(1,self.MAXOBJ):
            self.model += (self.OBJECTTYPE[i]==RackConfiguration.ELEMENTA).implies(self.MULT[i] == self.ELEMENT_MODULE_COUNT[i])

        for i in range(1,self.MAXOBJ):
            self.model += (self.OBJECTTYPE[i]==RackConfiguration.ELEMENTB).implies(2*self.MULT[i] == self.ELEMENT_MODULE_COUNT[i])

        for i in range(1,self.MAXOBJ):
            self.model += (self.OBJECTTYPE[i]==RackConfiguration.ELEMENTC).implies(3*self.MULT[i] == self.ELEMENT_MODULE_COUNT[i])

        for i in range(1,self.MAXOBJ):
            self.model += (self.OBJECTTYPE[i]==RackConfiguration.ELEMENTD).implies(4*self.MULT[i] == self.ELEMENT_MODULE_COUNT[i])

    def constraint_moduleII_requires_moduleV(self):

        # count number of moduleII for frame
        self.MODULEII_ASSIGNED_TO_FRAME = {}
        self.FRAME_MODULEII_COUNT = cpmpy.intvar(0,self.N*self.MAX_MULT,shape=self.MAXOBJ, name="framemoduleiicount")
        self.model += self.FRAME_MODULEII_COUNT[0] == 0
        for i in range(1,self.MAXOBJ):
            self.MODULEII_ASSIGNED_TO_FRAME[i] = cpmpy.intvar(0,self.N*self.MAX_MULT,self.MAXOBJ)
            self.model += self.MODULEII_ASSIGNED_TO_FRAME[i][0] == 0
            for j in range(1,self.MAXOBJ):
                cond = (self.FRAME_OF[j]==i)&(self.OBJECTTYPE[j]==RackConfiguration.MODULEII)
                self.model += (cond).implies(self.MODULEII_ASSIGNED_TO_FRAME[i][j] == self.MULT[j])
                cond = (self.FRAME_OF[j]!=i)|(self.OBJECTTYPE[j]!=RackConfiguration.MODULEII)
                self.model += (cond).implies(self.MODULEII_ASSIGNED_TO_FRAME[i][j] == 0)
            self.model += self.FRAME_MODULEII_COUNT[i]==sum(self.MODULEII_ASSIGNED_TO_FRAME[i])

        # count number of moduleV for frame
        self.MODULEV_ASSIGNED_TO_FRAME = {}
        self.FRAME_MODULEV_COUNT = cpmpy.intvar(0,self.N*self.MAX_MULT,shape=self.MAXOBJ, name="framemodulevcount")
        self.model += self.FRAME_MODULEV_COUNT[0] == 0
        for i in range(1,self.MAXOBJ):
            self.MODULEV_ASSIGNED_TO_FRAME[i] = cpmpy.intvar(0,self.N*self.MAX_MULT,self.MAXOBJ)
            self.model += self.MODULEV_ASSIGNED_TO_FRAME[i][0] == 0
            for j in range(1,self.MAXOBJ):
                cond = (self.FRAME_OF[j]==i)&(self.OBJECTTYPE[j]==RackConfiguration.MODULEV)
                self.model += (cond).implies(self.MODULEV_ASSIGNED_TO_FRAME[i][j] == self.MULT[j])
                cond = (self.FRAME_OF[j]!=i)|(self.OBJECTTYPE[j]!=RackConfiguration.MODULEV)
                self.model += (cond).implies(self.MODULEV_ASSIGNED_TO_FRAME[i][j] == 0)
            self.model += self.FRAME_MODULEV_COUNT[i]==sum(self.MODULEV_ASSIGNED_TO_FRAME[i])

        # moduleII requires moduleV
        for i in range(1,self.MAXOBJ):
            self.model += (self.FRAME_MODULEII_COUNT[i]>0)==(self.FRAME_MODULEV_COUNT[i]>0)

    def build_from_solution(self):

        configuration = RackConfiguration()
        objecttypes = self.OBJECTTYPE.value()
        mult = self.MULT.value()
        for i in range(1,self.N+1):
            configuration.create_object(i,mult[i],objecttypes[i])

        rackof = self.RACK_OF.value()
        for i in range(1,self.N+1):
            rackid = rackof[i]
            if rackid!=0:
                frame = configuration.object_dict[i]
                rack = configuration.object_dict[rackid]
                rack.frames.append(frame)
                frame.rack = rack

        frameof = self.FRAME_OF.value()
        for i in range(1,self.N+1):
            frameid = frameof[i]
            if frameid!=0:
                module = configuration.object_dict[i]
                frame = configuration.object_dict[frameid]
                frame.modules.append(module)
                module.frame = frame

        elementof = self.ELEMENT_OF.value()
        for i in range(1,self.N+1):
            elementid = elementof[i]
            if elementid!=0:
                module = configuration.object_dict[i]
                element = configuration.object_dict[elementid]
                element.modules.append(module)
                module.element = element

        return configuration

    def solve(self):
        """ solve model """
        if self.model.solve(time_limit=self.timelimit):
            print(self.model.status())
            print("solved")
            return True
        else:
            print(self.model.status())
            print("no solution")
            # print(mus(self.model.constraints))
            return False

    def print_csp_solution(self):
        objectcounts = self.OBJECTCOUNT.value()
        counts = [ RackConfiguration.TYPE_NAMES[i] + "_" + str(objectcounts[i]) for i in range(1,len(RackConfiguration.TYPE_NAMES)) ]
        print(f"counts={ counts }")
        #print(f"objectcount {self.OBJECTCOUNT.value()}")
        print(f"objecttype {[ RackConfiguration.TYPE_NAMES[i] for i in self.OBJECTTYPE.value()]}")
        print(f"rack_of {self.RACK_OF.value()}")
        print(f"rack_frame_count {self.RACK_FRAME_COUNT.value()}")
        print(f"frame_of {self.FRAME_OF.value()}")
        print(f"frame_module_count {self.FRAME_MODULE_COUNT.value()}")
        print(f"frame_moduleII_count {self.FRAME_MODULEII_COUNT.value()}")
        print(f"frame_moduleV_count {self.FRAME_MODULEV_COUNT.value()}")

        print(f"element_of {self.ELEMENT_OF.value()}")
        print(f"element_module_count {self.ELEMENT_MODULE_COUNT.value()}")
        print(f"isamoduleitoiv {self.ISAMODULEITOIV.value()}")

        print(f"mult {self.MULT.value()}")
        for i in range(1,self.N+1):
            print(f"assigned to rack {i} {self.ASSIGNED_TO_RACK[i].value()}")
        for i in range(1,self.N+1):
            print(f"assigned to frame {i} {self.ASSIGNED_TO_FRAME[i].value()}")
        for i in range(1,self.N+1):
            print(f"moduleII assigned to frame {i} {self.MODULEII_ASSIGNED_TO_FRAME[i].value()}")
        for i in range(1,self.N+1):
            print(f"moduleV assigned to frame {i} {self.MODULEV_ASSIGNED_TO_FRAME[i].value()}")

        for i in range(1,self.N+1):
            print(f"assigned to element {i} {self.ASSIGNED_TO_ELEMENT[i].value()}")

    def solve_and_get_configuration(self):
        if (self.solve()):
            configuration = self.build_from_solution()
            return configuration
        else:
            return None

    def solve_and_print_solution(self):
        configuration = self.solve_and_get_configuration()
        if configuration is not None:
            self.print_csp_solution()
            print(configuration.info())
            cvs = configuration.get_violated_constraints()
            if (len(cvs)>0):
                print("Violated constraints {cvs}")
        else:
            print("No solution found")

    def solve_and_show_solution(self):
        configuration = self.solve_and_get_configuration()
        if configuration is not None:
            print(configuration.info())
            cvs = configuration.get_violated_constraints()
            if (len(cvs)>0):
                print("Violated constraints {cvs}")
            dot = configuration.dot()
            return dot
        else:
            print("No solution found")

    @staticmethod
    def testcase_one_rack_single():
        lr = LiftedRacksExample(10,1)
        lr.model += lr.OBJECTTYPE[1] == RackConfiguration.RACKSINGLE
        lr.model += lr.OBJECTTYPE[2] == RackConfiguration.FRAME
        lr.model += lr.OBJECTTYPE[3] == RackConfiguration.ELEMENTA
        lr.model += lr.MULT[3] == 1
        lr.model += lr.OBJECTTYPE[4] == RackConfiguration.MODULEI
        lr.model += lr.OBJECTTYPE[5] == RackConfiguration.FRAME
        lr.solve_and_print_solution()

    @staticmethod
    def testcase_two_rack_double():
        lr = LiftedRacksExample(4,6)
        lr.model += lr.OBJECTTYPE[1] == RackConfiguration.RACKDOUBLE
        lr.model += lr.MULT[1] == 2
        lr.solve_and_print_solution()

    @staticmethod
    def testcase_21elementA_open():
        lr = LiftedRacksExample(20,5)
        lr.model += lr.OBJECTTYPE[1] == RackConfiguration.RACKSINGLE
        lr.model += lr.MULT[1] == 1
        lr.model += lr.OBJECTTYPE[2] == RackConfiguration.ELEMENTA
        lr.model += lr.MULT[2] == 5
        lr.model += lr.OBJECTTYPE[3] == RackConfiguration.ELEMENTA
        lr.model += lr.MULT[3] == 5
        lr.model += lr.OBJECTTYPE[4] == RackConfiguration.ELEMENTA
        lr.model += lr.MULT[4] == 5
        lr.model += lr.OBJECTTYPE[5] == RackConfiguration.ELEMENTA
        lr.model += lr.MULT[5] == 5
        lr.model += lr.OBJECTTYPE[6] == RackConfiguration.ELEMENTA
        lr.model += lr.MULT[6] == 1

        lr.solve_and_print_solution()

    @staticmethod
    def testcase_21elementA_closed():
        lr = LiftedRacksExample(9,20)
        lr.model += lr.OBJECTTYPE[1] == RackConfiguration.RACKSINGLE
        lr.model += lr.MULT[1] == 1
        lr.model += lr.OBJECTTYPE[2] == RackConfiguration.ELEMENTA
        lr.model += lr.MULT[2] == 5
        lr.model += lr.OBJECTTYPE[3] == RackConfiguration.ELEMENTA
        lr.model += lr.MULT[3] == 5
        lr.model += lr.OBJECTTYPE[4] == RackConfiguration.ELEMENTA
        lr.model += lr.MULT[4] == 5
        lr.model += lr.OBJECTTYPE[5] == RackConfiguration.ELEMENTA
        lr.model += lr.MULT[5] == 5
        lr.model += lr.OBJECTTYPE[6] == RackConfiguration.ELEMENTA
        lr.model += lr.MULT[6] == 1
        lr.model += lr.OBJECTTYPE[1] == RackConfiguration.RACKSINGLE
        lr.model += lr.MULT[1] == 1

        # closed world
        lr.model += lr.OBJECTCOUNT[RackConfiguration.ELEMENTA] == 21
        # no rackdouble
        lr.model += lr.OBJECTCOUNT[RackConfiguration.RACKDOUBLE] == 0

        lr.solve_and_print_solution()

    @staticmethod
    def testcase_21elementA_var2_closed():
        lr = LiftedRacksExample(4,100)
        lr.model += lr.OBJECTTYPE[1] == RackConfiguration.ELEMENTA
        lr.model += lr.MULT[1] == 20
        #lr.model += lr.OBJECTTYPE[2] == RackConfiguration.ELEMENTA
        #lr.model += lr.MULT[2] == 1

        # 2 racksingle
        lr.model += lr.OBJECTCOUNT[RackConfiguration.ELEMENTA] == 20
        lr.model += lr.OBJECTCOUNT[RackConfiguration.RACKDOUBLE] == 0
        lr.model += lr.OBJECTCOUNT[RackConfiguration.RACKSINGLE] == 1

        lr.solve_and_print_solution()



