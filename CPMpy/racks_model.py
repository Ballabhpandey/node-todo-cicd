from graphviz import Digraph
class RackConfiguration:

        # type constants
    UNUSED = 0
    RACKSINGLE = 1
    RACKDOUBLE = 2
    FRAME = 3
    MODULEI = 4
    MODULEII = 5
    MODULEIII = 6
    MODULEIV = 7
    MODULEV = 8
    ELEMENTA = 9
    ELEMENTB = 10
    ELEMENTC = 11
    ELEMENTD = 12
    NROFTYPES = 12

    # constants
    TYPE_NAMES = [ 
        "UNUSED",
        "RACKSINGLE",
        "RACKDOUBLE",
        "FRAME",
        "MODULEI",
        "MODULEII",
        "MODULEIII",
        "MODULEIV",
        "MODULEV",
        "ELEMENTA",
        "ELEMENTB",
        "ELEMENTC",
        "ELEMENTD"]

    object_dict = None

    def __init__(self):
        self.object_dict = {}

    def create_object(self,obj_id,mult,objecttype):
        if objecttype == RackConfiguration.RACKSINGLE:
            self.object_dict[obj_id] = RackSingle(obj_id,mult)
        elif objecttype == RackConfiguration.RACKDOUBLE:
            self.object_dict[obj_id] = RackDouble(obj_id,mult)
        elif objecttype == RackConfiguration.FRAME:
            self.object_dict[obj_id] = Frame(obj_id,mult)            
        elif objecttype == RackConfiguration.ELEMENTA:
            self.object_dict[obj_id] = ElementA(obj_id,mult)
        elif objecttype == RackConfiguration.ELEMENTB:
            self.object_dict[obj_id] = ElementB(obj_id,mult)
        elif objecttype == RackConfiguration.ELEMENTC:
            self.object_dict[obj_id] = ElementC(obj_id,mult)
        elif objecttype == RackConfiguration.ELEMENTD:
            self.object_dict[obj_id] = ElementD(obj_id,mult)
        elif objecttype == RackConfiguration.MODULEI:
            self.object_dict[obj_id] = ModuleI(obj_id,mult)
        elif objecttype == RackConfiguration.MODULEII:
            self.object_dict[obj_id] = ModuleII(obj_id,mult)
        elif objecttype == RackConfiguration.MODULEIII:
            self.object_dict[obj_id] = ModuleIII(obj_id,mult)
        elif objecttype == RackConfiguration.MODULEIV:
            self.object_dict[obj_id] = ModuleIV(obj_id,mult)
        elif objecttype == RackConfiguration.MODULEV:
            self.object_dict[obj_id] = ModuleV(obj_id,mult)
        elif objecttype == RackConfiguration.UNUSED:
            return None
        else:
            raise Exception(f"unknown type {objecttype}")
        return self.object_dict[obj_id]
    
    def get_violated_constraints(self):
        result = []
        for obj in self.object_dict.values():
            result.extend(obj.get_violated_constraints())
        return result

    def info(self):
        result = ""
        for rack in self.object_dict.values():
            if isinstance(rack,Rack):
                result += rack.info() + "\n"
        return result
    
    def dot(self):
        d = Digraph()

        for obj in self.object_dict.values():
            d.node(str(obj))
            if isinstance(obj,Rack):
                for frame in obj.frames:
                    d.edge(str(obj),str(frame))
            if isinstance(obj,Frame):
                for module in obj.modules:
                    d.edge(str(obj),str(module))
            if isinstance(obj,Element):
                for module in obj.modules:
                    d.edge(str(obj),str(module))    
        return d

class LiftedObject:
    id = None    
    mult = 0

    def __init__(self,id,mult):
        self.id = id
        self.mult = mult

    def __str__(self):
        result = f"{type(self).__name__}({self.id,self.mult}) "
        return result

    def info(self):
        return str(self)

class Rack(LiftedObject):
    frames = None

    def __init__(self,id,mult):
        super().__init__(id,mult)
        self.frames = []

    def info(self):
        result = str(self)
        frame_strings = ", ".join([ f.info() for f in self.frames])
        result += f"[{frame_strings} ]"
        return result

class RackSingle(Rack):    
     def get_violated_constraints(self):
        result = []
        nrofframes = sum([ f.mult for f in self.frames])
        if self.mult*4 != nrofframes:
            result.append((self,"nrofframes != 4"))
        return result

class RackDouble(Rack):
     def get_violated_constraints(self):
        result = []
        nrofframes = sum([ f.mult for f in self.frames])
        if self.mult*8 != nrofframes:
            result.append((self,"nrofframes != 8"))
        return result

class Element(LiftedObject):
    modules = None

    def __init__(self,id,mult):
        super().__init__(id,mult)
        self.modules = []

class ElementA(Element):

    def get_violated_constraints(self):
        result = []
        nrofmodules = sum([ m.mult for m in self.modules])
        if self.mult != nrofmodules:
            result.append((self,"elementA nrofmodules != 1"))
        return result

class ElementB(Element):
    def get_violated_constraints(self):
        result = []
        nrofmodules = sum([ m.mult for m in self.modules])
        if self.mult*2 != nrofmodules:
            result.append((str(self),"elementB nrofmodules != 2"))
        return result

class ElementC(Element):
    def get_violated_constraints(self):
        result = []
        nrofmodules = sum([ m.mult for m in self.modules])
        if self.mult*3 != nrofmodules:
            result.append((str(self),"elementC nrofmodules != 3"))
        return result

class ElementD(Element):
    def get_violated_constraints(self):
        result = []
        nrofmodules = sum([ m.mult for m in self.modules])
        if self.mult*4 != nrofmodules:
            result.append((str(self),"elementD nrofmodules != 4"))
        return result

class Module(LiftedObject):
    element = None
    frame = None

    def get_violated_constraints(self):
        result = []
        if self.frame is None:
            result.append((str(self),"no frame for module"))
        if not isinstance(self,ModuleV):
            if self.element is None:
                result.append((str(self),"no element for module"))

        return result

    def info(self):
        result = super().info()
        if not isinstance(self,ModuleV):
            result += f" of element {self.element} "
        return result

class ModuleI(Module):
    pass

class ModuleII(Module):
    pass

class ModuleIII(Module):
    pass

class ModuleIV(Module):
    pass

class ModuleV(Module):
    pass

class Frame(LiftedObject):
    rack = None
    modules = None

    def __init__(self,id,mult):
        super().__init__(id,mult)
        self.modules = []

    def get_violated_constraints(self):
        result = []
        if self.rack is None:
            result.append((self,"no rack for frame"))
        nrofmodules = sum([ m.mult for m in self.modules])
        if self.mult*5 < nrofmodules:
            result.append((str(self),"frame nrofmodules > 5"))

        nrofmoduleII = 0
        nrofmoduleV = 0
        for m in self.modules:
            if isinstance(m,ModuleII):
                nrofmoduleII = nrofmoduleII + 1
            elif isinstance(m,ModuleV):
                nrofmoduleV = nrofmoduleV + 1
        valid = (nrofmoduleII>0)==(nrofmoduleV>0)
        if not valid:
            result.append((self,f"moduleII requires moduleV {nrofmoduleII} {nrofmoduleV}"))
        return result

    def info(self):
        result = str(self)
        modules_string = ", ".join([ m.info() for m in self.modules])
        result += f"[{modules_string}]"
        return result


