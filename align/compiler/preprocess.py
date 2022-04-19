from align.schema.types import set_context
from align.schema.subcircuit import SubCircuit
from ..schema import constraint
from .util import get_next_level, get_base_model
from ..schema.graph import Graph
import logging
from align.schema.instance import Instance

logger = logging.getLogger(__name__)


def preprocess_stack_parallel(ckt_data, design_name):
    """
    Preprocess the input graph by reducing parallel device, series devices, remove dummy hierarchies.
    removes power pins to be sent as signal by recursively finding all connections to power pins
    and removing them from subcircuit definition and instance calls
    for each circuit different power connection creates an extra subcircuit
    Required by PnR as it does not make power connections as ports
    """
    top = ckt_data.find(design_name)
    for subckt in ckt_data:
        IsDigital = False
        FixSourceDrain = True
        MergeSeriesDevices = True
        MergeParallelDevices = True
        RemoveDummyDevices = True
        if isinstance(subckt, SubCircuit):
            logger.debug(f"Preprocessing stack/parallel circuit name: {subckt.name}")
            for const in subckt.constraints:
                if isinstance(const, constraint.ConfigureCompiler):
                    IsDigital = const.is_digital
                    FixSourceDrain = const.fix_source_drain
                    MergeSeriesDevices = const.merge_series_devices
                    MergeParallelDevices = const.merge_parallel_devices
                    RemoveDummyDevices = const.remove_dummy_devices
            if not IsDigital:
                logger.debug(
                    f"Starting no of elements in subckt {subckt.name}: {len(subckt.elements)}"
                )
                if FixSourceDrain:
                    # Insures Drain terminal of Nmos has higher potential than source and vice versa
                    define_SD(subckt)
                if MergeParallelDevices:
                    # Find parallel devices and add a parameter parallel to them, all other parameters should be equal
                    add_parallel_devices(subckt)
                if MergeSeriesDevices:
                    # Find parallel devices and add a parameter parallel to them, all other parameters should be equal
                    add_series_devices(subckt)
                if RemoveDummyDevices:
                    # remove dummy devices powered down or shorted D/G/S
                    remove_dummy_devices(subckt)
                logger.debug(
                    f"After reducing series/parallel, elements count in subckt {subckt.name}: {len(subckt.elements)}"
                )
    # Remove dummy hiearachies by design tree traversal from design top
    if isinstance(top, SubCircuit):
        IsDigital = False
        RemoveDummyHierarchies = True
        for const in top.constraints:
            if isinstance(const, constraint.ConfigureCompiler):
                IsDigital = const.is_digital
                RemoveDummyHierarchies = const.remove_dummy_hierarchies
        if not IsDigital and RemoveDummyHierarchies:
            # remove single instance subcircuits
            dummy_hiers = list()
            find_dummy_hier(ckt_data, top, dummy_hiers)
            if len(dummy_hiers) > 0:
                logger.debug(f"Found dummy hierarchies {dummy_hiers}")
                remove_dummies(ckt_data, dummy_hiers, top.name)


def remove_dummies(library, dummy_hiers, top):
    for dh in dummy_hiers:
        if dh == top:
            logger.debug(f"Cant delete top hierarchy {top}")
            return
        ckt = library.find(dh)
        assert ckt, f"No subckt with name {dh} found"
        with set_context(library):
            logger.info(f"Flattening dummy hierarchy {ckt.name}")
            for other_ckt in library:
                if isinstance(other_ckt, SubCircuit) and not other_ckt.name == ckt.name:
                    replace = {}
                    for inst in other_ckt.elements:
                        if inst.model == ckt.name:
                            logger.debug(
                                f"Removing instance {inst} with instance {ckt.elements[0].model}"
                            )
                            replace[inst.name] = ckt.elements[0]
                            # @Parijat, is there a better way to modify?
                    with set_context(other_ckt.elements):
                        for x, y in replace.items():
                            ele = other_ckt.get_element(x)
                            assert ele, f"{ele} not found in {other_ckt.name}"
                            pins = {}
                            for p, v in y.pins.items():
                                pins[p] = ele.pins[v]
                            # Emulated dictionary does not have update method. Update explicitly.
                            for k, v in ele.parameters.items():
                                y.parameters[k] = v
                            logger.debug(f"new instance parameters: {y.parameters}")
                            other_ckt.elements.append(
                                Instance(
                                    name=ele.name,
                                    model=y.model,
                                    pins=pins,
                                    parameters=y.parameters
                                )
                            )
                            logger.info(
                                f"updating {other_ckt.name} element {other_ckt.elements[-1]}"
                            )
                            other_ckt.elements.remove(ele)
            all_subckt = [
                module.name for module in library if isinstance(module, SubCircuit)
            ]
            library.remove(ckt)
            logger.info(f"Removing hierarchy {dh} from {all_subckt}")
            all_subckt_updated = [
                module.name for module in library if isinstance(module, SubCircuit)
            ]
            assert library.find(dh) is None, f"{all_subckt_updated}"


def find_dummy_hier(library, ckt, dummy_hiers):
    assert isinstance(dummy_hiers, list)
    all_subckts = set(
        str(e.model)
        for e in ckt.elements
        if isinstance(library.find(e.model), SubCircuit)
    )
    logger.debug(
        f"Checking hiearchy {ckt.name} subckts {all_subckts} filter: {dummy_hiers}"
    )
    for m in all_subckts - set(dummy_hiers):
        find_dummy_hier(library, library.find(m), dummy_hiers)
    if len(ckt.elements) == 1:
        dummy_hiers.append(ckt.name)


def swap_SD(circuit, G, node):
    """change_SD
    swap source drain nets of transistor]

    Args:
        circuit ([type]): [description]
        G ([type]): [description]
        node ([type]): [description]
    """
    nbrd = [nbr for nbr in G.neighbors(node) if "D" in G.get_edge_data(node, nbr)["pin"]][0]
    assert nbrd, f"incorrect node connections {circuit.get_element(node)}"
    nbrs = [nbr for nbr in G.neighbors(node) if "S" in G.get_edge_data(node, nbr)["pin"]][0]
    assert nbrs, f"incorrect node connections {circuit.get_element(node)}"
    # Swapping D and S
    logger.warning(f"Swapping D and S {node} {nbrd} {nbrs} {circuit.get_element(node)}")
    circuit.get_element(node).pins.update({"D": nbrs, "S": nbrd})


def define_SD(subckt):
    """define_SD
    Checks for scenarios where transistors D/S are flipped.
    It is valid configuration in spice as transistors D and S are invertible
    During subcircuit identification it becomes tricky as it requires multiple building blocks in the library
    One with normal connection and one with flipped connections
    Here, we traverses the circuit from power net to gnd and check
    1. PMOS 'S' pin at high potential (comes first in traversal)
    2. NMOS 'D' pin at high potential (comes first in traversal)
    Next check for Transmission gate like structures where both cases:
    We do another traversal from gnd net to power net and take a intersection of nodes to flip

    Args:
        circuit ([type]): [description]
    """

    power = list()
    gnd = list()
    for const in subckt.constraints:
        if isinstance(const, constraint.PowerPorts):
            power = const.ports
        elif isinstance(const, constraint.GroundPorts):
            gnd = const.ports
    if not power or not gnd:
        logger.debug(f"No power nor ground port specified for {subckt.name}")
        return

    G = Graph(subckt)
    ports = subckt.pins
    high = []
    low = []
    if power and gnd:
        high = list(set(power).intersection(set(ports)))
        low = list(set(gnd).intersection(set(ports)))
        logger.debug(f"Using power: {high} and ground: {low}")
    assert high, f"VDD port {power} not defined in subckt port {subckt.pins}"
    assert low, f"GND port {gnd} not defined in subckt port {subckt.pins}"

    logger.debug(f"Start checking source and drain in {subckt.name} ")

    high = [n for n in high if n in subckt.nets]
    low = [n for n in low if n in subckt.nets]

    if not high or not low:
        logger.debug(f"Power or ground pin is floating in {subckt.name}")
        return

    probable_changes_p = []
    traversed = high.copy()
    traversed.extend(gnd)
    while high:
        nxt = high.pop(0)
        for node in get_next_level(subckt, G, [nxt]):
            edge_type = G.get_edge_data(node, nxt)["pin"]
            if not {"S", "D"} & set(edge_type) or node in traversed:
                continue
            if subckt.get_element(node):
                base_model = get_base_model(subckt, node)
            else:
                assert node in subckt.nets, f"{node} not found in {subckt.nets}"
                base_model = "net"
            if "PMOS" == base_model:
                if "D" in edge_type:
                    probable_changes_p.append(node)
            elif "NMOS" == base_model:
                if "S" in edge_type:
                    probable_changes_p.append(node)
            high.append(node)
            traversed.append(node)
    if len(probable_changes_p) > 0:
        logger.debug(
            f"probable SD changes based on VDD {power} are {probable_changes_p}"
        )
    probable_changes_n = []
    traversed = low.copy()
    traversed.extend(list(set(power).intersection(set(ports))))
    while low:
        if len(probable_changes_p) == 0:
            break
        nxt = low.pop(0)
        for node in get_next_level(subckt, G, [nxt]):
            edge_type = G.get_edge_data(node, nxt)["pin"]
            if not {"S", "D"} & set(edge_type) or node in traversed:
                continue
            if subckt.get_element(node):
                base_model = get_base_model(subckt, node)
            else:
                assert node in subckt.nets, f"{node} not found in {subckt.nets}"
                base_model = "net"
            if "PMOS" == base_model:
                if "S" in edge_type:
                    probable_changes_n.append(node)
            elif "NMOS" == base_model:
                if "D" in edge_type:
                    probable_changes_n.append(node)
            low.append(node)
            traversed.append(node)
    if len(probable_changes_n) > 0:
        logger.debug(
            f"probable SD changes based on GND {power} are {probable_changes_n}"
        )
        for node in list(set(probable_changes_n) & set(probable_changes_p)):
            logger.warning(f"changing source drain: {node}")
            swap_SD(subckt, G, node)


def add_parallel_devices(ckt):
    """add_parallel_devics
        merge devices in parallel as single unit
        Keeps 1st device out of sorted list

    Parameters:
        ckt : subcircuit
        update (bool, optional): To turn this feature ON/OFF. Defaults to ON.
    """
    logger.debug(
        f"Checking parallel devices in {ckt.name}, initial ckt size: {len(ckt.elements)}"
    )

    for net in set(ckt.nets):
        pp_list = []
        parallel_devices = {}
        G = Graph(ckt)
        for node in G.neighbors(net):
            ele = ckt.get_element(node)
            if 'PARALLEL' not in ele.parameters:
                continue  # this element does not support multiplicity
            p = {**ele.pins, **ele.parameters}
            p["model"] = ele.model
            if p in pp_list:
                parallel_devices[pp_list.index(p)].append(ele)
            else:
                pp_list.append(p)
                parallel_devices[pp_list.index(p)] = [ele]
        for pd in parallel_devices.values():
            if len(pd) > 1:
                pd0 = sorted(pd, key=lambda x: x.name)[0]
                logger.info(f"removing parallel instances {[x.name for x in pd[1:]]} and updating {pd0.name} parameters")
                pd0.parameters["PARALLEL"] = str(sum([int(getattr(x.parameters, "PARALLEL", "1")) for x in pd]))
                for rn in pd[1:]:
                    G.remove(rn)


def add_series_devices(ckt):
    """add_series_devics
        merge devices in series as single unit
        Keeps 1st device out of sorted list

    Parameters:

        ckt : subcircuit
        update (bool, optional): To turn this feature ON/OFF. Defaults to ON.
    """
    logger.debug(
        f"Checking stacked/series devices, initial ckt size: {len(ckt.elements)}"
    )
    remove_nodes = []
    for net in set(ckt.nets) - set(ckt.pins):
        G = Graph(ckt)
        nbrs = sorted(list(G.neighbors(net)))
        if len(nbrs) == 2 and net not in remove_nodes:
            nbr1, nbr2 = [ckt.get_element(nbr) for nbr in nbrs]
            if 'STACK' not in nbr1.parameters:
                continue  # this element does not support stacking
            # Same instance type
            if nbr1.model != nbr2.model:
                continue
            # Valid only for Single pin connection e.g, set(D,S) or (+,-)
            if (
                len(G.get_edge_data(nbr1.name, net)["pin"]) != 1
                or len(G.get_edge_data(nbr2.name, net)["pin"]) != 1
            ):
                continue
            # Filter (D,D) or (S,S) or (G,G) connection
            if (
                G.get_edge_data(nbr1.name, net)["pin"]
                == G.get_edge_data(nbr2.name, net)["pin"]
            ):
                continue
            connections = set(
                [list(G.get_edge_data(nbr, net)["pin"])[0] for nbr in nbrs]
            )
            assert (
                len(connections) == 2
            ), f"Not a stack {nbrs} as connections: {connections} are not allowed"
            nbr1p = dict(**nbr1.parameters, **nbr1.pins)
            nbr2p = dict(**nbr2.parameters, **nbr2.pins)
            stack1 = int(nbr1p.pop("STACK", 1))
            stack2 = int(nbr2p.pop("STACK", 1))
            for connection in connections:
                assert connection in nbr1p, f"pin {connection} not found in {nbr1p}"
                assert connection in nbr2p, f"pin {connection} not found in {nbr2p}"
                del nbr1p[connection]
                del nbr2p[connection]

            if nbr1p == nbr2p and connections in [
                set(["D", "S"]),
                set(["PLUS", "MINUS"]),
            ]:
                logger.info(f"stacking {nbrs} {stack1 + stack2}")
                nbr1.parameters["STACK"] = str(stack1 + stack2)
                for p, n in nbr1.pins.items():
                    if net == n:
                        nbr1.pins[p] = nbr2.pins[p]
                G.remove(nbr2)


def remove_dummy_devices(subckt):
    logger.debug(f"Removing dummy devices, initial ckt size: {len(subckt.elements)}")

    def _find_base_model(subckt, model_name):
        model_definition = subckt.parent.find(model_name)
        while model_definition.base:
            model_definition = subckt.parent.find(model_definition.base)
        return model_definition.name

    power = list()
    gnd = list()
    for const in subckt.constraints:
        if isinstance(const, constraint.PowerPorts):
            power = const.ports
        elif isinstance(const, constraint.GroundPorts):
            gnd = const.ports
    if not power and not gnd:
        logger.debug(f"No power nor ground port specified for {subckt.name}")
        return
    remove_inst = []
    for inst in subckt.elements:
        base_model = _find_base_model(subckt, inst.model)
        if not all([k in inst.pins for k in 'DGS']):
            continue
        if (power and "PMOS" == base_model and inst.pins['G'] in power) or \
           (gnd and "NMOS" == base_model and inst.pins['G'] in gnd) or \
           ((base_model in ["NMOS", "PMOS"]) and inst.pins['D'] == inst.pins['G'] == inst.pins['S']):
            remove_inst.append(inst)

    G = Graph(subckt)
    for inst in remove_inst:
        G.remove(inst)
