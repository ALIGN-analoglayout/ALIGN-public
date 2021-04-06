import pathlib

from align.schema.subcircuit import SubCircuit
from align.schema.parser import SpiceParser
import logging
logger = logging.getLogger(__name__)

def compiler(input_ckt: pathlib.Path, design_name: str, pdk_dir: pathlib.Path, config_path:pathlib.Path, flat=0, Debug=False):
    
    """
    Reads input spice file, converts to a graph format and create hierarchies in the graph

    Parameters
    ----------
    input_ckt : input circuit path
        DESCRIPTION.
    design_name : name of top level subckt in design
        DESCRIPTION.
    flat : TYPE, flat/hierarchical
        DESCRIPTION. The default is 0.
    Debug : TYPE, writes output graph for debug
        DESCRIPTION. The default is False.

    Returns
    -------
    updated_ckt_list : list of reduced graphs for each subckt
        DESCRIPTION. reduced graphs are subckts after identification of hierarchies
    library : TYPE, list of library graphs
        DESCRIPTION.libraries are used to create hierarchies

    """
    logger.info("Starting topology identification...")
    logger.debug(f"Reading subckt: {input_ckt}")
    parser = SpiceParser()
    model_statemenets = config_path / 'model.txt'
    design_name = design_name.upper()
    with open(model_statemenets) as f:
        lines = f.read()
    parser.parse(lines)
    
    with open(input_ckt) as f:
        lines =  f.read()
    parser.parse(lines)
    circuit = parser.library[design_name]
    return circuit

if __name__ == "__main__":
    circuit_name = 'switched_capacitor_filter'
    input_circuit = pathlib.Path('../../examples/').resolve() / circuit_name / (circuit_name + '.sp')
    pdk_dir = pathlib.Path('../../pdks/FinFET14nm_Mock_PDK/')
    config_path =  pathlib.Path(__file__).resolve().parent.parent / 'config' 

    circuit = compiler(input_circuit, 'telescopic_ota', pdk_dir, config_path)
    print(circuit.elements)
