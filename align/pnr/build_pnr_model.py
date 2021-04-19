
import logging
import pathlib
import json
import re
from itertools import chain

from .. import PnR

logger = logging.getLogger(__name__)

NType = PnR.NType

def analyze_hN( tag, hN, beforeAddingBlockPins=False):
    logger.info( f'{tag} name {hN.name}')

    logger.info( f'Nets and PowerNets')
    for net in chain( hN.Nets, hN.PowerNets):
        logger.info( f'  {net.name}')
        for conn in net.connected:
            if conn.type == NType.Block:
                if 0 <= conn.iter2 < len(hN.Blocks):
                    blk = hN.Blocks[conn.iter2]
                    inst = blk.instance[0]

                    if 0 <= conn.iter < len(inst.blockPins):

                        logger.info( f'    {conn.type} {conn.iter} ({inst.blockPins[conn.iter].name}) {conn.iter2} ({inst.name} {inst.master})')
                    else:
                        logger.info( f'    {conn.type} {conn.iter} (<out of range>) {conn.iter2} ({inst.name} {inst.master})')                        

                else:
                    logger.info( f'    {conn.type} {conn.iter} (<unknown>) {conn.iter2} (<out of range>)')
            elif conn.type == NType.Terminal:
                assert conn.iter2 == -1
                if 0 <= conn.iter < len(hN.Terminals):
                    logger.info( f'    {conn.type} {conn.iter} ({hN.Terminals[conn.iter].name})')
                else:
                    logger.info( f'    {conn.type} {conn.iter} (<out of range>)')

    logger.info( f'PowerNets (second pass)')
    for net in hN.PowerNets:
        logger.info( f'  {net.name}')
        for conn in net.dummy_connected:
            if 0 <= conn.iter2 < len(hN.Blocks):
                blk = hN.Blocks[conn.iter2]
                logger.info( f'    blk.selectedInstance={blk.selectedInstance}')
                for inst_idx,inst in enumerate(blk.instance):
                    if beforeAddingBlockPins:
                        if 0 <= conn.iter < len(inst.dummy_power_pin):
                            logger.info( f'    {conn.iter} ({inst.dummy_power_pin[conn.iter].name}) {conn.iter2} ({inst.name} {inst.master}) inst_idx={inst_idx}')
                        else:
                            logger.info( f'    {conn.iter} (<out of range>) {conn.iter2} ({inst.name} {inst.master}) inst_idx={inst_idx}')                        
            else:
                logger.info( f'    {conn.iter} (<unknown>) {conn.iter2} (<out of range>)')

    logger.info( f'Blocks')
    for blk in hN.Blocks:
        logger.info( f'  blk.child={blk.child} len(blk.instance)={len(blk.instance)} blk.selectedInstance={blk.selectedInstance} blk.instNum={blk.instNum}')
        for inst in blk.instance:
            logger.info( f'    inst.name={inst.name} inst.master={inst.master} len(inst.dummy_power_pin)={len(inst.dummy_power_pin)}')


def ReadVerilogJson( DB, j):
    hierTree = []

    for module in j['modules']:

        temp_node = PnR.hierNode()
        temp_node.name = module['name']
        temp_node.isCompleted = 0

        Terminals = []
        for parameter in module['parameters']:
            temp_terminal = PnR.terminal()
            temp_terminal.name = parameter
            temp_terminal.type = 'input' # All nets are inputs, we don't use this for anything do we?
            Terminals.append( temp_terminal)
        temp_node.Terminals = Terminals

        terminal_map = { term.name : term for term in temp_node.Terminals}
        net_map = {}

        Blocks = []
        Nets = []

        Connecteds = []

        for instance in module['instances']:
            temp_blockComplex = PnR.blockComplex()
            current_instance = PnR.block()

            current_instance.master = instance['template_name']
            current_instance.name = instance['instance_name']

            blockPins = []

            def process_connection( iter, net_name):
                net_index = 0
                if net_name in net_map:
                    net_index = net_map[net_name]
                else:
                    net_index = len(Nets)
                    Nets.append( PnR.net())
                    Connecteds.append( [])
                    Nets[-1].name = net_name
                    
                    net_map[net_name] = net_index

                # Use a python list of list to workaround not being able to append to a C++ vector
                Connecteds[net_index].append( PnR.connectNode())
                Connecteds[net_index][-1].type = PnR.Block
                Connecteds[net_index][-1].iter = iter
                Connecteds[net_index][-1].iter2 = len(Blocks)

                return net_index


            for i,fa in enumerate(instance['fa_map']):
                temp_pin = PnR.pin()
                temp_pin.name = fa['formal']
                net_name = fa['actual']
                temp_pin.netIter = process_connection( i, net_name)
                blockPins.append( temp_pin)
                
            current_instance.blockPins = blockPins
            temp_blockComplex.instance = [ current_instance ]
            Blocks.append( temp_blockComplex)

        for net,connected in zip(Nets,Connecteds):
            net.connected = connected
            net.degree = len(connected)

        temp_node.Blocks = Blocks
        temp_node.Nets = Nets

        hierTree.append( temp_node)

    DB.hierTree = hierTree

    global_signals = []
    for global_signal in j['global_signals']:
        global_signals.append( (global_signal['prefix'], global_signal['formal'], global_signal['actual']))

    return global_signals

def _ReadMap( path, mapname):
    d = pathlib.Path(path)
    p = re.compile( r'^(\S+)\s+(\S+)\s*$')
    tbl = {}
    with (d / mapname).open( "rt") as fp:
        for line in fp:
            line = line.rstrip('\n')
            m = p.match(line)
            assert m
            k, v = m.groups()
            tbl[k] = str(d / v)
    return tbl

def _attach_constraint_files( DB, fpath):
    d = pathlib.Path(fpath)

    for curr_node in DB.hierTree:
        curr_node.bias_Vgraph = DB.getDrc_info().Design_info.Vspace
        curr_node.bias_Hgraph = DB.getDrc_info().Design_info.Hspace

        fp = d / f"{curr_node.name}.pnr.const.json"
        if fp.exists():
            with fp.open( "rt") as fp:
                jsonStr = fp.read()
            DB.ReadConstraint_Json( curr_node, jsonStr)
            logger.info(f"Finished reading contraint json file {curr_node.name}.pnr.const.json")
        else:
            logger.warning(f"No constraint file for module {curr_node.name}")
                
def _ReadLEF( DB, path, lefname):
    p = pathlib.Path(path) / lefname
    if p.exists():
        with p.open( "rt") as fp:
            s = fp.read()
            DB.ReadLEFFromString( s)
    else:
        logger.warn(f"LEF file {p} doesn't exist.")

def PnRdatabase( path, topcell, vname, lefname, mapname, drname):
    DB = PnR.PnRdatabase()

    assert drname.endswith('.json'), drname
    DB.ReadPDKJSON( path + '/' + drname)

    _ReadLEF( DB, path, lefname)
    DB.gdsData = _ReadMap( path, mapname)

    if vname.endswith(".verilog.json"):
        with (pathlib.Path(path) / vname).open( "rt") as fp:
            j = json.load( fp)
        global_signals = ReadVerilogJson( DB, j)
    else:
        global_signals = DB.ReadVerilog( path, vname, topcell)

    _attach_constraint_files( DB, path)
    DB.semantic0( topcell)
    DB.semantic1( global_signals)
    DB.semantic2()

    return DB
