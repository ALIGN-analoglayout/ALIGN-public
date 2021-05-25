
import logging
import pathlib

from .. import PnR


logger = logging.getLogger(__name__)

def calculate_HPWL_from_hN( hN):

    HPWL = 0

    logger_fn = logger.info

    for neti in hN.Nets:

        mx, Mx, my, My = None, None, None, None

        logger_fn( f'Working on {neti.name}')

        for connectedj in neti.connected:
            ntype,iter2,iter = connectedj.type, connectedj.iter2, connectedj.iter

            if ntype == PnR.NType.Terminal: continue

            blk = hN.Blocks[iter2]
            inst = blk.instance[blk.selectedInstance]

            gdsFile = pathlib.Path(inst.gdsFile).stem

            logger_fn( f'{hN.name} neti {ntype,iter2,iter} {inst.master} {inst.name} {gdsFile} {blk.selectedInstance}')
            for contact in inst.blockPins[iter].pinContacts:
                b = contact.placedBox
                bc = b.center()
                c = contact.placedCenter
                logger_fn( f'{c.x} {c.y} {bc.x} {bc.y}')
                assert c.x == bc.x and c.y == bc.y

                if mx is None or mx > c.x: mx = c.x
                if Mx is None or Mx < c.x: Mx = c.x
                if my is None or my > c.y: my = c.y
                if My is None or My < c.y: My = c.y
                    
        net_HPWL = Mx-mx + My-my if mx is not None else 0

        logger_fn( f'{net_HPWL}')
        logger_fn( f'==========')

        HPWL += net_HPWL
    return HPWL

def calculate_HPWL_from_placement_verilog_d( placement_verilog_d):

    HPWL = 0

    logger_fn = logger.info

    for neti in hN.Nets:

        mx, Mx, my, My = None, None, None, None

        logger_fn( f'Working on {neti.name}')

        for connectedj in neti.connected:
            ntype,iter2,iter = connectedj.type, connectedj.iter2, connectedj.iter

            if ntype == PnR.NType.Terminal: continue

            blk = hN.Blocks[iter2]
            inst = blk.instance[blk.selectedInstance]

            gdsFile = pathlib.Path(inst.gdsFile).stem

            logger_fn( f'{hN.name} neti {ntype,iter2,iter} {inst.master} {inst.name} {gdsFile} {blk.selectedInstance}')
            for contact in inst.blockPins[iter].pinContacts:
                b = contact.placedBox
                bc = b.center()
                c = contact.placedCenter
                logger_fn( f'{c.x} {c.y} {bc.x} {bc.y}')
                assert c.x == bc.x and c.y == bc.y

                if mx is None or mx > c.x: mx = c.x
                if Mx is None or Mx < c.x: Mx = c.x
                if my is None or my > c.y: my = c.y
                if My is None or My < c.y: My = c.y
                    
        net_HPWL = Mx-mx + My-my if mx is not None else 0

        logger_fn( f'{net_HPWL}')
        logger_fn( f'==========')

        HPWL += net_HPWL
    return HPWL
