from copy import deepcopy

import logging
logger = logging.getLogger(__name__)

def ViaArrayGenerator(term, *, WidthX, WidthY, SpaceX, SpaceY, NumX, NumY):
    logger.debug( f"ViaArrayGenerator: {term}")
    rect = term['rect']
    xstart = ( rect[0] + rect[2] ) // 2 - (WidthX * NumX + SpaceX * (NumX-1)) // 2
    ystart = ( rect[1] + rect[3] ) // 2 - (WidthY * NumY + SpaceY * (NumY-1)) // 2
    for i in range(NumX):
        for j  in range(NumY):
            new_term = deepcopy(term)
            new_rect = [xstart + i*(WidthX + SpaceX),
                        ystart + j*(WidthY + SpaceY),
                        xstart + i*(WidthX + SpaceX) + WidthX,
                        ystart + j*(WidthY + SpaceY) + WidthY]
            new_term['rect'] = new_rect
            yield new_term

def ColorClosure( *, info, errors=None):
    def func( term):
        colors = info['Color']
        assert len(colors) > 0

        if info['Direction'].upper() == 'H':
            c2 = (term['rect'][1]+term['rect'][3])
        elif info['Direction'].upper() == 'V':
            c2 = (term['rect'][0]+term['rect'][2])
        else:
            assert False, info['Direction']

        # Convert 2x to grid
        (q,r) = divmod( c2, 2*info['Pitch'])
        if r == 0:
            color = colors[q % len(colors)]
            colored_term = deepcopy(term)
            colored_term['color'] = color
            logger.debug( f"Adding {color}...{term}...{colored_term}") 
            return [term,colored_term]
        else:
            if errors is not None:
                errors.append( f"Wire to color is offgrid: {term} {c2} {q} {r} pitch {info['Pitch']}")
            return [term]

    return func
