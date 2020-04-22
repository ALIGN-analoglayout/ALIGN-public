def ViaArrayGenerator(rect, WidthX, WidthY, SpaceX, SpaceY, Number):
    xstart = ( rect[0] + rect[2] ) // 2 - (WidthX * Number[0] + SpaceX * (Number[0]-1)) // 2
    ystart = ( rect[1] + rect[3] ) // 2 - (WidthY * Number[1] + SpaceY * (Number[1]-1)) // 2
    for i in range(Number[0]):
        for j  in range(Number[1]):
            yield [xstart + i*(WidthX + SpaceX),
                   ystart + j*(WidthY + SpaceY),
                   xstart + i*(WidthX + SpaceX) + WidthX,
                   ystart + j*(WidthY + SpaceY) + WidthY]
