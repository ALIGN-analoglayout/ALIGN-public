def ViaArrayGenerator(rect, *, WidthX, WidthY, SpaceX, SpaceY, NumX, NumY):
    xstart = ( rect[0] + rect[2] ) // 2 - (WidthX * NumX + SpaceX * (NumX-1)) // 2
    ystart = ( rect[1] + rect[3] ) // 2 - (WidthY * NumY + SpaceY * (NumY-1)) // 2
    for i in range(NumX):
        for j  in range(NumY):
            yield [xstart + i*(WidthX + SpaceX),
                   ystart + j*(WidthY + SpaceY),
                   xstart + i*(WidthX + SpaceX) + WidthX,
                   ystart + j*(WidthY + SpaceY) + WidthY]
