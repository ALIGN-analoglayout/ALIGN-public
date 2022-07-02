
def show(n, m, h_edge_on, v_edge_on):

    def get_ch(s):
        ch = ' '
        if len(s) == 1:
            ch = list(s)[0]
        elif len(s) > 1:
            ch = '*'
        return ch

    for i in range(n):
        for ii in range(4):
            if i == n-1 and ii > 0:
                continue
            for j in range(m):
                for jj in range(6):
                    if j == m-1 and jj > 0:
                        continue
                    ch = ' '
                    if ii == 0 and jj == 0:
                        s = set()
                        s.update(h_edge_on(i, j))
                        s.update(h_edge_on(i, j-1))
                        s.update(v_edge_on(i, j))
                        s.update(v_edge_on(i-1, j))
                        ch = get_ch(s)

                    elif ii == 0 and jj > 0:
                        s = set()
                        s.update(h_edge_on(i, j))
                        ch = get_ch(s)

                    elif ii > 0 and jj == 0:
                        s = set()
                        s.update(v_edge_on(i, j))
                        ch = get_ch(s)

                    print(ch, end='')
            print('')

