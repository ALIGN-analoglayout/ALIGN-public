from collections import deque
import argparse
import random
from itertools import chain


def expand(n, s):
    """s is a tuple of length at most n"""
    if len(s) == n:
        return
    else:
        s_set = set(s)
        for i in range(n):
            if i not in s_set:
                yield s + (i,)

def check(s):
    """bad if a before A; ordering is aAbBcD"""
    already_there = set()
    for x in s:
        if x % 2 == 1 and (x-1) in already_there:
            return False
        already_there.add(x)
    return True

def fac(n):
    prod = 1
    for i in range(2, n+1):
        prod *= i
    return prod

def state_space_size(n):
    """1 + n + n(n-1) + n(n-1)(n-2) + ... + n!
    or n!/(1/n! + 1/(n-1)! + 1/(n-2)! + ... + 1/1)
"""

    fn = fac(n)

    s = 0
    for i in range(n, -1, -1):
        s += fn//fac(i)

    return s

def test_state_space_size():
    """1 + 2 + 2(1)
 -> a,A -> aA,Aa
       1 + 3 + (3)(2) + (3)(2)(1)
 -> a,b,c -> ab, ac, ba, bc, ca, cb -> abc, acb, bac, bca, cab, cba
"""
    assert state_space_size(2) == 5
    assert state_space_size(3) == 16




def simple(args):
    
    """
n: 2 count: 4 successes: 1 ratio: 4.0
n: 4 count: 33 successes: 6 ratio: 5.5
n: 6 count: 550 successes: 90 ratio: 6.111111111111111
n: 8 count: 16201 successes: 2520 ratio: 6.428968253968254
n: 10 count: 751056 successes: 113400 ratio: 6.623068783068783
n: 12 count: 50541769 successes: 7484400 ratio: 6.752948666559778
"""





    n = args.num_nets

    count = 0
    successes = 0

    done = False

    q = deque([()])
    while q and not done:
        e = q.popleft()
        for f in expand(n, e):
            ok = check(f)
            print(disp(e), '->', disp(f), ok)
            if len(f) == n and ok:
                successes += 1
                #done = True
            if ok:
                q.append(f)
        count += 1

    print(f'n: {n} state_space_size: {state_space_size(n)} count: {count} state_space_size/count: {state_space_size(n)/count} successes: {successes} count/successes: {count/successes}')


def strong(args):
    
    n = args.num_nets

    count = 0
    successes = 0

    done = False

    q = deque([()])
    while q and not done:
        e = q.popleft()
        if all(check(f) for f in expand(n, e)):
            for f in expand(n, e):
                if len(f) == n:
                    successes += 1
                    #done = True
                print(disp(e), '->', disp(f), True)
                q.append(f)
        count += 1

    print(f'n: {n} state_space_size: {state_space_size(n)} count: {count} state_space_size/count: {state_space_size(n)/count} successes: {successes} count/successes: {count/successes}')


def rand(args):
    n = args.num_nets
    s = args.num_samples

    rnd = random.Random()
    if args.seed is not None:
        rnd.seed(args.seed)

    successes = 0
    done = False

    trial = 0

    while trial < s and not done:
        order = list(range(n))
        rnd.shuffle(order)
        if check(order):
            print(f'{disp(order)} succeeded on trial {trial}')
            successes += 1
            done = True
        trial += 1

    print(f'{successes} out of {trial} trails')


def disp(s):
    origin = [ord('a'), ord('A')]
    return ''.join([chr(origin[x%2]+x//2) for x in s])


def pruning(args):
    n = args.num_nets
    s = args.num_samples

    rnd = random.Random()
    if args.seed is not None:
        rnd.seed(args.seed)

    successes = 0
    done = False

    failed = set()

    trial = 0
    while trial < s and not done:

        e = ()
        possible = set(range(n))

        for i in range(n):
            #print(f'before {disp(e)}')
            order = [j for j in possible if e + (j,) not in failed]

            if order:
                j = rnd.choice(order)
                e = e + (j,)
                possible.remove(j)
                ok = check(e)
                if not ok:
                    failed.add(e)
                    #print(f'marking {disp(e)} as failed')
                    break
                elif len(e) == n:
                    successes += 1
                    print(f'{disp(e)} succeeded on trial {trial}')
                    done = True
            else:
                break

        trial += 1

    print(f'{successes} out of {trial} trails')


def strong_pruning(args):
    n = args.num_nets
    s = args.num_samples

    rnd = random.Random()
    if args.seed is not None:
        rnd.seed(args.seed)

    successes = 0
    done = False

    failed = set()

    def strong_prune(e, possible):
        print(f'strong_prune: {disp(e)}')
        for x in chain((e[-1],), possible):
            f = e[:-1] + (x,)

            if not check(f):
                print(f'found failure: {disp(f)}')
                e = f
                while True:
                    f = e[:-2] + (e[-1],)
                    print(f'{disp(e)} -> {disp(f)}')
                    if check(f):
                        break
                    print(f'{disp(f)} failed')
                    e = f

                e = e[:-1]
                print(f'marked {disp(e)} as failed')
                failed.add(e)



    trial = 0
    while trial < s and not done:

        e = ()
        possible = set(range(n))

        for i in range(n):
            #print(f'before {disp(e)}')
            order = [j for j in possible if e + (j,) not in failed]

            if order:
                j = rnd.choice(order)
                e = e + (j,)
                possible.remove(j)
                ok = check(e)
                if not ok:
                    #print(f'marking {disp(e)} as failed')
                    strong_prune(e, possible)
                    break
                elif len(e) == n:
                    successes += 1
                    print(f'{disp(e)} succeeded on trial {trial}')
                    done = True
            else:
                break

        trial += 1

    print(f'{successes} out of {trial} trails')


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Tree Enumerator")
    parser.add_argument("-n", "--num_nets", type=int, default=6)
    parser.add_argument("-s", "--num_samples", type=int, default=100)
    parser.add_argument("-a", "--algorithm", type=str, default="enum")
    parser.add_argument("--seed", type=int, default=None)

    args = parser.parse_args()

    assert args.num_nets % 2 == 0

    if args.algorithm == "enum":
        simple(args)
    elif args.algorithm == "strong":
        strong(args)
    elif args.algorithm == "random":
        rand(args)
    elif args.algorithm == "random_with_pruning":
        pruning(args)
    elif args.algorithm == "random_with_strong_pruning":
        strong_pruning(args)
    else:
        assert False
