from collections import deque
import argparse
import random
from itertools import chain
from functools import reduce
from operator import __mul__

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
    return reduce(__mul__, range(2, n+1), 1)

def test_fac():
    assert fac(-1) == 1
    assert fac(0) == 1
    assert fac(1) == 1
    assert fac(2) == 2
    assert fac(3) == 6


def state_space_size(n):
    """1 + n + n(n-1) + n(n-1)(n-2) + ... + n!
    or n!/(1/n! + 1/(n-1)! + 1/(n-2)! + ... + 1/1)
"""

    fn = fac(n)
    return sum(fn//fac(i) for i in range(n, -1, -1))

def alt_state_space_size(n):
    """1 + n + n(n-1) + n(n-1)(n-2) + ... + n!
"""
    return sum(reduce(__mul__, range(n+1-i,n+1), 1) for i in range(0, n+1))

def test_state_space_size():
    """1
'' 
       1 + 1
'' -> a
       1 + 2 + 2(1)
'' -> a,A -> aA,Aa
       1 + 3 + (3)(2) + (3)(2)(1)
'' -> a,b,c -> ab, ac, ba, bc, ca, cb -> abc, acb, bac, bca, cab, cba
"""
    assert state_space_size(0) == 1
    assert state_space_size(1) == 2
    assert state_space_size(2) == 5
    assert state_space_size(3) == 16

    for i in range(1, 20):
        print(fac(i), state_space_size(i)/fac(i))

def test_alt_state_space_size():
    assert state_space_size(0) == 1
    assert state_space_size(1) == 2
    assert alt_state_space_size(2) == 5
    assert alt_state_space_size(3) == 16

    for i in range(1, 20):
        print(fac(i), alt_state_space_size(i)/fac(i))


def simple(args):

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
    if not s or max(s) < 52:
        return ''.join([chr(origin[x%2]+x//2) for x in s])
    else:
        return s


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


def strong_prune(e, possible):
    print(f'strong_prune: {disp(e)}')
    most_constraining_e = e

    for x in chain((e[-1],), possible):
        f = e[:-1] + (x,)

        if not check(f):
            print(f'found failure: {disp(f)}')
            e = f
            while True:
                f = e[:-2] + (e[-1],)
                ok = check(f)
                print(f'{disp(e)} -> {disp(f)} {ok}')
                if ok:
                    break
                e = f

            e = e[:-1]
            most_constraining_e = e

    return most_constraining_e


def strong_pruning(args):
    n = args.num_nets
    s = args.num_samples

    rnd = random.Random()
    if args.seed is not None:
        rnd.seed(args.seed)

    successes = 0
    done = False

    failed = set()


    trial = 0
    restarts = 0
    while trial + restarts < s and not done:

        e = ()
        possible = set(range(n))

        while len(e) < n:
            #print(f'before {disp(e)}')
            order = [j for j in possible if e + (j,) not in failed]

            if order:
                j = rnd.choice(order)
                e = e + (j,)
                possible.remove(j)
                ok = check(e)
                if not ok:
                    most_constraining_e = strong_prune(e, possible)
                    print(f'marked {disp(most_constraining_e)} as failed')
                    failed.add(most_constraining_e)
                    e = most_constraining_e[:-1]
                    print(f'Restarting with {disp(e)}')
                    e_s = set(e)
                    possible = set(i for i in range(n) if i not in e_s)
                    restarts += 1
                elif len(e) == n:
                    successes += 1
                    print(f'{disp(e)} succeeded on trial {trial}')
                    if not args.dont_stop_after_first:
                        done = True
            else:
                break

        trial += 1

    def plural(tag, value, p="s"):
        return f'{value} {tag}{p if value != 1 else ""}'

    print(f'{plural("success", successes, "es")} out of {plural("trial", trial)} and {plural("restart", restarts)}.')


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Tree Enumerator")
    parser.add_argument("-n", "--num_nets", type=int, default=6)
    parser.add_argument("-s", "--num_samples", type=int, default=100)
    parser.add_argument("-a", "--algorithm", type=str, default="enum")
    parser.add_argument("--seed", type=int, default=None)
    parser.add_argument("--dont_stop_after_first", action="store_true")

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
