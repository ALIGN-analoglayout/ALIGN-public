from collections import deque
import argparse
import random


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

    q = deque([()])
    while q:
        e = q.popleft()
        for f in expand(n, e):
            ok = check(f)
            print(disp(e), '->', disp(f), ok)
            if len(f) == n and ok:
                successes += 1
            if ok:
                q.append(f)
        count += 1

    print(f'n: {n} count: {count} successes: {successes} ratio: {count/successes}')


def rand(args):
    n = args.num_nets
    s = args.num_samples

    successes = 0
    for trial in range(s):
        order = list(range(n))
        random.shuffle(order)
        if check(order):
            print(f'{disp(order)} succeeded on trial {trial}')
            successes += 1

    print(f'{successes} out of {s} trails')


def disp(s):
    origin = [ord('a'), ord('A')]
    return ''.join([chr(origin[x%2]+x//2) for x in s])


def pruning(args):
    n = args.num_nets
    s = args.num_samples

    successes = 0

    failed = set()

    for trial in range(s):

        e = ()
        possible = set(range(n))

        for i in range(n):
            print(f'before {disp(e)}')
            order = [j for j in possible if e + (j,) not in failed]

            if order:
                j = random.choice(order)
                e = e + (j,)
                possible.remove(j)
                ok = check(e)
                if not ok:
                    failed.add(e)
                    print(f'marking {disp(e)} as failed')
                    break
                elif len(e) == n:
                    successes += 1
                    print(f'{disp(e)} succeeded on trial {trial}')
            else:
                break

    print(f'{successes} out of {s} trails')

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Tree Enumerator")
    parser.add_argument("-n", "--num_nets", type=int, default=6)
    parser.add_argument("-s", "--num_samples", type=int, default=100)
    parser.add_argument("-a", "--algorithm", type=str, default="enum")

    args = parser.parse_args()

    assert args.num_nets % 2 == 0

    if args.algorithm == "enum":
        simple(args)
    elif args.algorithm == "random":
        rand(args)
    elif args.algorithm == "random_with_pruning":
        pruning(args)
    else:
        assert False
