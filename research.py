"""Reproducible, bounded experiments. Output is evidence, not a proof."""
import argparse
import json
import random
import time
from pathlib import Path
from semigroups import bitset, closed_prefixes, from_generators, reference


def exhaustive(max_cutoff):
    rows = []
    for c in range(1, max_cutoff+1):
        count = target = canonical_target = 0
        minima = {}
        for bits in closed_prefixes(c):
            a = bitset(bits,c)
            assert a == reference(set(a.left),c)
            count += 1
            if a.gap is not None and 1 <= a.gap <= 6:
                target += 1
                canonical_target += a.canonical
                minima[str(a.gap)] = min(minima.get(str(a.gap),a.E),a.E)
                if a.E < 0:
                    return {'kind':'exhaustive','counterexample':a.record(),'completed_rows':rows}
        rows.append(dict(cutoff=c,prefixes=count,target_presentations=target,
                         canonical_targets=canonical_target,min_E_by_gap=minima))
    return {'kind':'exhaustive','max_cutoff':max_cutoff,'rows':rows,'counterexample':None}


def sample(seed, iterations, seconds):
    rng = random.Random(seed)
    start = time.monotonic()
    minima = {}
    eligible = 0
    counterexample = None
    for i in range(iterations):
        if time.monotonic()-start >= seconds:
            break
        d = rng.randint(1,6)
        m = rng.randint(max(2,d+1),160)
        c = rng.randint(m+d+1, min(1600,20*m))
        # Deliberately includes all choices of gcd(m,d); does not claim uniform sampling.
        extras = rng.sample(range(m+d+1,c),min(rng.randint(0,8),c-m-d-1))
        prefix = from_generators([m,m+d]+extras,c)
        a = bitset(sum(1 << n for n in prefix),c)
        if a.gap is None or not 1 <= a.gap <= 6:
            continue
        eligible += 1
        if i % 100 == 0:
            assert a == reference(prefix,c)
        if str(d) not in minima or a.E < minima[str(d)]['E']:
            minima[str(d)] = a.record()
        if a.E < 0:
            assert a == reference(prefix,c)
            counterexample = a.record()
            break
    else:
        i = iterations
    return dict(kind='nonuniform_random_sampling',seed=seed,requested_iterations=iterations,
                eligible_presentations=eligible,seconds=time.monotonic()-start,
                min_examples_by_gap=minima,counterexample=counterexample)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('mode',choices=['exhaustive','sample'])
    p.add_argument('--max-cutoff',type=int,default=18)
    p.add_argument('--seed',type=int,default=20261126)
    p.add_argument('--iterations',type=int,default=10000)
    p.add_argument('--seconds',type=int,default=120)
    p.add_argument('--output',required=True)
    args = p.parse_args()
    result = exhaustive(args.max_cutoff) if args.mode == 'exhaustive' else sample(args.seed,args.iterations,args.seconds)
    Path(args.output).parent.mkdir(parents=True,exist_ok=True)
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in ['rows','min_examples_by_gap']}))
