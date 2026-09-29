from small_r_fast2 import plan, saddle_family
rs = list(range(51, 300, 2))
S = {r: complex(v) for r, v in saddle_family(rs).items()}
tot = 0; worst = None
for r in rs:
    best = None
    for s0 in [1.5, 1.2]:
        p = plan(r, S[r], s0)
        if all(n is not None for n, _ in p):
            t = sum(n for n, _ in p)
            if best is None or t < best[0]: best = (t, s0, p)
    if best is None:
        print(r, 'FAIL'); continue
    tot += best[0]
    if r % 50 == 1 or r > 290: print(r, best[0], best[1], [(n, round(sl, 3)) for n, sl in best[2]], flush=True)
print('total', tot)
