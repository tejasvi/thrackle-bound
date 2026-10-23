"""Certificates for Thrackle78/Proof/Run3S<k>.lean (mirrors validB3, violB3, checkCert3 of Run3Defs.lean).
Kinds: 4 triangle, 5 4-cycle, 6 two 6-cycles with a common vertex and different edges, 7 a 6-cycle and an 8-cycle
with a common edge, 8/9/10 a copy of theta(2,3,3)/theta(2,3,4)/theta(3,3,7) (labels of the listing's vertices).
Writes one module per first label x4 (data + twelve slice theorems, one per x5)."""
import itertools, sys, os
from collections import Counter

LTH = {8: (7, [(0,1),(0,5),(0,6),(1,2),(2,3),(3,4),(3,6),(4,5)]),
       9: (8, [(0,1),(1,2),(2,3),(3,4),(4,0),(2,5),(5,6),(6,7),(7,0)]),
       10: (12, [(0,1),(1,2),(2,3),(0,4),(4,5),(5,3),(0,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,3)])}

def wl(xs): return [0, 1, 2, 3] + list(xs)
def wlAt(xs, t): return wl(xs)[t % 10]
def cEdgeB(a, b): return a < 6 and b < 6 and (b == (a + 1) % 6 or a == (b + 1) % 6)
def sameStep(xs, t, u):
    return (wlAt(xs, t) == wlAt(xs, u) and wlAt(xs, t + 1) == wlAt(xs, u + 1)) or \
           (wlAt(xs, t) == wlAt(xs, u + 1) and wlAt(xs, t + 1) == wlAt(xs, u))
def stepMult(xs, t): return sum(1 for u in range(10) if sameStep(xs, t, u))
def validB(xs):
    if len(xs) != 6: return False
    for k in range(6):
        x = xs[k]
        if not (x < 6 or x == k + 6 or any(x == kp + 6 and xs[kp] == kp + 6 for kp in range(k))):
            return False
    return True
def violB(xs):
    if any(wlAt(xs, t) == wlAt(xs, t + 1) for t in range(10)): return True
    if any(wlAt(xs, t) == wlAt(xs, t + 2) for t in range(10)): return True
    if any(cEdgeB(wlAt(xs, t), wlAt(xs, t + 1)) and stepMult(xs, t) >= 2 for t in range(10)): return True
    if any(stepMult(xs, t) >= 3 for t in range(10)): return True
    return False
def uEdge(xs, a, b):
    return cEdgeB(a, b) or any((a == wlAt(xs, t) and b == wlAt(xs, t + 1)) or (b == wlAt(xs, t) and a == wlAt(xs, t + 1))
                               for t in range(10))
def used(xs, l): return l < 6 or l in xs
def adjOf(xs):
    labs = sorted(set(range(6)) | set(xs))
    return {a: {b for b in labs if b != a and uEdge(xs, a, b)} for a in labs}
def cycles(adj, k):
    out = []
    for s in sorted(adj):
        def rec(path):
            if len(path) == k:
                if s in adj[path[-1]] and path[1] < path[-1]:
                    out.append(list(path))
                return
            for y in sorted(adj[path[-1]]):
                if y > s and y not in path:
                    rec(path + [y])
        rec([s])
    return out
def edges(c): return {frozenset((c[i], c[(i + 1) % len(c)])) for i in range(len(c))}
def theta_copy(adj, n, lst):
    labs = sorted(adj)
    nb = [[] for _ in range(n)]
    for a, b in lst:
        nb[a].append(b); nb[b].append(a)
    asg = [None] * n
    def rec(v):
        if v == n: return True
        for x in labs:
            if x in asg[:v]: continue
            if all(asg[u] in adj[x] for u in nb[v] if u < v):
                asg[v] = x
                if rec(v + 1): return True
                asg[v] = None
        return False
    return list(asg) if rec(0) else None
def cert(xs):
    adj = adjOf(xs)
    c3 = cycles(adj, 3)
    if c3: return (4, c3[0], [])
    c4 = cycles(adj, 4)
    if c4: return (5, c4[0], [])
    c6 = cycles(adj, 6)
    for a in c6:
        for b in c6:
            if set(a) & set(b) and edges(a) != edges(b):
                return (6, a, b)
    c8 = cycles(adj, 8)
    for a in c6:
        for b in c8:
            if edges(a) & edges(b):
                return (7, a, b)
    for k in (8, 9, 10):
        n, lst = LTH[k]
        l = theta_copy(adj, n, lst)
        if l is not None:
            return (k, l, [])
    return None
def checkCert(xs, c):
    """Independent re-check of a certificate, mirroring checkCert3."""
    k, a, b = c
    def cycOK(kk, cl):
        return len(cl) == kk and len(set(cl)) == kk and all(used(xs, l) for l in cl) and \
            all(uEdge(xs, cl[i], cl[(i + 1) % kk]) for i in range(kk))
    def sameCEdge(kk, ll, c1, d1, i, j):
        return (c1[i] == d1[j] and c1[(i + 1) % kk] == d1[(j + 1) % ll]) or \
               (c1[i] == d1[(j + 1) % ll] and c1[(i + 1) % kk] == d1[j])
    if k == 4: return cycOK(3, a)
    if k == 5: return cycOK(4, a)
    if k == 6:
        return cycOK(6, a) and cycOK(6, b) and any(l in b for l in a) and \
            any(not any(sameCEdge(6, 6, a, b, i, j) for j in range(6)) for i in range(6))
    if k == 7:
        return cycOK(6, a) and cycOK(8, b) and any(sameCEdge(6, 8, a, b, i, j) for i in range(6) for j in range(8))
    if k in LTH:
        n, lst = LTH[k]
        return len(a) == n and len(set(a)) == n and all(used(xs, l) for l in a) and \
            all(uEdge(xs, a[p], a[q]) for p, q in lst)
    return False

table, stats, nvalid = {}, Counter(), 0
for xs in itertools.product(range(12), repeat=6):
    if not validB(xs):
        continue
    nvalid += 1
    if violB(xs):
        continue
    c = cert(xs)
    assert c is not None, xs
    assert checkCert(xs, c), (xs, c)
    table[xs] = c
    stats[c[0]] += 1
print('valid', nvalid, 'certified', len(table), dict(sorted(stats.items())), file=sys.stderr)
outdir = sys.argv[1]
TRIV = {2: 'viol', 3: 'viol', 7: 'inval', 8: 'inval', 9: 'inval', 10: 'inval', 11: 'inval'}
for x4 in range(12):
    rows = sorted(xs for xs in table if xs[0] == x4)
    if x4 in TRIV:
        assert not rows
        args = ", ".join([str(x4)] + [f"x{i}.val" for i in range(5, 10)])
        L = ["import Thrackle78.Proof.Run3Defs\n",
             f"/-! Generated by `gen_run3_lean.py`: no pattern with `w₄ = {x4}` needs a certificate (" +
             ("the walk repeats a vertex or reverses at once" if TRIV[x4] == 'viol' else "the label is not valid") + "). -/\n",
             "namespace Thrackle78.Proof\n",
             f"/-- The certificate of a pattern `{x4} x5 … x9` (none needed). -/",
             f"def certOf3_{x4} (_x5 _x6 _x7 _x8 _x9 : Fin 12) : ℕ × List ℕ × List ℕ := (0, [], [])\n",
             f"theorem certOf3_ok_{x4} : ∀ x5 x6 x7 x8 x9 : Fin 12,",
             f"    validB3 [{args}] = true →",
             f"    violB3 [{args}] = false →",
             f"    checkCert3 [{args}] (certOf3_{x4} x5 x6 x7 x8 x9) = true := by"]
        if TRIV[x4] == 'viol' and x4 == 2:
            L += ["  intro x5 x6 x7 x8 x9 _ h",
                  f"  have hB : (List.range 10).any (fun t => decide (wlAt3 [{args}] t = wlAt3 [{args}] (t + 2))) = true := rfl",
                  f"  have hv : violB3 [{args}] = true := by unfold violB3; rw [hB]; simp",
                  "  rw [hv] at h",
                  "  exact absurd h (by decide)\n"]
        elif TRIV[x4] == 'viol':
            L += ["  intro x5 x6 x7 x8 x9 _ h",
                  f"  have hv : violB3 [{args}] = true := rfl",
                  "  rw [hv] at h",
                  "  exact absurd h (by decide)\n"]
        else:
            L += ["  intro x5 x6 x7 x8 x9 h",
                  f"  have hv : validB3 [{args}] = false := rfl",
                  "  rw [hv] at h",
                  "  exact absurd h (by decide)\n"]
        L.append("end Thrackle78.Proof")
        open(os.path.join(outdir, f"Run3S{x4}.lean"), "w").write("\n".join(L) + "\n")
        print(x4, 0, file=sys.stderr)
        continue
    L = ["import Thrackle78.Proof.Run3Defs\n",
         f"/-! Generated by `gen_run3_lean.py`: the certificates of the patterns with `w₄ = {x4}`, and their kernel check",
         "(one table and one theorem for each `w₅`). -/\n",
         "namespace Thrackle78.Proof\n"]
    for x5 in range(12):
        sub = [xs for xs in rows if xs[1] == x5]
        L.append("set_option maxHeartbeats 0 in")
        L.append(f"/-- The certificate of a pattern `{x4} {x5} x6 … x9` (the default only for invalid or violated patterns). -/")
        L.append(f"def certOf3_{x4}_{x5} : Fin 12 → Fin 12 → Fin 12 → Fin 12 → ℕ × List ℕ × List ℕ")
        for xs in sub:
            k, a, b = table[xs]
            L.append(f"  | {', '.join(str(x) for x in xs[2:])} => ({k}, {a}, {b})")
        L.append("  | _, _, _, _ => (0, [], [])\n")
        L.append("set_option maxHeartbeats 0 in")
        L.append(f"theorem certOf3_ok_{x4}_{x5} : ∀ x6 x7 x8 x9 : Fin 12,")
        L.append(f"    validB3 [{x4}, {x5}, x6.val, x7.val, x8.val, x9.val] = true →")
        L.append(f"    violB3 [{x4}, {x5}, x6.val, x7.val, x8.val, x9.val] = false →")
        L.append(f"    checkCert3 [{x4}, {x5}, x6.val, x7.val, x8.val, x9.val] (certOf3_{x4}_{x5} x6 x7 x8 x9) = true := by")
        L.append("  decide +kernel\n")
    L.append(f"/-- The certificate of a pattern `{x4} x5 … x9`. -/")
    L.append(f"def certOf3_{x4} (x5 x6 x7 x8 x9 : Fin 12) : ℕ × List ℕ × List ℕ :=")
    L.append("  match x5 with")
    for x5 in range(12):
        L.append(f"  | {x5} => certOf3_{x4}_{x5} x6 x7 x8 x9")
    L.append("")
    L.append(f"theorem certOf3_ok_{x4} : ∀ x5 x6 x7 x8 x9 : Fin 12,")
    L.append(f"    validB3 [{x4}, x5.val, x6.val, x7.val, x8.val, x9.val] = true →")
    L.append(f"    violB3 [{x4}, x5.val, x6.val, x7.val, x8.val, x9.val] = false →")
    L.append(f"    checkCert3 [{x4}, x5.val, x6.val, x7.val, x8.val, x9.val] (certOf3_{x4} x5 x6 x7 x8 x9) = true := by")
    L.append("  intro x5")
    L.append("  fin_cases x5")
    for x5 in range(12):
        L.append(f"  · exact certOf3_ok_{x4}_{x5}")
    L.append("")
    L.append("end Thrackle78.Proof")
    open(os.path.join(outdir, f"Run3S{x4}.lean"), "w").write("\n".join(L) + "\n")
    print(x4, len(rows), file=sys.stderr)
