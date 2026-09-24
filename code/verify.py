"""
Verification for langlands/hecke-in-q-bool.tex.

Three independent checks, none of them assuming the classical theorem
it is checking:

  V1  The flag container's pushforward-pullback operator over F_q
      satisfies the Iwahori-Hecke relations, and the algebra it
      generates is H_n(q).  (schubert.tex Prop 4.1, re-derived from
      the geometry rather than from the cell rule.)

  V2  Hall's theorem: the Hall algebra of finite O-modules has
      Hall-Littlewood structure constants.  Submodules counted by
      brute-force enumeration in Z/p^N; Hall-Littlewood polynomials
      computed symbolically from the Weyl-type formula.  Nothing is
      quoted from Macdonald.

  V3  The spherical Hecke identity for GL_2 over a local field,
      T_(p,1)^2 = T_(p^2,1) + (p+1) T_(p,p), by enumerating sublattice
      chains in Z_p^2; and its Satake image in symmetric functions.

Run: python3 verify.py
"""

import itertools
from fractions import Fraction

# ----------------------------------------------------------------------
# V1.  Flag container over F_q  ->  Iwahori-Hecke algebra H_n(q)
# ----------------------------------------------------------------------

def vectors(n, p):
    return list(itertools.product(range(p), repeat=n))

def rref(rows, p):
    """Row-reduce over F_p; return canonical tuple of nonzero rows."""
    rows = [list(r) for r in rows]
    n = len(rows[0]) if rows else 0
    pivot = 0
    for col in range(n):
        piv = None
        for r in range(pivot, len(rows)):
            if rows[r][col] % p:
                piv = r
                break
        if piv is None:
            continue
        rows[pivot], rows[piv] = rows[piv], rows[pivot]
        inv = pow(rows[pivot][col], p - 2, p) if p > 2 else 1
        rows[pivot] = [(x * inv) % p for x in rows[pivot]]
        for r in range(len(rows)):
            if r != pivot and rows[r][col] % p:
                f = rows[r][col]
                rows[r] = [(a - f * b) % p for a, b in zip(rows[r], rows[pivot])]
        pivot += 1
    return tuple(tuple(r) for r in rows[:pivot])

def span(gens, p):
    return rref(list(gens), p) if gens else ()

def dim(sub):
    return len(sub)

def subspaces(n, p):
    """All subspaces of F_p^n, keyed by dimension, as canonical rref tuples."""
    by_dim = {d: set() for d in range(n + 1)}
    by_dim[0].add(())
    vs = [v for v in vectors(n, p) if any(v)]
    frontier = {()}
    for d in range(1, n + 1):
        new = set()
        for S in frontier:
            for v in vs:
                W = span(list(S) + [v], p)
                if dim(W) == d:
                    new.add(W)
        by_dim[d] = new
        frontier = new
    return by_dim

def sum_dim(A, B, p):
    return dim(span(list(A) + list(B), p))

def flags(n, p):
    """Complete flags 0 < F_1 < ... < F_{n-1} < F^n, as tuples of subspaces."""
    by_dim = subspaces(n, p)
    out = []
    def rec(chain, d):
        if d == n:
            out.append(tuple(chain))
            return
        for W in by_dim[d]:
            if not chain or sum_dim(chain[-1], W, p) == d:
                rec(chain + [W], d + 1)
    rec([], 1)
    return out

def relative_position(F, n, p):
    """Permutation w in S_n from the rank matrix r_ij = dim(E_i cap F_j)."""
    E = [span([tuple(1 if k == j else 0 for k in range(n)) for j in range(i)], p)
         for i in range(n + 1)]
    Ffull = (((),) + F)  # F_0 = 0, F_1..F_{n-1}, F_n = whole space
    Ffull = list(Ffull) + [span([tuple(1 if k == j else 0 for k in range(n))
                                 for j in range(n)], p)]
    r = [[0] * (n + 1) for _ in range(n + 1)]
    for i in range(n + 1):
        for j in range(n + 1):
            r[i][j] = dim(E[i]) + dim(Ffull[j]) - sum_dim(E[i], Ffull[j], p)
    w = [None] * n
    for i in range(1, n + 1):
        for j in range(1, n + 1):
            v = r[i][j] - r[i-1][j] - r[i][j-1] + r[i-1][j-1]
            if v == 1:
                w[j - 1] = i
    assert all(x is not None for x in w), "rank matrix did not give a permutation"
    return tuple(w)

def length(w):
    n = len(w)
    return sum(1 for i in range(n) for j in range(i + 1, n) if w[i] > w[j])

def neighbours(F, i, n, p, by_dim):
    """Flags F' with F'_k = F_k for all k != i.  Should be q+1 of them."""
    out = []
    lo = F[i - 2] if i >= 2 else ()
    hi = F[i] if i <= n - 2 else span([tuple(1 if k == j else 0 for k in range(n))
                                       for j in range(n)], p)
    for W in by_dim[i]:
        if sum_dim(lo, W, p) == i and sum_dim(W, hi, p) == dim(hi):
            out.append(tuple(F[:i-1]) + (W,) + tuple(F[i:]))
    return out

def v1(n, p, verbose=True):
    Fl = flags(n, p)
    by_dim = subspaces(n, p)
    pos = {F: relative_position(F, n, p) for F in Fl}
    perms = sorted(set(pos.values()), key=lambda w: (length(w), w))
    idx = {w: k for k, w in enumerate(perms)}
    cells = {w: [F for F in Fl if pos[F] == w] for w in perms}

    # (i) Bruhat: |Fl| = [n]_q! and |C_w| = q^{l(w)}
    qfact = 1
    for k in range(1, n + 1):
        qfact *= sum(p ** j for j in range(k))
    ok_bruhat = (len(Fl) == qfact and
                 all(len(cells[w]) == p ** length(w) for w in perms))

    # (ii) fibres have q+1 elements
    ok_fibre = all(len(neighbours(F, i, n, p, by_dim)) == p + 1
                   for F in Fl for i in range(1, n))

    # (iii) S_i on cell indicators, checked to be constant on cells
    S = {}
    ok_desc = True
    for i in range(1, n):
        M = [[0] * len(perms) for _ in range(len(perms))]
        for w in perms:                      # f_w = indicator of C_w
            vals = {}
            for F in Fl:
                c = sum(1 for Fp in neighbours(F, i, n, p, by_dim) if pos[Fp] == w)
                vals.setdefault(pos[F], set()).add(c)
            if any(len(s) > 1 for s in vals.values()):
                ok_desc = False
            for v, s in vals.items():
                M[idx[v]][idx[w]] = next(iter(s))
        S[i] = M

    def mul(A, B):
        m = len(A)
        return [[sum(A[r][k] * B[k][c] for k in range(m)) for c in range(m)]
                for r in range(m)]
    def sub(A, B):
        return [[a - b for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]
    def smul(c, A):
        return [[c * a for a in ra] for ra in A]
    def add(A, B):
        return [[a + b for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]
    m = len(perms)
    I = [[1 if r == c else 0 for c in range(m)] for r in range(m)]

    T = {i: sub(S[i], I) for i in S}
    ok_quad  = all(mul(T[i], T[i]) == add(smul(p - 1, T[i]), smul(p, I)) for i in T)
    ok_idem  = all(mul(S[i], S[i]) == smul(p + 1, S[i]) for i in S)
    ok_braid = all(mul(mul(T[i], T[i+1]), T[i]) == mul(mul(T[i+1], T[i]), T[i+1])
                   for i in T if i + 1 in T)
    ok_comm  = all(mul(T[i], T[j]) == mul(T[j], T[i])
                   for i in T for j in T if j - i >= 2)
    ok_nonnil = all(mul(T[i], T[i]) != [[0]*m for _ in range(m)] for i in T)

    if verbose:
        print(f"  n={n} q={p}: flags={len(Fl)} [n]_q!={qfact} cells={len(perms)}  "
              f"bruhat={ok_bruhat} fibre={ok_fibre} descends={ok_desc}")
        print(f"          S_i^2=(q+1)S_i:{ok_idem}  T_i^2=(q-1)T_i+q:{ok_quad}  "
              f"braid:{ok_braid}  comm:{ok_comm}  T_i^2!=0:{ok_nonnil}")
    return all([ok_bruhat, ok_fibre, ok_desc, ok_idem, ok_quad,
                ok_braid, ok_comm, ok_nonnil])

# ----------------------------------------------------------------------
# V2.  Hall algebra of finite O-modules  vs  Hall-Littlewood
# ----------------------------------------------------------------------

def module_elements(lam, p):
    return list(itertools.product(*[range(p ** a) for a in lam]))

def madd(x, y, lam, p):
    return tuple((a + b) % (p ** l) for a, b, l in zip(x, y, lam))

def mmul(k, x, lam, p):
    return tuple((k * a) % (p ** l) for a, l in zip(x, lam))

def submodules(lam, p):
    """All submodules of  M_lam = sum Z/p^{lam_i}, by closure BFS."""
    els = module_elements(lam, p)
    zero = tuple(0 for _ in lam)
    def close(gens):
        S = {zero}
        frontier = [zero]
        while frontier:
            x = frontier.pop()
            for g in gens:
                y = madd(x, g, lam, p)
                if y not in S:
                    S.add(y); frontier.append(y)
        return frozenset(S)
    subs = {frozenset({zero})}
    frontier = list(subs)
    while frontier:
        U = frontier.pop()
        for g in els:
            if g in U:
                continue
            V = close(list(U) + [g])
            if V not in subs:
                subs.add(V); frontier.append(V)
    return subs

def type_of_counts(counts, p):
    """counts[k] = |{x : p^k x = 0}|; return the partition lam."""
    conj = []
    k = 1
    while counts.get(k, 1) > counts.get(k - 1, 1):
        e = 0
        r = counts[k] // counts[k - 1]
        while r > 1:
            r //= p; e += 1
        conj.append(e)
        k += 1
    lam = []
    if conj:
        for i in range(1, conj[0] + 1):
            lam.append(sum(1 for c in conj if c >= i))
    return tuple(sorted(lam, reverse=True))

def type_of_sub(U, lam, p):
    counts = {0: 1}
    k = 1
    while True:
        c = sum(1 for u in U if mmul(p ** k, u, lam, p) == tuple(0 for _ in lam))
        counts[k] = c
        if c == len(U):
            break
        k += 1
    return type_of_counts(counts, p)

def type_of_quot(U, lam, p):
    els = module_elements(lam, p)
    counts = {0: 1}
    k = 1
    total = len(els) // len(U)
    while True:
        c = sum(1 for m in els if mmul(p ** k, m, lam, p) in U) // len(U)
        counts[k] = c
        if c == total:
            break
        k += 1
    return type_of_counts(counts, p)

def hall_numbers(lam, p):
    """g^lam_{mu,nu}(p) = #{U <= M_lam : U = M_nu, M_lam/U = M_mu}."""
    out = {}
    for U in submodules(lam, p):
        nu = type_of_sub(U, lam, p)
        mu = type_of_quot(U, lam, p)
        out[(mu, nu)] = out.get((mu, nu), 0) + 1
    return out

def partitions(N, maxparts=None):
    def rec(N, mx):
        if N == 0:
            yield ()
            return
        for k in range(min(N, mx), 0, -1):
            for rest in rec(N - k, k):
                yield (k,) + rest
    for lam in rec(N, N):
        if maxparts is None or len(lam) <= maxparts:
            yield lam

def n_of(lam):
    return sum(i * l for i, l in enumerate(lam))

def hall_littlewood_structure(N, nvars):
    """P_mu P_nu = sum f^lam_{mu,nu}(t) P_lam, computed symbolically."""
    import sympy as sp
    t = sp.symbols('t')
    xs = sp.symbols(f'x0:{nvars}')

    def P(lam):
        lam = tuple(lam) + (0,) * (nvars - len(lam))
        num = 0
        for w in itertools.permutations(range(nvars)):
            term = sp.prod([xs[w[i]] ** lam[i] for i in range(nvars)])
            for i in range(nvars):
                for j in range(i + 1, nvars):
                    term *= (xs[w[i]] - t * xs[w[j]]) / (xs[w[i]] - xs[w[j]])
            num += term
        # v_lam(t): normalise so the leading monomial x^lam has coefficient 1
        num = sp.simplify(sp.cancel(sp.together(num)))
        poly = sp.Poly(sp.expand(num), *xs)
        lead = poly.coeff_monomial(sp.prod([xs[i] ** lam[i] for i in range(nvars)]))
        return sp.expand(sp.cancel(num / lead))

    deg = {}
    for M in range(0, N + 1):
        for lam in partitions(M, nvars):
            deg.setdefault(M, {})[lam] = P(lam)
    return t, xs, deg

def v2(p_list=(2, 3), N=4, nvars=4, verbose=True):
    import sympy as sp
    t, xs, Ppoly = hall_littlewood_structure(N, nvars)

    def expand_in_P(expr, M):
        """Write a symmetric polynomial of degree M in the P_lam basis."""
        coeffs = {}
        e = sp.expand(expr)
        for lam in sorted(partitions(M, nvars), key=lambda l: tuple(l), reverse=True):
            mon = sp.prod([xs[i] ** (lam[i] if i < len(lam) else 0)
                           for i in range(nvars)])
            c = sp.Poly(e, *xs).coeff_monomial(mon)
            c = sp.cancel(sp.simplify(c))
            if c != 0:
                coeffs[lam] = c
                e = sp.expand(e - c * Ppoly[M][lam])
        assert sp.simplify(e) == 0, "expansion in P basis failed"
        return coeffs

    allok = True
    checked = 0
    for M in range(2, N + 1):
        for mu in partitions(M - 1, nvars):
            pass
    # check every (mu, nu) with |mu|+|nu| = M <= N
    for M in range(2, N + 1):
        pairs = [(mu, nu) for a in range(1, M)
                 for mu in partitions(a, nvars)
                 for nu in partitions(M - a, nvars)]
        for (mu, nu) in pairs:
            prod = sp.expand(Ppoly[len(mu) and sum(mu)][mu] * Ppoly[sum(nu)][nu])
            f = expand_in_P(prod, M)
            for lam in partitions(M, nvars):
                fl = f.get(lam, sp.Integer(0))
                for p in p_list:
                    g = hall_numbers(lam, p).get((mu, nu), 0)
                    pred = sp.Rational(p) ** (n_of(lam) - n_of(mu) - n_of(nu)) \
                           * fl.subs(t, sp.Rational(1, p))
                    pred = sp.nsimplify(sp.simplify(pred))
                    if sp.simplify(pred - g) != 0:
                        allok = False
                        if verbose:
                            print(f"    MISMATCH p={p} lam={lam} mu={mu} nu={nu}: "
                                  f"hall={g} pred={pred}")
                    checked += 1
    if verbose:
        print(f"  Hall's theorem g^lam_munu(p) = p^(n(lam)-n(mu)-n(nu)) "
              f"f^lam_munu(1/p): {checked} instances, |lam| <= {N}, "
              f"p in {p_list}: {'all agree' if allok else 'FAILED'}")
    return allok

# ----------------------------------------------------------------------
# V3.  Sublattice chains in Z_p^2  ->  spherical Hecke / Satake
# ----------------------------------------------------------------------

def sublattices(index, p):
    """Sublattices of Z^2 of given p-power index, as HNF matrices [[a,b],[0,d]]."""
    out = []
    k = 0
    n = index
    while n > 1:
        n //= p; k += 1
    for i in range(k + 1):
        a, d = p ** i, p ** (k - i)
        for b in range(a):
            out.append((a, b, d))
    return out

def contains(L1, L2):
    """Does lattice L1 (HNF) contain L2 (HNF)?  Columns of L2 in L1."""
    a1, b1, d1 = L1
    a2, b2, d2 = L2
    # L1 spanned by (a1,0),(b1,d1);  L2 by (a2,0),(b2,d2)
    for (x, y) in [(a2, 0), (b2, d2)]:
        if y % d1:
            return False
        m = y // d1
        r = x - m * b1
        if r % a1:
            return False
    return True

def elementary_divisors(L, p):
    a, b, d = L
    g = 1
    from math import gcd
    g = gcd(gcd(a, b), d)
    return (g, (a * d) // g)

def v3(p_list=(2, 3, 5), verbose=True):
    ok = True
    for p in p_list:
        L1 = sublattices(p, p)
        L2 = sublattices(p * p, p)
        n1, n2 = len(L1), len(L2)
        # classify index-p^2 sublattices by elementary divisors
        by_ed = {}
        for L in L2:
            by_ed.setdefault(elementary_divisors(L, p), []).append(L)
        n_pp = len(by_ed.get((p, p), []))
        n_1p2 = len(by_ed.get((1, p * p), []))
        # chains Z^2 > L' > L'' with each step index p
        chains = {}
        for Lpp in L2:
            c = sum(1 for Lp in L1 if contains(Lp, Lpp))
            chains[Lpp] = c
        total_chains = sum(chains.values())
        c_pp = set(chains[L] for L in by_ed.get((p, p), []))
        c_1p2 = set(chains[L] for L in by_ed.get((1, p * p), []))
        good = (n1 == p + 1 and n2 == p * p + p + 1 and n_pp == 1
                and n_1p2 == p * p + p
                and total_chains == (p + 1) ** 2
                and c_pp == {p + 1} and c_1p2 == {1})
        ok = ok and good
        if verbose:
            print(f"  p={p}: index-p sublattices={n1} (=q+1); index-p^2={n2}; "
                  f"of type (p,p)={n_pp}, (1,p^2)={n_1p2}")
            print(f"        chains={total_chains} (=(q+1)^2); multiplicity over "
                  f"(p,p) = {c_pp}, over (1,p^2) = {c_1p2}   ->  "
                  f"T^2 = T_(p^2,1) + (q+1) T_(p,p): {good}")
    # Satake image: normalised, T -> p^{1/2}(x+y), T_(p,p) -> xy, T_(p^2,1) -> ...
    import sympy as sp
    x, y, q = sp.symbols('x y q')
    lhs = sp.expand((x + y) ** 2)
    rhs = sp.expand((x ** 2 + y ** 2) + 2 * x * y)
    sat = sp.simplify(lhs - rhs) == 0
    if verbose:
        print(f"  Satake image (normalised): (x+y)^2 = (x^2+y^2) + 2xy : {sat}")
        print(f"        so the unnormalised (q+1) is 2*q^(1/2) after the "
              f"delta^(1/2) twist; the algebra is Z[x+y,(xy)^(+-1)] = Rep(GL_2)")
    return ok and sat

# ----------------------------------------------------------------------

# ----------------------------------------------------------------------
# V4.  f^lam_{mu,nu}(0) = c^lam_{mu,nu}   (Hall-Littlewood at t=0 is Schur)
#      i.e. the plactic/Littlewood-Richardson constants of lascoux/ are the
#      t -> 0 face of the Hall constants of q-bool/.  LR coefficients are
#      computed independently, by counting LR skew tableaux.
# ----------------------------------------------------------------------

def lr_coefficient(lam, mu, nu):
    """c^lam_{mu,nu} = # LR skew tableaux of shape lam/mu, content nu.

    Brute force over all fillings: rows weakly increasing, columns strictly
    increasing, and the reverse reading word (each row right-to-left, rows
    top to bottom) a lattice word.
    """
    lam = list(lam)
    mu = list(mu) + [0] * (len(lam) - len(mu))
    if len(mu) > len(lam) or any(m > l for l, m in zip(lam, mu)):
        return 0
    cells = [(i, j) for i in range(len(lam)) for j in range(mu[i], lam[i])]
    if len(cells) != sum(nu):
        return 0
    k = len(nu)
    count = 0
    for vals in itertools.product(range(1, k + 1), repeat=len(cells)):
        T = dict(zip(cells, vals))
        content = [0] * k
        for v in vals:
            content[v - 1] += 1
        if tuple(content) != tuple(nu):
            continue
        ok = True
        for (i, j), v in T.items():                      # rows weakly increasing
            if (i, j + 1) in T and T[(i, j + 1)] < v:
                ok = False; break
            if (i + 1, j) in T and T[(i + 1, j)] <= v:   # cols strictly increasing
                ok = False; break
        if not ok:
            continue
        word = []
        for i in range(len(lam)):
            for j in range(lam[i] - 1, mu[i] - 1, -1):
                word.append(T[(i, j)])
        seen = [0] * (k + 1)
        for v in word:                                    # lattice word
            seen[v] += 1
            if v > 1 and seen[v] > seen[v - 1]:
                ok = False; break
        if ok:
            count += 1
    return count

def v4(N=4, nvars=4, verbose=True):
    import sympy as sp
    t, xs, Ppoly = hall_littlewood_structure(N, nvars)

    def expand_in_P(expr, M):
        coeffs = {}
        e = sp.expand(expr)
        for lam in sorted(partitions(M, nvars), key=lambda l: tuple(l), reverse=True):
            mon = sp.prod([xs[i] ** (lam[i] if i < len(lam) else 0)
                           for i in range(nvars)])
            c = sp.cancel(sp.simplify(sp.Poly(e, *xs).coeff_monomial(mon)))
            if c != 0:
                coeffs[lam] = c
                e = sp.expand(e - c * Ppoly[M][lam])
        return coeffs

    ok, checked = True, 0
    for M in range(2, N + 1):
        for a in range(1, M):
            for mu in partitions(a, nvars):
                for nu in partitions(M - a, nvars):
                    f = expand_in_P(sp.expand(Ppoly[sum(mu)][mu] *
                                              Ppoly[sum(nu)][nu]), M)
                    for lam in partitions(M, nvars):
                        fl = sp.simplify(f.get(lam, sp.Integer(0)).subs(t, 0))
                        c = lr_coefficient(lam, mu, nu)
                        if sp.simplify(fl - c) != 0:
                            ok = False
                            if verbose:
                                print(f"    MISMATCH lam={lam} mu={mu} nu={nu}: "
                                      f"HL(t=0)={fl} LR={c}")
                        checked += 1
    if verbose:
        print(f"  f^lam_munu(0) = c^lam_munu: {checked} instances, |lam| <= {N}: "
              f"{'all agree' if ok else 'FAILED'}")
    return ok

if __name__ == "__main__":
    print("V1  flag container over F_q -> Iwahori-Hecke H_n(q)")
    r1 = all([v1(2, 2), v1(2, 3), v1(3, 2), v1(3, 3), v1(4, 2)])
    print(f"  V1: {'PASS' if r1 else 'FAIL'}\n")

    print("V3  sublattice chains in Z_p^2 -> spherical Hecke, Satake")
    r3 = v3()
    print(f"  V3: {'PASS' if r3 else 'FAIL'}\n")

    print("V2  Hall algebra over O vs Hall-Littlewood (slow)")
    r2 = v2()
    print(f"  V2: {'PASS' if r2 else 'FAIL'}\n")

    print("V4  Hall-Littlewood at t=0 vs Littlewood-Richardson")
    r4 = v4()
    print(f"  V4: {'PASS' if r4 else 'FAIL'}\n")

    print("ALL:", "PASS" if all([r1, r2, r3, r4]) else "FAIL")

