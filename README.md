# langlands

What `~/git/q-bool` and `~/git/lascoux` already contain of the Langlands
programme, and what they do not.

Speculative in places, but the central observation is not: the operator
built in `q-bool/schubert.pdf` from a fibration of flag varieties **is**
the Iwahori–Hecke generator, and the relations verified there are a
presentation of H_n(q).

## Read

| File | What |
|------|------|
| `hecke-in-q-bool.pdf` | **The document.** Ten links, sixteen ledger rows, four verifications, and a section on what does not link |
| `code/verify.py` | The four computations. `python3 code/verify.py`, about two minutes |

## The four verifications

Each is independent of the theorem it checks — no result is quoted from
Macdonald, and V1 shares no code with `q-bool/code/flag.py`.

| | Claim | Scope |
|---|---|---|
| V1 | The flag container's pushforward–pullback operator satisfies the Iwahori–Hecke relations | (n,q) ∈ {(2,2),(2,3),(3,2),(3,3),(4,2)}; 315 flags, 24 cells in the largest |
| V2 | Hall's theorem: g^λ_μν(p) = p^(n(λ)−n(μ)−n(ν)) f^λ_μν(1/p) | 128 instances, \|λ\| ≤ 4, p ∈ {2,3} |
| V3 | T²_(p,1) = T_(p²,1) + (q+1)T_(p,p) by enumerating sublattice chains in ℤ_p², and its Satake image | p ∈ {2,3,5} |
| V4 | f^λ_μν(0) = c^λ_μν — the plactic constants are the Hall constants at t=0 | 64 instances, \|λ\| ≤ 4 |

V4 is the only statement joining the two source repositories to each
other rather than to Langlands.

## Headline claims

1. `schubert.pdf` constructs the Iwahori–Hecke algebra H_n(q); by
   Iwahori's theorem it is End_G(Ind_B^G 1). **Classical, proved in §3.**
2. Its refuted nilCoxeter conjecture's true target is the **Grothendieck
   polynomials of Lascoux–Schützenberger** — the K-theoretic basis, which
   is what point-counting sees. Its Question 5.2 is the Kostant–Kumar
   nilHecke ring, and is not open.
3. The Langlands dual group is the Bernstein centre of the **affine**
   Hecke algebra. `q-bool` is at 𝒪 in one document and 𝔽_q in another
   and has not joined them. §5 proposes the affine flag container.
4. `q-container.pdf` §9's Hall constants are Hall–Littlewood (verified),
   and **Macdonald Chapter V** identifies that algebra with the spherical
   Hecke algebra of GL_n over a local field, hence with Rep(ᴸGL_n).
   One chapter away.
5. The two-parameter Macdonald ceiling is the **loop direction** —
   Cherednik's DAHA, where t is the field size and q is loop rotation.
   Same gap as `lascoux`'s LLT gap (claimed, unproved).

## Build

    tectonic hecke-in-q-bool.tex
    python3 code/verify.py

## Sources

`~/git/q-bool` (`schubert`, `q-container`, `q-dirichlet`,
`finite-field-duality`), `~/git/lascoux` (`lascoux-container`,
`lenses-in-my-thesis2`). Neither is vendored here.
