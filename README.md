# Concrete instantiation of the capability-exposure analysis

Run:

```
python3 demo.py
```

Expected final line:

```
RESULT: all 22 checks passed.
```

The impersonation session prints `accept = 1`, and the exit code is `0`. The
default run takes under a second. Only the Python 3 standard library is used —
no third-party or cryptographic packages. Optional flags `--n`, `--bits` and
`--seed` override the defaults (`16`, `256`, fixed); the default seed makes the
run reproducible.

## What each step checks

The script builds a prime-order subgroup of `Z_p^*` for a safe prime
`p = 2q + 1`, generates a key `(A, B)` as the analyzed key generation does, and
sets `X = A.B`, `pk = g1^x1 . g2^x2`.

Step 2 confirms the serialized state is exactly `3nw` bits. Step 3 issues the
single leakage query the published interface admits and confirms it returns `X`
in exactly `2w` bits. Step 4 compares that width against the nominal leading
term of the advertised allowance; the printed note records that this term
ignores the subtracted `omega(log kappa)` slack and is therefore not the
theorem's exact allowance. Step 5 answers a freshly drawn challenge from the
retained pair and prints the verifier's accept bit. Step 6 confirms no
honest-prover oracle call was made.

Step 7 runs the analyzed key update as a **constraint-faithful implementation of
the printed update equations** — sample `E != 0` and `F` with `E.F = 0`, take a
non-singular `T` with `A.T = E`, set `B' = B + T.F`, then sample `E'`, `F'` the
same way, take a non-singular `T'` with `T'.B' = F'`, and set `A' = A + E'.T'`.
It satisfies every constraint the source states, while adding sampling
conditions for tractability rather than reproducing the source's sampling
distributions; the cross-epoch bridge below depends only on `A.T = E` and
`E.F = 0`, so it is unaffected by that difference. Step 7 checks the update's
defining equations, that `A'B' = A.B` with `pk` unchanged, and that the stored
length is preserved — the three observations the accompanying paper reports as
one combined table row — and confirms the pair retained beforehand still
authenticates. It then checks the **cross-epoch bridge**: the pre-update `A`
multiplied by the refreshed `B` is still `X`.

Step 8 runs the full cross-epoch chain, one pair-valued query per round. In
round `i` the pair `(f_A, z_B)` returns `A_i`; the update then runs; in round
`i+1` the pair `(z_A, f_B,alpha)` reads **only the refreshed `B`**, with
`alpha = A_i` hardwired into the second function's description rather than read
from `B`, and its output is `X`. Both output lengths are measured by the code
and checked against `nw + 1` and `2w + 1`. The recovered pair then authenticates
on a fresh challenge.

Step 9 recovers the
same pair through two
component-local queries totalling exactly `(n+2)w + 2` bits. Step 10 confirms an
incorrect pair is rejected, so the check in step 5 is not vacuous. Step 11
prints the analyzed article's identifiers, hash, and page locators.

## Scope

These checks cover the finite, mechanically verifiable layer only. The script
computes no discrete logarithm, performs no rewinding, establishes no theorem,
and measures no timing. The analytical arguments live in the accompanying
paper, not here.

## The analyzed article

`sources.json` identifies the analyzed article by title, venue, DOI, SHA-256,
and page locators. The article itself is not redistributed here.

## License

MIT. See `LICENSE`.
