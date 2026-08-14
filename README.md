# Concrete instantiation of the capability-exposure analysis

Run:

```
python3 demo.py
```

Expected final line:

```
RESULT: all 17 checks passed.
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
honest-prover oracle call was made. Step 7 runs the analyzed key update exactly
as the source prints it — sample `E != 0` and `F` with `E.F = 0`, take a
non-singular `T` with `A.T = E`, set `B' = B + T.F`, then sample `E'`, `F'` the
same way, take a non-singular `T'` with `T'.B' = F'`, and set `A' = A + E'.T'`
— checks its defining equations and that `A'B' = A.B` with `pk` unchanged, and
confirms the pair retained beforehand still authenticates. Step 8 recovers the
same pair through two
component-local queries totalling exactly `(n+2)w + 2` bits. Step 9 confirms an
incorrect pair is rejected, so the check in step 5 is not vacuous. Step 10
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
