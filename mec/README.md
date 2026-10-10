# MEC session attacks: offline reproduction

This directory reproduces, on concrete parameters, the two session attacks on the
mobile-edge-computing (MEC) procedure of CLR-IA that the accompanying paper derives
in main-paper Section VII (Propositions 15 and 16) and Supplement S6. The runs are
execution witnesses for that algebra. They are not proofs, and they are not covered
by the Lean development in `../lean/`.

## What is checked

The procedure is the four-message flow printed in CLR-IA, Section VI-A.3, printed
pp. 5629–5630:

```
M1 = (idU, Ru1, Ru2, Ti)
M2 = (idS, Rs1, Rs2, cS, Tj)
M3 = (idU, vu1, vu2, cU, Ti_prime)
M4 = (idS, vs1, vs2, Tj_prime)
```

- **Literal checks.** Both printed verification equations use `g1` as the second
  base. For an honest response the literal check holds exactly when
  `(g1/g2)^v2 = 1`, so with distinct generators honest sessions generally fail. The
  run evaluates both literal equations diagnostically.
- **Corrected reading.** Only those two bases are replaced by `g2`. Honest sessions
  then complete and both parties derive equal keys.
- **New-session impersonation (Proposition 15).** A separate adversary process that
  holds a registered party's actual product `X = AB` is accepted in either role and
  derives the honest peer's session key, before and after successful printed
  Updates.
- **Recovery of recorded session keys (Proposition 16).** From a completed honest
  transcript and one party's later complete key, the adversary recovers the
  historical exponents `r_hat = v - cX` and the session key. The strengthened
  version uses only the `2w`-bit product output of one whole-key leakage query,
  allowed exactly when `b0 + 2w + iota <= lambda` (Supplement S6-D). Checks occur
  in the order commitments, exponents, both DH inputs, key.
- **Controls.** Another representation `W != X` of the same public key passes a
  corrected authentication check but fails recovery; an incorrect product is
  rejected; expired messages are rejected; over-budget queries are refused before
  the leakage function is called and consume no budget.

## Conventions

All challenges and ephemerals are sampled in `Zq*`. Freshness is
`0 <= now - timestamp <= 30` in synthetic integer seconds; no general
replay-resistance claim is made. Identities are fixed test strings. `H` is SHA-256
of the ASCII canonical JSON array `[idU, idS, DH1, DH2]`; this encoding claims no
property beyond the source's one-way requirement.

The world reuses `../demo.py` unchanged for the safe-prime subgroup, state
serialization, the leakage function `f_AB` and the constrained Update sampler. The
sampler satisfies the printed update equations but **does not reproduce the source's
unspecified sampling distribution**; every constraint, the product and the public key
are checked after each successful Update, and failures are recorded. The 256-bit
subgroup fixes the group order and encoding width; it is not a security benchmark.
Probable primes use the artifact's Miller–Rabin routine, not a primality certificate.

For the alternative representation, the world draws `g1` with the artifact routine
and `alpha` uniformly in `Zq*`, sets `g2 = g1^alpha` and constructs
`W = (x1 + alpha, x2 - 1)`. The relation `alpha` stays in the world; finding `W` from
a public key is not an attacker premise. KeyGen samples a nonzero `A` and a uniform
`B`, as printed, without resampling zero coordinates of `X`.

## Data flow

`world.py` holds the keys, seeds, honest ephemerals, historical keys and Update
witnesses. `adversary.py` runs as a separate process with `python -I -S -B -u`, an
empty temporary working directory and a minimal environment, and receives only the
inputs of the corresponding proposition:

| Case | Inputs |
|---|---|
| Impersonation | public parameters, identities and public keys; the retained product `X`; its own timestamp and the synthetic clock |
| Recovery, main | public parameters and the four public messages; the later complete key `(A, B)` |
| Recovery, strengthened | the same public inputs; only the `2w`-bit leakage output |
| Recovery, controls | the same public inputs; the stated `W` or incorrect product |

No world seed, historical key, world state or honest ephemeral is an input. The
adversary records Python `open` audit events after its start; this covers neither
interpreter startup nor all native accesses. The arrangement is a separate-process
data flow, **not a sandbox**.

## Run

Python 3.9 or newer, standard library only, no network. From the repository root:

```
python -B mec/run_local.py
```

On Windows you can instead double-click `mec/RUN_MEC_H.cmd`. Defaults: 256-bit
subgroup, `n = 16`, seed `20261009`, `b0 = 7`. For a quick toy run use
`--bits 32`.

Each run writes a new pair `mec/records/mec_h1h2_user_<UTC time>_<id>.json` and
`.log`; existing records are never overwritten. The launcher prints
`RESULT: PASS` when the run exits normally and every recorded check passes. At the
defaults the record contains 197 checks, 30 adversary processes, 18 successful
Updates, 10 impersonation cases and 20 recovery cases. World-side values are
determined by the seed; the impersonation adversary draws its own ephemerals with
`SystemRandom`, so those values differ between runs.

## Records

`mec/records/` holds the public run record. Before the record is written, local path
prefixes are replaced by `<artifact>` (repository root), `<tmp>` (temporary
directory), `<python>` (Python installation) and `<home>` (user home); nothing else
is changed, and all checks are evaluated before this step.

The two records reviewed for the paper were produced by the same protocol, oracle,
check and adversary code before the input/output changes described at the top of
`world.py`. They contain local paths and private repository state and are kept in the
authors' private repository; their SHA-256 values are:

```
2b08bd5dc7d5a9cf80dd07ad00f196bc5c63bb51e17865e6d0826d86f75e7f68  mec_h1h2_final.json
ff8b2bf596d7bfdd7dc8bbe269c96b773122e2d6136f199832eb157002c4090b  mec_h1h2_user_20261009T133056599392Z_ab95c7de.json
```

Both report 197 of 197 checks passing.
