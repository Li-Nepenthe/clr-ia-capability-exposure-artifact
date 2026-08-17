# Artifact Update Report

Per `artifact-update-spec.md`. Artifact repo
`Li-Nepenthe/clr-ia-capability-exposure-artifact`, branch
`agent/cross-epoch-checks`, commit `108b4e3`.

**Status at the time of writing: §1 and §2 complete and verified. §3 and §4 NOT
done — see §5.6.** §3 (Zenodo re-release) requires access I do not have, and §4
is gated on §3 by the spec's own closing rule. One version-numbering conflict
was found and is reported rather than resolved unilaterally.

> **Superseded in part.** Everything §5.4, §5.5 and §5.6 list as outstanding has
> since been completed. The body below is left unedited as the record of that
> round; see [Resolution](#resolution) at the end for the current state.

---

## 5.1 Raw output of the new checks

Complete run, `python3 demo.py`, default parameters `n = 16`, `bits = 256`,
fixed seed. Exit code `0`.

```
[7] The same retained pair after the source's key update
    Update as printed in the source: B' = B + T.F, A' = A + E'.T'
    [ok  ] A6a : the update preserves the decoded pair and the public key -- A'.B' = A.B and pk unchanged
    [ok  ] A6b : the stored key actually changed -- sk' != sk
    [ok  ] A6c : the stored key keeps its length -- |sk'| = |sk| = 12288 bits
    [ok  ] A6d : the update's own constraints hold: E.F = 0 and E'.F' = 0 -- both leakage-free products vanish
    [ok  ] A6e : T and T' are non-singular -- both inverses exist over Z_q
    [ok  ] A6f : the update's defining equations hold: A.T = E and T'.B' = F' -- both verified directly
    [ok  ] A6g : the pair retained before the update still authenticates -- accept = 1
    [ok  ] A6h : the cross-epoch bridge: old A times refreshed B is still X -- A_i . B_(i+1) = X

[8] Cross-epoch capability exposure (R3), one query per round
    round i   (f_A, z_B) -> A_i     : 4097 bits
    [ok  ] A9a : round i output is exactly nw + 1 bits -- 4097 bits = 16*256 + 1
    round i+1 (z_A, f_B,alpha) -> X : 513 bits
    [ok  ] A9b : round i+1 output is exactly 2w + 1 bits -- 513 bits = 2*256 + 1
    [ok  ] A9c : the round i+1 output equals X, read from the refreshed B -- recovered X from B_(i+1)
    [ok  ] A9d : the cross-epoch pair authenticates on a fresh challenge -- accept = 1
    total across the two rounds     : 4610 bits

[9] Two component-local queries (R2)
    query 1 (f_A, z_B) returns A  : 4097 bits = nw + 1
    query 2 (z_A, f_B) returns X  : 513 bits = 1 + 2w
    [ok  ] A7a : two queries total exactly (n+2)w + 2 bits -- 4610 bits = (16+2)*256 + 2
    [ok  ] A7b : the pair recovered by the two queries equals the R1 result -- same X as step 3

[10] Negative control
    [ok  ] A8 : a session driven from an incorrect pair is rejected -- accept = 0

========================================================================
RESULT: all 22 checks passed.
```

Every item §5.1 requires is visible above:

| Required | Where |
|---|---|
| `A_i · B_{i+1} == X` assertion passes | `A6h` |
| round *i* measured output length = 4097 | step 8, first line and `A9a` |
| round *i+1* measured output length = 513 | step 8, third line and `A9b` |
| round *i+1* value equals `X` | `A9c` |
| impersonation `accept = 1` | `A9d` |

**The two lengths are measured, not hardcoded.** The code computes
`len(r_i_a) + len(r_i_b)` and `len(r_j_a) + len(r_j_b)` and only then compares
against the formulas `n*w + 1` and `2*w + 1`.

**`alpha` never reads `B`.** It is derived from round *i*'s output and passed as
the hardwired parameter of `f_B_with_hardwired_A(B2, alpha, w, q)`, whose only
data input is `B2`. The second round reads the **refreshed** `B2`, not `B`.

---

## 5.2 Row-by-row mapping to Table VIII

| # | Table VIII row | Artifact check | Implemented |
|---|---|---|---|
| 1 | Serialized state occupies `3nw` bits | `A1` | ✅ |
| 2 | The leakage query returns `X` in `2w` bits | `A2a`, `A2b` | ✅ |
| 3 | The query fits the nominal leading term | `A3` | ✅ |
| 4 | The forged transcript satisfies (4) | `A4` | ✅ |
| 5 | No honest-prover query is used | `A5` | ✅ |
| 6 | The update's own equations hold with `T, T̃` non-singular, preserve `A′B′ = AB` and `pk`, and leave the stored length fixed | `A6a` (product + pk), `A6c` (length), `A6d`, `A6e`, `A6f` (equations, non-singularity) | ✅ |
| 7 | The retained pair survives the update | `A6g` | ✅ |
| 8 | **The old `A` and the refreshed `B` still multiply to `X`, per (23)** | **`A6h`** | ✅ **new** |
| 9 | **Two cross-epoch queries yield `X` and are accepted — 4,097 + 513 bits, accept = 1** | **`A9a`–`A9d`** | ✅ **new** |
| 10 | Two component-local queries cost `(n+2)w+2` bits | `A7a`, `A7b` | ✅ |
| 11 | An incorrect pair is rejected | `A8` | ✅ |

**No Table VIII row is now unimplemented.** Rows 8 and 9 were the two the paper
claimed but the artifact did not perform; both are covered.

Row 6 is the row R17 merged from three. Per spec §1.3 the three underlying
checks were **not** deleted; the README explains the correspondence, and the
merged row's three observations map to `A6a` (`pk` unchanged), `A6c`
(12,288 bits), and `A6d`/`A6e`/`A6f` (all verified).

---

## 5.3 Existing checks unaffected

Baseline run from the pre-change commit versus the updated run, diffed on the
check lines:

```
14a15,19
> [ok  ] A6h : the cross-epoch bridge: old A times refreshed B is still X -- A_i . B_(i+1) = X
> [ok  ] A9a : round i output is exactly nw + 1 bits -- 4097 bits = 16*256 + 1
> [ok  ] A9b : round i+1 output is exactly 2w + 1 bits -- 513 bits = 2*256 + 1
> [ok  ] A9c : the round i+1 output equals X, read from the refreshed B -- recovered X from B_(i+1)
> [ok  ] A9d : the cross-epoch pair authenticates on a fresh challenge -- accept = 1
```

**The diff contains only `>` additions.** No line was removed and no line was
modified: all 17 pre-existing checks keep their identifiers, descriptions and
observed values. 17 → 22 checks; both runs exit `0`.

§1.4 properties re-verified after the change: no toy parameters (report values
are `n = 16`, `w = 256`), the article hash and page locators are unchanged, the
article is still not redistributed (no PDF in the repo), and the imports remain
`argparse, json, os, random, sys` — Python 3 standard library only. A scan for
internal-audit vocabulary and for "verbatim" returns zero hits.

---

## 5.4 Version and DOI — **INCOMPLETE**

| Item | Value |
|---|---|
| Artifact branch | `agent/cross-epoch-checks` |
| Artifact commit | `108b4e3` |
| Pushed to | `origin/agent/cross-epoch-checks` |
| Tag created | **none — see the conflict below** |
| Old version DOI | `10.5281/zenodo.21927554` |
| New version DOI | **not obtained** |
| Concept DOI | **not obtained** |

### Version-number conflict — blocking, needs your decision

Spec §2.3 says to raise the version to **v1.1.0**. That tag **already exists** in
the artifact repo:

```
b2526c8...  refs/tags/v1.0.0
075aca2...  refs/tags/v1.0.0^{}
274a565...  refs/tags/v1.1.0
e052dbc...  refs/tags/v1.1.0^{}
```

`v1.1.0` points at `e052dbc`, "Implement the source's exact key update
algorithm", which was the repository `HEAD` before this change. I verified it
does **not** contain the cross-epoch checks: its `demo.py` reports 17 checks and
has no bridge assertion. It is also byte-identical to the copy vendored at
`artifact/demo.py` in the manuscript repository.

So the spec's premise — that the current release is v1.0.0 and the next is
v1.1.0 — is one release out of date. Adding these checks is a
backwards-compatible feature addition on top of v1.1.0, which by the spec's own
reasoning makes the new release **v1.2.0**. I did not tag, because choosing the
public version number of a citable archive is yours, not mine.

### Why §3 was not performed

Creating the Zenodo archive requires authenticating to Zenodo (or triggering the
GitHub-Zenodo integration by publishing a release) and mints a permanent,
publicly citable DOI. I have neither the credentials nor the standing to publish
a release on your behalf, so §3 is left to you. Concretely:

1. Decide the version number — **v1.2.0** is my recommendation, given the above.
2. Merge `agent/cross-epoch-checks` into `main`.
3. Tag and push that version.
4. Publish the GitHub release so the Zenodo integration archives it, or upload
   manually.
5. Record the new **version DOI** and the **concept DOI**.
6. Confirm the archived download contains the new checks — running `demo.py`
   from the archive should print `RESULT: all 22 checks passed.`

---

## 5.5 Manuscript changes — **NOT PERFORMED, deliberately**

The manuscript repository is **untouched this round**. `git status` in
`clr-ia-research` is clean at `de62e09` (`r17-frozen`), the verified baseline.

The spec's closing rule is explicit:

> §3 未完成、未取得新 DOI 之前，不得执行 §4——否则参考文献会指向一个不存在的版本。

Since §3 could not be completed, reference [18] cannot be updated: any version
and DOI I wrote would point at an archive that does not exist. The `% PENDING`
marker likewise **must stay** — it is currently accurate, because the published
artifact still lacks these checks until the release is made.

When you have the new DOI, §4 is two edits:

1. `09_paper/latex/references.bib`, entry `clria2026artifact` — change
   `v1.0.0` to the new version and both `doi` and the `note` URL to the new
   version DOI.
2. `09_paper/latex/appendices/appendix_artifact.tex:45` — delete the whole
   `% PENDING:` comment line.

Nothing else in the manuscript changes. Appendix C's constraint-faithful wording
and the orientation qualification on the two cross-epoch rows are already
correct and must not be rewritten.

---

## 5.6 Outstanding — blocking for submission is **not** yet zero

The spec anticipated zero blocking items after this round. Two remain, both
downstream of §3:

1. **Zenodo release not made; no new DOI.** Needs your action, steps in §5.4.
2. **Reference [18] still cites v1.0.0 and DOI `10.5281/zenodo.21927554`**, and
   the `% PENDING` marker is still in `appendix_artifact.tex`. Both are correct
   as they stand and become wrong the moment the release exists — so §4 should
   follow immediately after §3.

The underlying defect the spec set out to fix — the artifact not performing what
Table VIII claims — **is fixed in code and verified**. What remains is
publication, not implementation.

### Also worth noting

`artifact/demo.py` vendored inside the manuscript repository is now one revision
behind the artifact repository. It was byte-identical to `v1.1.0`; it does not
contain the new checks. The spec restricts manuscript changes to reference [18]
and the `% PENDING` marker, so I did not sync it. Whether that vendored copy
should track the artifact repo, or be dropped in favour of the DOI reference, is
worth deciding separately.

---

## Resolution

Recorded 2026-08-17. Each item §5.4–§5.6 left open is settled below.

### Release and DOIs — done

| Item | Value |
|---|---|
| Version released | **v1.2.0** — the number recommended in §5.4 |
| Tag | `v1.2.0` → `66bfbed`, which is also `main` |
| Version DOI | `10.5281/zenodo.21966231` |
| Concept DOI | `10.5281/zenodo.21927554` |

The concept/version question §5.4 left blank is now answered, and the answer
corrects an assumption made elsewhere. Zenodo record `21966231` reports
`conceptrecid: 21927554` and `conceptdoi: 10.5281/zenodo.21927554`. So
`21927554` — recorded in §5.4 as the "old version DOI" — is in fact the
**concept DOI**, and requesting `21927554` redirects to the current version
record. The two identifiers are not two versions; they are the series and one
member of it.

### Manuscript §4 — done

Applied in `clr-ia-research`, commit `32a8665`, merged to `main` as `56d3511`:

1. `references.bib`, entry `clria2026artifact` — `v1.0.0` → `v1.2.0`, and both
   `doi` and the `note` URL → `10.5281/zenodo.21966231`.
2. `appendices/appendix_artifact.tex` — the `% PENDING:` line deleted. It had
   become false: the released artifact now performs both checks.

The paper cites the **version** DOI, not the concept DOI. This was a deliberate
reversal of a note in `references.bib` that had forbidden exactly that. The
reason is that the paper states the artifact's exact check count and exact
output lengths; a concept DOI retargets to whatever release is newest, so a
later release with different checks would silently falsify the citation.
Follow-up commit `ef773ef` rewrites that note to record the decision, both
DOIs, and what else would have to change to reverse it.

### Vendored copy — synced

The open question under "Also worth noting" is resolved in favour of tracking
the artifact repo. `artifact/demo.py` and `artifact/README.md` in the manuscript
repository are now byte-identical to `v1.2.0`; the vendored demo was run from
its new location and prints `RESULT: all 22 checks passed.`, exit `0`.
`artifact/LICENSE` was deliberately not touched: it differs only by CRLF versus
LF in a Windows working tree, with identical content. `sources.json` was already
identical.

### Blocking items for submission

Zero remaining from this round. The two in §5.6 are both closed.

Unrelated and still open: the artifact citation has no author list
(`% TODO before submission: artifact citation authors` in `references.bib`), and
the manuscript's author field is intentionally blank.
