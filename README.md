# Formalizing McCarthy's contexts

A Lean 4 formalization of claims from John McCarthy's *Notes on Formalizing
Context* (1993), together with new results about what those claims cost.

McCarthy observed that asserting `ist(c, p)` — "p is true in context c" —
generates an infinite regress of outer contexts, and asserted without proof that
"the regress is infinite, but … it is harmless." This development proves it, and
then shows that the regress is harmless **precisely because it is rigid**: the
transcendence schema does not merely permit the model in which each context
copies the one below, it forces it. That rigidity turns out to be incompatible
with the case McCarthy identifies as interesting, in which a transcending
context relaxes an assumption of the old.

Three further results show that the natural repairs are underdetermined.
Minimizing change over valuations always returns the unrelaxed tower; over
theories, circumscription admits incomparable minimal resolutions; and transfer
between contexts is *route-sensitive*: a skeptical consequence of the direct
route becomes merely credulous after passing through an intermediary. A finite
extension proves that its two routed blocks exhaust the actual minimal-block
subtype, then imposes (rather than infers) a uniform policy on that subtype.
The direct singleton has entropy `0`; routed selection has entropy `log 2`
nats. The remaining Shannon quantities are derived from an explicit finite
route/output joint law. Its separate loss-channel calculation assumes
memoryless, fresh-stage composition for the distinguished fact.  With routed
input probability `q`, the project's finite-sum mutual information of the
parameterized joint law is proved, including its zero-mass endpoint branches,
equal to `binEntropy (q / 2) - q * log 2` nats.  That actual finite-sum
quantity has exact capacity `log (5 / 4)` and unique optimizer `q = 2 / 5`;
because the input alphabet has exactly two routes, this `q`-family uniquely
parametrizes every input probability distribution.
Its coordinatewise product law is proved normalized for every fixed finite
input word; this supplies the memoryless channel model an asymptotic statement
would presuppose, not a coding theorem.

These quantities are read as *auditing*, not as data transmission: the input is
the system's own nondeterministic resolution of a lifting conflict, the output
is which facts an observer sees survive, and the maximum bounds how much of the
internal reasoning is recoverable from the external record.  On that reading the
sharper result is negative — the **zero-error capacity is `0`**.  Both routes
admit survival, so the all-survive word has positive probability under every
input word, and no decoder that is never wrong can separate two codewords at any
blocklength.  The resolution leaves a trace in what survives; that trace never
amounts to proof.

**24 results, no `sorry`.** Axiom use is confined to `propext`,
`Classical.choice` and `Quot.sound`; several results depend on no axioms at all.

## Building

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh   # if you lack elan
lake exe cache get                                        # prebuilt Mathlib oleans
lake build
```

`lake exe cache get` matters: without it the first build compiles Mathlib from
source, which takes hours. The toolchain (`lean-toolchain`) and the Mathlib
revision (`lakefile.lean`) are pinned to the environment the results were
verified in — Lean `v4.33.1`, Mathlib `0df444a3`.

`scripts/verify.sh` runs the full gate: build, a scan for `sorry` / `admit` /
`native_decide`, and the axiom audit.

## Layout

| path | contents |
|---|---|
| `Development/` | the readable development, one module per section of the paper |
| `Definitions/` | shared definition bundles |
| `Solutions/` | one `theorem solution` per result, in platform-submission form |

`Development/` supplies readable proof context and supporting lemmas;
`Definitions/`+`Solutions/` supplies independently compiling, platform-shaped
headline statements. Where both presentations cover a result they must not be
imported together, since they can deliberately declare overlapping names. This
is why the libraries are built from globs rather than through root files.

Start reading at `Development/Tower.lean`.

## Results

| module | result | |
|---|---|---|
| `Development/Tower.lean` | the transcendence tower is consistent | McCarthy §1, §5 |
| `Development/Transfinite.lean` | the canonical compositional valuation satisfies the schema at every ordinal stage; limit stages are unions | |
| `Development/Reification.lean` | reification is conservative; closure is not; distinct closure claims collide; relativization repairs it | |
| `Development/Relaxation.lean` | the schema has a **unique expansion over each fixed base valuation**; relaxation refutes it; the relaxed schema is not definitional | new |
| `Development/MinimalChange.lean` | change sets parametrize exactly; **minimal change collapses** to the unrelaxed tower; naming the change set determines the context | new |
| `Development/Theories.lean` | contexts as theories: classical consequence is monotone, circumscriptive consequence is not | new |
| `Development/Lifting.lean` | lifting transfers, is defeasible, and admits **incomparable minimal resolutions** | new |
| `Development/Chaining.lean` | lifting is **route-sensitive**: a skeptical direct consequence becomes merely credulous via an intermediary | new |
| `Development/InformationTheory.lean` | actual routed blocks are exactly `{p}` or `{q}`; direct Dirac entropy is `0`, routed entropy is `log 2` nats, every route-input distribution is uniquely parameterized by `q`, and the resulting formal finite-sum mutual information equals its entropy closed form and has capacity `log (5 / 4)` nats uniquely at `q = 2 / 5`; normalized product channels model repeated uses | new |
| `Definitions/Def_TranscendenceTowerInformationTheory.lean` + `Solutions/Sol_information_theory_joint_law.lean` | platform-shaped five-part headline: exact routed-block classification and its uniform law; unique direct singleton entropy `0`; fair routed entropy `log 2`; explicit-joint-law normalization, survival `3/4`, conditional entropy, and mutual information; and fresh-stage loss-channel composition | new |
| `Definitions/Def_TranscendenceTowerChannelCapacity.lean` + `Solutions/Sol_information_theory_channel_capacity.lean` | platform-shaped capacity extension: exhaustive unique parameterization of route priors, the induced joint law, its finite-sum mutual information's equivalence to the entropy closed form, exact one-use capacity `log (5 / 4)` uniquely at `q = 2 / 5`, and a normalized memoryless product channel for each fixed input word | new |
| `Development/ZeroErrorCapacity.lean` | the **zero-error capacity is `0`**: the all-survive word has positive probability under every input word, so no never-wrong decoder separates two codewords at any blocklength, and every zero-error code has rate `0`; a one-message code is exhibited so the bound is attained | new |
| `Development/FiniteInformation.lean` | supporting infrastructure, not a paper result: discrete entropy, joint and conditional entropy, and mutual information over arbitrary `Fintype`s — absent from Mathlib — with marginals, the chain rule, `I = H(a) + H(b) - H(a,b)`, Gibbs' inequality `I ≥ 0`, subadditivity, `H(b∣a) ≥ 0`, and `I = H(b) - H(b∣a)` hence `I ≤ H(b)` | new |

## Notes for the OSU COE cluster

Three things break a Lean build on these nodes, none of them the project's
fault:

- **Use an `el9` node.** Lean 4.33's bundled clang needs `GLIBC_2.29`; the login
  nodes ship glibc 2.28. Add `--constraint=el9` to your `srun` / `sbatch`.
- **Export the CA paths.** The toolchain ships a statically linked OpenSSL whose
  compiled-in CA path does not exist here, so every `lake exe cache get`
  download fails with `STORE routines::unregistered scheme` even though the
  system OpenSSL is fine:
  ```bash
  export SSL_CERT_FILE=/etc/pki/tls/certs/ca-bundle.crt
  export SSL_CERT_DIR=/etc/pki/tls/certs
  export CURL_CA_BUNDLE=/etc/pki/tls/certs/ca-bundle.crt
  ```
- **Keep it off `$HOME`.** Home directories are quota'd and the toolchain plus
  Mathlib cache runs to roughly 10 GB. Redirect `ELAN_HOME` and
  `XDG_CACHE_HOME` to scratch or project storage.

`lake update` is also known to hang here after writing `lake-manifest.json`; it
has already done its work by then, so check the manifest exists and go straight
to `lake exe cache get`.

## Paper

The accompanying paper, *Harmless and Pointless*, is in [`paper/`](paper/) as
LaTeX source. Each of its theorems cites the Lean identifier that proves it.

## On method

Machine checking prevents gaps in proofs. It does not prevent proving the wrong
thing, and this development hit that failure mode once: an early statement of
the non-conservativity result compiled, contained no `sorry`, and was vacuous —
the theory it quantified over has no models, because the extension of a truth
predicate always contains the tautologies. A refutation claim about a theory
with no models establishes nothing.

Every result here is therefore checked twice: once by the kernel, and once
against a vacuity discipline. For any statement quantifying over models, the
model class is proved non-empty; for any hypothesis defined in-file, a witness
is exhibited; headline results are restated inline as `example`s so a name
cannot quietly mean something weaker than advertised.

## Provenance

The Lean development was produced with Claude (Anthropic, Opus 5) in a session
directed by the author. The results' standing does not rest on that: every
theorem is checked by the Lean kernel, which is independent of whatever produced
the proof, and the axiom audit is machine-generated. A reader who distrusts the
provenance entirely can rebuild the development and lose nothing.

## License

MIT — see [LICENSE](LICENSE). Mathlib, on which this depends, is Apache-2.0.
