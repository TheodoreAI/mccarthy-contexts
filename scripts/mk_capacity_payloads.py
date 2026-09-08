#!/usr/bin/env python3
"""Build the Prove2Me payloads for the channel-capacity node.

Reads the Lean sources so the JSON can never drift from what compiles, and
extracts `theorem solution`'s type verbatim for `formal_statement`.
"""

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "build" / "payloads"
OUT.mkdir(parents=True, exist_ok=True)

DEF_FILE = ROOT / "Definitions" / "Def_TranscendenceTowerChannelCapacity.lean"
SOL_FILE = ROOT / "Solutions" / "Sol_information_theory_channel_capacity.lean"

DEFINITION_NAME = "TranscendenceTowerChannelCapacity"
THEOREM_NAME = "TranscendenceTower.InformationTheory.one_use_channel_capacity"

PREAMBLE = (
    "import Definitions.Def_TranscendenceTowerChannelCapacity\n"
    "\n"
    "set_option autoImplicit false\n"
    "\n"
    "open scoped BigOperators\n"
    "open TranscendenceTower TranscendenceTower.ContextTheories "
    "TranscendenceTower.Lifting\n"
    "open TranscendenceTower.InformationTheoryPlatform\n"
    "open TranscendenceTower.InformationTheoryCapacityPlatform"
)

SOURCE = (
    "Mateo Estrada, Harmless and Pointless: Consistency, rigidity, and the "
    "indeterminacy of context transfer in McCarthy's formalization of context, "
    "7 September 2026, Section 8.1 (Capacity and memoryless repeated use), "
    "Theorem thm:capacity and the displayed identity for "
    "I_joint(q) preceding it."
)

TAGS = [
    "logic",
    "formalization",
    "context",
    "information-theory",
    "nonmonotonic-reasoning",
]


def extract_solution_type(text: str) -> str:
    """Return the type ascribed to `theorem solution`, verbatim."""
    start = text.index("theorem solution :")
    body = text[start:]
    end = body.index(":= by")
    typ = body[len("theorem solution :"):end]
    return typ.rstrip()


solution_type = extract_solution_type(SOL_FILE.read_text(encoding="utf-8"))
formal_statement = f"theorem {THEOREM_NAME} :{solution_type} := by sorry\n"

# Guard: the platform rejects a statement that does not end in `:= by sorry`,
# and a silently empty extraction would produce nonsense prose around it.
assert formal_statement.strip().endswith(":= by sorry")
assert "blockChannel" in formal_statement
assert "Real.log (5 / 4)" in formal_statement

DEFINITION_NL = r"""This bundle extends the finite route/survival channel of the companion information-theory bundle with the ingredients needed to state a capacity result and a memoryless repeated-use model. It adds no theorems; every claim about these objects is proved in the theorem that imports it.

The underlying one-use channel has input alphabet $\{\mathsf{direct},\mathsf{viaMid}\}$ and Boolean output, with
$$
K(\mathsf{direct},\mathsf{true})=1,\qquad
K(\mathsf{direct},\mathsf{false})=0,\qquad
K(\mathsf{viaMid},\mathsf{true})=K(\mathsf{viaMid},\mathsf{false})=\tfrac12 .
$$
A fact transferred directly always survives; a fact transferred through the intermediate context survives with probability one half. This is a Z-channel with crossover $1/2$.

The bundle introduces the following. Let $q\in\mathbb{R}$.

- **The parameterized input prior** $p_q$, assigning probability $q$ to $\mathsf{viaMid}$ and $1-q$ to $\mathsf{direct}$. Because the input alphabet has exactly two elements, this one-parameter family is exhaustive: every input distribution is $p_q$ for exactly one $q\in[0,1]$.
- **The induced joint law** $J_q(r,b)=p_q(r)\,K(r,b)$ on input/output pairs, together with its output marginal $m_q(b)=\sum_r J_q(r,b)$, the output entropy $H(m_q)$, and the channel conditional entropy $\sum_r p_q(r)\,H(K(r,\cdot))$.
- **Two mutual informations.** The closed form
$$
I(q)=H_{\mathrm{bin}}(q/2)-q\log 2,
$$
and the operative quantity $I_{\mathrm{joint}}(q)$, defined as the project's finite Shannon sum over the four cells of $J_q$, in which a cell of zero mass contributes zero. The two are separate definitions on purpose: proving they agree on $[0,1]$ is part of the theorem, not built into the statement.
- **The memoryless product channel** $K_n(x,y)=\prod_{i}K(x_i,y_i)$ over input words $x:\mathrm{Fin}\,n\to\{\mathsf{direct},\mathsf{viaMid}\}$ and output words $y:\mathrm{Fin}\,n\to\mathbb{B}$. This is a conditional mass function only; it is not a code, an encoder, or a decoder.

All entropies and informations are measured in nats, matching Mathlib's `Real.binEntropy`, which uses natural logarithms. One bit is $\log 2$ nats.

Formalization note. The definitions are stated over all of $\mathbb{R}$ rather than over a subtype of $[0,1]$; the range hypotheses $0\le q\le 1$ appear on the theorems instead. This keeps the objects computable to state and avoids carrying coercions through every sum.
"""

THEOREM_NL = r"""$$
I_{\mathrm{joint}}(q)=H_{\mathrm{bin}}\!\left(\frac{q}{2}\right)-q\log 2
\quad\text{on }[0,1],
\qquad
\max_{q\in[0,1]} I_{\mathrm{joint}}(q)=\log\frac54,
\qquad
\operatorname*{arg\,max}_{q\in[0,1]} I_{\mathrm{joint}}(q)=\frac25 .
$$

Consider the finite channel in which a fact transferred directly between contexts always survives, and a fact transferred through an intermediate context survives with probability one half. Let $q$ be the probability that the routed input is used. Because the input alphabet has exactly two elements, this single parameter is exhaustive: every input probability distribution on the route alphabet equals $p_q$ for exactly one $q\in[0,1]$, so optimizing over $q$ really is optimizing over all input distributions rather than over a convenient sub-family.

The result has five parts.

1. **The parameterized law is a distribution.** For each $q\in[0,1]$ the four-cell joint mass $J_q$ on input/output pairs is nonnegative and sums to one.
2. **Exhaustive parameterization.** For every finite distribution on the route alphabet there is a unique $q\in[0,1]$ with that distribution equal to $p_q$.
3. **The finite sum equals the closed form.** On $[0,1]$, the project's finite Shannon sum $I_{\mathrm{joint}}(q)$ — the actual summation over the four cells, with zero-mass cells contributing zero — equals $H_{\mathrm{bin}}(q/2)-q\log 2$. Separately, that closed form is the difference of the output entropy and the channel conditional entropy. The endpoints $q=0$ and $q=1$ are handled on their own, since cells vanish there and the logarithms of the interior argument are undefined.
4. **Capacity and its unique optimizer.** For every $q\in[0,1]$ both quantities are bounded above by $\log(5/4)$, with equality if and only if $q=2/5$; both attain $\log(5/4)$ at $q=2/5$. The one-use capacity of this channel is therefore exactly $\log(5/4)$ nats, and the optimizing input distribution is unique.
5. **Memoryless repeated use.** For every $n$ and every fixed input word, the coordinatewise product channel $K_n$ is a probability distribution over output words. The degenerate cases agree with expectation: $K_0$ is the unit mass on the empty word, and $K_1$ is the original one-use channel.

The bound is stated for both the closed form and the finite sum, so the capacity claim certifies the project's own definition rather than a hand-chosen expression that merely looks like it.

**Limits.** Part 5 supplies the memoryless finite channel that a coding theorem would presuppose, and nothing more. It constructs no encoder and no decoder, and proves no achievability, converse, or asymptotic statement; $\log(5/4)$ is proved here as the maximum of the one-use mutual information, not as an operational rate. Entropies are in nats.
"""

EXPLANATION = r"""$$
I_{\mathrm{joint}}(q)=H_{\mathrm{bin}}\!\left(\frac{q}{2}\right)-q\log 2,
\qquad
\max_{q\in[0,1]} I_{\mathrm{joint}}(q)=\log\frac54
\ \text{ uniquely at } q=\frac25 .
$$

The channel is a Z-channel: the direct input is noiseless, and the routed input survives with probability one half. Writing $q$ for the probability of the routed input, the output is $\mathsf{true}$ with probability $1-q/2$, so the output entropy is $H_{\mathrm{bin}}(q/2)$, while the conditional entropy is $q\log 2$ because only the routed input is noisy. The mutual information is the difference, and the capacity claim is the maximization of that difference over $q\in[0,1]$.

The proof proceeds in five stages.

1. **Normalization.** The prior $p_q$ is nonnegative and sums to one for $q\in[0,1]$, and each channel row is a distribution; the product $J_q(r,b)=p_q(r)K(r,b)$ inherits both properties. Sums over the two-element route alphabet and over `Bool` are discharged by the bundle's enumeration lemmas.

2. **Exhaustive parameterization.** Given any distribution $\mathrm{pr}$ on the route alphabet, the value $q=\mathrm{pr}(\mathsf{viaMid})$ is forced, and normalization pins $\mathrm{pr}(\mathsf{direct})=1-q$; nonnegativity of the two entries gives $0\le q\le 1$. Uniqueness follows by evaluating any two candidate parameters at $\mathsf{viaMid}$. This is what upgrades a maximum over the family to a genuine capacity.

3. **Finite sum equals closed form.** This is the step that carries the real content, because the definition being certified is a four-cell sum with a zero-mass guard, not an entropy expression. The interior case $0<q<1$ expands the four cells, cancels the guard, and reduces to a logarithm identity; the endpoints are evaluated separately, since at $q=0$ the routed cells vanish and at $q=1$ the direct cells do, and in both cases the guard contributes zero rather than an undefined logarithm. The closed form is separately identified with the difference of output and conditional entropy.

4. **The bound and its equality case.** Maximizing $H_{\mathrm{bin}}(q/2)-q\log 2$ over $[0,1]$ gives the stationary point $q=2/5$, where the value is $\log(5/4)$. The inequality is proved for all admissible $q$, and the equality case is proved as an iff, so $2/5$ is certified as the unique optimizer rather than merely as a point where the maximum happens to be attained. Transporting the bound along stage 3 gives the same statement for the finite sum.

5. **Product channel.** Normalization of $K_n$ for a fixed input word is induction on the coordinates, using that each row of $K$ is a distribution; the sum over output words factors as a product of per-coordinate sums, each equal to one. The cases $n=0$ and $n=1$ are read off directly.

**Formalization note.** Entropies are in nats, following Mathlib's `Real.binEntropy`. The parameter $q$ ranges over $\mathbb{R}$ with the interval constraints carried as hypotheses rather than in a subtype. The mutual information being bounded is the project's own finite sum, with the closed form proved equal to it rather than substituted for it. The proof is free of `sorry` and `native_decide`, and its axiom use is confined to `propext`, `Classical.choice`, and `Quot.sound`.

**Limits.** The repeated-use component establishes that the coordinatewise product is a normalized conditional law — the memoryless channel model that precedes coding. It defines no code and proves no achievability, converse, or asymptotic result, so $\log(5/4)$ is established here as the maximum of the one-use mutual information and not as an operational transmission rate.
"""

definition_payload = {
    "definition_name": DEFINITION_NAME,
    "definition_title": r"Capacity and memoryless repeated use for the route/survival channel",
    "definition": DEF_FILE.read_text(encoding="utf-8"),
    "natural_language_statement": DEFINITION_NL,
    "source": SOURCE,
    "tags": TAGS,
    "private": True,
}

problem_payload = {
    "theorem_name": THEOREM_NAME,
    "theorem_title": r"One-use capacity $\log(5/4)$ of the route/survival channel, uniquely at $q=2/5$",
    "formal_statement": formal_statement,
    "natural_language_statement": THEOREM_NL,
    "preamble": PREAMBLE,
    "source": SOURCE,
    "tags": TAGS,
    "private": True,
}

(OUT / "payload_def_capacity.json").write_text(
    json.dumps(definition_payload, ensure_ascii=False, indent=2), encoding="utf-8"
)
(OUT / "payload_thm_capacity.json").write_text(
    json.dumps(problem_payload, ensure_ascii=False, indent=2), encoding="utf-8"
)
(OUT / "explanation_capacity.md").write_text(EXPLANATION, encoding="utf-8")

print(f"wrote payloads to {OUT}")
print(f"definition_name: {DEFINITION_NAME}")
print(f"theorem_name:    {THEOREM_NAME}")
print()
print("--- formal_statement ---")
print(formal_statement)
