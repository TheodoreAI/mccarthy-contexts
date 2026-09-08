#!/usr/bin/env python3
"""Build the Prove2Me payloads for the zero-error and memoryless-converse nodes.

Extracts each `theorem solution` signature verbatim from its solution file, so
the JSON cannot drift from what compiles.
"""

import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "build" / "payloads"
OUT.mkdir(parents=True, exist_ok=True)

SOURCE = (
    "Mateo Estrada, Harmless and Pointless: Consistency, rigidity, and the "
    "indeterminacy of context transfer in McCarthy's formalization of context, "
    "7 September 2026, Section 8."
)
TAGS = ["logic", "formalization", "context", "information-theory",
        "nonmonotonic-reasoning"]


def signature(path: pathlib.Path) -> str:
    """Everything between `theorem solution` and the proof, verbatim.

    A solution may close with `:= by <tactics>` or with `:= <term>`; neither
    statement contains `:=` inside its type, so the first occurrence delimits
    the signature in both cases.
    """
    text = path.read_text(encoding="utf-8")
    start = text.index("theorem solution")
    body = text[start + len("theorem solution"):]
    return body[:body.index(":=")].rstrip()


# ---------------------------------------------------------------- zero error
ze_sig = signature(ROOT / "Solutions" / "Sol_information_theory_zero_error.lean")
ze_stmt = f"theorem TranscendenceTower.InformationTheory.zero_error_capacity{ze_sig} := by sorry\n"
assert ze_stmt.strip().endswith(":= by sorry")
assert "ZeroErrorCode" in ze_stmt

ZE_DEF_NL = r"""Zero-error coding for the finite route/survival channel.

The underlying channel has two inputs. A fact transferred directly always survives; a fact transferred through an intermediate context survives with probability one half. Writing $K_n$ for the $n$-fold memoryless product of that channel, this bundle adds the notions needed to ask whether the route can ever be recovered with *certainty* rather than merely on average.

A code of length $n$ carrying $M$ messages is an encoder $e:\{1,\dots,M\}\to\{\mathsf{direct},\mathsf{viaMid}\}^{n}$ together with a decoder $d$ on output words. It is a **zero-error code** when the decoder is correct on the entire support of each codeword:
$$
K_n(e(m), y) > 0 \;\Longrightarrow\; d(y) = m .
$$
The bundle also names the **rate** $\log M / n$, in nats per channel use, and the all-survive output word.

Formalization note. The zero-error condition is stated as a support condition rather than as an error probability equal to zero. The two agree, but the support form mentions no probability measure and makes the argument finite combinatorics: what matters is only which output words a codeword *can* produce, not how often.
"""

ZE_THM_NL = r"""$$
\text{zero-error capacity} = 0,
\qquad\text{while}\qquad
\max_q I(X;Y) = \log\tfrac54 > 0 .
$$

For the route/survival channel, no code of any blocklength carries more than one message without the possibility of error. Consequently every zero-error code has rate $0$, and the zero-error capacity of the channel is exactly $0$ — even though its one-use mutual information has a strictly positive maximum.

The reason is a single observation about the channel's support. Both routes admit survival, so the all-survive word $(\mathsf{true},\dots,\mathsf{true})$ has positive probability under *every* input word. A decoder that is never wrong must therefore return the same message for every codeword, which leaves room for only one. No observation ever rules any input out.

The statement has four parts: that every zero-error code satisfies $M \le 1$ and has rate $0$; that a one-message zero-error code exists, so the bound is attained rather than vacuous; that the all-survive word is possible under every input word, which is the mechanism; and that the comparison quantity $\log(5/4)$ is strictly positive, so the gap between the two capacities is real.

**Interpretation.** Read as a statement about auditing rather than transmission, this says that an observer watching which facts survive can never be *certain* which resolution the system applied, at any number of observations. Positive one-use information means the resolution leaves a trace; zero zero-error capacity means that trace never amounts to proof.

**Limits.** Nothing here is asymptotic, and no claim is made about how quickly confidence can approach certainty; that is an achievability question and is not addressed.
"""

ZE_EXPL = r"""$$
\text{no zero-error code carries more than one message, at any blocklength.}
$$

The whole proof rests on one property of the channel's support. Both rows of the one-use channel give positive mass to survival: the direct route survives with probability $1$, the routed one with probability $1/2$. Hence for any input word $x$, the product $K_n(x, (\mathsf{true},\dots,\mathsf{true})) = \prod_i K(x_i, \mathsf{true})$ is a product of strictly positive factors, so it is positive.

The argument then runs as follows.

1. **The all-survive word is universally possible.** Positivity of a finite product of positive reals gives $K_n(x,\mathbf{true}) > 0$ for every input word $x$, with no hypothesis on $x$ at all.

2. **A never-wrong decoder collapses.** Suppose a code has $M \ge 2$. Applying the correctness condition to the all-survive word twice, once for message $0$ and once for message $1$, forces $d(\mathbf{true}) = 0$ and $d(\mathbf{true}) = 1$ simultaneously. Those are distinct elements of a finite index type, so this is a contradiction and $M \le 1$.

3. **Rate.** With $M \le 1$ the only cases are $M = 0$ and $M = 1$, and $\log M / n$ vanishes in both, since $\log 1 = 0$ and the convention $\log 0 = 0$ applies to the degenerate case.

4. **Non-vacuity.** A one-message code is exhibited explicitly: encode the single message as the all-direct word and let the decoder return that message unconditionally. Correctness is immediate because the message type has one element. So the bound $M \le 1$ is attained, and the theorem is not a statement about an empty class of codes.

**Formalization note.** The zero-error condition is a support condition, not a probability-zero condition, so no measure-theoretic apparatus is needed and the argument is finite. The proof is free of `sorry` and `native_decide`, with axiom use confined to `propext`, `Classical.choice` and `Quot.sound`.

**Limits.** This is a statement about certainty, not about confidence. It does not bound how fast an observer's confidence can grow with more observations, and it proves no asymptotic or coding-theoretic result.
"""

ze_def = {
    "definition_name": "TranscendenceTowerZeroError",
    "definition_title": r"Zero-error codes for the route/survival channel",
    "definition": (ROOT / "Definitions" / "Def_TranscendenceTowerZeroError.lean")
        .read_text(encoding="utf-8"),
    "natural_language_statement": ZE_DEF_NL,
    "source": SOURCE + " Theorem thm:zeroerror.",
    "tags": TAGS,
    "private": True,
}
ze_thm = {
    "theorem_name": "TranscendenceTower.InformationTheory.zero_error_capacity",
    "theorem_title": r"The zero-error capacity of the route/survival channel is $0$",
    "formal_statement": ze_stmt,
    "natural_language_statement": ZE_THM_NL,
    "preamble": (
        "import Definitions.Def_TranscendenceTowerZeroError\n\n"
        "set_option autoImplicit false\n\n"
        "open scoped BigOperators\n"
        "open TranscendenceTower TranscendenceTower.ContextTheories "
        "TranscendenceTower.Lifting\n"
        "open TranscendenceTower.InformationTheoryPlatform\n"
        "open TranscendenceTower.InformationTheoryCapacityPlatform\n"
        "open TranscendenceTower.ZeroErrorPlatform"
    ),
    "source": SOURCE + " Theorem thm:zeroerror.",
    "tags": TAGS,
    "private": True,
}

# ------------------------------------------------------------------ converse
cv_sig = signature(ROOT / "Solutions" / "Sol_memoryless_converse.lean")
cv_stmt = f"theorem TranscendenceTower.ConversePlatform.memoryless_converse{cv_sig} := by sorry\n"
assert cv_stmt.strip().endswith(":= by sorry")
assert "channelJoint" in cv_stmt and "errorProb" in cv_stmt

CV_DEF_NL = r"""Words, product laws, memoryless channels, and the guess/truth quantities of Fano's inequality, over arbitrary finite alphabets.

This bundle extends the generic finite-information definitions with what is needed to speak about *repeated* use of a channel and about a decoder that may be wrong.

For words, it supplies the equivalence between words of length $n+1$ and (prefix, last symbol) pairs; the reading of a law on words of length $n+1$ as a two-variable joint law on that pair; the $i$-th **coordinate marginal** of a law on words; and the **product law** $\prod_i \mathrm{rows}_i(w_i)$ induced by a family of per-coordinate laws.

For channels, the **channel joint** of an input prior $\mathrm{pr}$ and a channel $K$ is
$$
J(x,y) = \mathrm{pr}(x)\prod_{i} K(x_i, y_i),
$$
an input word drawn from the prior and pushed through the channel coordinatewise and independently. The prior is arbitrary and need not be a product, so correlation across uses is permitted.

For decoding, given a joint law $J$ on (guess, truth) it defines the correct and erroneous mass,
$$
P_c=\sum_g J(g,g),\qquad P_e=\sum_{g}\sum_{w\ne g}J(g,w),
$$
together with the comparison law used to prove Fano's inequality: mass $P_c$ on the guess itself and $P_e/M$ on every answer, scaled by the guess marginal.

Formalization note. That comparison law is a *sub*-probability: its rows sum to at most one, not to one. This is deliberate, and it is what removes all counting of the off-diagonal from the proof, at the cost of the constant $\log M$ in place of the textbook $\log(M-1)$.
"""

CV_THM_NL = r"""$$
I(X^{n};Y^{n})\;\le\;\sum_{i}\bigl[H(Y_i)-H(Y_i\mid X_i)\bigr],
\qquad
H(\text{truth}\mid\text{guess})\;\le\;h(P_e)+P_e\log M .
$$

Five facts about repeated use of a memoryless channel and about what a decoder can recover from it, over arbitrary finite alphabets, in nats.

1. **The independence bound.** For any law on words of length $n$, the entropy of the word is at most the sum of the entropies of its coordinate marginals. Observing $n$ things at once is never more uncertain than observing them separately and adding up.

2. **Memorylessness.** The entropy of a product law is exactly the sum of the entropies of its factors. Independent uses contribute independently; nothing accumulates across them.

3. **The $n$-use bound.** For a memoryless channel and *any* prior on input words — correlated across uses or not — the information the output word carries about the input word is at most the sum over coordinates of the information a single use carries. Bounding each summand by the one-use capacity then gives the familiar $I(X^n;Y^n)\le nC$. That the prior is arbitrary is the content: correlating the inputs is permitted and does not help.

4. **Fano's inequality.** For a joint law on (guess, truth) over an alphabet of size $M$ with error probability $P_e$, the uncertainty about the truth that survives knowing the guess is at most $h(P_e)+P_e\log M$, where $h$ is the binary entropy. If the guess is usually right, little uncertainty remains.

5. **The weak converse.** If in addition the information the guess carries about the truth is at most $B$, then the entropy of the truth is at most $B$ plus that same error term. For a uniform truth over $M$ possibilities this reads $(1-P_e)\log M \le B + h(P_e)$: a decoder that is usually right can only have been distinguishing about $e^{B}$ possibilities.

The mathematics is classical. What is established is that these identities and bounds hold for the *guarded finite sums* as defined, with zero-mass cells contributing zero by an explicit case split rather than by a limit, and under no positivity hypotheses on the marginals.

**Limits.** The constant in item 4 is $\log M$, not the sharper textbook $\log(M-1)$. The bound $B$ in item 5 is a hypothesis rather than an instantiation: items 3 and 5 concern different quantities — $I(X^n;Y^n)$ and $I(\text{guess};\text{truth})$ — and joining them requires the data processing inequality, which is not proved here. No achievability statement is made or approached.
"""

CV_EXPL = r"""$$
I(X^{n};Y^{n})\le\sum_i\bigl[H(Y_i)-H(Y_i\mid X_i)\bigr],
\qquad
H(\text{truth}\mid\text{guess})\le h(P_e)+P_e\log M .
$$

Two independent arguments, joined at the end.

**The channel side.** The $n$-use bound is $I=H(Y^n)-H(Y^n\mid X^n)$ with each term handled separately.

For $H(Y^n)$, the independence bound is proved by induction on the length of a word, peeling off the *last* coordinate: a law on $\mathrm{Fin}(n+1)\to\beta$ is read as a two-variable joint law on (prefix, last symbol), and ordinary two-variable subadditivity applies at each step. This deliberately avoids conditional mutual information and an $n$-fold chain rule; it needs nothing beyond the two-variable results. Two small lemmas identify the marginals of that split: the last-symbol marginal is the last coordinate marginal, and marginalizing out the last symbol commutes with taking an earlier coordinate marginal.

For $H(Y^n\mid X^n)$, memorylessness is exact rather than an inequality. Cellwise, the guard in the conditional entropy fires whenever either the prior or the product mass vanishes, and both degenerate branches must land on the same value as the regular one; once that is checked, the conditional entropy collapses to the prior-average of the summed per-coordinate row entropies. A reindexing — averaging a function of the $i$-th input symbol against a law on words is the same as averaging it against that law's $i$-th coordinate marginal — turns this into $\sum_i H(Y_i\mid X_i)$.

**The decoder side.** Fano's inequality is Gibbs' inequality against a designed comparison law: put the correct-answer mass on the guess itself and spread $P_e/M$ over every answer. Because that law is only required to be a *sub*-probability, each row is bounded by summing $P_e/M$ over the whole alphabet rather than over the $M-1$ wrong answers, and no cardinality arithmetic enters the proof.

The delicate step is that the comparison mass must be strictly positive wherever the joint law has mass, or the guarded sum would compare against a vanishing denominator. This holds because a diagonal cell is dominated by the correct-answer mass and an off-diagonal cell by the error mass, so whichever branch of the weight applies is positive exactly when the cell is. The cellwise bound $\log x \le x-1$ then gives the result after the comparison sum is evaluated, splitting the double sum into its diagonal and off-diagonal parts.

**Joining them.** The weak converse follows immediately from Fano together with $I = H(\text{truth}) - H(\text{truth}\mid\text{guess})$.

**Formalization note.** All quantities are guarded finite sums in nats over arbitrary `Fintype`s. Normalization appears as a hypothesis rather than as a bundled invariant. The proof is free of `sorry` and `native_decide`, with axiom use confined to `propext`, `Classical.choice` and `Quot.sound`.

**Limits.** Fano is proved with $\log M$ rather than $\log(M-1)$. The converse carries an abstract bound $B$: items 3 and 5 are about $I(X^n;Y^n)$ and $I(\text{guess};\text{truth})$ respectively, and the data processing inequality that would join them is not proved. Stating the converse in a form where the two alphabets coincided would have concealed that gap rather than closed it.
"""

cv_def = {
    "definition_name": "TranscendenceTowerConverse",
    "definition_title": r"Words, memoryless channels, and the quantities of Fano's inequality",
    "definition": (ROOT / "Definitions" / "Def_TranscendenceTowerConverse.lean")
        .read_text(encoding="utf-8"),
    "natural_language_statement": CV_DEF_NL,
    "source": SOURCE + " Subsection 8.2 (What repeated observation cannot buy).",
    "tags": ["information-theory", "entropy", "formalization", "probability"],
    "private": True,
}
cv_thm = {
    "theorem_name": "TranscendenceTower.ConversePlatform.memoryless_converse",
    "theorem_title": r"Single-letterization, Fano's inequality, and the weak converse over finite alphabets",
    "formal_statement": cv_stmt,
    "natural_language_statement": CV_THM_NL,
    "preamble": (
        "import Definitions.Def_TranscendenceTowerConverse\n\n"
        "set_option autoImplicit false\n\n"
        "open scoped BigOperators\n"
        "open TranscendenceTower.FiniteInformation\n"
        "open TranscendenceTower.ConversePlatform"
    ),
    "source": SOURCE + " Subsection 8.2 (What repeated observation cannot buy), Theorems thm:nuse and thm:fano.",
    "tags": ["information-theory", "entropy", "formalization", "probability"],
    "private": True,
}

for name, obj in [
    ("payload_def_zeroerror.json", ze_def),
    ("payload_thm_zeroerror.json", ze_thm),
    ("payload_def_converse.json", cv_def),
    ("payload_thm_converse.json", cv_thm),
]:
    (OUT / name).write_text(json.dumps(obj, ensure_ascii=False, indent=2),
                            encoding="utf-8")
(OUT / "explanation_zeroerror.md").write_text(ZE_EXPL, encoding="utf-8")
(OUT / "explanation_converse.md").write_text(CV_EXPL, encoding="utf-8")

print(f"wrote payloads to {OUT}")
print("zero-error theorem:", ze_thm["theorem_name"])
print("converse theorem:  ", cv_thm["theorem_name"])
