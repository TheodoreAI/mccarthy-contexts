#!/usr/bin/env python3
"""Build the Prove2Me payloads for the generic finite-information node.

Extracts `theorem solution`'s binders and type verbatim from the solution file,
so the JSON cannot drift from what compiles.  Unlike the capacity node, this
theorem carries binders (`(α β : Type) [Fintype α] [Fintype β]`), so the
extraction keeps everything between the declaration name and `:= by`.
"""

import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "build" / "payloads"
OUT.mkdir(parents=True, exist_ok=True)

DEF_FILE = ROOT / "Definitions" / "Def_TranscendenceTowerFiniteInformation.lean"
SOL_FILE = ROOT / "Solutions" / "Sol_finite_information_basics.lean"

DEFINITION_NAME = "TranscendenceTowerFiniteInformation"
THEOREM_NAME = "TranscendenceTower.FiniteInformation.finite_information_basics"

PREAMBLE = (
    "import Definitions.Def_TranscendenceTowerFiniteInformation\n"
    "\n"
    "set_option autoImplicit false\n"
    "\n"
    "open scoped BigOperators\n"
    "open TranscendenceTower.FiniteInformation"
)

SOURCE = (
    "Mateo Estrada, Harmless and Pointless: Consistency, rigidity, and the "
    "indeterminacy of context transfer in McCarthy's formalization of context, "
    "7 September 2026, Section 8 (A finite information calculation) -- "
    "supporting infrastructure for the finite Shannon quantities used there, "
    "stated over arbitrary finite alphabets. Standard textbook identities; cf. "
    "Cover and Thomas, Elements of Information Theory, 2nd ed., Ch. 2 "
    "(Theorem 2.2.1 chain rule, Theorem 2.6.3 nonnegativity of mutual "
    "information, Theorem 2.6.6 subadditivity)."
)

TAGS = ["information-theory", "entropy", "formalization", "probability"]


def extract_solution_signature(text: str) -> str:
    """Everything between `theorem solution` and `:= by`, verbatim."""
    start = text.index("theorem solution")
    body = text[start + len("theorem solution"):]
    end = body.index(":= by")
    return body[:end].rstrip()


signature = extract_solution_signature(SOL_FILE.read_text(encoding="utf-8"))
formal_statement = f"theorem {THEOREM_NAME}{signature} := by sorry\n"

assert formal_statement.strip().endswith(":= by sorry")
assert "Fintype" in formal_statement
assert "mutualInfo" in formal_statement and "condEntropy" in formal_statement

DEFINITION_NL = r"""Shannon's finite information quantities, over arbitrary finite alphabets.

Let $\alpha$ and $\beta$ be finite types and let $p$ be a real-valued mass function. All quantities below are plain finite sums measured in nats, and every logarithm is natural.

The **Shannon summand** is $s(p)=p\log p^{-1}$, and the **entropy** of a mass function on $\alpha$ is $H(p)=\sum_{x\in\alpha}s(p(x))$. The usual convention $0\log 0=0$ is not imposed by a side condition; it is inherited from the Lean convention $\log 0=0$, which makes $s(0)=0$ definitionally.

For a joint mass function $J$ on $\alpha\times\beta$ the bundle defines the two **marginals**
$$
p(a)=\sum_{b\in\beta}J(a,b),
\qquad
m(b)=\sum_{a\in\alpha}J(a,b),
$$
the **joint entropy** $H(\alpha,\beta)=\sum_{a}\sum_{b}s(J(a,b))$, the **conditional entropy**
$$
H(\beta\mid\alpha)=\sum_{a}\sum_{b}J(a,b)\log\frac{p(a)}{J(a,b)},
$$
and the **mutual information**
$$
I(\alpha;\beta)=\sum_{a}\sum_{b}J(a,b)\log\frac{J(a,b)}{p(a)\,m(b)} .
$$
In the last two, a cell with $J(a,b)=0$ contributes $0$ by an explicit guard rather than by a limiting argument. Finally, a mass function is a **distribution** when it is nonnegative and sums to one.

These definitions are the discrete counterparts of quantities Mathlib currently provides only in measure-theoretic form: it supplies the binary entropy function and a Kullback-Leibler divergence on measures, but no discrete entropy, conditional entropy or mutual information. Stating anything about product alphabets -- for instance $I(\alpha^n;\beta^n)$ for a memoryless channel -- requires the definitions to be polymorphic in the alphabet, which is the point of this bundle.

Formalization note. Mass functions are bare functions `α → ℝ` over a `Fintype` rather than elements of a probability-mass type, and normalization appears as a hypothesis on the theorems rather than as a bundled invariant. The explicit zero-mass guard, rather than a positivity hypothesis, is what allows the identities to be stated for every nonnegative joint law.
"""

THEOREM_NL = r"""$$
H(\alpha,\beta)=H(\alpha)+H(\beta\mid\alpha),
\qquad
I(\alpha;\beta)=H(\alpha)+H(\beta)-H(\alpha,\beta),
\qquad
I(\alpha;\beta)\ge 0 .
$$

The basic identities and inequalities of discrete Shannon information theory, over arbitrary finite alphabets $\alpha$ and $\beta$, in nats. Throughout, $J$ is a joint mass function on $\alpha\times\beta$ with nonnegative cells, $p$ and $m$ are its marginals, and normalization $\sum_{a,b}J(a,b)=1$ is assumed only where it is needed.

The statement collects eight facts.

1. **Marginals inherit normalization.** If $J$ is a distribution then so are $p$ and $m$.
2. **Chain rule.** $H(\alpha,\beta)=H(\alpha)+H(\beta\mid\alpha)$, requiring only nonnegativity.
3. **Mutual information from entropies.** $I(\alpha;\beta)=H(\alpha)+H(\beta)-H(\alpha,\beta)$, again requiring only nonnegativity.
4. **Gibbs' inequality.** $I(\alpha;\beta)\ge 0$ for any joint distribution: a joint law is never less informative than the product of its own marginals.
5. **Subadditivity.** $H(\alpha,\beta)\le H(\alpha)+H(\beta)$, immediate from 3 and 4.
6. **Conditional entropy is nonnegative.** $H(\beta\mid\alpha)\ge 0$.
7. **The standard form.** $I(\alpha;\beta)=H(\beta)-H(\beta\mid\alpha)$.
8. **Information is bounded by output entropy.** $I(\alpha;\beta)\le H(\beta)$.

Items 6 through 8 are the single-letter ingredient of a weak converse to the channel coding theorem: they bound what one use of a channel can convey by the entropy of what is observed.

The mathematics is standard. What the statement establishes is that these identities hold for the *guarded finite sums* as defined -- with zero-mass cells contributing zero by an explicit case split rather than by a limit -- and for every nonnegative joint law, with no positivity hypothesis on the marginals. That is the form in which the definitions are actually usable.

**Limits.** These are single-letter facts about one joint law. Nothing here concerns product alphabets, conditional mutual information, Fano's inequality, or any asymptotic statement, and no channel coding theorem is proved or approached.
"""

EXPLANATION = r"""$$
H(\alpha,\beta)=H(\alpha)+H(\beta\mid\alpha),
\qquad
I(\alpha;\beta)=H(\alpha)+H(\beta)-H(\alpha,\beta),
\qquad
I(\alpha;\beta)\ge 0 .
$$

Every part is proved cellwise and then summed. The recurring difficulty is not the algebra but the zero-mass guard: the definitions of $H(\beta\mid\alpha)$ and $I(\alpha;\beta)$ contain an explicit case split on $J(a,b)=0$, so each identity needs its degenerate branch discharged separately, and the interior branch needs the relevant marginal to be strictly positive.

The key observation that makes this work without extra hypotheses is that a cell never exceeds its own marginal: $J(a,b)\le p(a)$ and $J(a,b)\le m(b)$, since each marginal is a sum of nonnegative terms including that cell. Hence whenever $J(a,b)>0$ both marginals are automatically positive, and the logarithms are defined exactly where they are used.

1. **Marginals.** Nonnegativity is termwise. That $p$ sums to one is the hypothesis; that $m$ does requires exchanging the order of summation.

2. **Chain rule.** For $J(a,b)>0$,
$$
s(J(a,b))=J(a,b)\log\frac{p(a)}{J(a,b)}+J(a,b)\log p(a)^{-1},
$$
by splitting the logarithm of the quotient. Both sides vanish when $J(a,b)=0$. Summing over $b$ and factoring $\log p(a)^{-1}$ out of the second group turns $\sum_b J(a,b)$ into $p(a)$, giving $s(p(a))$; summing over $a$ finishes.

3. **Entropy form of mutual information.** Cellwise,
$$
J\log\frac{J}{p\,m}=J\log p^{-1}+J\log m^{-1}-s(J),
$$
using $\log(pm)=\log p+\log m$, valid since both are positive on nonzero cells. The three groups sum to $H(\alpha)$, $H(\beta)$ and $-H(\alpha,\beta)$ respectively, the middle one after exchanging the order of summation.

4. **Gibbs' inequality.** Apply $\log x\le x-1$ to $x=p(a)m(b)/J(a,b)$, which is positive on nonzero cells. This bounds the negated summand by $p(a)m(b)-J(a,b)$. On zero cells the negated summand is $0$ and the bound is $p(a)m(b)\ge 0$, so it holds there too. Summing, the right-hand side telescopes to $1-1=0$, because the product of the marginals is itself normalized -- which follows from $\sum_a\sum_b p(a)m(b)=\left(\sum_a p(a)\right)\left(\sum_b m(b)\right)$. Hence $-I\le 0$.

5. **Subadditivity** is item 4 rewritten through item 3.

6. **Nonnegativity of conditional entropy.** On a nonzero cell, $p(a)/J(a,b)\ge 1$ because the cell is dominated by its marginal, so the logarithm is nonnegative and the summand is a product of nonnegative factors.

7 and 8. Combining the chain rule with item 3 gives $I=H(\beta)-H(\beta\mid\alpha)$ by cancellation, and item 6 then yields $I\le H(\beta)$.

**Formalization note.** Entropies are in nats. Mass functions are bare `α → ℝ` over a `Fintype`, with normalization carried as a hypothesis rather than bundled. The proof is free of `sorry` and `native_decide`, and its axiom use is confined to `propext`, `Classical.choice` and `Quot.sound`.

**Limits.** These are single-letter facts about a single joint law. Conditional mutual information, the n-fold chain rule, Fano's inequality and every asymptotic statement are outside the scope of this result.
"""

definition_payload = {
    "definition_name": DEFINITION_NAME,
    "definition_title": r"Discrete entropy, conditional entropy and mutual information over finite alphabets",
    "definition": DEF_FILE.read_text(encoding="utf-8"),
    "natural_language_statement": DEFINITION_NL,
    "source": SOURCE,
    "tags": TAGS,
    "private": True,
}

problem_payload = {
    "theorem_name": THEOREM_NAME,
    "theorem_title": r"Chain rule, $I=H(\alpha)+H(\beta)-H(\alpha,\beta)$, and Gibbs' inequality over finite alphabets",
    "formal_statement": formal_statement,
    "natural_language_statement": THEOREM_NL,
    "preamble": PREAMBLE,
    "source": SOURCE,
    "tags": TAGS,
    "private": True,
}

(OUT / "payload_def_finiteinfo.json").write_text(
    json.dumps(definition_payload, ensure_ascii=False, indent=2), encoding="utf-8"
)
(OUT / "payload_thm_finiteinfo.json").write_text(
    json.dumps(problem_payload, ensure_ascii=False, indent=2), encoding="utf-8"
)
(OUT / "explanation_finiteinfo.md").write_text(EXPLANATION, encoding="utf-8")

print(f"wrote payloads to {OUT}")
print("--- formal_statement ---")
print(formal_statement)
