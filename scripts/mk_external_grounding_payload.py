#!/usr/bin/env python3
"""Build the Prove2Me draft payload and proof explanation for the Theorem of
Necessary External Grounding (`Sol_necessary_external_grounding.lean`).

Extracts `formal_statement` verbatim from `Solutions/Sol_necessary_external_grounding.lean`
so the JSON payload cannot drift from the locally verified proof.
"""

import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "build" / "payloads"
OUT.mkdir(parents=True, exist_ok=True)

SOURCE = (
    "Mateo Estrada, On the Necessity of External Semantic Oracles in "
    "Autonomous Software Engineering Systems: A Meta-Theoretic Analysis via "
    "Context Logic, Tarski's Undefinability, and Relativized Computability, "
    "2026, Sections 3-4 (Lemmas 1-3 and Theorem 1: Necessary External Grounding)."
)

TAGS = [
    "logic",
    "formalization",
    "context",
    "computability",
    "nonmonotonic-reasoning",
    "default-logic",
]

PREAMBLE = (
    "import Definitions.Def_TranscendenceTowerContextUniformity\n"
    "import Mathlib.Computability.Halting\n\n"
    "set_option autoImplicit false\n\n"
    "open Computable\n"
    "open Nat.Partrec (Code)\n"
    "open TranscendenceTower.UniformityPlatform"
)


def signature(name: str) -> str:
    text = (ROOT / "Solutions" / name).read_text(encoding="utf-8")
    start = text.index("theorem solution")
    body = text[start + len("theorem solution"):]
    cut = body.index(":= by")
    sig = body[:cut].rstrip()
    assert body[cut:].startswith(":= by\n"), name
    return sig


THM_NAME = "TranscendenceTower.ExternalGroundingPlatform.necessary_external_grounding"
THM_STMT = f"theorem {THM_NAME}" + signature("Sol_necessary_external_grounding.lean") + " := by sorry\n"

THM_NL = r"""Let $\mathrm{Code}$ be the type of partial recursive program codes (`Nat.Partrec.Code`) with universal evaluator $\mathrm{Code.eval} : \mathrm{Code} \to \mathbb{N} \rightharpoonup \mathbb{N}$ and bounded-step evaluator $\mathrm{Code.evaln} : \mathbb{N} \to \mathrm{Code} \to \mathbb{N} \to \mathrm{Option}\;\mathbb{N}$, and let $\mathrm{CForm}\;A\;C$ be the modal context language over signed atoms $A$ and context indices $C$ from `Def_TranscendenceTowerContextUniformity`.

The **Theorem of Necessary External Grounding** establishes four joint limits and guarantees for autonomous verification pipelines:

1. **Multi-Oracle Rice Undecidability:** For every semantic specification $\mathrm{Spec} \subseteq \mathrm{Code}$ (meaning $\mathrm{Code.eval}\;c_1 = \mathrm{Code.eval}\;c_2 \implies (c_1 \in \mathrm{Spec} \iff c_2 \in \mathrm{Spec})$) that is non-trivial ($\exists c_{\text{yes}} \in \mathrm{Spec}$ and $\exists c_{\text{no}} \notin \mathrm{Spec}$), every computable base verifier $d_0 : \mathrm{Code} \to \mathrm{Bool}$ (`Computable d₀`), and every finite pipeline $\mathrm{Os} : \mathrm{List}(\mathrm{Code} \to \mathrm{Bool})$ of internalized computable verification sub-oracles ($\forall O \in \mathrm{Os},\;\mathrm{Computable}\;O$), there exists a program $c_* \in \mathrm{Code}$ on which the conjunctive pipeline verdict disagrees with $\mathrm{Spec}$:
$$
\Bigl(\mathrm{Os.foldl}\;(\lambda\, b\, O \Rightarrow b \mathbin{\&\&} O(c_*))\;(d_0(c_*)) = \mathsf{true}\Bigr) \iff c_* \notin \mathrm{Spec}.
$$

2. **Computability of Bounded Test Harnesses:** For every step bound $k \in \mathbb{N}$, input $x \in \mathbb{N}$, and target output $y \in \mathbb{N}$, the bounded execution test $c \mapsto \mathrm{decide}(\mathrm{Code.evaln}\;k\;c\;x = \mathrm{some}\;y)$ is a computable sub-oracle (`Computable`), so adjoining finitely many bounded test assertions into $\mathrm{Os}$ remains trapped inside Part 1.

3. **Closed-Loop Collapse & Undecidability under Semantic Drift:** For any context-free specification $\mathrm{Ax} \subseteq \mathrm{CForm}\;A\;C$ ($\forall p \in \mathrm{Ax},\;\mathrm{IsBase}\;p$), any proposition-uniform default rule schema $S \subseteq \mathrm{Rule}\;A\;C$ (`PropUniformRules S`) whose consequents are consistent with $\mathrm{Ax}$, and any Reiter extension $\mathrm{Ext}$ (`IsExtension Ax S Ext`), if a base-language requirement $G_*$ (`IsBase G_*`) holds in the target operational environment $v_{\text{real}}$ ($\mathrm{Models}\;\mathrm{Ax}\;v_{\text{real}}$ and $\mathrm{eval}\;v_{\text{real}}\;G_* = \mathsf{true}$) while a drifted model $v_{\text{drift}}$ satisfies $\mathrm{Ax}$ ($\mathrm{Models}\;\mathrm{Ax}\;v_{\text{drift}}$) and falsifies $G_*$ ($\mathrm{eval}\;v_{\text{drift}}\;G_* = \mathsf{false}$), then $G_*$ is undecidable in the closed loop $\mathrm{Ext}$:
$$
G_* \notin \mathrm{Ext} \quad\wedge\quad \mathrm{neg}\;G_* \notin \mathrm{Ext}.
$$

4. **Soundness, Sufficiency, and Non-Uniformity of Supervisory External Grounding:** Under the hypotheses of Part 3 with $G_* \notin \mathrm{Cn}(\mathrm{Ax})$, for any outer operational context $c_{\text{real}} \in C$, the external semantic oracle injection
$$
\mathrm{LiftAx} = \bigl\{\mathrm{ist}(c_{\text{real}}, G_*),\;\mathrm{ist}(c_{\text{real}}, G_*) \to G_*\bigr\}
$$
is consistent with $\mathrm{Ax}$ (`Consistent (Ax ∪ LiftAx)`), certifies $G_*$ ($G_* \in \mathrm{Cn}(\mathrm{Ax} \cup \mathrm{LiftAx})$), and is necessarily non-uniform ($\neg\,\mathrm{PropUniform}\;\mathrm{LiftAx}$).
"""

THM_EXPL = r"""We prove the four-part **Theorem of Necessary External Grounding** over concrete partial recursive program codes $\mathrm{Code}$ (`Nat.Partrec.Code`) and the modal context language $\mathrm{CForm}\;A\;C$ of `Def_TranscendenceTowerContextUniformity`:

$$
\begin{aligned}
&\text{(1)}\quad \forall\,\mathrm{Spec}\subseteq\mathrm{Code}\;\text{semantic, non-trivial},\;\forall d_0,\mathrm{Os}\;\text{computable},\;\exists c_*,\;\bigl(P_{\mathrm{Os}}(c_*)=\mathsf{true} \iff c_*\notin\mathrm{Spec}\bigr),\\
&\text{(2)}\quad \forall k,x,y\in\mathbb{N},\;\mathrm{Computable}\bigl(c \mapsto \mathrm{decide}(\mathrm{Code.evaln}\;k\;c\;x = \mathrm{some}\;y)\bigr),\\
&\text{(3)}\quad \mathrm{Ax}\subseteq L\;\text{base},\;\mathrm{PropUniformRules}\;S,\;\mathrm{IsExtension}\;\mathrm{Ax}\;S\;\mathrm{Ext},\;v_{\text{real}}\models G_*,\;v_{\text{drift}}\models\neg G_* \implies G_*\notin\mathrm{Ext}\;\wedge\;\mathrm{neg}\;G_*\notin\mathrm{Ext},\\
&\text{(4)}\quad \mathrm{LiftAx}=\bigl\{\mathrm{ist}(c_{\text{real}},G_*),\;\mathrm{ist}(c_{\text{real}},G_*)\to G_*\bigr\} \implies \mathrm{Consistent}(\mathrm{Ax}\cup\mathrm{LiftAx})\;\wedge\;G_*\in\mathrm{Cn}(\mathrm{Ax}\cup\mathrm{LiftAx})\;\wedge\;\neg\mathrm{PropUniform}(\mathrm{LiftAx}).
\end{aligned}
$$

The central idea is that any finite architecture of internalized verification checks and proposition-uniform reflection rules remains closed under two Collapse principles: on the computability side, folding finitely many computable sub-oracles preserves `ComputablePred` and therefore hits Rice's theorem (`ComputablePred.rice₂`); on the context-logic side, proposition-uniform rules commute with constant truth-value substitutions (`boolSubst`), collapsing base-language consequences of any Reiter extension to $\mathrm{Cn}(\mathrm{Ax})$ and forcing any sound external grounding to break proposition-uniformity.

First, for Part (1), given two computable predicates $f, g : \mathrm{Code} \to \mathrm{Bool}$, their pointwise conjunction $c \mapsto f(c) \mathbin{\&\&} g(c)$ is expressed as `cond (f c) (g c) false`, which is computable by `Computable.cond`. Structural induction on the sub-oracle list $\mathrm{Os}$ (`pipeline_foldl_computable`) then shows that the conjunctive pipeline

$$
P_{\mathrm{Os}}(c) = \mathrm{Os.foldl}\;(\lambda\, b\, O \Rightarrow b \mathbin{\&\&} O(c))\;(d_0(c))
$$

is computable, making $\{c \in \mathrm{Code} \mid P_{\mathrm{Os}}(c) = \mathsf{true}\}$ a `ComputablePred`. If no program $c_*$ satisfied $P_{\mathrm{Os}}(c_*) = \mathsf{true} \iff c_* \notin \mathrm{Spec}$, classical negation (`not_exists` and `not_iff`) would yield $P_{\mathrm{Os}}(c) = \mathsf{true} \iff c \in \mathrm{Spec}$ for all $c$, transferring `ComputablePred` to $\mathrm{Spec}$ via `ComputablePred.of_eq`. Applying `ComputablePred.rice₂` under the extensionality hypothesis forces $\mathrm{Spec} = \emptyset$ or $\mathrm{Spec} = \mathrm{Set.univ}$, contradicting the non-triviality witnesses $c_{\text{yes}} \in \mathrm{Spec}$ and $c_{\text{no}} \notin \mathrm{Spec}$.

Second, for Part (2), `Nat.Partrec.Code.primrec_evaln` establishes that theuncurried bounded evaluator $(k, c, x) \mapsto \mathrm{Code.evaln}\;k\;c\;x$ is primitive recursive. Composing with primitive recursive constant pairing $c \mapsto (k, (c, x))$ and `Primrec.eq` against $\mathrm{some}\;y$ proves that $c \mapsto \mathrm{decide}(\mathrm{Code.evaln}\;k\;c\;x = \mathrm{some}\;y)$ is primitive recursive (`PrimrecPred.decide`) and therefore `Computable` via `Primrec.to_comp`.

Third, for Part (3), induction on the Reiter stage hierarchy (`stage_subset_Cn_consequents`) shows that any fixed-point extension $\mathrm{Ext}$ (`IsExtension Ax S Ext`) satisfies

$$
\mathrm{Ext} \subseteq \mathrm{Cn}\bigl(\mathrm{Ax} \cup \{r.\mathrm{conseq} \mid r \in S\}\bigr).
$$

Because `PropUniformRules S` implies `PropUniform` of the consequent set, the monotone dichotomy (`monotone_dichotomy`) applies: given any model $M \models \mathrm{Ax}$ and any witness model $W \models \mathrm{Ax} \cup \{r.\mathrm{conseq} \mid r \in S\}$, we form the constant substitution $\sigma_M = \mathrm{boolSubst}\;M$ sending each atom $a$ to $\top$ (`verum`) or $\bot$ (`falsum`) according to $M.\mathrm{atom}\;a$. On base formulas, $\mathrm{eval}\;W\;(\mathrm{subst}\;\sigma_M\;\varphi) = \mathrm{eval}\;M\;\varphi$ (`eval_subst_boolSubst_base`), while proposition-uniformity guarantees $\mathrm{subst}\;\sigma_M\;\gamma \in \{r.\mathrm{conseq} \mid r \in S\}$, so pulling $W$ back along $\sigma_M$ via `eval_subst` turns $M$ into a model of $\mathrm{Ax} \cup \{r.\mathrm{conseq} \mid r \in S\}$. Consequently,

$$
\mathrm{Ext} \cap L = \mathrm{Cn}(\mathrm{Ax}) \cap L.
$$

Since $v_{\text{drift}} \models \mathrm{Ax}$ has $\mathrm{eval}\;v_{\text{drift}}\;G_* = \mathsf{false}$, we obtain $G_* \notin \mathrm{Cn}(\mathrm{Ax})$ and thus $G_* \notin \mathrm{Ext}$. Symmetrically, since $v_{\text{real}} \models \mathrm{Ax}$ has $\mathrm{eval}\;v_{\text{real}}\;G_* = \mathsf{true}$, we have $\mathrm{eval}\;v_{\text{real}}\;(\mathrm{neg}\;G_*) = \mathsf{false}$, so $\mathrm{neg}\;G_* \notin \mathrm{Cn}(\mathrm{Ax})$ and $\mathrm{neg}\;G_* \notin \mathrm{Ext}$.

Finally, for Part (4), given $v_{\text{real}} \models \mathrm{Ax}$ with $\mathrm{eval}\;v_{\text{real}}\;G_* = \mathsf{true}$ and an external context index $c_{\text{real}} \in C$, we construct the meta-valuation

$$
\mathrm{realityMetaVal}(v_{\text{real}}) = \bigl\langle v_{\text{real}}.\mathrm{atom},\; (c, p) \mapsto \mathrm{eval}\;v_{\text{real}}\;p \bigr\rangle.
$$

Because base formulas contain no `ist` modalities, `eval_eq_of_atom_eq` shows that $\mathrm{realityMetaVal}(v_{\text{real}})$ agrees with $v_{\text{real}}$ on $\mathrm{Ax}$ and on $G_*$; moreover, it evaluates both $\mathrm{ist}(c_{\text{real}}, G_*)$ and $\mathrm{ist}(c_{\text{real}}, G_*) \to G_*$ to $\mathsf{true}$, establishing `Consistent (Ax ∪ LiftAx)`. In any model of $\mathrm{Ax} \cup \mathrm{LiftAx}$, modus ponens on $\mathrm{ist}(c_{\text{real}}, G_*)$ and $\mathrm{ist}(c_{\text{real}}, G_*) \to G_*$ yields $G_* \in \mathrm{Cn}(\mathrm{Ax} \cup \mathrm{LiftAx})$. Lastly, if $\mathrm{LiftAx}$ were proposition-uniform (`PropUniform LiftAx`), then `monotone_dichotomy` applied to the consistent union $\mathrm{Ax} \cup \mathrm{LiftAx}$ would force $G_* \in \mathrm{Cn}(\mathrm{Ax})$, contradicting $G_* \notin \mathrm{Cn}(\mathrm{Ax})$.
"""

payload = {
    "problems": [
        {
            "theorem_name": THM_NAME,
            "theorem_title": "Theorem of Necessary External Grounding",
            "formal_statement": THM_STMT,
            "natural_language_statement": THM_NL,
            "preamble": PREAMBLE,
            "source": SOURCE,
            "tags": TAGS,
            "private": True,
        }
    ],
    "private": True,
}

assert THM_STMT.strip().endswith(":= by sorry")
(OUT / "payload_thm_external_grounding.json").write_text(
    json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8"
)
(OUT / "Sol_necessary_external_grounding.expl.md").write_text(
    THM_EXPL, encoding="utf-8"
)
print("wrote:", OUT / "payload_thm_external_grounding.json")
print("wrote:", OUT / "Sol_necessary_external_grounding.expl.md")
