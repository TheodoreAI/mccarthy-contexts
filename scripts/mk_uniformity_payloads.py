#!/usr/bin/env python3
"""Build the Prove2Me payloads for the three uniformity nodes.

Each `formal_statement` is extracted verbatim from its solution file, so the
JSON cannot drift from what compiles locally.
"""

import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "build" / "payloads"
OUT.mkdir(parents=True, exist_ok=True)

SOURCE = ("Mateo Estrada, Uniformity and Transcendence: a trichotomy for "
          "lifting schemas in the logic of context, 8 September 2026")

TAGS = ["logic", "formalization", "context", "nonmonotonic-reasoning",
        "default-logic"]

PREAMBLE = (
    "import Definitions.Def_TranscendenceTowerContextUniformity\n\n"
    "set_option autoImplicit false\n\n"
    "open TranscendenceTower.UniformityPlatform"
)


def signature(name: str) -> str:
    """Everything between `theorem solution` and the proof, verbatim.

    The delimiter is `:= by`, not `:=`: these statements contain named
    arguments such as `shiftAut (A := A) oc`, so the first bare `:=` is inside
    the type rather than at the end of it.  Every solution here closes with a
    tactic block, which is asserted below.
    """
    text = (ROOT / "Solutions" / name).read_text(encoding="utf-8")
    start = text.index("theorem solution")
    body = text[start + len("theorem solution"):]
    cut = body.index(":= by")
    sig = body[:cut].rstrip()
    assert body[cut:].startswith(":= by\n"), name
    return sig


# ------------------------------------------------------------------ the bundle

DEF_NL = r"""The language of contexts, its semantics, Reiter extensions for default lifting schemas, and the two families of automorphism that act on all of it.

**The language.** Formulas are built from signed atoms, falsity and implication, together with a modality $\mathrm{ist}_c(\varphi)$ for each context $c$ drawn from an arbitrary index type. Nothing constrains the modality: $\mathrm{ist}_c(\varphi)$ is simply a further atom. A valuation assigns truth values to the atoms and to the modal atoms, and the connectives are read classically. Consequence $\mathrm{Cn}(T)$ is truth in every model of $T$, and a theory is consistent when it has a model. The **base language** is the fragment with no occurrence of $\mathrm{ist}$: this is the language in which facts about the world are stated, and it is where conservativity is measured.

**Substitution.** A substitution acts on atoms and is extended homomorphically, acting inside the scope of $\mathrm{ist}$. A set of formulas is *proposition-uniform* when it is closed under every substitution, and a set of rules is proposition-uniform when its rules are.

**Extensions.** A default rule is a triple $\dfrac{\alpha:\beta}{\gamma}$ of prerequisite, justification and consequent. The stages of the Reiter construction are $E_0=\mathrm{Cn}(T)$ and
$$
E_{i+1}=\mathrm{Cn}(E_i)\;\cup\;\bigl\{\gamma : \tfrac{\alpha:\beta}{\gamma}\in S,\ \alpha\in E_i,\ \neg\beta\notin E\bigr\},
$$
and $E$ is an **extension** when $E=\bigcup_i E_i$ — a fixed point of its own stage construction rather than a closure, since the test on $\neg\beta$ refers to $E$ itself. A schema is *monotone* when every justification is $\top$.

**Automorphisms.** A *logical automorphism* is a bijection of formulas realised on valuations: composing with it agrees with evaluating against a transformed valuation, and it commutes with negation. Two families are constructed. The **shift** along an equivalence of the context type relabels every context index and fixes the atoms; it is the map under which the levels of a tower are compared. The **atom automorphisms** are given by a permutation $\pi$ of the atoms together with an arbitrary sign pattern $\varepsilon$; together they form the group $\{0,1\}^{A}\rtimes\mathrm{Sym}(A)$, which is $\mathrm{Aut}(L)$. A theory is *symmetric* under a group when that group moves any model of it to any other.

**Formalization note.** Atoms carry a sign: `lit a false` is the atom $a$ and `lit a true` is $\neg a$, with negation flipping the sign rather than forming $p\to\bot$. This is not cosmetic. An atom automorphism must be a bijection of *formulas* for the preimage of a schema to be the schema; with unsigned atoms, applying a sign flip twice to $a$ returns $\neg\neg a$, a distinct formula, so the group acts only on the Lindenbaum algebra. The signed presentation makes the action a genuine involution on literals and makes it coincide with a substitution, which is what lets proposition-uniformity be applied to it directly.

The bundle contains definitions together with the proof obligations that constructing them requires — an equivalence cannot be written down without its two inverse laws, and a logical automorphism cannot be written down without the lemma relating its two actions. Every substantive claim about these objects is proved in the theorems that import the bundle.
"""

# ------------------------------------------------------- 1. monotone dichotomy

MONO_STMT = ("theorem TranscendenceTower.UniformityPlatform.uniformity_monotone_dichotomy"
             + signature("Sol_uniformity_monotone_dichotomy.lean")
             + " := by sorry\n")

MONO_NL = r"""$$
T\subseteq L \ \text{context-free},\quad \Gamma \ \text{proposition-uniform},\quad T\cup\Gamma \ \text{consistent}
\;\Longrightarrow\;
\mathrm{Cn}(T\cup\Gamma)\cap L=\mathrm{Cn}(T)\cap L .
$$

A monotone lifting schema that treats all propositions alike proves no new sentence of the base language. Uniformity and novelty are incompatible, and already in the monotone case, where the extension is unique automatically.

Four parts.

1. **The dichotomy.** If the base theory $T$ contains no context machinery and the schema's consequents $\Gamma$ are closed under substitution, then either $T\cup\Gamma$ is inconsistent or every base sentence it proves was already a consequence of $T$.

2. **Conservativity.** The same statement as an equality of sets: the extension meets the base language in exactly the base consequences of $T$.

3. **The copy schema is proposition-uniform.** Its consequents are the sentences $\mathrm{ist}_c(p)\to p$, and substituting inside one produces another.

4. **The copy schema is consistent**, witnessed by the canonical valuation in which $\mathrm{ist}_c(p)$ says exactly what $p$ says.

Parts 3 and 4 are not decoration. Without them the dichotomy could hold vacuously, constraining an empty class of schemas; together they exhibit the intended example satisfying every hypothesis.

The informal claim being made precise is that a rule earns the name *rule* by being indifferent to which proposition it lifts, and that this indifference is exactly what prevents it from delivering a particular new fact. If it delivers $\varphi$, then under substitution it must deliver every substitution instance of $\varphi$, and those are jointly unsatisfiable whenever $\varphi$ is not already forced.

**Limits.** The result is about monotone schemas; the defeasible case needs the trichotomy, where uniqueness can fail instead. Context-freeness of $T$ is essential and not a technicality: a base theory that already speaks of contexts can supply a premise the schema exports, and non-conservativity then follows for reasons having nothing to do with lifting. Nothing here says a lifting schema is useless — it says that whatever content one carries must come from somewhere other than its uniformity.
"""

MONO_EXPL = r"""$$
\text{if } \varphi\in\mathrm{Cn}(T\cup\Gamma)\cap L \text{ and } \varphi\notin\mathrm{Cn}(T), \text{ then } T\cup\Gamma \text{ has no model.}
$$

The argument is semantic and turns on a single lemma.

**The substitution lemma.** For a substitution $s$, evaluating $s\varphi$ against a valuation $v$ is the same as evaluating $\varphi$ against the *pulled-back* valuation $s^{*}v$, which reads an atom through $s$ and a modal atom through its substituted form:
$$
v \models s\varphi \iff s^{*}v \models \varphi .
$$
This is an induction on $\varphi$ with one line per constructor, and it replaces the usual route of extracting a finite derivation and substituting into it — which would need a proof calculus and compactness.

**The proof.** Suppose $\varphi$ is a base sentence in $\mathrm{Cn}(T\cup\Gamma)$ but not in $\mathrm{Cn}(T)$. Then some model $M$ of $T$ falsifies $\varphi$. Freeze $M$ into a substitution $s$ sending each atom to $\top$ or $\bot$ according to its value in $M$. On the base language $s$ makes every atom a constant, so $s\psi$ evaluates to $M(\psi)$ against *any* ambient valuation.

Now take any model $v$ of $T\cup\Gamma$ — one exists by the consistency hypothesis — and consider $s^{*}v$. It models $T$, because each $\psi\in T$ is base and $v\models s\psi$ which equals $M(\psi)=\text{true}$. It models $\Gamma$, because proposition-uniformity puts $s\gamma$ back in $\Gamma$ for each $\gamma\in\Gamma$, and $v$ models that. So $s^{*}v$ models $T\cup\Gamma$ and therefore satisfies $\varphi$. But $v\models s\varphi$ says exactly that, and $s\varphi$ evaluates to $M(\varphi)=\text{false}$. Contradiction.

**Non-vacuity.** For the copy schema, uniformity is immediate from the shape of the consequents, and consistency is witnessed by the canonical valuation: define an evaluation in which $\mathrm{ist}_c(p)$ takes the value of $p$, and each $\mathrm{ist}_c(p)\to p$ becomes an instance of $x\to x$.

**Formalization note.** The frame plays no role whatsoever. The paper observes this in a remark; in the formalization it is structural, since no successor map on contexts appears in any statement or proof — contexts are an arbitrary index type. The theorem therefore holds for *any* arrangement of contexts, not only for a tower. Consequence is semantic throughout, so no proof calculus is defined and compactness is never used. The development is free of `sorry` and `native_decide`, with axiom use confined to `propext`, `Classical.choice` and `Quot.sound`.
"""

# -------------------------------------------------------------- 2. rigidity

RIG_STMT = ("theorem TranscendenceTower.UniformityPlatform.uniformity_rigidity"
            + signature("Sol_uniformity_rigidity.lean")
            + " := by sorry\n")

RIG_NL = r"""$$
\sigma^{-1}(E)=E,
\qquad\text{hence}\qquad
\mathrm{ist}_c(\varphi)\in E \iff \mathrm{ist}_{\mathrm{out}(c)}(\sigma\varphi)\in E .
$$

If a lifting schema treats the contexts uniformly — it is its own preimage under the shift — then its unique consistent extension is shift-invariant, and every level of the tower carries the same content as every other.

Five parts.

1. **Rigidity.** For a context-free base theory and a schema preserved by the shift, if the extension is consistent and unique then it is shift-invariant.

2. **The consequence for levels.** Invariance says $\mathrm{ist}_c(\varphi)$ belongs to the extension exactly when $\mathrm{ist}_{\mathrm{out}(c)}(\sigma\varphi)$ does, where $\sigma$ is the shift.

3. **The consequence on the base language.** There $\sigma$ acts as the identity, so the equivalence reads $\mathrm{ist}_c(\varphi)\in E \iff \mathrm{ist}_{\mathrm{out}(c)}(\varphi)\in E$: about the world, the levels say literally the same thing.

4. **A monotone schema has at most one consistent extension.** When every justification is $\top$ the consistency test never fails, the stages stop depending on the candidate, and the fixed point is forced.

5. **The copy schema is an instance.** It is monotone, consistent and shift-invariant, so its unique extension satisfies the conclusion. Without this the theorem could be about an empty class.

The reading is that inertness, not novelty, is what uniform treatment of contexts delivers — and that this is a guarantee rather than a defect wherever the requirement is the absence of drift: persistent records, audit trails, any setting in which a commitment made earlier must still mean the same thing later.

**Limits.** The shift must carry the right-hand side of part 2; dropping it, as one is tempted to, gives a false statement as soon as $\varphi$ itself contains an occurrence of $\mathrm{ist}$, since the shift relabels the context indices inside $\varphi$ too. Only on the base language, part 3, is the unshifted form correct. The frame map is required to be a **bijection** rather than merely a total injection; see the explanation for exactly where surjectivity is used. Nothing here decides the merely injective case.
"""

RIG_EXPL = r"""$$
E \text{ an extension} \;\Longrightarrow\; \sigma^{-1}(E) \text{ an extension} \;\Longrightarrow\; \sigma^{-1}(E)=E .
$$

The proof is organised around an arbitrary **logical automorphism** of the context language rather than around the shift, because the same lemma is needed twice — once here and once for the trichotomy, where the automorphism is an atom permutation instead.

**The transport lemma.** Let $e$ be a bijection of formulas realised by a bijection of valuations, in the sense that $v\models e\varphi$ iff $e^{*}v\models\varphi$, and commuting with negation. Suppose $e$ preserves $\mathrm{Cn}(T)$ and satisfies $e^{-1}(S)=S$ on the schema. Then $e^{-1}$ carries extensions to extensions. The proof shows stage by stage that
$$
E_i\bigl(e^{-1}(E)\bigr) \;=\; e^{-1}\bigl(E_i(E)\bigr),
$$
and takes the union. Three ingredients: consequence commutes with $e^{-1}$; the firing set of the schema commutes with $e^{-1}$; and preimage commutes with unions.

**Where surjectivity is used, and why it is a hypothesis rather than an oversight.** Both of the first two ingredients need it.

For consequence, one inclusion is free, but the other requires every model of $e^{-1}(X)$ to be the image of a model of $X$ — which is exactly surjectivity of the induced map on valuations.

For the firing set, a rule of $S$ must be pullable back along $e$. Given a rule whose consequent is $e\gamma$, one needs a rule of $S$ with consequent $\gamma$, and the inverse action on rules supplies it only when $e$ is invertible on formulas. With a merely injective frame map, a rule whose consequent lies outside the image of the shift has no preimage rule to fire, and the stagewise correspondence breaks. This is the step at which an informal proof is likely to say that groundedness is inherited stagewise by the same argument.

**Consistency transports**, since the valuation bijection carries a model of $E$ to a model of $e^{-1}(E)$. So $e^{-1}(E)$ is a consistent extension, and uniqueness gives $e^{-1}(E)=E$.

**Rigidity** is this at $e=\sigma$, the shift along the frame map. The hypothesis that $\sigma$ preserves $\mathrm{Cn}(T)$ follows from the base theory being context-free, since the shift fixes the base language pointwise.

**The consequence for levels** is then immediate: $\sigma(\mathrm{ist}_c(\varphi))=\mathrm{ist}_{\mathrm{out}(c)}(\sigma\varphi)$ by definition, so invariance is exactly the displayed equivalence — with the shift on the right-hand side, and only removable when $\varphi$ lies in the base language.

**Uniqueness in the monotone case** is separate and short: a consistent theory cannot contain $\neg\top$, so a monotone rule always fires, the stages become independent of the candidate, and any two consistent extensions are unions of the same stages.

**Formalization note.** Extensions are the Reiter fixed point transcribed directly, with the justification test referring to the candidate. Consequence is semantic. The development is free of `sorry` and `native_decide`; rigidity itself depends only on `propext` and `Quot.sound`.

**Limits.** The frame map is a bijection. No claim is made about the merely injective case: no counterexample was found, but this argument does not reach it.
"""

# ------------------------------------------------------------ 3. trichotomy

TRI_STMT = ("theorem TranscendenceTower.UniformityPlatform.uniformity_trichotomy"
            + signature("Sol_uniformity_trichotomy.lean")
            + " := by sorry\n")

TRI_NL = r"""$$
\textbf{(C)}\ \text{conservative}
\quad\vee\quad
\textbf{(U)}\ \text{not exactly one consistent extension}
\quad\vee\quad
\textbf{(P)}\ \text{not proposition-uniform}.
$$

Over a base theory that a group of automorphisms moves transitively across its models, every lifting schema satisfies at least one of the three. You may have new conclusions, or a determinate answer, or a uniform rule; not all three.

Four parts.

1. **The trichotomy.** Given a group $G$ of logical automorphisms preserving $\mathrm{Cn}(T)$ and the base language, and transitive on the models of $T$, any schema with a consistent extension is conservative, or fails uniqueness of that extension, or is not preserved by $G$.

2. **Proposition-uniformity implies invariance of the schema.** If a schema is closed under every substitution, then every atom automorphism carries it to itself — in both directions, since the inverse of an atom automorphism is again a substitution. This is the bridge between the informal notion of uniformity and the group-theoretic hypothesis of part 1.

3. **The tautological theory is symmetric.** Given two valuations, flip exactly the atoms where they disagree. No permutation is needed, and the flip has arbitrary support.

4. **The copy schema occupies corner (C)**, established through the trichotomy rather than by direct computation: it is proposition-uniform and monotone, hence preserved and uniquely extended, so the theorem places it in (C).

Part 3 is where the shape of the group matters. The flip used there has arbitrary support, so it does not lie in the group generated by permutations of atoms together with negations of single atoms — conjugating a single-atom negation by a permutation yields another single-atom negation, so that group contains only finitely supported sign patterns and is not transitive on valuations when the atom set is infinite. $\mathrm{Aut}(L)$ must be taken as the full $\{0,1\}^{A}\rtimes\mathrm{Sym}(A)$.

**Limits.** Symmetry of the base theory is a genuine hypothesis, not a consequence of the subject matter; it is used only to move an arbitrary model of $T$ onto a fixed one, and any condition doing that would serve. The tautological theory is the case of interest, since the question is whether the tower is by itself a source of new facts. The setting is propositional. The result is a disjunction: it says where content can come from, not that a context logic cannot have any.
"""

TRI_EXPL = r"""$$
\text{unique consistent } E \ \wedge\ g(E)=E \ \wedge\ T \text{ symmetric} \;\Longrightarrow\; E\cap L=\mathrm{Cn}(T)\cap L .
$$

The proof is in two steps, and the first is not proved again here.

**Step 1: the extension is invariant.** This is the transport lemma of the rigidity node, instantiated at an atom automorphism instead of at the shift. An automorphism preserving $\mathrm{Cn}(T)$ and preserving the schema carries extensions to extensions and preserves consistency, so uniqueness forces $g^{-1}(E)=E$. The two theorems really are one lemma; only the group differs.

**That the schema is preserved** is part 2 of the statement, and it is where the informal hypothesis does its work. An atom automorphism *is* a substitution — it sends the atom $a$ to a signed atom — so proposition-uniformity gives one inclusion directly. Its inverse is again a substitution of the same shape, and composing the two is the identity on formulas, which gives the other inclusion. This is what an informal proof means when it says that invertibility plus uniformity yields $g(S)=S$.

**Step 2: invariance forces conservativity.** Suppose a base sentence $\varphi$ lies in $E$ but not in $\mathrm{Cn}(T)$, so some model $M$ of $T$ falsifies it. The extension is consistent, so it has a model $v$; and $E$ contains $\mathrm{Cn}(T)$, so $v$ is a model of $T$. Symmetry supplies a $g$ in the group carrying $M$ to $v$ — at the level of atoms, which is all that base formulas see. Then $g\varphi$ is false at $v$, because $g$ is an isomorphism of the satisfaction relation and $\varphi$ is false at $M$. But $g\varphi$ lies in $E$ by Step 1, so $v$ satisfies it. Contradiction.

**On compactness.** A natural way to finish Step 2 is to collect the whole orbit $\{g\varphi\}$, observe that $T$ together with the orbit is unsatisfiable, and appeal to compactness to convert unsatisfiability into inconsistency. With a semantic consequence operator there is nothing to convert: a theory with no model is inconsistent by definition. Moreover the orbit is unnecessary. A single automorphism suffices — the one carrying the counter-model onto a model already in hand — so the infinite index set does no work at all in this argument.

**Symmetry of the tautological theory** is proved by exhibiting the automorphism: take the identity permutation and the sign pattern that is true exactly where the two valuations disagree. It is an involution, and it carries one to the other.

**Formalization note.** Atoms carry a sign, and negation flips that sign on a literal. This is what makes an atom automorphism a bijection of formulas rather than a bijection only up to logical equivalence: with unsigned atoms, a sign flip applied twice to $a$ yields the distinct formula $\neg\neg a$, the group acts on the Lindenbaum algebra alone, and the preimage of a schema is not the schema — so Step 1 does not typecheck. The development is free of `sorry` and `native_decide`, with axiom use confined to `propext`, `Classical.choice` and `Quot.sound`.

**Limits.** Symmetry of $T$ is a hypothesis. The setting is propositional; the substitution argument should survive the passage to first-order but the automorphism group becomes more delicate there and that has not been checked. Corner (C) is exhibited here; occupancy of (U) and (P) is established elsewhere in the same development, by explicit multi-extension and disguised-assertion constructions.
"""

# ---------------------------------------------------------------- 4. records

AUDIT_STMT = ("theorem TranscendenceTower.UniformityPlatform.record_audit"
              + signature("Sol_uniformity_audit.lean")
              + " := by sorry\n")

AUDIT_NL = r"""$$
\varphi \in E_n \quad\Longleftrightarrow\quad \varphi \in \mathrm{Cn}(\Lambda_{\le n})
\qquad (\varphi \in L)
$$

A record whose update rule treats all propositions alike says exactly what was logged. Every fact in it is attributable to a revision, and nothing in it is lost silently.

Read the contexts of a lifting schema as the revisions of a record. At revision $n$ a set $\Lambda_n$ of **entries** is logged; entries lie in the base language, since they are claims about the world rather than about the record. Write $\Lambda_{\le n}$ for the entries logged at or before $n$, let $S$ be a fixed update schema with consequents $\Gamma$, and let $E_n$ be an extension of $(\Lambda_{\le n}, S)$.

Four parts.

1. **Audit.** If $S$ is proposition-uniform and $\Lambda_{\le n}\cup\Gamma$ is consistent, then a base sentence lies in the extension exactly when it follows from the entries. The update rule contributes nothing about the world.

2. **Attribution.** If a base sentence is present at revision $n$ and absent at revision $m$, then it follows from the entries logged up to $n$ and not from those logged up to $m$. Some entry between the two revisions is therefore necessary for it: no fact appears that no revision accounts for.

3. **No silent loss.** For $m \le n$, every base sentence of $E_m$ lies in $E_n$. The record's content about the world only grows.

4. **A monotone schema's extension is not $\mathrm{Cn}(\Lambda \cup \Gamma)$.** With the tautological base and the single rule $\frac{a\,:\,\top}{a}$, the extension is $\mathrm{Cn}(\emptyset)$, which does not contain $a$, while $\mathrm{Cn}(\emptyset\cup\{a\})$ does. A monotone rule still carries a prerequisite, and a rule whose prerequisite is never derived never fires.

Part 4 is included because the identity it refutes is the natural bridge between the two halves of this subject, and stating the audit property without it invites the reader to prove it a shorter way that does not work.

**What is not assumed.** The schema need not be monotone: the practically interesting update rules — carry the previous value forward unless something supersedes it — are covered. The base theory need not be symmetric, which matters, because a log is a specific claim about the world and could never satisfy a symmetry hypothesis. Non-uniqueness of the extension is not an obstacle either: the statement holds of every extension, so what multiple extensions cost is reproducibility rather than auditability.

**Limits.** Consistency of $\Lambda_{\le n}\cup\Gamma$ is a hypothesis, and a necessary one: a log that contradicts what the update rule could ever say is a record that proves anything. Context-freeness of the entries is likewise necessary, and so is proposition-uniformity — a schema naming a particular sentence is an assertion in disguise, and it is the assertion rather than the record that would be doing the work.
"""

AUDIT_EXPL = r"""$$
E_n \subseteq \mathrm{Cn}(\Lambda_{\le n}\cup\Gamma)
\quad\text{and}\quad
\mathrm{Cn}(\Lambda_{\le n}\cup\Gamma)\cap L = \mathrm{Cn}(\Lambda_{\le n})\cap L .
$$

The whole result is those two facts composed. The first is a one-line induction; the second is the monotone dichotomy.

**The inclusion.** Every stage of the fixed-point construction lies inside $\mathrm{Cn}(\Lambda_{\le n}\cup\Gamma)$. The base stage is $\mathrm{Cn}(\Lambda_{\le n})$, which is contained in it because $\mathrm{Cn}$ is monotone. A successor stage is the consequences of the previous stage together with whichever consequents fired; the first part is handled by monotonicity and idempotence of $\mathrm{Cn}$, and the second because a fired consequent belongs to $\Gamma$ by definition. No hypothesis on the schema is used anywhere in this argument — not monotonicity, not uniformity — which is what makes the audit property available for defeasible update rules.

**The dichotomy.** Proposition-uniformity of the schema gives proposition-uniformity of its consequents, since an atom substitution applied to a rule is again a rule of the schema and acts on the consequent componentwise. The monotone dichotomy then applies with base theory $\Lambda_{\le n}$ and consequent set $\Gamma$, and returns that no new base sentence is derivable.

**Composing them.** A base sentence in $E_n$ lies in $\mathrm{Cn}(\Lambda_{\le n}\cup\Gamma)$ by the inclusion, hence in $\mathrm{Cn}(\Lambda_{\le n})$ by the dichotomy. The converse holds because the base stage of the construction is already $\mathrm{Cn}(\Lambda_{\le n})$, so the extension contains it.

**Attribution and monotonicity** are then immediate. If the sentence is absent at revision $m$ it cannot follow from the entries logged up to $m$, since anything that did would be in $E_m$; and the entries are cumulative, so $\mathrm{Cn}(\Lambda_{\le m})\subseteq\mathrm{Cn}(\Lambda_{\le n})$ for $m\le n$.

**The counterexample.** Take the tautological base and the single rule $\frac{a\,:\,\top}{a}$. Its prerequisite $a$ is not a tautology — the valuation sending every atom to false witnesses this — so the rule never fires, every stage is $\mathrm{Cn}(\emptyset)$, and the extension is $\mathrm{Cn}(\emptyset)$. But $\mathrm{Cn}(\emptyset\cup\{a\})$ contains $a$. Hence the reverse inclusion fails, and the identity between a monotone schema's extension and $\mathrm{Cn}(\Lambda\cup\Gamma)$ holds only for prerequisite-free schemas.

**Formalization note.** Consequence is semantic: $\mathrm{Cn}(T)$ is truth in every valuation satisfying $T$, so no proof calculus is defined and compactness is never used. Extensions are the staged Reiter construction transcribed directly, with the justification test referring to the candidate extension itself. The two sets that would otherwise need names — the consequents of a schema and the entries logged up to a revision — appear inline in the statement, so this node introduces no definitions of its own beyond those already published. The development is free of `sorry` and `native_decide`, with axiom use confined to `propext`, `Classical.choice` and `Quot.sound`.
"""

# ----------------------------------------------------------------- assembly

definition = {
    "definition_name": "TranscendenceTowerContextUniformity",
    "definition_title": ("The context language, Reiter extensions, and the "
                         "automorphisms acting on them"),
    "definition": (ROOT / "Definitions"
                   / "Def_TranscendenceTowerContextUniformity.lean")
        .read_text(encoding="utf-8"),
    "natural_language_statement": DEF_NL,
    "source": SOURCE + ", Section 2 (Framework), Definitions 1-11, in particular Definition 11 (Atom automorphisms).",
    "tags": TAGS,
    "private": True,
}

theorems = [
    {
        "theorem_name": "TranscendenceTower.UniformityPlatform.uniformity_monotone_dichotomy",
        "theorem_title": ("Monotone proposition-uniform lifting schemas are "
                          "conservative"),
        "formal_statement": MONO_STMT,
        "natural_language_statement": MONO_NL,
        "preamble": PREAMBLE,
        "source": SOURCE + ", Theorem 15 (Monotone dichotomy), Section 3.",
        "tags": TAGS,
        "private": True,
    },
    {
        "theorem_name": "TranscendenceTower.UniformityPlatform.uniformity_rigidity",
        "theorem_title": ("A context-uniform schema has a shift-invariant "
                          "extension"),
        "formal_statement": RIG_STMT,
        "natural_language_statement": RIG_NL,
        "preamble": PREAMBLE,
        "source": SOURCE + ", Theorem 21 (Rigidity), Section 5.",
        "tags": TAGS,
        "private": True,
    },
    {
        "theorem_name": "TranscendenceTower.UniformityPlatform.uniformity_trichotomy",
        "theorem_title": ("Conservativity, non-uniqueness, or non-uniformity: "
                          "a trichotomy for lifting schemas"),
        "formal_statement": TRI_STMT,
        "natural_language_statement": TRI_NL,
        "preamble": PREAMBLE,
        "source": SOURCE + ", Theorem 18 (Trichotomy), Section 4.",
        "tags": TAGS,
        "private": True,
    },
    {
        "theorem_name": "TranscendenceTower.UniformityPlatform.record_audit",
        "theorem_title": ("A record whose update rule is uniform says exactly "
                          "what was logged"),
        "formal_statement": AUDIT_STMT,
        "natural_language_statement": AUDIT_NL,
        "preamble": PREAMBLE,
        "source": (SOURCE + ", Section 6 (Records): Theorem 25 (Audit), "
                   "Corollary 26 (Attribution), Corollary 27 (No silent loss), "
                   "and Remark 6 (Prerequisites)."),
        "tags": TAGS,
        "private": True,
    },
]

EXPLANATIONS = {
    "Sol_uniformity_monotone_dichotomy.lean": MONO_EXPL,
    "Sol_uniformity_rigidity.lean": RIG_EXPL,
    "Sol_uniformity_trichotomy.lean": TRI_EXPL,
    "Sol_uniformity_audit.lean": AUDIT_EXPL,
}

for stmt in (MONO_STMT, RIG_STMT, TRI_STMT, AUDIT_STMT):
    assert stmt.strip().endswith(":= by sorry"), stmt[:120]
assert "PropUniform" in MONO_STMT
assert "shiftAut" in RIG_STMT and "Monotone" in RIG_STMT
assert "SymmetricUnder" in TRI_STMT and "AutL" in TRI_STMT
assert "IsExtension" in AUDIT_STMT and "Monotone" in AUDIT_STMT
assert "consequents" not in AUDIT_STMT and "logUpTo" not in AUDIT_STMT

(OUT / "payload_def_uniformity.json").write_text(
    json.dumps(definition, ensure_ascii=False, indent=2), encoding="utf-8")
(OUT / "payload_thms_uniformity.json").write_text(
    json.dumps(theorems, ensure_ascii=False, indent=2), encoding="utf-8")
for sol, expl in EXPLANATIONS.items():
    (OUT / (sol.replace(".lean", "") + ".expl.md")).write_text(
        expl, encoding="utf-8")

print("definition:", definition["definition_name"])
for t in theorems:
    print("theorem:  ", t["theorem_name"])
print("payloads in", OUT)
