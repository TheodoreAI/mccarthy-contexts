$$
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
