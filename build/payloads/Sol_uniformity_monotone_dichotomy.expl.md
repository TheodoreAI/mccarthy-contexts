$$
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
