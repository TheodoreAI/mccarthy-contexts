$$
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
