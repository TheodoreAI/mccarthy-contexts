$$
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
