We prove the four-part **Theorem of Necessary External Grounding** over concrete partial recursive program codes $\mathrm{Code}$ (`Nat.Partrec.Code`) and the modal context language $\mathrm{CForm}\;A\;C$ of `Def_TranscendenceTowerContextUniformity`:

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
