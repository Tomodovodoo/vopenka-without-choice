# E10-E12: the repaired Schmerl route

This mathematical note is retained from proof development. Historical implementation labels are superseded by the [current repair summary](../README.md). The summary identifies the exact formalized scope.

This note gives the mathematical repair used to construct an elementary extension of cardinality \(\aleph_1\) with no proper ZF end extension from a countable ZF model. The standard-Q completeness theorem and the named-model application are now implemented. The application constructs a fresh coding ground containing an actual refutation support and all names for the original model, then combines the two forcing constructions with InternalQ soundness. The exact exports, independent review scopes and remaining generic absoluteness obligation are recorded in the countability integration record. The formal handoff table below describes the earlier implementation obligations, not their current status.

The core sentence below proves E06 through the selected-filter property it needs. The additional construction and `FinSmall` clause in the E05 coverage repair give the stronger E05 assertion about every maximal filter having an \(\omega_1\)-cofinal chain. Section 7 records the exact distinction and the added proof.

The source under review is [Enayat, *Models of set theory: extensions and dead-ends*, Appendix, Stage 2](https://doi.org/10.1017/jsl.2026.10199). All uses of choice in this note take place in the ambient ZFC universe. The object model is only required to satisfy ZF.

## 1. Exact input from the diamond construction

Fix a countable \(M_0\models\mathrm{ZF}\) in an ambient universe \(W\models\mathrm{ZFC}\). Force with the usual \(\omega_1\)-closed diamond forcing. In \(W_1\), the corrected Rubin construction gives an elementary extension \(N\succ M_0\) of size \(\aleph_1\) with the following properties:

* definable directed orders without a maximum have cofinal \(\omega_1\)-chains;
* maximally compatible filters with cofinal \(\omega_1\)-chains are parametrically definable in the original language.

Two qualifications belong to this input. Global filters are **definable**, rather than necessarily coded by sets of \(N\). Applying the literal coded version to the ordinal order would produce a set of all ordinals. Also, on a general poset, inclusion maximality of a directed filter does not by itself imply maximal compatibility. For internal finite partial functions the two notions agree, because the union of two compatible functions is an internal condition. The Appendix's separation argument uses maximal compatibility. These corrections are stated and checked in [RubinDefinableFilters.lean](../../../../ZFVP/ModelTheory/RubinDefinableFilters.lean).

We use only these consequences of the corrected construction:

1. The class tree \(T_{\mathrm{cl}}^N\), with nodes \((x,\alpha)\) where \(N\models x\subseteq V_\alpha\), has ordinal rank of external cofinality \(\omega_1\). Every cofinal branch is definable in \(N\).
2. For each internally infinite \(s\in N\), choose an increasing, cofinal chain \(C_s\) of internally finite subsets of \(s\), of order type \(\omega_1\).
3. Let \(T_s\) consist of internal binary functions whose domains lie in \(C_s\), ordered by extension. Every cofinal branch \(B\) generates the full filter

   \[
   F_B=\{p\in\operatorname{Fin}^N(s,2):
                       \exists b\in B\ p\subseteq b\}.
   \tag{S-F}
   \]

   This is a maximally compatible filter with a cofinal \(\omega_1\)-chain. It is therefore definable in \(N\), and Separation on the internal set \(\operatorname{Fin}^N(s,2)\) gives a code \(m\in N\) for all of \(F_B\).

For the last claim, any two branch nodes have a common later node. Any internal finite function compatible with every branch node is below a branch node on a domain containing its own domain. Thus it belongs to \(F_B\). This proves the required maximal compatibility without a converse claim about arbitrary filters. The branch nodes themselves are cofinal in \(F_B\).

There are at most \(\aleph_1\) branches of each tree: class branches have original-language definitions with finite tuples from \(N\), and function branches inject into their full filter codes. The total family of trees has size at most \(\aleph_1\).

## 2. Specialization and preservation of the ground branches

First restrict each rank order to a chosen cofinal copy of \(\omega_1\). The restriction has countable predecessor sets, whether or not the entire original rank order has countable initial sections. Cofinal branches of the restriction correspond to cofinal branches of the original tree by downward closure.

For a restricted tree, enumerate its at most \(\aleph_1\) branches. Choose on each branch a marker beyond its divergences from all earlier branches. At stage \(\xi<\omega_1\) there are only countably many earlier branches, so a rank above those divergences exists. Remove the branch tails after the markers to obtain the usual core, and use the anchor map when extending a coloring from the core. A cofinal branch through the core would have been one of the enumerated branches and would pass its marker, a contradiction. Every chain in the core is countable, because an uncountable chain would have cofinal ranks and generate such a branch.

Specialize all these cores at once. A condition is a finite coloring of their tagged disjoint union by \(\omega\), with distinct colors on distinct comparable nodes. Every chain in this disjoint union lies in one component and is countable. The finite-condition specialization theorem therefore makes this forcing \(P\) ccc. Its square has the same property: \(P\times P\) is the corresponding finite-coloring forcing on two disjoint copies of the union. This proves ccc of the square directly. It does not use the false assertion that an arbitrary product of ccc forcings is ccc. See [SchmerlSpecializationProducts.lean](../../../../ZFVP/ModelTheory/SchmerlSpecializationProducts.lean).

The generic coloring extends through the anchor maps to weak colorings of the original trees. For each tree the color range is externally countable, and on selected nodes it satisfies

\[
 x\leq y,z\ \land\ f(x)=f(y)=f(z)
       \quad\Longrightarrow\quad y\leq z\ \lor\ z\leq y.
 \tag{S-W}
\]

Here is the branch-preservation argument needed for the application. Let \(\dot B\) be a name for a cofinal branch through a ground ranked tree whose rank order has uncountable cofinality. In \(W_1\), form the set of pairs of forcing conditions which force their two branch copies to contain incomparable nodes. Choose a maximal antichain \(A\) inside this set. Since \(P\times P\) is ccc, \(A\) is countable. Choose a pair of splitting nodes for each member of \(A\), and bound all their ranks by one rank \(\gamma\).

Below an arbitrary condition, strengthen to a condition \(q\) forcing a node of \(\dot B\) above \(\gamma\). The diagonal pair \((q,q)\) is incompatible with every member of \(A\): compatibility would place both of that member's incomparable nodes below the same higher tree node. If two extensions of \(q\) could still force incomparable branch nodes, their pair would lie in the splitting set and be compatible with a member of \(A\), contradicting the preceding sentence. Thus all nodes that can be put on \(\dot B\) below \(q\) form a ground chain. Their downward closure is a ground cofinal branch, and \(q\) forces \(\dot B\) to be that branch. Such \(q\) are dense.

Consequently \(P\) adds no cofinal branch to any of the relevant trees. Every branch in \(W_1[H]\) still has its original definition or full filter code in \(N\). The precise local name argument is [SchmerlBranchPreservation.lean](../../../../ZFVP/ModelTheory/SchmerlBranchPreservation.lean), especially `CofinalBranchName.stabilizes_dense`.

## 3. One fixed countable infinitary sentence

Let \(L_0\) be the set-theory language with the countably many constants for \(M_0\). Enlarge it by finitely many relation symbols for the selected class ranks, selected domain chains, and color graphs. The relations for function trees take \(s\) as a variable. There is no separate symbol or conjunct for each element of the later uncountable model.

Use internal ordered pairs to code tree nodes. All the tree, rank, finite-function, and original membership relations are first-order formulas in this fixed language. The sentence \(\Phi\) includes the elementary diagram of \(M_0\), the ZF axioms, and the clauses below. These constitute one \(L_{\omega_1,\omega}(Q)\) sentence with a ground countable code.

### Actual uncountable cofinality

For a rank sort \(O\), rank order \(\leq_O\), and selected cofinal rank predicate \(D\), use

\[
 \begin{split}
 &(Qd)D(d),\\
 &\forall d\,[D(d)\to O(d)],\\
 &\forall a\,[O(a)\to\neg(Qd)(D(d)\land d\leq_O a)],\\
 &\forall a\,[O(a)\to\exists d(D(d)\land a\leq_O d)].
 \end{split}
 \tag{S-C}
\]

Under standard Q semantics, \(D\) is uncountable and each bounded part of \(D\) is countable. If \(O\) had a countable cofinal subset, \(D\) would be a countable union of countable bounded parts, a contradiction in the ambient ZFC universe. Thus \(\operatorname{cf}(O)>\omega\).

For \(T_s\), require \(C_s\) to be a linearly ordered cofinal family of internally finite subsets of \(s\), and impose (S-C) on its domain order. The clauses are universally quantified over internally infinite \(s\). For the class tree use the ordinal rank order and a cofinal predicate on it. Merely adding \((Q\alpha)\operatorname{Ord}(\alpha)\) would not give the cofinality conclusion.

### Branch candidates and original-language definitions

Require the color graph to be functional and total on selected nodes. Require its entire used range to be countable by

\[
                  \neg(Qc)\exists x\,\operatorname{Color}(c,x),
\]

and impose (S-W). For a selected node \(b\), define the full branch candidate

\[
 \begin{split}
 \psi_b(x)\quad\Longleftrightarrow\quad
 &x\in T\ \land\ \exists y\in T\,
 [\operatorname{Selected}(y)\land x\leq y\\
 &\qquad\land(y\leq b\ \lor\ (b\leq y\land f(b)=f(y)))].
 \end{split}
 \tag{S-B}
\]

Let \(\operatorname{Cof}(\psi_b)\) say that its ranks are cofinal in the full rank order. Whenever this holds, (S-W) makes \(\psi_b\) a cofinal branch. Conversely, for any cofinal branch, the selected nodes on it have a color occurring cofinally, by (S-C) and countability of the color range. Choose a node \(b\) of that color on the branch. The weak-fork condition makes every same-colored selected successor of \(b\) lie on that branch, and those successors are cofinal. Therefore (S-B) defines exactly the full branch.

Enumerate **only** the formulas \(\varphi_n(x,\bar z_n)\) of \(L_0\), allowing every finite parameter arity. For the class tree impose

\[
 \forall b\Bigl[
   \operatorname{Selected}(b)\land\operatorname{Cof}(\psi_b)
   \ \to\
   \bigvee_{n<\omega}\exists\bar z_n\,
       \forall x\bigl(\psi_b(x)\leftrightarrow
                          \varphi_n(x,\bar z_n)\bigr)
              \Bigr].
 \tag{S-D}
\]

The auxiliary predicates in \(\psi_b\) do not occur in any \(\varphi_n\). Thus the consequence is definability in the original reduct. Enumerating formulas of the expanded language would allow \(\psi_b\) itself and make this condition vacuous. The fixed-syntax construction and semantic extraction are in [SchmerlInfinitaryTreeSentence.lean](../../../../ZFVP/ModelTheory/SchmerlInfinitaryTreeSentence.lean).

### Full function-filter codes

For a selected function node \(b\in T_s\), define

\[
 \begin{split}
 \Xi_{s,b}(p)\quad\Longleftrightarrow\quad
 &p\in\operatorname{Fin}^N(s,2)\ \land\
 \exists y\in T_s\,[p\subseteq y\\
 &\qquad\land(y\subseteq b\ \lor\
           (b\subseteq y\land f_s(b)=f_s(y)))].
 \end{split}
 \tag{S-X}
\]

Here \(T_s\) is already restricted to the selected domains. Require

\[
 \forall s\,\forall b\Bigl[
   \operatorname{Infinite}^N(s)\land b\in T_s
      \land\operatorname{Cof}(\psi_{s,b})
   \ \to\ \exists m\,\forall p\,
                  (p\in m\leftrightarrow\Xi_{s,b}(p))
                         \Bigr].
 \tag{S-K}
\]

This is a first-order clause in the expansion. It codes all the finite partial functions below the branch. A code containing only the selected nodes would not suffice. The equivalence between the cofinal-candidate clauses and coding the branch-generated full filters is in [SchmerlFunctionCandidates.lean](../../../../ZFVP/ModelTheory/SchmerlFunctionCandidates.lean).

The expanded \(N\) in \(W_1[H]\) satisfies \(\Phi\). The chosen rank and domain chains witness (S-C); the generic weak colorings supply (S-W); Section 2 ensures that every cofinal candidate is an old branch; Section 1 supplies its original-language definition or full filter code. This verifies the clauses for every parameter in \(N\).

## 4. Keeping the ccc argument internal

If the formal ambient ground is a countable model \(K\models\mathrm{ZFC}\), \(\omega_1^K\) is externally countable. The preceding combinatorial proofs must be interpreted **inside \(K\)**. An external theorem about uncountable subsets of the type of elements of \(K\) cannot prove an internal ccc assertion.

For omega-one preservation, let \(p\) force that \(\dot g:\omega^K\to\omega_1^K\). Work in \(K\), and for every \(n\in\omega^K\) take an internal maximal antichain below \(p\) deciding \(\dot g(n)\). Internal Choice produces the internal family of antichains and their value maps. Internal ccc makes each antichain countable in \(K\); internal countable union and regularity bound all possible values below a single \(\beta<\omega_1^K\). The forcing theorem then gives \(p\Vdash\operatorname{ran}(\dot g)\subseteq\beta\). No new countable sequence is cofinal in \(\omega_1^K\), so it remains the first uncountable ordinal.

The same discipline applies to Section 2. Its splitting set, maximal antichain, chosen splitting witnesses, countability proof, and common rank bound must all be sets of \(K\), obtained using its ZFC axioms. A generic then meets the internally definable dense set of conditions deciding a ground branch. This is exactly the name-level statement required for the internally constructed trees. It does not assert that every arbitrary external branch of a countable \(K\) is represented by a name in \(K\).

For the first forcing, the descending decision construction through every \(n\in\omega^K\), followed by its internal closure bound, proves omega-one preservation in the same internal way. These two arguments prove that \(K\) and its two-step extension have the same internal \(\omega_1\).

## 5. Keisler transfer and the size bound

The mathematical input is Keisler's completeness theorem for the countable infinitary logic with Q interpreted as uncountability. His original paper identifies the infinitary extension as Theorem 4.7, following its omitting-types theorem. [Keisler, *Logic with the quantifier "there exist uncountably many"*, 1970](https://doi.org/10.1016/S0003-4843(70)80005-5). Its bibliographic entry is also on [Keisler's publications page](https://people.math.wisc.edu/~hkeisler/papers.html).

Here is the transfer once that exact completeness theorem and its proof-code interpretation are in place. Suppose \(W\subseteq W'\) are ZFC universes with the same \(\omega_1\), and \(\Phi\in W\) is the fixed countable sentence. If \(W'\) has a standard model of \(\Phi\) but \(W\) has none, completeness in \(W\) supplies a ground refutation of \(\Phi\). View this refutation in \(W'\). Its ground syntax codes and rule instances remain valid; for an infinitary proof tree, its ground ordinal ranking still witnesses well-foundedness. Soundness in \(W'\) contradicts its standard model of \(\Phi\). The formal theorem needed here is upward validity of an existing ground refutation. It is unnecessary to claim that every proof in the extension was already in the ground.

For the other direction, an old standard model remains a standard model in an omega-one-preserving extension. Old countable definable sets retain their enumerations. An old uncountable definable set contains an injection from the old \(\omega_1\), by ground AC, and that injection still has uncountable domain. Structural induction through the ground infinitary syntax therefore preserves all Q truth values as well as the ordinary Boolean and first-order clauses.

Apply the downward direction to \(W'=W_1[H]\). It produces a standard model of \(\Phi\) in \(W\).

The reduction to cardinality \(\aleph_1\) is a separate argument. Close the countable set of subformulas of \(\Phi\) under the required syntactic operations. In a standard model, start with \(\aleph_1\) elements, including the interpretations of its constants. At each of countably many closure stages, for every formula in this fragment and every finite parameter tuple already selected, add one existential witness when needed and \(\aleph_1\) distinct witnesses for each true Q formula. Ambient Choice permits these selections, and each stage has size at most \(\aleph_1\). The union has size exactly \(\aleph_1\). Induction on the fragment shows that existential truth is preserved by the witness choices; true Q instances retain \(\aleph_1\) witnesses, and false Q instances remain countable after restriction. Countable conjunctions are handled by the same structural induction. Thus the restricted structure still satisfies \(\Phi\).

### The remaining completeness implementation

The current `KeislerDerivation` soundness theorem does not establish completeness of that particular calculus. Its connection to the cited theorem must be proved. The following are the substantive construction steps, rather than additional hypotheses for the final export:

* obtain a countable weak model of a consistent fragment, with Q truth recorded consistently and with the required infinitary types omitted;
* prove the countable extension lemma, preserving weak elementarity, omitting the types that would add elements to a Q-small fiber over old parameters, and adding fresh witnesses to the designated Q-large fibers;
* iterate the extension lemma through \(\omega_1\), scheduling every formula and parameter tuple, and prove the union truth lemma for the countable fragment;
* show that every Q-small fiber is frozen at a countable stage and every Q-large fiber acquires \(\aleph_1\) distinct witnesses, yielding standard semantics;
* derive completeness for the repository's exact proof codes, then the transfer and size-reduction statements above.

These steps cannot be replaced by first-order compactness of the expansion alone. No formal completeness claim is made by this note.

## 6. Extracting the endpoint E06

Let \(M\) be the original reduct of the size-\(\aleph_1\) standard model of \(\Phi\). Its elementary-diagram constants give an elementary embedding of \(M_0\); take an isomorphic copy so that this is an inclusion.

Every amenable class \(A\) of \(M\) gives a full branch in its class tree, consisting of its coded intersections with the internal rank segments. Sections 3 and 5 make that branch definable in the original reduct, so \(A\) is definable there. Thus \(M\) is rather classless.

Now let \(j:M\to E\) be any membership end extension with \(E\models\mathrm{ZF}\). Fix an internally infinite \(s\in M\) and a binary function \(\chi:j(s)\to2\) in \(E\). For every chosen internally finite domain \(c\in C_s\), the graph

\[
                         \chi\mathbin{\upharpoonright}j(c)
\]

is old. This uses the internal finite-subset absoluteness lemma for ZF end extensions. It does not assume that \(c\) is externally finite. These restrictions form a full cofinal branch of \(T_s\). Clause (S-K) codes its entire filter by some \(m\in M\).

In \(E\),

\[
                              j(\bigcup m)=\chi.
\]

One inclusion follows because every member of the coded filter lies below a branch restriction. For the other, take a pair \((x,\chi(x))\). The end-extension property makes \(x\) an old element of \(s\). Some chosen finite domain contains its singleton, so that pair lies in the corresponding branch restriction, which is itself a member of the coded filter. Thus every binary function on an old internally infinite set is old. Internally finite domains use finite-subset absoluteness directly. Characteristic functions now show that \(j\) preserves every powerset.

For any subset definable in \(E\) with parameters from \(E\), Separation in \(E\) forms its intersection with each \(j(s)\). Powerset preservation makes each such intersection old. Its trace on \(M\) is consequently amenable, hence definable in \(M\) by rather classlessness. Thus every ZF end extension of \(M\) is conservative. The theorem that no model of ZF has a proper conservative ZF end extension rules out a proper \(E\).

These last steps are represented by [SchmerlFunctionTreeEndExtension.lean](../../../../ZFVP/ModelTheory/SchmerlFunctionTreeEndExtension.lean) and `no_conservative_proper_end_extension` in [NoConservativeEndExtension.lean](../../../../ZFVP/ModelTheory/NoConservativeEndExtension.lean). The endpoint follows from the selected-filter property just proved; no converse from arbitrary maximal filters to selected branches enters this argument.

## 7. Exact effect on E05 and the formal workplan

The supplied route to E06 is

\[
 \begin{gathered}
 \text{corrected diamond construction}
 \ \Longrightarrow\ \text{branch definitions and full filter codes},\\
 \text{ccc square specialization}\ +\ \text{fixed corrected }\Phi
 \ +\ \text{Keisler transfer}\\
 \Longrightarrow\ \text{rather classless model with selected-filter coding}
 \Longrightarrow\ \text{powerset preservation of every ZF end extension}\\
 \Longrightarrow\ \text{conservativity}\ \Longrightarrow\ \text{E06}.
 \end{gathered}
\]

The E05 contract quantifies over every maximal filter on \(\operatorname{Fin}^M(s,2)\) having a cofinal \(\omega_1\)-chain. The existing branch-to-filter construction proves that selected branches give such filters. Its converse requires the additional domain-coverage condition

\[
                    \forall c\in C_s\ \exists p\in F\quad
                                    c\subseteq\operatorname{dom}(p).
 \tag{S-cover}
\]

Maximality by itself only gives coverage of individual elements of \(s\); it cannot replace (S-cover) for an internally finite set that may be externally infinite. The core sentence \(\Phi\) does not supply that implication.

The E05 coverage repair supplies a stronger realized sentence \(\Phi^+\). At every Rubin successor it omits the types for new members of old internally finite sets, using the corrected block cofinality criterion and internal finite induction. Thus every internally finite set in the diamond union is externally countable. The single clause

\[
 \forall a\,[\operatorname{Finite}(a)\to\neg(Qx)(x\in a)]
\]

preserves this requirement through the standard-Q transfer. For a maximal filter with an \(\omega_1\)-cofinal chain, individual domain coverage can now be bounded over every countable selected domain by one chain index. This proves (S-cover), reconstructs the entire filter from its selected branch, and establishes the full E05 conclusion using (S-K). The additional requirement is an output of the construction and part of the transferred sentence. It is not an extra hypothesis on the input model or a weakening of weak Rubinness.

| Node | Concrete mathematical repair | Remaining formal work |
| --- | --- | --- |
| E08/E09 | Add the finite-set omission types at each successor; the diamond union then satisfies `FinSmall`. | Prove the internal finite cofinal-union lemma, joint type omission, and persistence of old finite-set membership through the elementary chain. |
| E10 | Specialize the disjoint union of the branch cores; prove ccc of its square; use the splitting-antichain proof to preserve branches. | Internalize these ZFC arguments and the two-step forcing application, retaining all internal countability and name hypotheses. |
| E11 | One countable language, explicit Q cofinality, original-language class definitions, and full-filter code clause (S-K). | Assemble the whole fixed sentence, its ground realization, and extraction of the selected-filter property. Individual semantic lemmas are not this assembly. |
| E12 | Use exact standard-Q completeness; transport an existing ground refutation; prove the fragment witness-closure size bound. | Complete the weak-model and \(\omega_1\)-chain construction and connect it to the actual derivation codes. |
| E05 | Use the stronger realized sentence \(\Phi^+\), derive (S-cover) from `FinSmall`, and code every maximal filter in the original contract. | Implement the coverage and full-filter reconstruction of the E05 repair, then assemble the actual weakly Rubin model theorem. |
| E06 | Apply the explicit alternative through selected-filter coding, finite-subset absoluteness, powerset preservation, and rather classlessness. | Compose the actual construction and extraction theorems with the checked end-extension lemmas; retain the original countable-input and size-\(\aleph_1\) conclusion. |

This is a mathematical proof handoff with named inputs. It is not evidence that E05, E06, or E10-E12 have passed their Lean completion gates.
