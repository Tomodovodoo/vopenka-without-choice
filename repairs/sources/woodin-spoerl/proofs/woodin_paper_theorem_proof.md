# The corrected Woodin theorem needed by the paper

This mathematical note is retained from proof development. Historical implementation labels are superseded by the [current repair summary](../README.md). The summary identifies the exact formalized scope.

10 September update. The source-to-restricted-lift proof is the current W04 target. It connects the construction, actual enumeration invariant, directed quotient bound, relative generic movement and low-name forcing theorem, and specifies the remaining Lean interfaces. The earlier whole successor-rank contract is excluded from the paper's proof route. The W01-W10 ledger records written proofs and formal status separately.

This theorem and proof use a consistent least-failure seed, distinguish the raw inverse limit from its completed stage, and state the lift on the final ranks used by finite restoration. The accompanying proof bundle includes the detailed supporting arguments. The W02 handoff and W04 bridge track Lean correspondence and the remaining implementation.

Read the full proof bundle for this proof together with every supporting appendix. The applied passages record the LaTeX changes now present in V13.

## 1. Statement and conventions

Work in ZF and suppose AC fails. Let \(\mu\) be the least ordinal for which \(\mathrm{DC}_\mu\) fails, and let \(\Omega>\mu\) be supercompact in Woodin's sense. Here \(\mathrm{DC}_\xi\) means dependent choice for ordinal histories of length \(\xi\). The ground facts below show that \(\mu\) is regular and lies below every ground supercompact.

For an infinite regular cardinal \(\nu\), let \(C_\nu^\kappa\) have conditions the partial functions \(p\) on \(\nu\times\kappa\) such that
\[
|\operatorname{dom}(p)|<\nu,\qquad
p(i,\xi)\in V_{1+\xi},
\]
ordered by reverse inclusion. Ranks, the regular lower index, and the collapse are interpreted in the extension immediately preceding that collapse.

Use the sparse presentation with bounded normalized coordinate names specified in the presentation appendix. It is explicitly equivalent to the bounded saturated-name presentation. Write \(a_\eta=\langle s_\eta,K_\eta\rangle\), where \(s_\eta\) contains the six carrier, order, top, projection, empty-tail inclusion and prefix-replacement tables through \(\eta\), and \(K_\eta\) is the actual cutoff table including the seed. The fixed presentation defines its name pools from these data. At marked \(\eta\), the whole code belongs to \(V_{\eta+\omega}\).

Define the completed stages \(P_\beta,c_\beta\) as follows.

* \(P_0\) is trivial and \(c_0=\mu\). The seed need not be inaccessible.
* At a successor, \(c_{\alpha+1}\) is the least ground strongly inaccessible \(\kappa>c_\alpha\) for which
  \[
  P_\alpha*\dot C_{c_\alpha}^{\kappa}
       \Vdash\mathrm{DC}_{<\kappa}.
  \]
  This two-step forcing is \(P_{\alpha+1}\).
* At a nonzero limit \(\beta\), put \(\gamma_\beta=\sup_{\alpha<\beta}c_\alpha\). If it is ground strongly inaccessible, take the direct limit and set \(c_\beta=\gamma_\beta\).
* Otherwise take the raw inverse limit \(R_\beta\), including its inherited support restrictions at earlier direct cuts. In its extension put \(d_\beta=(\gamma_\beta^+)^{V[H]}\). This ordinal has a constant value by weak homogeneity. Take the least successful ground inaccessible \(\kappa>\gamma_\beta\) for
  \[
  R_\beta*\dot C_{d_\beta}^{\kappa}
       \Vdash\mathrm{DC}_{<\kappa},
  \]
  and use this completed forcing for \(P_\beta\), with \(c_\beta=\kappa\).

A stage \(\gamma\) is marked if \(c_\gamma=\gamma\). Completed projections include the collapse completing their stage. A direct stage has no extra collapse coordinate. This convention removes the ambiguity between a raw inverse limit and the collapse appended to it.

**Theorem.** The construction is defined through \(\Omega\). Its endpoint \(Q=P_\Omega\) is weakly homogeneous and uniformly \(\Sigma_3\)-definable over \(V_\Omega\). Let \(G\subseteq Q\) be generic, \(G_\alpha\) its completed prefix generics, and \(W=V[G]\).

1. **Ranks and Choice.** Every marked \(\gamma\leq\Omega\) is a direct stage, remains strongly inaccessible in \(W\), and
   \[
   W_\gamma=V_\gamma[G_\gamma]=(V[G_\gamma])_\gamma
   \models\mathrm{ZFC}.
   \tag{A}
   \]
   Every ground supercompact \(\gamma\leq\Omega\) is marked.
2. **Factors and generic movement.** The prefix maps give complete factorizations. Over \(V[G_\alpha]\), each later quotient has lower bounds in its separative preorder for directed families with an ordinal enumeration of length below \(c_\alpha\). Consequently it preserves \(\mathrm{DC}_{<c_\alpha}\) and adds no shorter sequences of old sets. If \(t\in Q\) and its completed \(\alpha\)-prefix belongs to \(G_\alpha\), there is a generic \(G^*\) such that
   \[
   t\in G^*,\qquad G^*_\alpha=G_\alpha,\qquad V[G^*]=W.
   \tag{B}
   \]
3. **The rank lift.** Suppose
   \[
   J:V_{\bar\gamma+\omega}\longrightarrow V_{\gamma+\omega}
   \]
   is elementary, \(J(\bar\gamma)=\gamma<\Omega\),
   \[
   e=\operatorname{crit}(J)<\bar\gamma<\delta=J(e),
   \]
   \(\gamma\) is marked, and \(J\) maps the actual complete iteration code through \(\bar\gamma\) to that through \(\gamma\). Then \(\bar\gamma,e,\delta\) are marked and there is an elementary map
   \[
   j:W_{\bar\gamma}\longrightarrow W_\gamma
   \tag{C}
   \]
   with critical point \(e\), \(j(e)=\delta\), and
   \[
   j(x)=J(x)\qquad(x\in V_{\bar\gamma}^V).
   \]
   Its graph belongs to \(W_\Omega\).
4. **Finite windows.** For each \(k<\omega\) there is an effectively obtained finite \(r_k\) such that, if \(\lambda<\Omega\) is marked, the relevant ranks compute their actual prefixes, and
   \[
   V_\lambda\prec_{\Sigma_{r_k}}V_\Omega,
   \]
   then
   \[
   W_\lambda\prec_{\Sigma_k}W_\Omega.
   \tag{D}
   \]
   In particular this applies when \(\lambda,\Omega\) are ground supercompact and have the same sufficiently high ground \(C^{(r_k)}\) correctness.

The theorem makes no assertion about Woodin's ambient-HOD clause. In (C), the domain is the final rank \(W_{\bar\gamma}\). The next collapse at a marked stage can add subsets of its endpoint, so rank stabilization alone does not give a lift on the whole successor rank. The separate successor-rank audit gives a sufficient repair under an additional taller ground-embedding hypothesis; that hypothesis is not asserted here.

## 2. Ground facts and the successor step

The ground-facts proof derives the following from Woodin's Definition 220 and Lemma 222: supercompact cardinals are strongly inaccessible and \(C_2\)-correct, their ranks satisfy ZF, small embeddings can have their critical point above any prescribed smaller bound, and the regular least-failure seed \(\mu\) lies below each supercompact.

The collapse proof proves the strict restoration lemma. If \(\delta\) is ground supercompact, the prefix \(P\) and its order belong to \(V_\delta\), and
\[
P\Vdash\text{"\(\nu<\delta\) is infinite regular and
                    \(\mathrm{DC}_{<\nu}\)"},
\]
then above any prescribed bound below \(\delta\) there is a ground strongly inaccessible \(\kappa<\delta\) with
\[
P*\dot C_\nu^\kappa
 \Vdash\operatorname{Reg}(\kappa)\land\mathrm{DC}_{<\kappa}.
\tag{1}
\]

The proof first bounds ordinal decisions in a small column subcollapse, proving regularity of the upper inaccessible without Choice. A small ground embedding then reflects any serial relation into a bounded source rank. The full collapse well-orders the source relation's bounded pool of names. Taking the least permitted successor in that well-order gives a branch; every short history lies in the smaller extension by closure. Mapping the branch pointwise gives \(\mathrm{DC}_\nu\), and the cardinal-equivalent-length argument gives \(\mathrm{DC}_{<\delta}\).

To obtain a cutoff strictly below \(\delta\), apply one ground small embedding with critical point above the prescribed bounds. The closed-model reflection proof identifies global DC with DC inside its \(\Sigma_1^*\)-correct rank extensions. Therefore the larger collapse's DC reflects to the collapse at that critical point. This is where the strengthened correctness is used. No prior preservation of supercompactness by \(P\) is assumed.

## 3. Quotient bounds and the raw inverse limit

The inverse-limit proof constructs the quotient bound using one base-forcing name for an enumerated directed family. It labels possible ground values by the base conditions that force them. At each coordinate it takes the union of graph entries guarded by those conditions and the already constructed prefix.

One label condition witnesses the comparison at every coordinate. The evaluated graphs are a compatible family of size below the regular lower collapse index, so their union is a condition. For every later inaccessible direct cut, the possible values' least support bounds form a ground function on a set of rank below that cut. Strong inaccessibility bounds all those supports at once. The same argument bounds coordinate-name ranks below the current upper cutoff. The recursion is therefore a legal ground condition, including at raw inverse limits.

This gives the directed-family assertion in part 2. Applying it to descending condition-and-name histories gives DC preservation and the stated absence of new short sequences, with all needed dependent choice used in the completed base extension.

At a non-inaccessible limit \(\beta\), this bound is available before the new DC conclusion. The raw extension preserves the earlier \(\mathrm{DC}_{<c_\alpha}\) and regular \(c_\alpha\). Thus \(\gamma=\gamma_\beta\) is a limit cardinal there and \(\mathrm{DC}_{<\gamma}\) holds.

A ground unbounded map \(V_\rho\to\gamma\), for some \(\rho<\gamma\), witnesses failure of strong inaccessibility. An earlier collapse well-orders this ground domain by an ordinal below \(\gamma\), so the raw extension makes \(\gamma\) singular. Fix a cofinal sequence of length \(\operatorname{cf}(\gamma)<\gamma\). DC at that length builds coherent blocks, each extendible using DC below \(\gamma\). Their union proves \(\mathrm{DC}_\gamma\).

Every ordinal below the raw extension's own \(\gamma^+\) has cardinality at most \(\gamma\). The ordinal-length argument therefore proves
\[
R_\beta\Vdash
\mathrm{DC}_{<(\gamma^+)^{V[\dot H]}}
\land\operatorname{Reg}\bigl((\gamma^+)^{V[\dot H]}\bigr).
\tag{2}
\]
The regularity follows from \(\mathrm{DC}_\gamma\), which gives the choice needed to bound a putative short cofinal sequence in the successor. This proves the assertion from Woodin's printed page 324 for the raw forcing, before the extra collapse.

Weak homogeneity makes that successor a constant ordinal \(d\). Since \(R_\beta\in V_\Omega\), small forcing preserves strong inaccessibility of \(\Omega\), giving \(d<\Omega\). Apply (1) to \(R_\beta,d\) and append the least successful collapse. The regularity needed for this collapse has already been proved in (2).

## 4. Completing the construction and identifying marked stages

The construction proof performs a simultaneous induction on all the stated data. At successors, (1) supplies a cutoff below \(\Omega\). At a limit below \(\Omega\), regularity of \(\Omega\) bounds the cutoff supremum and the raw forcing rank below \(\Omega\).

If the limit supremum \(\gamma\) is strongly inaccessible, the stage index \(\beta\) equals \(\gamma\): otherwise its cofinal cutoff sequence would be an unbounded map from the smaller ordinal \(\beta\) into \(\gamma\). The direct-limit quotient bounds preserve DC at every length below \(\gamma\). To prove regularity, for each \(\xi<\gamma\) choose an earlier \(c_\alpha>\xi\). Any proposed cofinal \(\xi\)-sequence belongs to the earlier extension, where the small prefix preserves strong inaccessibility of \(\gamma\). Its range is consequently bounded.

At the other limits, use Section 3 and then append the restoration collapse. The presentation proof supplies the rank estimates, exact splice maps, and canonical automorphisms throughout this induction. Row permutations at a collapse move one condition's used rows away from the other's; normalized union gives a common extension. The specified inverse permutations and normalization give actual automorphisms. Their recursion respects all earlier direct supports and can fix an arbitrary earlier prefix. This proves weak homogeneity and (B).

Repeat the boundedness induction with any ground supercompact \(\delta\leq\Omega\) as outer bound. The same least-choice recursion then has \(c_\alpha<\delta\) for every \(\alpha<\delta\). Since \(c_\alpha\geq\alpha\), its supremum at \(\delta\) is \(\delta\); the direct rule makes \(c_\delta=\delta\). In particular the endpoint at \(\Omega\) exists.

The definition proof supplies actual bounded certificates for the presentation operations. The global positive DC restoration test is \(\Pi_2\), and its failure is \(\Sigma_2\). A supplied history with least successful cutoffs therefore has an \(\exists\forall\exists\) definition. At \(V_\Omega\), \(C_2\) correctness makes all the \(\Pi_2\) tests, their failures, and the bounded operations agree with the universe. Uniqueness identifies the internal recursion with the actual one. Existentially quantifying a prefix containing a sparse condition gives the stated \(\Sigma_3\) endpoint definition.

## 5. Endpoint ranks and ZFC

The actual-stage enumeration proof proves the precise invariant
\[
V[G_i]\models
\forall\rho<i\ \exists\nu<c_i\ \exists f:\nu\twoheadrightarrow V_\rho
\qquad(i\leq\Omega).
\tag{E}
\]
At the trivial seed this is vacuous. Suppose it holds at \(i\). Closure and \(\mathrm{DC}_{<c_i}\) imply that the quotient adds no functions of length below \(c_i\) with old values. An old short enumeration of \(X\) then shows that no new subset of \(X\) is added, by pulling a characteristic function back along the enumeration. Induction on rank preserves all ranks through \(i\). The actual next collapse enumerates each of those ranks by \(c_i<c_{i+1}\), proving (E) at \(i+1\).

At a nonzero limit \(\theta\), fix \(\rho<\theta\) and take the specified earlier index \(i=\rho+1<\theta\). Its enumeration of \(V_\rho\) has length below \(c_i\), and the actual quotient to the completed \(\theta\) preserves that rank. The same enumeration works at \(\theta\), since \(c_i<c_\theta\). This argument applies to direct and completed inverse limits. Repeating it with the separately constructed endpoint gives (E) at \(\Omega\). It does not choose a family of earlier enumerations.

At a marked \(\gamma\), (E) gives an ordinal enumeration of each \(W_\eta\), \(\eta<\gamma\), of length below \(\gamma\). The tail preserves these ranks and regularity of \(\gamma\). For Replacement in \(W_\gamma\), form the output-rank function using ambient satisfaction for this set structure, compose it with one short enumeration of its domain's rank, and use regularity to bound the outputs. For Choice, take the least enumeration index meeting each member of a family. The resulting graph has rank below \(\gamma\). The other ZF axioms follow from transitivity and the rank construction.

Bounded name pools give a name in \(V_\gamma\) for every resulting object. Conversely every such name has bounded support and a value of rank below \(\gamma\). This proves all equalities in (A), including when \(W\) is the later full extension.

## 6. The rank lift

Assume the hypotheses of (C). The captured actual cutoff table makes \(\bar\gamma\) marked. For \(\alpha<e\), its actual cutoff \(c_\alpha\) is fixed by \(J\), since both tables agree and \(J(\alpha)=\alpha\). If \(c_\alpha\geq e\), then
\[
c_\alpha=J(c_\alpha)\geq J(e)=\delta>\bar\gamma,
\]
contradicting source markedness. Thus all those cutoffs lie below \(e\). The critical-point argument makes \(e\) strongly inaccessible. Hence \(e\) is marked, and its image \(\delta\) is marked.

For \(q\in G_{\bar\gamma}\), covariance of the captured projections gives
\[
J(q)\restriction\delta=J(q\restriction e)
                      =q\restriction e\in G_\delta.
\tag{3}
\]
The last equality holds because individual direct-limit conditions of \(P_e\) belong to \(V_e\).

In \(V[G_\delta]\), form the directed family
\[
D=J^{\prime\prime}G_{\bar\gamma}
\]
in the target quotient \(P_\gamma/G_\delta\). The source generic has rank below \(\delta\). Part (A) at \(\delta\) makes it well-orderable of size below \(\delta\), so \(D\) has an ordinal enumeration of that size. Part 2 gives a quotient lower bound \(t\). Applying (B) above \(\delta\) produces \(G^*\) containing \(t\), with \(G^*_\delta=G_\delta\) and the same full extension. In particular the source generic is unchanged.

A generic containing a condition below \(z\) in the separative preorder contains \(z\), by the dense set of conditions below \(z\) or incompatible with it. Hence
\[
J^{\prime\prime}G_{\bar\gamma}\subseteq G^*_\gamma.
\tag{4}
\]

The set-coded rank-lifting proof now applies. Its low name pools and their atomic and finite-formula forcing certificates fit in the displayed larger ranks. The certificate clauses are bounded in supplied sets and have unique solutions; their existence is proved in the ambient ZF universe. Therefore \(J\) carries the source forcing certificate to the actual target one. This does not assume that \(V_{\bar\gamma+\omega}\) or \(V_{\gamma+\omega}\) is a ZF model. The W04 bridge, Sections 7-8, gives the exact support bounds and the definable induction needed for all internal formula codes.

Define
\[
j(\tau^{G_{\bar\gamma}})=J(\tau)^{G^*_\gamma}
\quad\text{for low source names }\tau.
\]
The truth lemma, covariance and (4) prove well-definedness and elementarity. Check names give agreement with \(J\) on ground elements. Part (A) identifies both interpreted structures with the final ranks in the same \(W\). The graph is a set by Replacement and has rank below \(\gamma+\omega<\Omega\), so it belongs to \(W_\Omega\). This proves (C).

## 7. Finite windows and the paper's application

The endpoint-forcing proof supplies a uniform formula \(\vartheta_k\) over each correctly computed endpoint rank. For bounded formulas it uses ordinary set forcing at one prefix containing the names and condition. Complete projections and bounded absoluteness make the answer independent of that prefix. Density clauses then handle unbounded quantifiers. First the low-name structure for a definable-class generic is shown to satisfy ZFC, using an external set name for that structure and the fixed-formula forcing theorem. Applying that construction to the single partial-satisfaction formula at level \(k\) gives the uniform definition and truth lemma at that level.

Choose \(r_k\) above the complexities of that formula and its negation after eliminating the fixed iteration predicates. Ground \(\Sigma_{r_k}\)-elementarity makes the two endpoint forcing relations agree on source names and source conditions. Truth in the source supplies a source-generic forcing condition, whose assertion transfers to the target. Applying the same argument to the negation proves agreement in both directions. This proves (D).

In V13, take \(k=N+1\). Enlarge the fixed captured code to include the actual cutoff table and all complete prefix data. The paper's finite-reflection step gives the required ground embedding and ground correctness at \(\bar\theta,\theta,\Omega\). Part (C) gives directly
\[
e:W_{\bar\theta}\longrightarrow W_\theta,
\qquad e(\bar\alpha)=\alpha.
\]
Part (D) gives \(W_{\bar\theta},W_\theta\prec_{\Sigma_{N+1}}W_\Omega\). These are precisely the rank embeddings and correctness assertions used in the paper's Bagaria--Poveda characterization. No successor-rank lift is used in this application.

This completes the corrected theorem from the stated Woodin large-cardinal input and the detailed supporting proofs. It is a mathematical proof package. The W02 handoff records which source-correspondence lemmas have Lean proof terms and which assembly, downstream formalization and validation checks remain.

## 8. Dependency check

The supporting lemmas have local hypotheses because they are used inside a simultaneous construction. Their use in the theorem has the following order.

| Required fact | Discharge |
| --- | --- |
| A common regular seed below each supercompact | Ground facts, Section 3 |
| A successful cutoff strictly below the outer supercompact | Collapse proof, Section 7, using closed-model DC reflection |
| Legal names and deterministic operations | Presentation proof, Sections 1--6 |
| Bounds before the raw-limit DC assertion | Inverse-limit proof, Lemma 1 |
| The raw extension's own regular successor and DC below it | Inverse-limit proof, Lemmas 2--6 |
| Earlier regularity for every traversed collapse | Simultaneous construction, Section 3 |
| Complete projections and relative generic movement | Presentation proof, Section 6.2, and construction, Section 5 |
| Actual marked endpoints, including every ground supercompact | Construction, Section 4 |
| Rank stabilization, size bounds and ZFC | W03 actual enumeration proof, Sections 2--8 |
| Actual internal computation and the \(\Sigma_3\) definition | Definition proof, Sections 5--6 |
| The directed master family in the smaller extension | Main proof, Section 6, and rank-lifting proof, Section 5 |
| Elementarity of the rank lift without ZF at the taller source rank | Rank-lifting proof, Sections 1--4 |
| The forcing formula reflected by the finite-window argument | Endpoint-forcing proof, Sections 1--4 |

The base induction does not use either later lifting conclusion. The raw DC argument uses no property of the collapse that it justifies appending. The finite-window assertion requires correctness for its own forcing formula, rather than inferring it from the \(\Sigma_3\) definition of the iteration alone.
