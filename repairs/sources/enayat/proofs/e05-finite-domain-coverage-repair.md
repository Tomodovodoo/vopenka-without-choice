# E05: making every internally finite domain countable

This mathematical note is retained from proof development. Historical implementation labels are superseded by the [current repair summary](../README.md). The summary identifies the exact formalized scope.

The selected-function-tree route proves the full weakly Rubin conclusion after one additional requirement is included in both the ground construction and the infinitary sentence:

\[
 \operatorname{FinSmall}\quad\equiv\quad
 \forall a\,[\operatorname{Finite}(a)
                     \to\neg(Qx)(x\in a)].
 \tag{F0}
\]

Here `Finite` is the model's internal finite-set predicate, and Q has standard external uncountability semantics. Thus (F0) says that every internally finite set is externally countable. It does not say that those sets are externally finite.

Enayat's Remark 5.22 notes that the Rubin construction can give an \(\aleph_1\)-like natural-number order. This would imply (F0). The proof below supplies the particular strengthening of the successor construction that is needed, instead of leaving the remark as an unexplained input. [Enayat, *Models of set theory: extensions and dead-ends*, Remark 5.22](https://doi.org/10.1017/jsl.2026.10199).

## 1. A finite cofinal-union lemma inside ZF

Work inside a model \(A\models\mathrm{ZF}\). Let \(D\) be a definable directed order with no maximum, and let \(a\) be an internally finite set. A finite product of such orders can be used for \(D\). Let \(R(m,d)\) be a fixed definable relation with the displayed parameters.

If

\[
              \{d\in D:\exists m\in a\ R(m,d)\}
\]

is cofinal in \(D\), then \(\{d\in D:R(m,d)\}\) is cofinal for some \(m\in a\).

Suppose every fiber fails to be cofinal. Then for each \(m\in a\) there is a bound beyond which \(R(m,d)\) never holds. Induct along an internal finite enumeration of \(a\), combining the next bound with the previous one by directedness. This internal finite induction gives one bound working for all \(m\in a\), contradicting cofinality of the union. All quantifiers belong to the fixed first-order definition of \(R\). This proof works for an internally finite \(a\) even when its extension is externally infinite. It uses no choice axiom in \(A\).

## 2. Preserve old internally finite sets at a Rubin successor

Let \(A\models\mathrm{ZF}\) be countable externally, with a countable family of inseparable pairs and a countable list of its definable directed orders without a maximum. Let \(T\) be the elementary diagram of \(A\), with new constants \(d_i\) required to lie above all old elements of the corresponding orders.

Use the corrected **block** cofinality criterion: for a sentence involving a finite tuple \(\bar d\) of new constants,

\[
 T+\sigma(\bar d)\text{ is consistent}
 \quad\Longleftrightarrow\quad
 A\models\forall\bar r\,\exists\bar s>\bar r\,
                                      \sigma(\bar s).
 \tag{F1}
\]

The tuples range over the appropriate finite product of directed orders. The bounds form one universal block, followed by one witness block. This is the criterion proved in [RubinBlockLemmas.lean](../../../../ZFVP/ModelTheory/RubinBlockLemmas.lean). The alternating quantifier prefix printed in the source is not used.

For each internally finite \(a\in A\), add the type

\[
 p_a(x)=\{x\in\dot a\}\cup
                       \{x\ne\dot m:m\in^A a\}
 \tag{F2}
\]

to the list of types to omit. A model omitting \(p_a\) adds no new member to this old finite set. There are countably many such types because \(A\) is externally countable.

We prove that \(T\) locally omits \(p_a\). Fix \(\theta(x,\bar d)\) such that \(T+\exists x\,\theta(x,\bar d)\) is consistent. If

\[
              T+\exists x\,[\theta(x,\bar d)\land x\notin\dot a]
\]

is consistent, it already denies a member of \(p_a\). Otherwise (F1) supplies a product bound beyond which every \(\theta\)-witness lies in \(a\). Consistency of \(\exists x\theta\), again by (F1), says that witnesses still exist cofinally beyond this bound.

Apply Section 1 to the definable relation \(\theta(m,\bar s)\) on that final cone, with index set \(a\). Some old \(m\in^A a\) has \(\theta(m,\bar s)\) true cofinally. By (F1), \(T+\theta(\dot m,\bar d)\) is consistent. Hence so is

\[
              T+\exists x\,[\theta(x,\bar d)\land x=\dot m],
\]

which denies the member \(x\ne\dot m\) of \(p_a\). This proves local omission.

The separating types for the given inseparable pairs are already locally omitted by the corrected A.5 argument in [SeparatingTypesOmitted.lean](../../../../ZFVP/ModelTheory/SeparatingTypesOmitted.lean). Apply the countable omitting-types theorem, with equality, to their union with all the types (F2). The same theory \(T\) is used for both families. The result is a countable elementary extension \(A\prec B\) which preserves the inseparable pairs, supplies the prescribed upper bounds, and satisfies

\[
       \forall a\in A\,[A\models\operatorname{Finite}(a)
             \ \Longrightarrow\
          \operatorname{Ext}_B(a)=\operatorname{Ext}_A(a)].
 \tag{F3}
\]

Omission of the additional types supplies (F3). It is not a new assumption about the extension produced by the old successor theorem.

## 3. The diamond chain retains this requirement

Use the strengthened successor from Section 2 in the usual diamond construction. At each countable stage carry the existing countable family of inseparable pairs. When a diamond guess is undefinable in that stage, add it and its complement as a new inseparable pair. Run the strengthened upper-bound construction at each successor, whether or not a new pair was added. Include the natural-number order among the definable directed orders. At countable limit stages take the elementary union.

The final union \(N\) has size \(\aleph_1\). Every stage is countable, giving the upper bound, and the new natural number above all previous natural numbers at each successor gives the lower bound. Every internally finite \(a\in N\) appears in some countable stage. Elementarity recognizes it as internally finite there, and (F3) prevents every later stage from adding members to it. Its extension in \(N\) is therefore countable. This proves (F0). In particular, the natural-number order of \(N\) is uncountable and has countable proper initial segments.

The corrected Rubin conclusion still follows from the diamond argument. To check that the added preservation demand has not weakened it, let \(F\) be a maximally compatible filter with a cofinal \(\omega_1\)-chain, and suppose it is not definable in \(N\). On a club of stages, the expansion by its trace is elementary in \((N,F)\); a diamond guess hits such a stage \(A\). Its trace \(S=F\cap A\) is undefinable in \(A\), since a definition there would transfer to a definition of \(F\) in the expanded elementary extension. Thus \(S,A\setminus S\) become a preserved inseparable pair.

The set \(S\) is countable. An element \(p\in F\) above it exists by the cofinal \(\omega_1\)-chain. For \(q\in P^A\setminus S\), elementarity of the expansion and maximal compatibility give \(r\in S\) incompatible with \(q\). Since \(r\leq p\), \(q\not\leq p\). Consequently the original-language formula

\[
                            x\in P\ \land\ x\leq p
\]

separates \(S\) from \(A\setminus S\) in a later stage containing \(p\), a contradiction. The conjunction also excludes elements outside \(P\). Thus the filter is definable. As before, for the internal set \(\operatorname{Fin}^N(s,2)\), Separation turns definability into a code.

This is the corrected diamond input needed by the Schmerl route, now with (F0) proved as an additional output.

## 4. Add FinSmall to the sentence and transfer it

Replace the sentence \(\Phi\) in the Schmerl route by

\[
                              \Phi^+=\Phi\land\operatorname{FinSmall}.
 \tag{F4}
\]

(F0) is one fixed \(L_{\omega,\omega}(Q)\) clause, so the language and sentence code remain countable. The strengthened diamond model satisfies it. Subsequent forcing preserves the external countability of each old finite-set extension because its old countable enumeration remains available, and the underlying object structure is unchanged. Thus the expanded model after specialization satisfies \(\Phi^+\).

Apply the same standard-Q Keisler transfer and size-\(\aleph_1\) fragment reduction to \(\Phi^+\). Every internally finite set in the resulting model is externally countable by the literal standard-Q semantics of (F0). This is the required semantic property after transfer; it does not rely on the new model being a forcing extension of the diamond model.

## 5. Cover entire finite domains in an arbitrary filter

Let \(M\models\Phi^+\), let \(s\) be internally infinite, and let \(F\) be any maximal filter on \(\operatorname{Fin}^M(s,2)\) with an increasing cofinal chain \(\langle p_\alpha:\alpha<\omega_1\rangle\). We prove the missing selected-domain coverage and then recover the entire filter.

First, every \(x\in^M s\) lies in the domain of some member of \(F\). Otherwise the singleton function assigning 0 to \(x\) is compatible with every member of \(F\). Union with this singleton and downward closure would give a larger filter. Equivalently, use the equality of maximality and maximal compatibility for internal finite partial functions.

Fix a selected domain \(c\in C_s\). It is internally finite and therefore externally countable by (F0). For each \(x\in^M c\), choose a member of \(F\) covering \(x\), and an index \(\alpha_x\) above that member in the cofinal chain. Ambient countable choice and regularity of the external \(\omega_1\) give one \(\beta<\omega_1\) with \(\alpha_x\leq\beta\) for every such \(x\). Hence

\[
                             c\subseteq\operatorname{dom}(p_\beta).
 \tag{F5}
\]

For an empty domain any member of the nonempty filter suffices. Thus every selected domain is covered by one member of \(F\), which is precisely (S-cover).

For each selected domain \(c\), restrict a covering member of \(F\) to \(c\). The result is an internal node of \(T_s\) and belongs to \(F\), since a maximal filter is downward closed. The restriction is independent of the chosen covering member: directedness makes any two members of \(F\) compatible, so they agree on their common domain. These restrictions form a full cofinal branch \(B\) of the selected function tree.

Its generated filter equals \(F\). One inclusion follows from downward closure. For the other, given \(p\in F\), choose \(c\in C_s\) containing \(\operatorname{dom}(p)\). The branch node on \(c\) agrees with \(p\), by compatibility, and therefore extends \(p\). Thus \(p\in F_B\).

The full-filter coding clause (S-K) codes \(F_B=F\). This proves the original E05 clause for **every** maximal filter in its contract, without adding (S-cover) as an assumption. Along with rather classlessness and the selected cofinal domain chains, the model is weakly Rubin. E06 follows either through the usual weakly Rubin theorem or through the direct selected-filter argument already supplied.

## 6. Formal handoff

The following table records the original implementation handoff. These steps now feed the proved `ZFVP.Schmerl.exists_alephOneWeaklyRubinExtension`, whose final statement assumes only a nonempty countable ZF model in Lean `Type`. See the countability integration record for the compiled exports and exact independent review boundaries.

| Step | Required statement and existing base |
| --- | --- |
| E08 finite preservation | Internal finite cofinal-union lemma; local omission of (F2) using the block criterion; omit these types together with the separating types. Use `RubinBlockLemmas`, `SeparatingTypesOmitted`, and `OmittingTypesEq`. |
| E09 strengthened chain | Carry (F3) at every successor; prove that each old finite set has the same members at every later stage and is countable in the union. |
| E11 extra sentence | Add exactly the standard-Q clause (F0) to the existing corrected sentence, and extract external countability from it in every standard model. |
| E05 full extraction | Prove (F5), construct the selected branch, and use the existing full-filter candidate coding theorem to obtain the code of the arbitrary filter. |

The mathematical proof above repairs the missing coverage implication for the constructed model by establishing an additional property of that model. It preserves the original weakly Rubin conclusion. Standard-Q completeness and the named-model application are now proved. Generic satisfiability absoluteness over a prescribed ground remains a separate E12 obligation.
