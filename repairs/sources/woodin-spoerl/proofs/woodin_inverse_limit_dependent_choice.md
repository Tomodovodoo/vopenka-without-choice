# Dependent choice at Woodin's inverse-limit stages

This mathematical note is retained from proof development. Historical implementation labels are superseded by the [current repair summary](../README.md). The summary identifies the exact formalized scope.

This note supplies the argument for the dependent-choice assertion on printed page 324 of W. Hugh Woodin, *Suitable extender models I*, in the proof of Theorem 226. The source is the local paper, printed pages 321-324.

The argument concerns the raw inverse limit before the additional collapse. It assumes the construction and its stated regularity and dependent-choice assertions have been established at every earlier stage. We specify the presentation of the iteration, construct its quotient bounds in the ground model, and then prove the dependent-choice assertion.

Throughout, stronger forcing conditions are smaller. We work in ZF. For an ordinal \(\eta\), \(\mathrm{DC}_\eta\) means the following history form of dependent choice: if \(X\ne\varnothing\) and \(R\subseteq X^{<\eta}\times X\) satisfies
\[
\forall s\in X^{<\eta}\ \exists x\in X\ R(s,x),
\]
there is \(f:\eta\to X\) such that
\[
R(f\mathbin{\upharpoonright}i,f(i))\qquad(i<\eta).
\]
We write \(\mathrm{DC}_{<\tau}\) for all these instances with \(\eta<\tau\). Finite instances hold in ZF. Restricting paths, with the relation extended arbitrarily past its original length when necessary, proves monotonicity in the index.

**The limit-stage assertion.** Let \(\beta\) be a nonzero limit stage of Woodin's iteration, and let
\[
\gamma=\sup_{\alpha<\beta}\kappa_\alpha.
\]
Suppose \(\gamma\) is not strongly inaccessible in the ground model, so that this stage takes the inverse-limit branch. Put
\[
Q=\varprojlim_{\alpha<\beta}Q_\alpha.
\]
For every \(V\)-generic \(H\subseteq Q\), we will prove
\[
V[H]\models
\mathrm{DC}_{<(\gamma^+)^{V[H]}}
\quad\text{and}\quad
\operatorname{Reg}\bigl((\gamma^+)^{V[H]}\bigr).
\tag{1}
\]
In particular, both conclusions hold before the collapse whose lower index is \((\gamma^+)^{V[H]}\) is appended.

**The presentation of the iteration.** Write \(\pi_{ij}:Q_j\to Q_i\) for the coherent projections. Use the usual coordinate presentation, with canonical embeddings \(e_{ij}\) obtained by inserting empty tails. Direct limits are the bounded-support part of the coherent inverse limit, with the same coordinatewise order. At an inverse stage followed by a collapse, distinguish the raw inverse limit from the completed two-step stage.

If \(q\) is a condition extending through stage \(i\), and \(r\leq\pi_i(q)\), define \(q[r]\) by replacing its prefix through \(i\) by \(r\), leaving its subsequent coordinate names unchanged. Then
\[
q[r]\leq q,\qquad \pi_i(q[r])=r,\qquad q[\pi_i(q)]=q,
\tag{2}
\]
and
\[
\pi_j(q[r])=(\pi_jq)[r]\qquad(i\leq j).
\tag{3}
\]
For projections below \(i\), the result is the corresponding projection of \(r\).

These are literal identities of the coordinate presentation. At a two-step stage, prefix replacement keeps the second-coordinate name. At an inverse limit it acts coordinatewise. At a direct limit it changes only a bounded prefix and therefore preserves bounded support. This proves the identities by recursion, including across earlier stages that themselves consist of an inverse limit followed by a collapse.

The embeddings satisfy the useful identity
\[
s\leq e_{ij}(r)\quad\Longleftrightarrow\quad \pi_{ij}(s)\leq r.
\tag{4}
\]
We use the same notation for projections and embeddings involving the raw limits.

At a collapse with upper endpoint \(\Theta\), use the saturated set presentation of \(P*\dot{\mathbb C}\): the permissible second coordinates are all \(P\)-names belonging to \(V_\Theta\) that their first coordinate forces to be conditions of
\[
\mathbb C=\operatorname{Coll}(\delta,<V_\Theta).
\]
The empty tail is represented by the literal empty name. Here \(P\in V_\Theta\), \(\Theta\) is strongly inaccessible in the ground model, and
\[
P\Vdash\text{"\(\delta<\Theta\) is an infinite regular cardinal."}
\tag{5}
\]
The lower index can be a \(P\)-name, as at a previous inverse stage; all inequalities involving it are then forced inequalities.

We record why these name and rank conventions are available in ZF. Woodin's strong inaccessibility means
\[
\forall\rho<\Theta\ \forall h:V_\rho\to\Theta\
\sup\operatorname{ran}(h)<\Theta.
\tag{6}
\]
Consequently any function from a set of rank below \(\Theta\) into \(\Theta\) has bounded range, by extending it to a suitable \(V_\rho\) with default value \(0\).

For a forcing \(P\in V_\Theta\), define
\[
N_0=\varnothing,\qquad
N_{\rho+1}=\mathcal P(N_\rho\times P),\qquad
N_\lambda=\bigcup_{\rho<\lambda}N_\rho
\quad(\lambda\text{ limit}).
\tag{7}
\]
These are increasing sets of names. For every generic \(K\), evaluation of \(N_\rho\) covers \(V[K]_\rho\). At a successor, a name \(\tau\) whose value is a subset of \(V[K]_\rho\) is represented in \(N_{\rho+1}\), in that generic extension, by
\[
\{(\sigma,s)\in N_\rho\times P:s\Vdash\sigma\in\tau\}.
\]
The forcing truth lemma proves the assertion; limits follow by union. The rank recurrence for (7) adds only finitely many ranks at a successor and takes a supremum at a limit. Regularity of \(\Theta\) therefore gives \(N_\rho\in V_\Theta\) for \(\rho<\Theta\).

This also proves that \(P\) preserves (6). Given a name for a function \(V[K]_\rho\to\Theta\), work below a condition in \(K\) forcing its type. Its possible values on names in \(N_\rho\) are described by a partial function on \(N_\rho\times P\): a pair \((\sigma,s)\) specifies the unique ordinal that \(s\) forces to be the value, when \(s\) is below that condition and decides such a value. Extend the partial function by \(0\). Equation (6) bounds this ground-model function. Every actual value occurs among those possible values.

In particular, \(\Theta\) is still regular in \(V[K]\). A collapse condition has domain of cardinality below \(\delta<\Theta\), so its coordinate ordinals are bounded in \(\Theta\). Its values consequently have ranks bounded below \(\Theta\), and the condition belongs to \(V[K]_\Theta\). Equation (7) supplies a name in \(V_\Theta\) for it. Truth and density give the saturated two-step presentation without a simultaneous choice of representatives.

The same coding gives
\[
Q_i\in V_{\kappa_i+\omega}.
\tag{8}
\]
For a collapse stage this follows from the name bound \(V_{\kappa_i}\). At a limit, a thread has rank bounded by its index and the ranks of its coordinate conditions, plus a fixed finite amount. Direct-limit conditions form a subset of the same set of threads. At an inverse stage the subsequent inaccessible endpoint is above those ranks. These observations prove (8) by induction. We will use the consequence
\[
Q_\alpha\in V_{\kappa_\lambda}
\quad\text{whenever }\alpha<\lambda
\text{ and }\lambda\text{ is a direct-limit stage}.
\tag{9}
\]

**Lemma 1. The tail bound.** For every \(\alpha<\beta\), \(Q_\alpha\) forces that the projection quotient of \(Q\), equipped with its separative preorder, is \((<\kappa_\alpha)\)-directed closed.

Here is the precise order in this statement. If \(G\subseteq Q_\alpha\) is generic, let
\[
R_{\alpha,\beta}
=\{q\in Q:\pi_{\alpha,\beta}(q)\in G\}.
\]
This is the set of ground-model conditions satisfying the displayed requirement, with its inherited order \(\leq\). Define
\[
q\leq_G^*r
\quad\Longleftrightarrow\quad
\forall s\in R_{\alpha,\beta}\,
\bigl(s\leq q\Longrightarrow
\exists t\in R_{\alpha,\beta}\ (t\leq s,r)\bigr).
\tag{10}
\]
The assertion is that every directed subset of this preorder that is enumerated by an ordinal \(\nu<\kappa_\alpha\) has a lower bound for \(\leq_G^*\).

Thus we first use the separative preorder on the same set of conditions, without choosing representatives from equivalence classes. If actual separative equivalence classes are used instead, the stage hypothesis \(\mathrm{DC}_{<\kappa_\alpha}\) gives the choice of fewer than \(\kappa_\alpha\) representatives and yields the same closure assertion for that presentation.

*Proof.* Prefix replacement gives the usual factorization
\[
Q\simeq Q_\alpha*\dot R_{\alpha,\beta}.
\tag{11}
\]
Indeed, send \(q\) to \((\pi_\alpha q,\check q)\). Given a condition \((p,\dot q)\) in the two-step forcing, strengthen \(p\) to decide \(\dot q=\check q_0\). Since this condition forces \(\pi_\alpha(q_0)\in\dot G\), strengthen again below \(\pi_\alpha(q_0)\). Prefix replacement of \(q_0\) gives a condition whose image extends the given pair. This proves density. The same argument applies to any two intermediate stages. Passing from an inherited order to its separative preorder leaves the forcing extension unchanged.

Fix \(\alpha<\beta\), let \(B=Q_\alpha\), and let \(G\subseteq B\) be generic. Suppose \(D\ne\varnothing\) is a directed set as in the lemma, and fix a surjection
\[
f:\nu\to D,\qquad 0<\nu<\kappa_\alpha.
\]
Choose a \(B\)-name \(\dot f\) and \(p\in G\) forcing these properties, with \(\nu\) a ground-model ordinal. Define in \(V\)
\[
E=\{(d,\xi,q):
d\leq p,\ \xi<\nu,\ q\in Q,\
d\leq q_\alpha,\
d\Vdash_B\dot f(\xi)=\check q\},
\tag{12}
\]
where \(q_j=\pi_{j,\beta}(q)\).

For each actual value \(q=f(\xi)\), some \(d\in G\) satisfies \((d,\xi,q)\in E\). First decide the value, and then use directedness of the generic filter to strengthen below \(p\) and \(q_\alpha\). For a fixed pair \((d,\xi)\), there is at most one \(q\) with \((d,\xi,q)\in E\). This uniqueness will provide rank and support bounds without a choice function.

We now perform one recursion in \(V\), with parameters \(p,\dot f,E\). Put \(b_\alpha=p\), and use its projections below \(\alpha\). At each later stage construct \(b_j\) and prove both coherence
\[
b_j\in Q_j,\qquad
\pi_{\alpha j}(b_j)=p,\qquad
\pi_{ij}(b_j)=b_i
\quad(\alpha\leq i\leq j),
\tag{C}
\]
and the following comparison invariant:
\[
\begin{split}
&(d,\xi,q)\in E,\quad c\leq b_j,\quad
r\leq\pi_{\alpha j}(c),\quad r\leq d\\
&\hspace{35mm}\Longrightarrow c[r]\leq q_j.
\end{split}
\tag{B}
\]
At a raw inverse limit the same statements refer to its raw conditions and projections.

The base case of (B) says \(r\leq d\leq q_\alpha\), and follows immediately. The point of (B) is that the same base condition \(r\), below the same decision \(d\), controls every later coordinate. It also applies to every strengthening of the constructed bound.

Consider a collapse operation
\[
P^+=P*\dot{\mathbb C},
\]
including one appended after an earlier inverse limit. Suppose the bound \(b^-\) and (B) have already been established in \(P\). Write
\[
\pi_{P^+}(q)=(q^-,\dot q^+).
\]
By the earlier-stage induction, \(P\) forces that the lower collapse index \(\delta\) is regular and
\[
\nu<\kappa_\alpha\leq\delta<\Theta.
\tag{13}
\]
Let \(e:B\to P\) be the canonical embedding. Define a \(P\)-name by the following formula, with no selection of names:
\[
\begin{split}
\dot u=\{(\sigma,s):\
&\exists(d,\xi,q)\in E\ \exists t\in P\\
&[(\sigma,t)\in\dot q^+\ \land\
s\leq b^-\ \land\
s\leq e(d)\ \land\
s\leq q^-\ \land\
s\leq t]\}.
\end{split}
\tag{14}
\]
All quantifiers here range over sets. The fact that this name belongs to the required \(V_\Theta\) is checked below.

Let \(K\subseteq P\) be generic with \(b^-\in K\), and let \(K_\alpha\) be its projected \(B\)-generic. For every
\[
q\in\operatorname{ran}(\dot f^{K_\alpha}),
\]
choose \(d\in K_\alpha\) witnessing its occurrence in (12). Since \(e(d)\in K\), there is \(c\in K\) below both \(b^-\) and \(e(d)\). Thus \(\pi_\alpha(c)\leq d\). Apply (B) with \(r=\pi_\alpha(c)\); equations (2) and (4) give
\[
c=c[r]\leq q^-.
\]
Consequently
\[
q^-\in K
\quad\text{for every }q\in\operatorname{ran}(\dot f^{K_\alpha}).
\tag{15}
\]

It follows directly from (14) that
\[
\dot u^K
=\bigcup_{q\in\operatorname{ran}(\dot f^{K_\alpha})}
(\dot q^+)^K.
\tag{16}
\]
For the forward inclusion, a supporting condition \(s\in K\) makes its decision \(d\) belong to \(K_\alpha\). For the reverse inclusion, use (15) and take a common strengthening in \(K\) of the finitely many conditions \(b^-,e(d),q^-,t\) appearing in (14).

We justify compatibility of the functions on the right of (16), including the separative-order point. A projection admitting prefix replacement preserves the separative preorder. Otherwise an extension of a projected condition witnessing failure of the projected comparison could be lifted below the original condition, contradicting (10).

There is also the following two-step consequence. If two conditions in a two-step quotient satisfy a separative comparison, then, after an intermediate generic containing their prefixes is fixed, their evaluated tails satisfy the corresponding separative comparison. To prove this, suppose an evaluated tail has an extension incompatible with the other evaluated tail. Name that extension and strengthen a condition of the intermediate generic to force these facts and to lie below both prefixes. The resulting two-step condition extends the first condition and is incompatible with the second, contradicting the original separative comparison. A bounded name for the tail extension is available by (7) and density.

For two members \(q_0,q_1\) of the range of \(\dot f^{K_\alpha}\), directedness supplies a member \(q_2\) separatively below both. These are assertions about the fixed ground-model quotient over \(K_\alpha\); its set, order and compatibility relation remain the same in further extensions. Projection to \(P^+\), followed by the preceding two-step observation and (15), shows that the evaluated tail of \(q_2\) is separatively below the evaluated tails of \(q_0\) and \(q_1\). In any preorder, two elements having a common separative lower bound are compatible: first extend that lower bound compatibly with one element, and then extend the result compatibly with the other. The two evaluated tails are therefore compatible collapse conditions. As partial functions, they agree wherever their domains overlap.

The union in (16) also has a sufficiently small domain in ZF. Fix a definable well-order of the ordinal-pair set \(\delta\times\Theta\). For example, order first by the maximum of the coordinates, then by the first coordinate, then by the second. Restrict this order to each domain in the \(\nu\)-indexed family. The order type of each restriction is below the initial ordinal \(\delta\), because that domain has cardinality below \(\delta\). Its increasing enumeration is uniquely determined. Regularity of \(\delta\) and \(\nu<\delta\) bound all these order types by a single ordinal \(\epsilon<\delta\). Assign a point of the union to its least index of occurrence and to its position in that domain's increasing enumeration. This injects the union into \(\nu\times\epsilon\), a set of cardinality below \(\delta\). For \(\delta=\omega\) the assertion is finite arithmetic; for larger \(\delta\) it is the ZF cardinal arithmetic of well-orderable infinite sets.

The value restrictions for the collapse are inherited by the union. Thus (16) is a condition of \(\mathbb C^K\). If \(b^-\notin K\), (14) evaluates to the empty condition, since every supporting condition lies below \(b^-\). Therefore \(\dot u\) has a valid collapse value in every generic extension.

To check its name rank, send \((d,\xi)\in B\times\nu\) to the rank of the unique possible \(\dot q^+\) in (12), and to \(0\) if there is none. This is a ground-model function into \(\Theta\), because the original tail names belong to \(V_\Theta\). Equations (6) and (8) give a bound on its range: \(B\times\nu\) has rank below \(\Theta\). All subnames \(\sigma\) used in (14) consequently have bounded rank below \(\Theta\); the conditions \(s\) belong to \(P\in V_\Theta\). Forming ordered pairs and their set adds only finitely many ranks. Hence
\[
\dot u\in V_\Theta.
\tag{17}
\]
This verifies membership in the saturated presentation and permits the definition
\[
b^+=(b^-,\dot u)\in P^+.
\]

Coherence is literal, since the first coordinate is \(b^-\). To verify (B), take
\[
c=(c^-,\tau)\leq b^+,\qquad
r\leq\pi_\alpha(c),d,\qquad(d,\xi,q)\in E.
\]
The earlier instance of (B) gives
\[
c^-[r]\leq q^-.
\tag{18}
\]
Moreover \(c^-[r]\) is below \(b^-\) and \(e(d)\). Formula (14), or its evaluation in every generic containing \(c^-[r]\), therefore gives
\[
c^-[r]\Vdash\dot u\supseteq\dot q^+.
\]
Since \(c\leq b^+\), the same condition forces \(\tau\supseteq\dot u\). Together with (18) this proves
\[
c[r]=(c^-[r],\tau)\leq(q^-,\dot q^+).
\tag{19}
\]
This is (B) at the collapse operation.

Now consider a direct-limit stage \(\lambda>\alpha\). Set
\[
\Lambda=\sup_{j<\lambda}\kappa_j=\kappa_\lambda.
\]
This is a ground-model strongly inaccessible cardinal. In fact
\[
\lambda=\Lambda.
\tag{20}
\]
The increasing sequence of cardinals gives \(\lambda\leq\Lambda\). If \(\lambda<\Lambda\), its cofinal map \(j\mapsto\kappa_j\) would contradict (6), since \(\lambda\) has rank below \(\Lambda\).

For a possible value \(q\) in (12), let \(\sigma_\lambda(q)<\lambda\) be the least support bound of \(q_\lambda\), equivalently the least \(k\) such that
\[
q_\lambda=e_{k\lambda}(q_k).
\]
Such a bound exists because \(q_\lambda\) belongs to the direct limit. Uniqueness in (12) makes
\[
(d,\xi)\longmapsto\sigma_\lambda(q),
\]
with default value \(0\), a ground-model function \(B\times\nu\to\lambda\). By (9), (20) and (6), choose \(k<\lambda\), \(k\geq\alpha\), strictly above all its values. This bounds all possible supports of the name, including values not realized in the particular generic \(G\).

Every selected \(q_\lambda\) has literal empty tails after \(k\). At each intervening collapse operation, (14) therefore gives the literal empty name. A recursion through the intervening direct and inverse limits now gives
\[
b_j=e_{kj}(b_k)\qquad(k\leq j<\lambda).
\tag{21}
\]
Thus the coherent history has bounded support and defines \(b_\lambda\in Q_\lambda\). The earlier bounds are its projections. Property (B) follows from its earlier instances and the coordinatewise order on the direct limit.

At a raw inverse limit \(\lambda>\alpha\), define
\[
b_\lambda^-=\langle b_j:j<\lambda\rangle.
\tag{22}
\]
Coherence makes this a condition of the inverse limit. The recursion has been performed in \(V\) from the fixed ground-model parameters \(p,\dot f,E\), so Replacement gives
\[
b_\lambda^-\in V.
\tag{23}
\]
This membership is essential: an arbitrary thread assembled only in \(V[G]\) need not be a member of the ground-model inverse-limit forcing.

For (B), let \(c\leq b_\lambda^-\), let \((d,\xi,q)\in E\), and fix one \(r\leq\pi_\alpha(c),d\). At every \(\alpha\leq j<\lambda\), (3) and the earlier comparison yield
\[
\pi_j(c[r])=(\pi_jc)[r]\leq q_j.
\tag{24}
\]
Below \(\alpha\), the comparison follows by projecting \(r\leq d\leq q_\alpha\). The inverse-limit order is coordinatewise, so
\[
c[r]\leq\pi_\lambda^-(q).
\tag{25}
\]
In particular, (24) uses the same \(r\) at every coordinate. There is no choice of coordinatewise witnesses to amalgamate.

At an earlier inverse stage followed by a collapse, perform (22) through (25) and then (14) through (19). The regularity in (13) is available from the completed induction at that earlier stage. At the present stage \(\beta\), stop at the raw inverse limit. This completes the recursion proving (C) and (B).

Let \(b=b_\beta^-\in Q\). Since \(\pi_\alpha(b)=p\in G\), it belongs to \(R_{\alpha,\beta}\). Fix \(q=f(\xi)\in D\) and any inherited-order extension \(c\leq b\) in that quotient. Choose \(d\in G\) with \((d,\xi,q)\in E\), and then choose
\[
r\in G,\qquad r\leq\pi_\alpha(c),d.
\]
Property (B) gives \(c[r]\leq q\), while (2) gives \(c[r]\leq c\) and \(\pi_\alpha(c[r])=r\in G\). Thus \(c[r]\) witnesses compatibility in the quotient. By (10),
\[
b\leq_G^*q\qquad(q\in D).
\tag{26}
\]
The empty family is bounded by the top condition. This proves Lemma 1. \(\square\)

The use of the separative order cannot simply be omitted. Even the quotient of a forcing over itself need not have inherited-order closure. For example, if \(B=2^{<\omega}\) is Cohen forcing and \(G\) is generic, the increasing finite initial segments of its generic real form a descending sequence in the inherited order on \(G\) with no finite-string lower bound. All members of \(G\) are nevertheless equivalent in its separative preorder.

**Lemma 2. Preservation of short dependent choice.** Suppose
\[
M\models\mathrm{ZF}+\mathrm{DC}_\eta,\qquad \eta<\kappa,
\]
and \(M\) satisfies that the separative preorder of a forcing \(R\) is \((<\kappa)\)-closed. Then
\[
M^R\models\mathrm{DC}_\eta.
\tag{27}
\]
Also, for every \(A\in M\), forcing with \(R\) adds no functions \(\eta\to A\).

*Proof.* Fix a name \((\dot X,\dot S)\) for a serial history relation of length \(\eta\), and a condition \(p_0\) forcing this assertion. The direct subnames appearing in \(\dot X\) form a fixed set \(N\). Whenever a condition forces that an admissible next element of \(\dot X\) exists, densely below that condition some member of \(N\) names such an element. This is the forcing truth property for existential quantification and membership; it requires no maximum principle that chooses a name simultaneously below every condition.

Work in \(M\). Apply \(\mathrm{DC}_\eta\) to histories of pairs from the set \(R\times N\). A valid history consists of conditions descending in the separative preorder, all below \(p_0\), together with names whose membership and successive \(\dot S\)-requirements are forced by the corresponding conditions. At stage \(i<\eta\), closure gives a bound for its \(i\) earlier conditions. That bound forces the earlier names to form a history in \(\dot X^i\). Seriality and the preceding density observation give a strengthening and a name in \(N\) for the next admissible value. At the empty history start below \(p_0\). On invalid histories allow an arbitrary fixed pair, making the relation serial on all histories of \(R\times N\). Induction ensures that the history produced by dependent choice is valid.

Closure also applies to the resulting sequence of length \(\eta\), because \(\eta<\kappa\). Its lower bound forces that the canonical name for the sequence of chosen names is a solution. All these constructions are operations on sets of names. Separative comparison suffices since forcing statements are monotone for that preorder. If necessary, take a common inherited-order extension with \(p_0\) to obtain a condition below \(p_0\) in the original order. Starting below each possible \(p_0\) proves density and hence (27).

For the second assertion, use histories of conditions and elements of \(A\), deciding the value of a given name for a function \(\eta\to\check A\) at each step. The final lower bound decides the entire function as a function belonging to \(M\). Again these bounds are dense below any condition forcing the type of the function. \(\square\)

This is the usual closure and dependent-choice argument, with the needed choice principle stated explicitly. For background, Karagila's [*Preserving Dependent Choice*, Section 2](https://ueaeprints.uea.ac.uk/69607/1/Accepted_Manuscript.pdf) discusses the relation between closed forcing, distributivity and dependent choice in ZF.

**Application to the raw inverse limit.** Let \(H\subseteq Q\) be generic and \(H_\alpha\) its projection. Given \(\eta<\gamma\), choose \(\alpha<\beta\) with \(\eta<\kappa_\alpha\). The earlier-stage hypothesis says
\[
V[H_\alpha]\models\mathrm{DC}_\eta.
\]
Factorization (11), Lemma 1 and Lemma 2 give
\[
V[H]\models\mathrm{DC}_\eta.
\]
Therefore
\[
V[H]\models\mathrm{DC}_{<\gamma}.
\tag{28}
\]

Lemma 2 also shows that \(\kappa_\alpha\) remains a regular cardinal in \(V[H]\). It is a regular cardinal in \(V[H_\alpha]\), and a collapse of its cardinality or cofinality would supply a new cofinal map from some ordinal \(\eta<\kappa_\alpha\) into \(\kappa_\alpha\). Such a map cannot be added by the quotient. Thus
\[
\gamma=\sup_{\alpha<\beta}\kappa_\alpha
\]
remains a cardinal in \(V[H]\). For example, an injection of \(\gamma\) into an ordinal below \(\gamma\) would restrict to a forbidden injection of some larger \(\kappa_\alpha\) into that ordinal.

**Lemma 3. The earlier collapses make \(\gamma\) singular.** In the present inverse-limit case,
\[
\operatorname{cf}^{V[H]}(\gamma)<\gamma.
\tag{29}
\]

*Proof.* The failure of ground-model strong inaccessibility supplies \(\rho<\gamma\) and a ground-model function
\[
u:V_\rho^V\to\gamma
\]
with unbounded range. Its domain is nonempty, so we may take \(\rho\geq1\).

Choose an ordinary successor stage \(j+1<\beta\) with
\[
\rho<\kappa_{j+1}<\gamma.
\]
The collapse at that stage has lower index \(\lambda=\kappa_j<\gamma\) and upper endpoint \(\kappa_{j+1}\). In its preceding universe \(W=V[H_j]\), its generic union has a total column at coordinate \(\rho\) that surjects
\[
\lambda\longrightarrow V_{1+\rho}^{W}.
\tag{30}
\]
Indeed, assigning a value at a prescribed unused point gives density of totality. For any \(x\in V_{1+\rho}^{W}\), fewer than \(\lambda\) points of that column are used by a condition, so a fresh point can be assigned value \(x\). This proves density of hitting every such \(x\). These arguments use individual extensions of conditions, not a simultaneous choice of them.

The set \(V_\rho^V\) is a subset of the range set in (30). The retraction that fixes its members and sends every other value to \(\varnothing\) produces a surjection
\[
v:\lambda\to V_\rho^V.
\]
This map belongs to the successor-stage extension and hence to \(V[H]\). The composite \(u\circ v:\lambda\to\gamma\) is cofinal. Since \(\lambda<\gamma\), (29) follows. \(\square\)

This step uses the ground-model definition of strong inaccessibility. Failure of that definition is not itself the assertion that \(\gamma\) was already singular. The collapse in (30) converts its witness into a cofinal map with a small ordinal domain.

**Lemma 4. The singular block argument.** For a nonzero limit ordinal \(\zeta\), ZF proves
\[
\mathrm{DC}_{<\zeta}+\mathrm{DC}_{\operatorname{cf}(\zeta)}
\ \Longrightarrow\ \mathrm{DC}_\zeta.
\tag{31}
\]

*Proof.* Let \(\nu=\operatorname{cf}(\zeta)\), fix a cofinal map \(a:\nu\to\zeta\), and fix a serial history relation \(R\subseteq X^{<\zeta}\times X\). Let \(S\) be the set of all valid partial \(R\)-paths of length below \(\zeta\), including the empty path.

Suppose \(h=\langle s_j:j<i\rangle\), \(i<\nu\), is an increasing history under extension of paths. Its union \(s=\bigcup_{j<i}s_j\) is valid. Its length is below \(\zeta\): otherwise the \(i\)-sequence of lengths would be cofinal in \(\zeta\), contrary to the definition of \(\nu\).

Choose the particular ordinal
\[
\tau=\max(\operatorname{dom}(s),a(i))+1<\zeta.
\]
The instance \(\mathrm{DC}_\tau\) extends \(s\) to a valid path \(t\) of length \(\tau\). To see that a prescribed prefix can be retained, apply \(\mathrm{DC}_\tau\) to the relation requiring the value \(s(j)\) at stages \(j<\operatorname{dom}(s)\), and using \(R\) afterwards. This relation is serial on all histories, and its produced path has exactly the prescribed valid prefix.

Define a relation on histories from \(S\) by requiring such a \(t\) for increasing histories \(h\), and allowing the empty path for other histories. The preceding argument proves seriality. Apply \(\mathrm{DC}_\nu\). Induction shows that the resulting \(\nu\)-sequence of paths is increasing and that its \(i\)-th path extends past \(a(i)\). Its union therefore has length \(\zeta\), is a valid \(R\)-path, and proves (31). \(\square\)

In particular, (28), (29) and (31) yield
\[
V[H]\models\mathrm{DC}_\gamma.
\tag{32}
\]

**Lemma 5. Passing to the successor cardinal.** For every infinite cardinal \(\kappa\),
\[
\mathrm{ZF}+\mathrm{DC}_\kappa
\ \vdash\ \mathrm{DC}_{<\kappa^+}.
\tag{33}
\]

*Proof.* If an ordinal instance of dependent choice fails, let \(\mu\) be the least failing ordinal below any one specified failure. All finite instances hold. Also \(\mathrm{DC}_\xi\) implies \(\mathrm{DC}_{\xi+1}\), by first constructing a path of length \(\xi\) and then choosing one more admissible value. Thus \(\mu\) is an infinite limit ordinal.

If \(\operatorname{cf}(\mu)<\mu\), minimality gives both hypotheses of Lemma 4, contradicting failure at \(\mu\). Hence
\[
\operatorname{cf}(\mu)=\mu.
\]
Such an ordinal is a regular initial ordinal, therefore a regular cardinal. Under \(\mathrm{DC}_\kappa\), monotonicity excludes \(\mu\leq\kappa\). There is no cardinal strictly between \(\kappa\) and \(\kappa^+\), so no ordinal below \(\kappa^+\) can be a failure. \(\square\)

Applying Lemma 5 inside \(V[H]\) to the cardinal \(\gamma\) and (32) proves the requested assertion:
\[
\boxed{V[H]\models\mathrm{DC}_{<(\gamma^+)^{V[H]}}.}
\tag{34}
\]
This argument avoids trying to reorder a history-dependent relation along an arbitrary bijection of its index set.

**Lemma 6. Regularity for the appended collapse.** In ZF,
\[
\mathrm{DC}_\kappa\quad\Longrightarrow\quad
\operatorname{Reg}(\kappa^+)
\tag{35}
\]
for every infinite cardinal \(\kappa\).

*Proof.* First \(\mathrm{DC}_\kappa\) implies choice for every family of nonempty sets indexed by an ordinal at most \(\kappa\): at stage \(i\), choose a member of the \(i\)-th set. Use their union as the underlying set of the serial history relation.

Suppose \(\delta=\kappa^+\) were singular. Let
\[
\nu=\operatorname{cf}(\delta)<\delta,
\qquad
\langle a_i:i<\nu\rangle
\]
be a cofinal sequence of ordinals below \(\delta\). Since \(\nu\) is a cardinal, \(\nu\leq\kappa\). Each \(a_i\) admits an injection into \(\kappa\). The choice principle just proved selects injections \(j_i:a_i\to\kappa\) for all \(i<\nu\).

For \(\xi<\delta\), let \(i(\xi)\) be the least index with \(\xi<a_{i(\xi)}\). Then
\[
\xi\longmapsto\bigl(i(\xi),j_{i(\xi)}(\xi)\bigr)
\]
injects \(\delta\) into \(\nu\times\kappa\), which injects into \(\kappa\) by cardinal arithmetic for well-orderable sets. This contradicts \(\delta=\kappa^+\). \(\square\)

Equation (32) and Lemma 6 prove the remaining assertion of (1). The induction therefore has the following order:
\[
\begin{gathered}
\text{earlier-stage hypotheses and the ground-model bound recursion}\\
\Longrightarrow\text{raw inverse-limit tail closure}\\
\Longrightarrow\mathrm{DC}_{<\gamma},\\[2mm]
\text{earlier collapses and failure of ground-model inaccessibility}
\Longrightarrow\operatorname{cf}(\gamma)<\gamma,\\[2mm]
\mathrm{DC}_{<\gamma}+\operatorname{cf}(\gamma)<\gamma
\Longrightarrow\mathrm{DC}_\gamma
\Longrightarrow
\mathrm{DC}_{<\gamma^+}+\operatorname{Reg}(\gamma^+).
\end{gathered}
\tag{36}
\]
After these steps, the additional collapse with lower index \(\gamma^+\) can be appended. Its own union calculation uses the regularity just proved. No closure property of that additional collapse was used to obtain its lower index's regularity.

**A compact insertion for the proof on page 324.** The following paragraph can be used once the tail-bound lemma has been established.

> For every \(\alpha<\beta\), the projection quotient of the raw inverse limit \(Q\) over \(Q_\alpha\), in its separative preorder, is \((<\kappa_\alpha)\)-directed closed. This follows by forming the coordinate union names in the ground model from a name for the directed family, retaining one base decision in the comparison invariant at every coordinate; strong inaccessibility bounds all possible supports at direct limits. Factoring over \(Q_\alpha\) therefore preserves \(\mathrm{DC}_\eta\) and adds no ordinal sequences of length \(\eta<\kappa_\alpha\). Hence \(V^Q\models\mathrm{DC}_{<\gamma}\), and \(\gamma\) remains a cardinal. Since \(\gamma\) is not strongly inaccessible in \(V\), some \(u:V_\rho^V\to\gamma\), \(\rho<\gamma\), is cofinal. An earlier successor collapse makes \(V_\rho^V\) a surjective image of an ordinal \(\lambda<\gamma\), so \(V^Q\models\operatorname{cf}(\gamma)<\gamma\). Constructing a path in cofinally many blocks now gives \(\mathrm{DC}_\gamma\). A least failing ordinal for dependent choice must be a regular cardinal, so \(\mathrm{DC}_{<(\gamma^+)^{V^Q}}\) follows. Finally \(\mathrm{DC}_\gamma\) implies that \((\gamma^+)^{V^Q}\) is regular, supplying the hypothesis for the next collapse.

**Correspondence with the existing formalization.** The definition [ForcesProjectionQuotientClosedBelow](../../../../ZFVP/ModelTheory/ProjectionQuotientClosureForcing.lean) uses the separative order and asks for descending-sequence closure. Lemma 1 proves the stronger directed version in the specified coordinate presentation. The invariant (B) is the mathematical form of [IsWoodinCommonLiftBoundAt](../../../../ZFVP/ModelTheory/WoodinCommonLiftInvariant.lean). Its inverse-limit step is precisely (24): project one restricted strengthening and apply the earlier comparison at every coordinate. This file is a mathematical proof note, not a claim that a new Lean theorem has been compiled.
