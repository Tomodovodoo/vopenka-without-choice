# From Woodin's construction to the restricted lift

This mathematical note is retained from proof development. Historical implementation labels are superseded by the [current repair summary](../README.md). The summary identifies the exact formalized scope.

10 September 2026. This is the current proof target for W04, following the
request to complete the route used by the paper. It replaces W04's earlier
requirement of a lift on the whole final successor ranks. That stronger
statement is recorded in the separate audit;
it is not an input to this proof or to finite restoration.

The proof below connects the construction to the lift and gives the exact
interfaces still needed in Lean. The complete proof bundle
contains the supporting construction arguments. A written proof and an
implemented Lean theorem are different deliverables. No new Lean theorem
or fresh kernel check is claimed here.

## 1. Statement and the code that is captured

Work in ZF. Suppose AC fails, let \(\mu\) be the least ordinal at which
history-dependent choice fails, and let \(\Omega>\mu\) be supercompact
in Woodin's choiceless sense. Use the construction in Section 2.
Write \(P_i,c_i\) for its completed stages and cutoffs, including its
trivial seed, and write \(\pi_{ij},E_{ij},L_{ij}\) for projection,
empty-tail inclusion and prefix replacement. Stronger conditions are
smaller. In the sparse presentation the inclusions are literal, the
projections are restrictions, and the top is the empty function.

For each completed index \(\eta\), the complete code \(a_\eta\) is the
ordered pair

\[
a_\eta=\langle s_\eta,K_\eta\rangle.
\tag{1}
\]

Here \(K_\eta=\langle c_i:i\leq\eta\rangle\), and \(s_\eta\) is the
six-table forcing code through \(\eta\). Its fields are the carriers,
orders, tops, projections, empty-tail inclusions and prefix-replacement
maps. Include the seed when indexing this code. Normalized name pools
are obtained from its bases by the one fixed presentation convention;
they are not arbitrary extra choices.

At infinite marked heights all conditions in all these rows belong to \(V_\eta\).
Each graph entry adds a fixed finite number of ordered pairs. There are
only finitely many tables, so

\[
a_\eta\in V_{\eta+\omega}.
\tag{2}
\]

This is the precise finite-rank bound needed to capture (1). It concerns
the whole code, rather than just its forcing carrier. The actual Lean
bound is
`woodinSparseSourceStageCode_pair_finiteRank_at_fixedPoint` in
[WoodinSparseSourceFiniteRank](../../../../ZFVP/ModelTheory/WoodinSparseSourceFiniteRank.lean).
At infinite source indices the seed reindexing leaves the index fixed.
At finite indices it is the specified left-addition map \(i\mapsto1+i\),
as proved in W02.

**Restricted lifting theorem.** Let \(G\subseteq P_\Omega\) be generic,
let \(W=V[G]\), and let \(G_i=G\cap P_i\). Suppose

\[
\begin{gathered}
J:V_{\bar\gamma+\omega}\longrightarrow V_{\gamma+\omega}
   \quad\text{is elementary},\\
J(\bar\gamma)=\gamma<\Omega,\qquad
e=\operatorname{crit}(J)<\bar\gamma<J(e)=\delta,\qquad
c_\gamma=\gamma,\qquad J(a_{\bar\gamma})=a_\gamma .
\end{gathered}
\tag{3}
\]

Then \(\bar\gamma,e,\delta\) are marked. There is a set \(j\in W_\Omega\)
such that

\[
j:W_{\bar\gamma}\longrightarrow W_\gamma
\quad\text{is elementary},\qquad
\operatorname{crit}(j)=e,\qquad j(e)=\delta,
\tag{4}
\]

and \(j(x)=J(x)\) for every ground \(x\in V_{\bar\gamma}\).
In particular \(J(\bar\alpha)=\alpha\), for an ordinal
\(\bar\alpha<\bar\gamma\), implies \(j(\bar\alpha)=\alpha\).

The source and target in (4) are the full final ranks of the same \(W\).
No equality of their successor ranks with earlier extensions is used.

## 2. Construction inputs, in their order of proof

The primary large-cardinal input is Woodin's Definition 220 and its
small-embedding characterization, Lemma 222. The collapse is the one
defined before Lemma 225, on printed pages 321-322 of
Suitable extender models I.
The iteration follows the successor and completed inverse clauses on
printed pages 323-324, with a single consistent least-failure seed.
Woodin's printed page 325 supplies the marked-rank lifting route.
We do not import all clauses of Theorem 226 as a theorem.

Here is the order in which the auxiliary results are established.

1. The least failure \(\mu\) is an infinite regular cardinal and is below
   every ground supercompact. A singular least failure would be repaired
   by dependent choice on cofinally many coherent blocks. Woodin
   supercompactness gives \(C_2\)-correctness, and reflecting a least
   failure into the supercompact rank gives the strict bound.
   The ground-facts proof
   supplies these arguments.
2. If \(P\), its order and its top are below a ground supercompact
   \(\Delta\), and \(P\) forces that \(\nu<\Delta\) is regular and
   \(\mathrm{DC}_{<\nu}\) holds, there is, above every prescribed
   smaller bound, a ground strongly inaccessible \(\lambda<\Delta\)
   such that \(P*\dot C_\nu^\lambda\) forces
   \(\operatorname{Reg}(\lambda)+\mathrm{DC}_{<\lambda}\).
   The strict-restoration proof
   proves this after the arbitrary-prefix form of Lemma 225.
   The required global-to-rank reflection of DC is proved in the
   closed-model argument;
   it is not inferred from bare rank elementarity.
3. Start with \(P_0=\{1\}\), \(c_0=\mu\). At each successor append
   \(C_{c_i}^{c_{i+1}}\), where \(c_{i+1}\) is the least successful
   ground inaccessible upper cutoff. At a limit take the direct limit
   when the supremum of the previous cutoffs is ground strongly
   inaccessible. Otherwise take the raw inverse limit first and then
   append the restoration collapse. Its lower index is the raw
   extension's own Hartogs successor of that supremum.
4. Before appending that last collapse, establish quotient bounds from
   the earlier completed stages by Section 3 below. These preserve
   their dependent choice and regular cardinals. If the limit
   supremum is \(\lambda\) and is not ground strongly inaccessible,
   a ground unbounded map \(V_\rho\to\lambda\), together with an
   earlier collapse of its domain, makes \(\lambda\) singular in the
   raw extension. Coherent cofinal blocks give
   \(\mathrm{DC}_\lambda\). A least failure of dependent choice is
   regular, hence \(\mathrm{DC}_{<\lambda^+}\) follows.
   This also gives the choice needed to prove
   \(\operatorname{Reg}(\lambda^+)\). These are Lemmas 2-6 of the
   raw inverse-limit proof.
   Only now apply step 2 to complete this inverse stage.
5. Simultaneous induction gives every stage below \(\Omega\), strict
   increase of the cutoffs, \(i\leq c_i<\Omega\), regularity of \(c_i\)
   and \(\mathrm{DC}_{<c_i}\) in the completed extension. At an
   inaccessible direct limit the index equals the cutoff supremum:
   a smaller index would itself index a forbidden cofinal map.
   Smallness of each earlier prefix and the quotient's preservation
   of short ordinal sequences prove regularity there.
   Repeat the induction with any ground supercompact
   \(\Delta\leq\Omega\) as the bound. It gives \(c_i<\Delta\) for
   \(i<\Delta\), and therefore \(c_\Delta=\Delta\).
   This includes the final direct row at \(\Omega\).
   See the construction proof.

All forcing here uses the specified bounded names. The
W02 proof constructs a single
coherent normalization and sparse comparison through every branch and
the endpoint. It proves the projections, sections and replacement
identities, transports the actual least cutoffs, and compares generic
filters and their models. Thus the preceding construction results apply
to these actual \(P_i,c_i\), rather than an independently postulated
iteration with similar properties.

The induction just described has no dependency on (4). In particular,
regularity of a raw inverse stage's successor is proved before it is
used as a lower collapse index.

## 3. The directed quotient bound needed for a master condition

Fix a completed prefix \(B=P_\alpha\), a later completed stage
\(P_\beta\), and a \(B\)-generic \(H\). The quotient consists of ground
conditions \(q\in P_\beta\) with \(\pi_{\alpha\beta}(q)\in H\).
Use its separative preorder

\[
q\leq_H^*r\quad\Longleftrightarrow\quad
\forall u\leq q\ \exists v\leq u,r
\quad\text{within this quotient}.
\tag{5}
\]

**Bound lemma.** Every directed family in this quotient enumerated by
an ordinal \(\nu<c_\alpha\) has a lower bound for (5).

Here is the construction, including why the result is a ground
condition. Take a base name \(\dot f\) for its enumeration and
\(p\in H\) forcing the type and directedness. In \(V\), form all triples
\((d,\xi,q)\) with
\(d\leq p,\pi_{\alpha\beta}(q)\), \(\xi<\nu\), and
\(d\Vdash_B\dot f(\xi)=\check q\). For fixed \(d,\xi\) the value \(q\)
is unique.

Construct one coherent family \(b_i\) in \(V\), starting with
\(b_\alpha=p\), and retain the comparison invariant

\[
\begin{split}
(d,\xi,q)\text{ is such a triple},\quad u\leq b_i,\quad
r\leq\pi_{\alpha i}(u),d\\
\Longrightarrow\ u[r]\leq\pi_{i\beta}(q).
\end{split}
\tag{6}
\]

At a collapse coordinate, take the union of the possible tail graphs,
guarding each graph entry by its decision \(d\), the constructed prefix
bound, and the original condition's prefix. In an intermediate generic
containing that bound, (6) places every selected original prefix in the
generic. The guarded name therefore evaluates to the union of the
selected collapse conditions. Directedness in (5) makes their evaluated
graphs compatible. Projection with prefix replacement preserves
separative comparison; after fixing the intermediate generic, the
two-step quotient comparison implies compatibility of the evaluated
tails. A contrary tail extension would give a contrary two-step
extension by naming it and strengthening its prefix.

The union is a legal collapse condition. The lower collapse index is
regular and at least \(c_\alpha>\nu\). The domains are subsets of an
ordinal product and have canonical increasing enumerations. Regularity
bounds their order types, and assigning each point to its least
occurrence injects their union into a product of two ordinals of
cardinality below that lower index.

The guarded union name has rank below the upper inaccessible cutoff.
Indeed, the ranks of possible names are uniquely indexed by
\(B\times\nu\), a set below that cutoff. Ground strong inaccessibility
bounds those ranks. Normalize the resulting name by the fixed W02 map.
The comparison and normalization laws preserve (6).

At each later inaccessible direct cut, the least support bound of
each possible condition is likewise indexed by \(B\times\nu\).
Strong inaccessibility bounds all these supports at once. Beyond this
bound the union names are empty, so the constructed thread is a legal
direct-limit condition. At a raw inverse cut take the coherent thread;
it is a ground set by the ground recursion. The same base
strengthening \(r\) in (6) works at every coordinate. Complete an
inverse stage by the same collapse step, using the lower-index
regularity established in Section 2.

At the desired completed endpoint, \(b=b_\beta\) has prefix \(p\in H\).
If \(q=f(\xi)\) and \(u\leq b\) is in the quotient, choose a realizing
decision \(d\in H\) and then \(r\in H\) below \(d,\pi_\alpha(u)\).
Equation (6) gives \(u[r]\leq u,q\) in the quotient. This proves
\(b\leq_H^*q\). The empty family is bounded by the top.

The full guarded-name calculation
gives the union formula and verifies (6) at each branch. Although that
note stops at a raw terminal inverse limit, its recursion has all the
completed collapse and direct steps just used. Stopping instead at
any completed \(\beta\), including \(\Omega\), proves the stated lemma.

The existing `ForcesProjectionQuotientClosedBelow` predicate asks for
descending-sequence closure. Its meaning must remain unchanged. The
bound lemma is an additional theorem about directed families; it is
not obtained by renaming that predicate.

## 4. The actual enumeration invariant

Put \(M_i=V[G_i]\). For every completed source index \(i\leq\Omega\),

\[
M_i\models
\forall\rho<i\ \exists\nu<c_i\
\exists f:\nu\twoheadrightarrow V_\rho^{M_i}.
\tag{7}
\]

This is the invariant that bridges the construction to the rank
identifications used in lifting. Its full proof is
W03, Sections 2-8.
The following induction fixes its strict inequalities.

Dependent choice of length \(\nu<c_i\), together with separative
closure, constructs a descending history deciding every value of a
name for a function \(\nu\to A\), for an old set \(A\). A final bound
decides the entire function. Thus the tail adds no such functions.
If \(f:\nu\twoheadrightarrow X\) is old, a new subset of \(X\) would
give a new characteristic function on \(\nu\) by inverse image.
Consequently enumerations of the ranks below \(\theta\) imply
preservation of all ranks through \(\theta\).

At zero, (7) is vacuous. At successor \(i+1\), (7) at \(i\) first
preserves \(V_\rho\) for \(\rho\leq i\). The actual next collapse
supplies a \(c_i\)-enumeration of each of those old, now unchanged
ranks. Its columns surject onto \(V_{1+\rho}\); retract onto
\(V_\rho\), using the empty set as default when \(\rho>0\).
For \(\rho=0\) use the empty map. Since \(c_i<c_{i+1}\), this gives
(7) at \(i+1\). Regularity of the upper cutoff before that collapse
comes from smallness of \(P_i\) in its ground inaccessible rank.

At a nonzero limit \(i\), fix \(\rho<i\) and use the specified earlier
stage \(h=\rho+1<i\). Its rank \(V_\rho^{M_h}\) has an enumeration of
length below \(c_h\). The quotient to the actual completed \(i\)
preserves that rank by the preceding argument. The same enumeration
therefore witnesses (7) at \(i\), since \(c_h<c_i\).
This works for completed inverse limits too; it does not claim that
all their names have bounded support. At \(\Omega\) repeat this limit
argument using the endpoint code. No simultaneous choice of
enumerations is used.

At a marked \(\eta\), (7), regularity of \(c_\eta=\eta\), and the
no-new-short-functions assertion give

\[
(M_\eta)_\eta=W_\eta\models\mathrm{ZFC}.
\tag{8}
\]

For Replacement, use ambient set satisfaction for \(V_\eta^{M_\eta}\)
to form the function of output ranks for an instance. Compose it
with one short enumeration of a rank containing its domain.
Regularity bounds its range below \(\eta\).
For Choice, an ordinal enumeration of a rank containing a family
supplies the least-index choice from each member; its graph has
rank below \(\eta\). The remaining ZF axioms follow from transitivity
and finite rank bounds. A later tail preserves the shorter ranks and
regularity of \(\eta\), so (8) concerns the full final extension.

Finally set
\[
N_\eta=\{\tau\in V_\eta:\tau\text{ is a }P_\eta\text{-name}\}.
\]
Then
\[
\{\tau^{G_\eta}:\tau\in N_\eta\}=W_\eta.
\tag{9}
\]
For coverage, put a given \(x\in W_\eta\) in an earlier stabilized
rank and use a small prefix containing it. The pools
\(B_0=\varnothing\), \(B_{\xi+1}=\mathcal P(B_\xi\times P)\),
\(B_\lambda=\bigcup_{\xi<\lambda}B_\xi\) cover its extension ranks.
At a successor the all-witness name
\(\{(\sigma,p):\sigma\in B_\xi,\ p\Vdash\sigma\in\dot x\}\)
proves coverage by atomic truth. Their ranks are bounded below
\(\eta\) by \(\zeta+\omega\cdot(\xi+1)\) for a suitable
\(\zeta<\eta\). Conversely evaluation of a name in \(V_\eta\)
has rank below \(\eta\). Its used conditions also lie in one
prefix: their least prefix indices form a ground function from
a set below \(\eta\), whose range strong inaccessibility bounds.

## 5. Relative generic movement

For two collapse conditions \(u,v\in C_\lambda^\theta\), let \(A,B\)
be their used row sets. Swap \(A\), in increasing order, with the
first \(\operatorname{otp}(A)\) rows outside \(A\cup B\), and fix
the other rows. This is a specified permutation. The moved \(u\)
has row support disjoint from \(v\), so their union is a condition.

At a later coordinate, transport the first condition's name by the
already constructed prefix automorphism, perform this row operation,
and normalize. Its inverse uses the inverse permutation, inverse
prefix transport and normalization. The W02 uniqueness of normalized
representatives makes the composites literal identities. This also
works for the canonical Hartogs-successor lower-index name at a
completed inverse stage. Empty names stay empty. Common-extension
support is contained in the union of the two original supports;
all earlier direct support restrictions are preserved.

Given a common extension of the two prefixes through \(\alpha\),
start with the identity at that prefix and run this recursion only
after \(\alpha\). Hence the full automorphism fixes \(P_\alpha\)
pointwise. If \(\pi_\alpha(t)\in G_\alpha\), the set of \(s\) such that
some such ground automorphism sends \(s\) below \(t\) is dense below
the embedded prefix \(\pi_\alpha(t)\). Genericity supplies \(s\in G\).
The image generic therefore satisfies

\[
t\in G^*,\qquad G_\alpha^*=G_\alpha,\qquad V[G^*]=V[G].
\tag{10}
\]

The presentation proof, Section 6.2
verifies this recursion on the actual normalized coordinates.

## 6. Deriving the common prefix and the master condition

Assume (3). Evaluation of the captured actual cutoff tables gives
\(c_{\bar\gamma}=\bar\gamma\). For \(i<e\), \(J(i)=i\), and the common
actual cutoff table gives \(J(c_i)=c_i\). If \(c_i\geq e\), then
\(c_i=J(c_i)\geq\delta>\bar\gamma\), contradicting
\(c_i<c_{\bar\gamma}=\bar\gamma\). Hence \(c_i<e\).

The critical point \(e\) is ground strongly inaccessible. It is above
\(\omega\), and \(J\) fixes \(V_e\) pointwise by rank induction.
A ground unbounded \(f:V_\xi\to e\), \(\xi<e\), would belong to
\(V_{\bar\gamma+\omega}\). Its image would be unbounded in \(\delta\).
But its domain and every value are fixed, so \(J(f)=f\), a
contradiction. Since \(i\leq c_i<e\) for \(i<e\), the cutoff supremum
at \(e\) equals \(e\). The direct rule makes \(e\) marked, and
cutoff covariance makes \(\delta=J(e)\) marked. Also \(\delta<\gamma\)
by \(e<\bar\gamma\) and elementarity.

Every individual condition of \(P_e\) belongs to \(V_e\) and is fixed.
For \(q\in G_{\bar\gamma}\), projection covariance therefore gives

\[
\pi_{\delta\gamma}(J(q))
 =J(\pi_{e\bar\gamma}(q))
 =\pi_{e\bar\gamma}(q)\in G_e\subseteq G_\delta.
\tag{11}
\]

Thus \(D=J''G_{\bar\gamma}\) is directed in the quotient
\(P_\gamma/G_\delta\). This set belongs to \(M_\delta\): the ground
set \(J\) and the earlier generic \(G_{\bar\gamma}\) are both there.
The rank of \(G_{\bar\gamma}\) is below \(\bar\gamma+2<\delta\).
Apply (7) at \(\delta\) to a rank containing its conditions.
Least preimages give an ordinal enumeration of
\(G_{\bar\gamma}\) of length below \(\delta\); apply \(J\) pointwise
to obtain such an enumeration of \(D\). The high rank of \(J\)
does not obstruct this cardinality calculation.

Section 3 gives \(t\in P_\gamma/G_\delta\) below \(D\) in the
separative quotient preorder. Include \(t\) in \(P_\Omega\) by its
empty tail, and use (10) at \(\delta\). This produces \(G^*\) with
the same full extension and with \(G_\delta^*=G_\delta\), hence
also \(G_{\bar\gamma}^*=G_{\bar\gamma}\).

A generic filter containing \(t\leq^*q\) contains \(q\). It meets the
dense set of conditions below \(q\) or incompatible with \(q\);
the second alternative cannot meet a filter containing \(t\).
Apply this in \(M_\delta\) to the quotient generic. We obtain

\[
J''G_{\bar\gamma}\subseteq G_\gamma^*.
\tag{12}
\]

## 7. Low-name forcing and the elementary graph

At a marked \(\eta\), \(P_\eta,N_\eta\subseteq V_\eta\). They may
themselves have rank \(\eta\). Both sets, their finite-assignment
sets, and all the following relation tables belong to
\(V_{\eta+\omega}\).

The test for being a low name is bounded once \(V_\eta,P_\eta\)
are supplied. A candidate \(\tau\in V_\eta\) is a name exactly when
it belongs to a set \(E\in V_\eta\) closed under taking immediate
subnames and every entry of every member of \(E\) is a pair
\((\sigma,p)\) with \(\sigma\in E,p\in P_\eta\).
Foundation proves the converse; the subname closure of a name
proves existence of \(E\). The actual hierarchy through \(\eta\)
has a graph below \(\eta+\omega\), so its defining recursion also
gives \(J(V_{\bar\gamma})=V_\gamma\).
This definition and (3) therefore give

\[
J(N_{\bar\gamma})=N_\gamma.
\tag{13}
\]

Code forced equality and membership on this subname-closed pool
by the simultaneous atomic recursion. Membership says that
conditions identifying the first name with an active member of
the second are dense below the given condition. Equality says
that every active member of either name is densely forced to
belong to the other. The sorted pair of name ranks decreases
at each recursive call. For compound formulas use

\[
\begin{aligned}
F_{\neg\varphi}(p,b)&\ \longleftrightarrow\
                 \forall q\leq p\ \neg F_\varphi(q,b),\\
F_{\varphi\wedge\psi}(p,b)&\ \longleftrightarrow\
                 F_\varphi(p,b)\wedge F_\psi(p,b),\\
F_{\exists x\,\varphi}(p,b)&\ \longleftrightarrow\
 \forall q\leq p\ \exists r\leq q\ \exists\tau\in N_\eta\
                 F_\varphi(r,\tau^\frown b).
\end{aligned}
\tag{14}
\]

Use finite functions for assignments. Since \(\eta\) is a limit
cardinal, every such assignment belongs to \(V_\eta\), uniformly
over all finite lengths. The atomic tables are subsets of finite
products of \(V_\eta\); the complete table \(F\) is a subset of
\(\omega\times P_\eta\times N_\eta^{<\omega}\).
Thus the tables and a fixed finite number of auxiliary codes fit
below \(\eta+\omega\).

Ambient ZF proves their existence and uniqueness by recursion.
Their defining checks have only bounded quantifiers in the
supplied sets. Consequently the rank \(V_{\eta+\omega}\) recognizes
the actual tables by bounded absoluteness. No ZF or Replacement
assumption about that rank is required.

Atomic truth, directedness of the generic for conjunction, and
the decision and witness dense sets for negation and existential
quantification give

\[
\{\tau^H:\tau\in N_\eta\}\models\varphi(b^H)
\quad\longleftrightarrow\quad
\exists p\in H\ F_\varphi(p,b).
\tag{15}
\]

At an existential step, choose one witnessing name after meeting
its dense set. This does not use the maximum principle or a
choice function on all interpreted values. The
set-coded proof
gives the atomic clauses and each truth-lemma direction explicitly.

Elementarity of \(J\), the captured orders, and (13) send the
source tables to tables satisfying the target bounded clauses.
External uniqueness identifies them with the actual target
tables. Formula codes are fixed. By (12) and (15),

\[
j(\tau^{G_{\bar\gamma}})
       =J(\tau)^{G_\gamma^*},\qquad \tau\in N_{\bar\gamma},
\tag{16}
\]

is well-defined: a source forcing witness to equality transfers
to a target forcing witness. Transfer in the same way a witness
to a formula and a witness to its negation. This proves
elementarity in both directions. Equation (9), applied to \(G\)
and \(G^*\), identifies the domain and target in (16) with the
two full final ranks in (4), since both generics produce \(W\).

For ground \(x\in V_{\bar\gamma}\), its check name has rank below
\(\bar\gamma\). Uniqueness of the check-name recursion gives
\(J(\check x)=\check{J(x)}\). Hence \(j(x)=J(x)\), which proves
the critical-point and ordinal-capture conclusions.
Replacement on the set \(N_{\bar\gamma}\) forms the graph of \(j\)
in \(W\). It is a subset of \(W_{\bar\gamma}\times W_\gamma\),
so its rank is at most \(\gamma\) plus a fixed finite constant.
Since \(\gamma<\Omega\) and \(\Omega\) is an inaccessible limit,
\(j\in W_\Omega\). This completes the restricted lifting theorem.

## 8. Internal formula codes and arbitrary ground models

The Lean conclusion needed by W09 is an internal set-coded elementary
embedding, not merely preservation of every externally standard formula.
The same proof has that strength when carried out inside ZF.

For a set \(N\) of names, form its evaluation graph and the evaluation
graph on all internally finite assignments. The assertion of (15)
can be written as one predicate of the internal formula code in the
generic quotient, using these graphs, the checked forcing table,
and set satisfaction for the set of evaluated names. The atomic,
Boolean and quantifier arguments above prove its constructor clauses.
Definable induction on internal syntax inside that quotient proves it
for every internal formula code. Every internally finite tuple of
evaluated names has an internally finite tuple of ground name
representatives: finite choice is a theorem of ZF, and finite
tuples of ground elements in the extension have ground representatives.
No external induction over a nonstandard syntax tree is asserted.

This part is already available in the general theorem
`ForcingContext.groundGenericTruth` in
[InternalGenericTruth](../../../../ZFVP/ModelTheory/InternalGenericTruth.lean).
It is stated for any set of names \(D\); its first theorem has no
\(P\in V_\eta\) or \(C_1(\eta)\) hypothesis. The more specialized
`lowRank_internalGenericTruth` in the same file does have those
extra hypotheses and is not the endpoint interface to instantiate.

Likewise
`IsCodedMembershipEmbedding.value_internalForcingTruthTable` in
[InternalForcingTableTransport](../../../../ZFVP/ModelTheory/InternalForcingTableTransport.lean)
transports bounded table certificates between arbitrary transitive
source and target sets, with its explicit support and code-fixation
premises. At the present endpoints take the support to be \(V_\eta\),
prove its finite-sequence closure from inaccessible limit rank bounds,
and use the tables of Section 7. The entire internal syntax family
belongs to \(V_e\), so it and its codes are fixed.
This gives internal coded elementarity for the graph in (16).

For an externally ill-founded countable ground model, use its forcing
quotient of internal names by forced equality; do not evaluate its
names by external rank recursion. The ground, quotient and all
set-coded inductions above are then interpreted internally.
The model-transfer proof
explains this passage. An external standard-formula truth argument
alone would not discharge the internal-code conclusion.

## 9. How finite reflection supplies every hypothesis

In the finite-restoration proof take \(k=N+1\), its forcing-complexity
bound \(r_k\), and the finite list \(\Xi_N\). Include the assertion that
\(x=a_\theta\) is the actual code (1), together with the required
supercompactness and ground correctness of \(\theta\).
All code predicates belong to the fixed finite dictionary.

The finite-reflection proof
produces
\[
\eta<e<\bar\theta<\bar\theta+\omega<\bar\rho<\delta
 <\theta<\theta+\omega<\rho
\]
and \(J_0:V_{\bar\rho}\to V_\rho\) with
\[
J_0(e)=\delta,\quad J_0(\bar\theta)=\theta,\quad
J_0(\bar\alpha)=\alpha,\quad J_0(\bar x)=a_\theta .
\]
The reflected finite assertion and its correctness bound identify
\(\bar x\) with the actual \(a_{\bar\theta}\).
Equation (2) puts this code in the domain of
\(J=J_0\restriction V_{\bar\theta+\omega}\), so
\(J(a_{\bar\theta})=a_\theta\). Thus every hypothesis of (3) holds.

The lift gives directly \(j:W_{\bar\theta}\to W_\theta\) in
\(W_\Omega\), with the critical point and ordinal capture required by
Bagaria-Poveda. The finite-window theorem supplies
\(W_{\bar\theta},W_\theta\prec_{\Sigma_{N+1}}W_\Omega\).
These are precisely W09's inputs. The
effective complexity recipe
computes the new bounds after adding the complete-code assertion,
including both polarities. Its construction of \(t_N\) is noncircular.

Carrier-only recovery and lifting beyond these marked ranks are
independent additional results. Neither is a dependency of this route.

## 10. Lean implementation contracts

The following are proposed interfaces, not new declaration names claimed
to exist. Keep the underlying iteration definition and the existing
descending-closure predicate unchanged.

| Step | Exact remaining implementation | Existing starting point |
| --- | --- | --- |
| W04.1 | Export the ordinal-enumerated directed version of (5) for actual completed sparse quotients, including the endpoint. Prove it by the guarded recurrence and its common-base comparison; transport it through the specified normalization. | [WoodinCommonLiftInvariant](../../../../ZFVP/ModelTheory/WoodinCommonLiftInvariant.lean), [WoodinQuotientBoundRecursion](../../../../ZFVP/ModelTheory/WoodinQuotientBoundRecursion.lean), [WoodinCollapseDirectedClosure](../../../../ZFVP/SetTheory/WoodinCollapseDirectedClosure.lean) |
| W04.2 | Construct the normalized iteration automorphism, inverse, and relative common extension; deduce (10) for the actual endpoint generic. | [WoodinCollapseHomogeneity](../../../../ZFVP/SetTheory/WoodinCollapseHomogeneity.lean) and the explicit proof in Section 5 |
| W04.3 | From the actual complete-code equation derive markedness of \(\bar\gamma,e,\delta\), fixed \(P_e\)-conditions, and projection equation (11). | [WoodinSparseSourceInvariant](../../../../ZFVP/ModelTheory/WoodinSparseSourceInvariant.lean), [WoodinSparseSourceFiniteRank](../../../../ZFVP/ModelTheory/WoodinSparseSourceFiniteRank.lean) |
| W04.4 | In the actual \(\delta\)-prefix quotient, form \(J''G_{\bar\gamma}\), prove its short enumeration from W03, apply W04.1-2, and obtain (12). | [WoodinRankConstruction](../../../../ZFVP/ModelTheory/WoodinRankConstruction.lean), [WoodinFixedPointModel](../../../../ZFVP/ModelTheory/WoodinFixedPointModel.lean) |
| W04.5 | Prove low-name and support covariance, and table bounds for \(P_\eta\subseteq V_\eta\). Instantiate general table transport and general internal generic truth. | [InternalForcingTableTransport](../../../../ZFVP/ModelTheory/InternalForcingTableTransport.lean), [InternalForcingTableBounds](../../../../ZFVP/Syntax/InternalForcingTableBounds.lean), [InternalGenericTruth](../../../../ZFVP/ModelTheory/InternalGenericTruth.lean) |
| W04.6 | Build (16) as an internal graph; use actual sparse low-name coverage and the common final quotient to identify its domain and target. Prove check agreement, internal coded elementarity, critical point, and graph membership in the endpoint rank. | [NameMapGraph](../../../../ZFVP/SetTheory/NameMapGraph.lean), [WoodinFixedPointLowNames](../../../../ZFVP/ModelTheory/WoodinFixedPointLowNames.lean), [WoodinFixedPointModel](../../../../ZFVP/ModelTheory/WoodinFixedPointModel.lean) |
| W09 connection | Capture \(a_\theta\), discharge its rank and source-definition agreement, and apply W04.6 directly on marked ranks. | finite-restoration proof and complexity calculation |

The existing
[SuccessorRankLiftData](../../../../ZFVP/ModelTheory/SuccessorRankLift.lean)
requires the whole source forcing and order to belong to its lower rank
and requires \(C_1\)-correct endpoints. Those hypotheses need not hold
at a marked stage. Do not strengthen (3) to fit that structure.
Use the general table lemmas in W04.5 and the proven coverage (9).

Formal completion still requires proof terms for these interfaces, their
assembly on the actual iteration, the project's build and axiom audit,
and statement correspondence review. The mathematical dependency is now
the restricted theorem (3)-(4), whose proof above discharges each of its
construction, cardinality, forcing and graph obligations.
