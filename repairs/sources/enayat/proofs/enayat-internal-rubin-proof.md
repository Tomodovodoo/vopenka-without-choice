# An internal Rubin construction with preservation of finite sets

This mathematical note is retained from proof development. Historical implementation labels are superseded by the [current repair summary](../README.md). The summary identifies the exact formalized scope.

## Statement and interpretation

Let V satisfy ZF and internal Choice, and let kappa be its Hartogs number of omega. Assume that V has an internal diamond sequence A on kappa. Let M0 be an actual internally countable binary structure code in V satisfying full internally coded ZF. The application also supplies standard omega and external countability of V. We retain those hypotheses, although the construction below uses internal set operations throughout.

There are actual codes N and f in V such that f is an internally coded elementary embedding of M0 into N, N satisfies full internally coded ZF, its carrier has internal cardinality kappa, it satisfies the two corrected Rubin clauses, and every set which N regards as finite has an internally countable member trace in V.

The first Rubin clause asks for an actual strictly increasing cofinal kappa-sequence in every internally parametrically definable directed poset without a maximum. The second asks that an actual maximally compatible directed subset with such a cofinal sequence be internally parametrically definable. Maximal compatibility means that a point compatible with every member belongs to the subset. A definition may use any internal formula code and any internally finite tuple of parameters. The conclusion is definability, not member-coding of an arbitrary proper class.

In this proof, sets, functions, finite sequences, countability, consistency, ordinals, clubs and stationarity are interpreted inside V unless another model is named. In particular, an M-finite set is finite according to the coded structure M. Its member trace need not be finite according to V. A satisfaction assertion about M uses the actual satisfaction set for M, rather than ambient membership.

Internal Choice makes kappa the first uncountable cardinal and makes it regular. Indeed, the union of countably many countable ordinals is countable: choose enumerations, combine them with a pairing function on omega, and enumerate the union. Thus a countable sequence cannot be cofinal in kappa. Every ordinal below kappa is countable. These facts will be used only within V.

## The upper-bound theory

Fix a countable coded M with carrier D satisfying full coded ZF. Its internally parametrically definable sets and relations form a countable family. An enumeration of D, the countability of the syntax, and the finite parameter tuples give an enumeration of their definitions. List the definable directed strict orders without a last element as (P_i, <_i). Starting with a reflexive partial order, its strict part is the order used here. This list is nonempty, since it includes M's ordinals under strict inclusion.

Use a countable relational language with equality and membership, constants c_a for a in D, and constants d_i for the orders. The background theory T consists of the complete elementary diagram of M, the sentences P_i(d_i), and c_a <_i d_i for all a in P_i. These form an actual countable theory. The elementary diagram is a set obtained by separation from the sentence codes using M's satisfaction set. Each order formula has a finite tuple of old parameters.

Let sigma be a sentence, and list the distinct d-constants occurring in it as d_{k_0}, ..., d_{k_{p-1}}. Abstract them to variables s_0, ..., s_{p-1}; the result sigma*(s) is an M-formula with finitely many old parameters. Write P for the product of these p definable carriers, as computed in V. This notation does not assert that the corresponding definable classes are sets in M. All block statements below are M-formulas obtained by quantifying their coordinates individually.

For a body B(s), define

\[
\operatorname{BE}(B)\iff
 \forall r\in P\ \exists s\in P\,
 [\bigwedge_{j<p}r_j<_{k_j}s_j\ \land B(s)],
\]

and

\[
\operatorname{EA}(B)\iff
 \exists r\in P\ \forall s\in P\,
 [\bigwedge_{j<p}r_j<_{k_j}s_j\ \longrightarrow B(s)].
\]

These are simultaneous blocks, not alternating quantifiers. The zero-coordinate product contains the empty tuple. Coordinatewise directedness and the absence of a last element imply that every finite collection of lower bounds has a strict upper bound. Consequently EA is closed under finite conjunction, EA(not B) is equivalent to not BE(B), and EA(B) contradicts BE(not B).

The following exact criterion concerns syntactic consistency inside V:

\[
 T\cup\{\sigma\}\text{ is consistent}\quad\Longleftrightarrow\quad
 M\models\operatorname{BE}(\sigma^*).
\tag{1}
\]

For the forward direction, if BE fails, choose its witnessing old tuple r. The elementary diagram contains the sentence that every tuple above r fails sigma*. The finitely many axioms asserting membership of the displayed d-constants and r_j <_j d_{k_j} then derive not sigma. This contradicts consistency.

For the reverse direction, any purported proof of contradiction uses an internally finite set of diagram sentences and upper-bound constraints. Combine its finitely many bounds for each coordinate in the support of sigma. BE gives values for these coordinates satisfying sigma above all those bounds. Give each remaining d-constant mentioned in the proof a strict upper bound for its finitely many constraints. Interpret all old constants by themselves. This is an M-realization of every premise used by the proof, including equality, contrary to the soundness induction on that finite proof. This proves (1) without an application of external compactness. Taking sigma to be truth also proves consistency of T.

The support list, abstraction, substitutions, block quantifiers and finite conjunctions in this argument are obtained by recursion on syntax codes in V. They are actual codes with the displayed satisfaction clauses. Thus (1) applies uniformly to every internal sentence and internally finite context.

## Separating types over the enlarged theory

Let U,W be actual subsets of D which are inseparable in M: no internal formula with a finite tuple of parameters defines a set containing U and missing W. For every q and formula psi(v,x_0,...,x_{q-1}) in the language of T, form the q-type

\[
 p_{U,W,\psi}(x)=
 \{\psi(c_a,x):a\in U\}\ \cup
 \{\neg\psi(c_b,x):b\in W\}.
\]

Suppose a formula theta(x) is consistent with T and implies every member of this type. Choose one distinct finite list of d-indices covering both theta and psi. Abstraction gives formulas theta*(x,s) and psi*(v,x,s). Define, in M,

\[
\begin{aligned}
 \Lambda(v)&=\operatorname{EA}
   (\neg\exists x\,[\theta^*(x,s)\land\neg\psi^*(v,x,s)]),\\
 \Delta(v)&=\operatorname{EA}
   (\neg\exists x\,[\theta^*(x,s)\land\psi^*(v,x,s)]).
\end{aligned}
\]

The supposed implications make each corresponding negated type instance inconsistent with theta. Criterion (1) and its EA dual therefore put U inside Lambda and W inside Delta.

Lambda and Delta are disjoint. If v belonged to both, combine their eventual bounds. Consistency of theta gives BE(exists x theta*) by (1). Choose s above the combined bound and a tuple x satisfying theta*. Either psi*(v,x,s) holds or it does not. The first contradicts the Delta bound and the second the Lambda bound. Thus Lambda contains U and misses W, contrary to inseparability.

Both displayed predicates are single internally coded M-formulas with finite old parameter tuples. Their formation only abstracts the finitely many d-constants and appends finite quantifier blocks. This proves local omission, equivalently nonprincipality, over the entire upper-bound theory T. It does not concern the elementary diagram alone.

## Types for old finite sets

For each a in D such that M regards a as finite, let

\[
 p_a(x)=\{x\mathrel E c_a\}\ \cup
         \{x\ne c_m:m\mathrel E a\}.
\]

Suppose a T-consistent theta(x) implies this type. Use a fixed support list for theta, and put B(s,x)=theta*(x,s). Criterion (1) gives BE(exists x B). It also gives

\[
 \operatorname{EA}(\forall x\,[B(s,x)\longrightarrow x\mathrel E a]),
\tag{2}
\]

and, for each old m E a,

\[
 \operatorname{EA}(\forall x\,[B(s,x)\longrightarrow x\ne m]).
\tag{3}
\]

Combining (3) requires induction in M, not a finite enumeration of a's ambient trace. For a varying M-set b, use the single formula

\[
 \left[\forall m\in b\ \operatorname{EA}
       (\forall x[B(s,x)\to x\ne m])\right]
 \longrightarrow
 \operatorname{EA}
       (\forall m\in b\ \forall x[B(s,x)\to x\ne m]).
\tag{4}
\]

It holds for the empty set: choose a tuple in P and the exclusion condition is vacuous. If it holds for b, the hypothesis for b union {m} supplies the hypothesis for b and one further eventual bound for m. Use the induction conclusion for b and combine its bound with the bound for m, coordinate by coordinate. Transitivity of the strict orders preserves both conclusions above the combined bound. Hence (4) holds for b union {m}.

Full coded ZF in M supplies finite-set induction for this precise formula, with all the parameters from B and the displayed orders. Applying it to the M-finite a combines (3) into one eventual bound excluding every member of a. Combine that bound with (2). BE(exists x B) now supplies, above the common bound, a B-solution belonging to a and unequal to every member of a. Taking that solution itself as the member gives a contradiction.

This proves local omission of p_a over T. No choice principle in M is used, and the argument permits a's trace to be infinite according to V.

## The internal Henkin construction

At a successor we have a countable family of inseparable pairs. The family of their separating types is countable, because the language and the set of finite arities are countable. The finite-set types are indexed by a subset of D and are countable as a family too. Each type is an actual set of formulas. Keep T as the permanent background and add a countable pool of fresh Henkin constants h_i.

Inside V enumerate the sentences, the existential formulas and all pairs consisting of a type index and a tuple of constant names of its arity. Run a recursion on omega whose state is a finite set of added sentences, consistent together with T. Sentence decisions preserve consistency by classical deduction. For an existential formula, add its Henkin witness implication using an h_i absent from the finite state and that formula. This preserves consistency: a contrary finite proof, followed by the deduction theorem and generalization of the fresh constant, would contradict consistency of the preceding state. Every theory axiom is already in the permanent background. An equivalent schedule may enumerate them explicitly.

Here is the omission step, including its parameter issue. Write the current finite conjunction as delta(h), where h lists all the Henkin constants occurring in it or in the tuple t at which omission is required. The old c-constants and the upper-bound d-constants remain in the language of T. Replace the distinct h-constants by variables u and form

\[
 \vartheta(x)=\exists u\,
 [\delta(u)\land\bigwedge_{j<q}x_j=t_j(u)].
\tag{5}
\]

This is a formula of the type's arity, and T together with its existential closure is consistent. Otherwise the old finite condition, which supplies the corresponding witnesses, would be inconsistent. Local omission gives a type member eta such that T together with exists x(theta(x) and not eta(x)) is consistent.

The latter sentence is equivalent to exists u(delta(u) and not eta(t(u))). The fresh-constant lemma therefore says that T together with delta(h) and not eta(t(h)) is consistent. To see the needed direction of that lemma, a contradiction with fresh constants would, after deduction and generalization of those constants, derive the negation of the existential closure from T. The h-constants are fresh for T even when they have occurred in previous finite conditions. Formula (5) accommodates repeated names and old constants by its explicit equality constraints. This proves the omission step without changing T or assuming that a type stays nonprincipal under arbitrary new axioms.

Use internal enumerations to make the next consistent choice, taking the least permissible index. The tests are statements about coded finite proofs. Natural recursion and separation/replacement in V give the entire sequence as an actual function. Let H be T together with the union of the finite conditions. Every finite proof from H is contained in T and one sufficiently late finite condition, so H is consistent. It decides every sentence, contains Henkin witnesses and omits each type at each tuple of names. Completeness and consistency also imply deductive closure: if a consequence were rejected, its negation and a finite proof of it would contradict consistency.

Enumerate all constant names by omega. Quotient them by equality in H and represent each equality class by its least index. This is an actual subset of omega in V. Set E([c],[d]) iff the sentence c E d belongs to H. Equality axioms make this independent of representatives. The truth induction on internal formula codes has the following steps. Atomic formulas use the definition and equality. Boolean connectives use complete consistent deductive closure. For an existential, an accepted existential has a named witness by the schedule, and a satisfying named instance implies its existential closure by deduction. These steps establish the truth lemma for every internal formula and assignment.

The resulting countable binary code M' models T. Sending a to the class of c_a gives an actual elementary embedding, for every internal formula and finite tuple. In particular M' satisfies full coded ZF. All the separating types are omitted. If a new-parameter formula separated the images of U,W, choose names for its finite parameter tuple; it would realize the corresponding separating type, a contradiction. Finally, an element of c_a not equal to any c_m for m E a would realize p_a. Thus no old M-finite set gains a member.

This proves the required successor theorem with all three properties simultaneously: upper bounds, preservation of the specified inseparable pairs, and preservation of every old finite set.

## An actual recursion on kappa

Relabel M0 onto a countable subset D_0 of kappa using an actual injection of its carrier into omega. Retain this relabelling as f_0. We will construct literal elementary inclusions M_alpha=(D_alpha,E_alpha), with D_alpha a countable subset of kappa and E_alpha a subset of D_alpha squared.

At stage beta put U_beta=A(beta) intersect D_beta and W_beta=D_beta minus U_beta. Record whether this pair is inseparable in M_beta. At the successor of alpha apply the proved successor theorem to all orders definable in M_alpha and all pairs recorded as inseparable at indices beta<=alpha. There are countably many such indices. The induction invariant ensures that these same pairs are still inseparable in M_alpha, so the theorem's hypothesis holds. Also preserve all M_alpha-finite sets.

Relabel the extension onto a countable subset of kappa while fixing D_alpha pointwise and including alpha. If alpha is already in D_alpha there is no extra constraint. Otherwise assign alpha to one fresh element of the extension. There is such an element because the new bound for M_alpha's ordinals cannot be old: if it were the image of an old ordinal, its own upper-bound axiom would make it strictly above itself. Map the remaining new elements injectively into the remaining ordinals. A countable set of used ordinals leaves kappa many unused ordinals, so these choices exist inside V. Transport the relation along the relabelling. This gives M_{alpha+1} and alpha belongs to D_{alpha+1}.

At an internal nonzero limit lambda<kappa take the union of the preceding carriers and relations. This is a countable structure because lambda is countable and V has Choice. The inclusions into the union are elementary for every internal first-order formula. For completeness, use induction on the formula: atomic relations agree by the chain invariant; negation uses the induction equivalence; a witness in an earlier model remains a witness; and a witness in the union lies in some later stage, where elementarity reflects the existential assertion to the stage containing its parameters. Each internally finite parameter tuple lies in one stage. The argument is an internal syntax induction in V.

There is no class-choice assumption in this recursion. All possible stage records (D,E) belong to the fixed set

\[
 B=\mathcal P(\kappa)\times\mathcal P(\kappa\times\kappa).
\]

Fix in V a well-order of B. From a coded history of length at most kappa, the assertions of countability, coded ZF, elementarity, upper bounds, preserved finite sets and preserved guessed pairs are first-order assertions about sets and their coded satisfaction relations. Choose the least admissible successor record in this fixed well-order. At a limit the carrier and relation are uniquely specified unions. On invalid histories or an empty candidate set use the fixed initial record. This defines a total first-order operation on a set of histories, for example the union of B^alpha for alpha<=kappa. Internal transfinite recursion yields an actual sequence of length kappa. Induction using the preceding existence proofs shows that along this sequence every history is legal, so the fallback is never used there.

Preservation of a fixed old finite set composes at successors. At a limit every purported new member appears at an earlier stage; the induction hypothesis at that stage puts it in the original trace. Inseparability of a fixed recorded pair also persists at limits: a separating formula uses a finite tuple of parameters lying in an earlier stage; elementarity makes it a separator there, contrary to the induction hypothesis. These arguments verify the invariants needed for every successor of the recursion.

Take the final union. Its carrier is exactly kappa, since every alpha entered at its successor, and its relation E is an actual subset of kappa squared. The same union truth induction gives full coded ZF and an actual coded elementary embedding f=f_0 from M0. An original recorded inseparable pair remains inseparable in this final union by the finite-parameter argument. Every old finite set retains exactly its original member trace.

## The first Rubin clause

Let P,R be a definable directed poset without a maximum in N. Its formula codes and finite parameter tuple are available over some M_{alpha_0}; only the parameters need to belong to the stage. Elementarity says that the same definitions give a directed poset without a maximum in every M_beta for beta>=alpha_0. The successor construction supplies a point d_beta in D_{beta+1} strictly above every point of P intersect D_beta. Select the least ordinal point satisfying that condition; replacement gives an actual function beta -> d_beta.

Let sigma(i)=alpha_0+i using internal ordinal addition. For i<kappa these are countable ordinals, sigma is strictly increasing, sigma(i)>=alpha_0, and sigma(i)>=i. Put c(i)=d_{sigma(i)}. If i<j then d_{sigma(i)} belongs to D_{sigma(j)}, so the upper-bound property gives R(c(i),c(j)) and distinctness. Every x in P belongs to some D_beta, and sigma(beta)>=beta, so x is below c(beta). This is the required actual cofinal strictly increasing kappa-sequence.

## Diamond reflection and the second Rubin clause

Let F be an actual maximally compatible directed subset of a definable poset P,R in N, with an actual strictly increasing cofinal kappa-sequence, and suppose F has no internal parameter definition. All constructions in this paragraph occur in V.

There is a club C_1 of limit alpha such that D_alpha=alpha. For each beta the countable D_beta is bounded in kappa. Close an ordinal successively above these bounds for all smaller beta and take the supremum of omega many steps. Regularity keeps it below kappa. At a closure point, continuity gives D_alpha subset alpha, and the rule putting beta into D_{beta+1} gives the reverse inclusion. Limits of these closure points have the same property by continuity.

For q in P minus F, maximal compatibility gives an h(q) in F with no common upper bound with q in P. Choose the least ordinal witness; elsewhere set h(q)=q. There is a club C_2 closed under h. More generally, any countable family of finitary functions on kappa has a club of simultaneous closure points. To prove unboundedness, start above any ordinal and repeatedly close its countable initial segment under all the functions, then take the supremum of omega steps. At each step only countably many values are added, and regularity bounds their supremum below kappa. A finite tuple below the final supremum is contained in one step. Closedness follows by putting any finite tuple below a limit of closure points into one of those closure points. This proof gives an actual club set by separation.

For each internal unary formula phi(x,z) and finite parameter tuple b in kappa choose the least g_phi(b) witnessing disagreement between phi(x,b) in N and F. Such a witness exists because F has no internal parameter definition. The syntax is countable, so these are a countable family of finitary functions. Their definition uses the actual satisfaction set for N and the actual parameter F. The preceding argument gives a club C_3 closed under them.

Diamond applied to the actual subset F of kappa gives a stationary set of alpha with A(alpha)=F intersect alpha. Intersect it with C_1,C_2,C_3 and the club of indices above the parameters defining P,R. At an index alpha in this intersection the guessed pair is precisely

\[
 U=F\cap D_\alpha,\qquad W=D_\alpha\setminus F.
\]

It is inseparable in M_alpha. Otherwise a stage definition would agree with F on D_alpha. Elementarity interprets the same definition in N, and its disagreement witness g_phi(b) lies in D_alpha by C_3, a contradiction. Thus this is a recorded pair, and the recursion makes it inseparable in N. Closure under h ensures that each q in P intersect D_alpha outside F has an incompatible partner in F intersect D_alpha.

The latter trace is countable. For every x in it choose an index of the given cofinal chain above x; the least index suffices. By regularity of kappa, all these indices are bounded by one k<kappa. If the trace is empty take k=0. Let e be the chain point at k. Transitivity makes e an upper bound of the whole trace. The N-definition

\[
 X=\{x\in P:R(x,e)\}
\]

contains U. It misses W: points outside P are excluded immediately, and if q in P intersect W belonged to X, its partner h(q) belongs to U and is also below e. Then e would be a common upper bound in P of q and h(q), contradicting their incompatibility. This separates the recorded pair in N, a contradiction. Therefore F has an internal formula and finite parameter definition, as required.

All clubs and the guessed subset used here are actual sets of V. The argument invokes internal diamond and internal regularity, not external stationarity of kappa.

## FinSmall and the forcing application

If a in N is regarded as finite, choose M_alpha containing a. Elementarity says that M_alpha also regards it as finite. Finite preservation at all later stages and at the final union identifies its final trace with its trace in M_alpha. That is a subset of the internally countable D_alpha. Restrict an actual injection D_alpha -> omega to this trace. This proves the required internal countability and hence FinSmall.

The constructed f and N are actual elements of V, obtained from the internal Henkin sequences, fixed-set successor selection and internal transfinite recursion. The relation of N is represented by E, independently of V's own membership relation. The satisfaction and embedding assertions quantify over the complete internal syntax and all internally finite parameter assignments. No external model has been inserted into V by an absoluteness claim.

In the application take V to be the actual diamond-forcing extension. Once its stated ZF, Choice, preserved Hartogs number, internal diamond and coded M0 hypotheses are established, apply the construction there. External ill-foundedness does not alter any of its internal set recursions or its use of the coded models' own ZF instances. This supplies the exact internally coded Rubin source for the subsequent specialization construction. Verification of that subsequent forcing and its interpretation remains a separate route, as does implementation of this existence theorem in Lean.
