# R18: the exact Cantor predicate implies ordinary real measurability

This mathematical note is retained from proof development. Historical implementation labels are superseded by the [current repair summary](../README.md). The summary identifies the exact formalized scope.

## 1. Exact statement and internal conventions

Work in ZF + DC. Let \(C=2^\omega\), \(S=2^{<\omega}\), and let \([s]\) be the cylinder determined by \(s\in S\). All natural numbers, finite sets, functions, recursions and sequences in this proof are internal sets.

For a finite \(F\subseteq S\) and a common length bound \(M\), put

\[
 \operatorname{Sh}_M(F)=\{t\in2^M:\exists s\in F\ (s\preceq t)\}.
\]

Use exactly the predicate in `ZFVP/SetTheory/LebesgueNull.lean`:

\[
 \operatorname{SmallMeasure}(F,m)\iff
 \exists M\in\omega\ \bigl[
   (\forall s\in F\ |s|\le M)\ \land\
   \operatorname{Sh}_M(F)\times2^m\hookrightarrow2^M\bigr].
\]

The Cantor null predicate is

\[
 \operatorname{Null}_C(N)\iff
 \forall m\in\omega\ \exists f:\omega\to S\ \bigl[
 N\subseteq\bigcup_i[f(i)]\ \land\
 \forall k\in\omega\ \operatorname{SmallMeasure}(f``k,m)\bigr].
\]

For \(g:\omega\to\mathcal P(S)\), write
\(G_g=\bigcap_n\bigcup_{s\in g(n)}[s]\). The assumed regularity property is

\[
 \operatorname{LM}_C(B)\iff
 \exists g\ [B\subseteq G_g\ \land\ \operatorname{Null}_C(G_g\setminus B)],
 \qquad
 \operatorname{ALL\_LM}_C\iff\forall B\subseteq C\ \operatorname{LM}_C(B).
\]

Let \(\mathbb R\) be the ordinary Dedekind cuts of the canonical rational field. Define \(\lambda^*(A)\) as the infimum of the total lengths of all total sequences of nonempty rational open intervals covering \(A\). The infimum takes values in \([0,\infty]\). We prove

\[
 \mathrm{ZF}+\mathrm{DC}\ \vdash\
 \operatorname{ALL\_LM}_C\ \longrightarrow\
 \forall A\subseteq\mathbb R\ \forall T\subseteq\mathbb R\quad
 \lambda^*(T)=\lambda^*(T\cap A)+\lambda^*(T\setminus A).
\]

We also prove that, in ZF + DC, this Caratheodory criterion for a set \(A\) is equivalent to the existence of a real \(G_\delta\) set \(H\supseteq A\) with \(\lambda^*(H\setminus A)=0\), including when \(A\) is unbounded.

DC implies countable choice. For a sequence of nonempty sets \(X_n\), let \(T\) be the set of finite functions selecting from the first \(k\) sets, and order successive states by extension by one entry. This is a serial relation on a nonempty set. A DC sequence has lengths \(k_0+n\); its union is a choice function on \(\omega\). This argument and finite choice use induction on internal naturals. All later uses of countable choice concern sets of candidate witnesses.

Fix a bijection \(e:\omega\to S\) by coding a length-\(n\) word \(s\) as
\(2^n-1+\sum_{i<n}s(i)2^{n-1-i}\). Fix an arithmetic enumeration of rational endpoint pairs and a pairing bijection \(\omega\cong\omega^2\). These choices are explicit definitions.

For nonnegative sequences, the sum is the supremum of all internally finite partial sums. Equivalently it is the supremum over all finite sets of indices, since each such set is bounded. This proves invariance under bijective reindexing, the flattening inequality for double sums, and interchange with finite addition. The finite geometric identity and its supremum give \(\sum_i2^{-(i+1)}=1\). The internal Archimedean property of Dedekind cuts gives \(2^{-n}\to0\).

## 2. From finite unions to total summed covers

Define

\[
 w(F)=2^{-M}|\operatorname{Sh}_M(F)|
\]

at any common length bound. If \(L\ge M\), splitting words at \(M\) gives a bijection
\(\operatorname{Sh}_L(F)\cong\operatorname{Sh}_M(F)\times2^{L-M}\). Thus \(w(F)\) is independent of the bound. Use \(M=0\) for the empty family.

Finite product counting and the finite pigeonhole principle give

\[
 \operatorname{SmallMeasure}(F,m)\iff w(F)\le2^{-m}.
 \tag{1}
\]

Indeed, an injection between finite sets exists exactly when their finite cardinalities are ordered. The forward assertion is proved by induction on the codomain cardinal, and the reverse assertion by enumerating both finite sets. These are internal finite arguments. At a common level, counting finite unions also proves monotonicity, finite subadditivity, and

\[
 w(F)\le\sum_{s\in F}2^{-|s|},
 \qquad
 w(F)=\sum_{s\in F}2^{-|s|}\quad\hbox{if }F\hbox{ is prefix-free}.
 \tag{2}
\]

For any \(U\subseteq S\), let \(P(U)\) consist of the members of \(U\) with no proper prefix in \(U\). It is prefix-free, and its cylinder union equals that of \(U\): each word in \(U\) has a shortest prefix in \(U\).

Suppose \(f\) is a null-cover witness at precision \(m\), and put \(P=P(\operatorname{ran}f)\). Every finite \(E\subseteq P\) lies in an initial image \(f``k\). To obtain \(k\), take the maximum of the least occurrence indices of the finitely many words in \(E\). Equations (1) and (2) imply

\[
 \sum_{s\in E}2^{-|s|}\le2^{-m}.
 \tag{3}
\]

Consequently the sequence equal to \(2^{-|e(i)|}\) when \(e(i)\in P\), and zero otherwise, has sum at most \(2^{-m}\). This conclusion bounds the reduced prefix-free family. The sum over the original possibly repeated cover is not used.

In fact the following exact equivalence holds:

\[
 \operatorname{Null}_C(N)\iff
 \forall r\in\omega\ \exists h:\omega\to S\quad
 N\subseteq\bigcup_i[h(i)],\qquad
 \sum_i2^{-|h(i)|}\le2^{-r}.
 \tag{4}
\]

For the forward implication, take the original witness at precision \(r+1\), form \(P\), and set

\[
 h(i)=
 \begin{cases}
 e(i),&e(i)\in P,\\
 0^{r+i+2},&e(i)\notin P.
 \end{cases}
\]

The selected words cover \(N\). Equation (3) bounds their total cost by \(2^{-(r+1)}\); the padding costs at most another \(2^{-(r+1)}\). This works for finite and empty \(P\) as well. Conversely, a total summed cover bounds every finite union by (2), and (1) gives precisely the original injection condition. No countable choice is used in (4).

## 3. The binary map and its closed images

For \(x\in C\), let

\[
 a_n(x)=\sum_{i<n}x(i)2^{-(i+1)},\qquad b(x)=\sup_n a_n(x).
\]

Finite geometric sums show
\(0\le b(x)-a_n(x)\le2^{-n}\). Thus the graph of \(b:C\to[0,1]\) is a set by Replacement.

For \(y\in[0,1]\), construct its digits recursively. If the current word \(s\) has length \(n\), choose the next digit to be zero when \(y<a_s+2^{-(n+1)}\), and one otherwise. The induction invariant is
\(y\in[a_s,a_s+2^{-n}]\), with successive words extending one another. Internal recursion gives a branch \(c(y)\), and the shrinking bound proves \(b(c(y))=y\). This defines a section without choice.

For a length-\(n\) word \(s\), finite sums and the tail bound give

\[
 b(s^\frown x)=a_s+2^{-n}b(x),\qquad
 b[[s]]=[a_s,a_s+2^{-n}]=:I_s.
 \tag{5}
\]

In particular both cylinder endpoints occur, and agreement through \(n\) bits bounds the distance of two images by \(2^{-n}\). This proves continuity and the rational-open inverse-image coding.

The endpoint fibers are singletons. If distinct branches first differ after a prefix \(s\), the difference of their first unequal digits can be cancelled only by the maximal tail on the zero side and the zero tail on the one side. Thus every nontrivial fiber has exactly the form

\[
 \{s^\frown0^\frown1^\omega,\ s^\frown1^\frown0^\omega\}.
 \tag{6}
\]

These are exactly the two expansions of an interior dyadic. The reduced dyadic denominator determines the position of the last digit in its terminating expansion, excluding any third expansion.

Cantor compactness is provable internally in ZF. Given a cylinder cover, call a word bad when its cylinder has no finite subcover. A bad word has a bad child. If the empty word were bad, repeatedly take the zero child when it is bad and the one child otherwise. This is a uniquely defined recursion with the first-order invariant that every selected word is bad. Its internal union is a branch; a covering prefix contradicts badness. A general open cover reduces to the set of all cylinders contained in some member of the cover. A finite cylinder subcover needs only finitely many cover-member witnesses. Closed Cantor subsets inherit this compactness by adjoining their open complement.

For a closed \(F\subseteq C\), the real set \(b[F]\) is closed. If \(y\notin b[F]\), the words \(s\) for which \(y\notin I_s\) cover \(F\), by the shrinking bound. A finite such family suffices. Its finitely many closed intervals have a positive minimum distance from \(y\); a rational neighborhood of \(y\) misses their union. The empty-family case means \(F=\varnothing\). Hence the complement has the canonical rational-open code

\[
 \{(p,q)\in\mathbb Q^2:p<q,\ (p,q)\cap b[F]=\varnothing\}.
 \tag{7}
\]

This proof uses internal definable recursion and finite choice. It does not assume external compactness of the externally viewed collection of a model's reals.

## 4. The specified real outer measure and null transfer

Write \(\mathcal I=\{(p,q)\in\mathbb Q^2:p<q\}\). A genuine cover is a total \(d:\omega\to\mathcal I\), and its cost is the sum of its interval lengths. Such covers of any set exist, since \((-n-1,n+1)\) covers \(\mathbb R\).

Temporary empty interval symbols of cost zero do not change the infimum. For any positive rational \(\varepsilon\), replace an empty entry at position \(i\) with \((0,\varepsilon2^{-(i+1)})\). The new cover is genuine and increases cost by at most \(\varepsilon\). Thus finite and empty auxiliary covers are legitimate when taking infima, while every final null witness can still be a total genuine interval cover.

Monotonicity and \(\lambda^*(\varnothing)=0\) follow directly. For countable subadditivity, the case \(\sum_n\lambda^*(A_n)=\infty\) is immediate. In the finite case, countable choice selects for each \(n\) a cover with cost below
\(\lambda^*(A_n)+\varepsilon2^{-(n+1)}\). Flattening gives a cover of the union with cost at most \(\sum_n\lambda^*(A_n)+\varepsilon\). Let \(\varepsilon\) decrease to zero. Therefore null sets form a hereditary countable ideal. Singletons are null by rational interval covers of arbitrarily small length.

Now suppose \(\operatorname{Null}_C(N)\). Fix \(r\), and use (4) with bound \(2^{-(r+1)}\). For each selected word \(h(i)\), enlarge the closed interval \(I_{h(i)}\) from (5) by \(\eta_i/2\) at each endpoint, where \(\eta_i=2^{-(r+i+2)}\). These genuine rational open intervals cover \(b[N]\), and their total length is at most

\[
 2^{-(r+1)}+\sum_i\eta_i=2^{-r}.
\]

Consequently

\[
 \operatorname{Null}_C(N)\ \longrightarrow\ \lambda^*(b[N])=0.
 \tag{8}
\]

For each fixed precision this uses one original witness and definable operations. It does not select an array of all precision witnesses.

For later finite-measure bounds, \(\lambda^*([a,d])=d-a\). Compactness of \([a,d]\) follows by taking the continuous affine image of compact \(C\) under \(x\mapsto a+(d-a)b(x)\). Every interval cover therefore has a finite subcover. A finite interval cover has total length at least \(d-a\): sort \(a,d\) and the finitely many covering endpoints between them, assign each resulting gap to the first interval covering its midpoint, and sum the gap lengths. Gaps assigned to one interval have total length at most its length by finite telescoping. The reverse outer-measure bound follows from rational intervals containing \([a,d]\) with length approaching \(d-a\). This proves normalization from finite counting and compactness, without invoking a measure representation theorem.

## 5. Caratheodory measurability for this outer measure

The Caratheodory measurable sets form a complete sigma algebra. Here are the needed proofs for the outer measure just defined.

A null set satisfies the criterion because its intersection with any \(T\) is null and removing it leaves \(\lambda^*(T)\) unchanged. Monotonicity and subadditivity prove both statements, including infinite outer measure. Every subset of a null set is therefore measurable.

Complements preserve the criterion. Applying the criteria for two measurable sets successively splits \(T\) into three disjoint pieces and proves closure under finite unions by subadditivity. For disjoint measurable \(E_n\), induction gives

\[
 \lambda^*(T)=\sum_{i<k}\lambda^*(T\cap E_i)
       +\lambda^*\left(T\setminus\bigcup_{i<k}E_i\right).
\]

The final term is at least \(\lambda^*(T\setminus\bigcup_iE_i)\). Take the supremum over \(k\), then use countable subadditivity on \(T\cap\bigcup_iE_i\). This proves the criterion for the union. Disjointizing a general sequence proves countable-union closure, and the same argument gives countable additivity on measurable disjoint sets. It requires no further choice beyond the proof of subadditivity.

For a rational \(q\), split every covering interval at \(q\) into its left and right open parts, admitting temporary empty parts. Their lengths add to the original length. Taking infima proves the required lower bound for the two parts of any \(T\). The omitted singleton \(\{q\}\) is null, so \(( -\infty,q)\) satisfies the criterion. Its union with \(\{q\}\) is measurable; finite differences give every rational open interval. Every open set is the union over its canonical subset of the fixed rational basis, represented by a sequence with empty sets at inactive positions. Hence all real open, closed and \(G_\delta\) sets are measurable.

Rational translation preserves outer measure because it takes genuine rational interval covers to covers with unchanged lengths, and the inverse translation gives the reverse inequality. Applying the criterion to translated test sets proves translation invariance of measurability.

If measurable \(E\) has finite outer measure, a cover of cost below \(\lambda^*(E)+\varepsilon\) has an open union \(U\supseteq E\) with finite outer measure. Splitting \(U\) by the criterion for \(E\) yields

\[
 \lambda^*(U\setminus E)<\varepsilon.
 \tag{9}
\]

Only finite quantities are subtracted here.

### 5.1 Expanded countable argument, including infinite values

The following supplies the supremum and selection steps used above. It is an
argument in ZF + DC, not an appeal to an external enumeration of a model.

For a nonnegative extended-real sequence \(u\), define
\(\sum_n u_n=\sup_N\sum_{n<N}u_n\). Each finite subset of \(\omega\) is bounded,
so this is also the supremum of the sums over finite subsets of indices.
For increasing \(x_N\) and fixed \(c\in[0,\infty]\),
\[
 \sup_N(x_N+c)=(\sup_N x_N)+c.
\]
If either term on the right is infinite, the assertion follows respectively
from \(x_N+\infty=\infty\), or by making \(x_N\) exceed any prescribed finite
bound. If both are finite, the upper inequality is monotonicity; for every
positive rational \(\eta\), some \(x_N>\sup_Nx_N-\eta\), which proves the lower
inequality. Repeating this argument proves that a finite sum commutes with
suprema over independently varying indices. All finite repetition here is
induction in the internal \(\omega\).

Fix a definable bijection \(\pi:\omega\to\omega^2\). For any nonnegative array
\(a_{ni}\),
\[
 \sum_j a_{\pi(j)}=\sum_n\sum_i a_{ni}.
 \tag{11}
\]
Indeed, any finite set of pairs is contained in a rectangle \(N\times I\).
Conversely every such rectangle has a finite preimage under \(\pi\), hence
a bounded preimage. Thus the left side is the supremum of rectangle sums.
For fixed \(N\), taking the supremum over \(I\) gives
\(\sum_{n<N}\sum_i a_{ni}\): finitely many independent truncation indices
can be replaced by their maximum. The preceding finite-sum/supremum identity
justifies this also when one of the row sums is infinite. Taking the supremum
over \(N\) proves (11). No choice principle is used in this reindexing proof.

For countable subadditivity, let \(A_n\subseteq\mathbb R\) be a set-coded
sequence and \(s=\sum_n\lambda^*(A_n)\). If \(s=\infty\), the desired inequality
is immediate. Otherwise fix a positive rational \(\varepsilon\) and put
\(\eta_n=\varepsilon2^{-(n+1)}\). For each \(n\), the candidate set
\[
 X_n=\{d\in\mathcal I^\omega:d\text{ covers }A_n,
                   \ \operatorname{cost}(d)<\lambda^*(A_n)+\eta_n\}
\]
is nonempty. Otherwise \(\lambda^*(A_n)+\eta_n\) would be a lower bound for
all cover costs, contrary to the defining greatest-lower-bound property of
\(\lambda^*(A_n)\). Separation defines each \(X_n\), and Replacement defines
the sequence \(n\mapsto X_n\). Countable choice, supplied by DC, selects
\(d_n\in X_n\). Flatten the interval array using \(\pi\). It is a total
genuine cover of \(\bigcup_nA_n\), and (11) bounds its cost by
\(s+\sum_n\eta_n=s+\varepsilon\). Consequently
\(\lambda^*(\bigcup_nA_n)\le s+\varepsilon\) for every positive rational
\(\varepsilon\), hence it is at most \(s\). The latter implication follows
from rational density if the left side is finite; if it is infinite, even
the bound for \(\varepsilon=1\) is impossible. This proves countable
subadditivity in all cases.

Here is the full countable measurable-union step. Suppose \(E_n\) are disjoint
and measurable, set \(E=\bigcup_nE_n\), and fix an arbitrary \(T\subseteq\mathbb R\).
Put \(c=\lambda^*(T\setminus E)\) and
\(s_N=\sum_{n<N}\lambda^*(T\cap E_n)\). Successive applications of the
criterion give
\[
 \lambda^*(T)=s_N+
  \lambda^*\left(T\setminus\bigcup_{n<N}E_n\right)\ge s_N+c.
\]
The supremum identity above therefore yields
\(\lambda^*(T)\ge\sum_n\lambda^*(T\cap E_n)+c\), including \(c=\infty\)
and an infinite sum. Countable subadditivity gives
\(\lambda^*(T\cap E)\le\sum_n\lambda^*(T\cap E_n)\). Hence
\[
 \lambda^*(T)\ge\lambda^*(T\cap E)+\lambda^*(T\setminus E).
\]
The reverse inequality is finite subadditivity, proving the criterion for
\(E\). For general measurable \(A_n\), use the definable disjointization
\(E_n=A_n\setminus\bigcup_{i<n}A_i\); finite algebra closure proves that
each \(E_n\) is measurable. No new witness choices are required.

Every open \(U\) has the canonical basis code
\(\{(p,q)\in\mathcal I:(p,q)\subseteq U\}\). A fixed enumeration of
\(\mathcal I\) represents \(U\) as a sequence of measurable intervals,
using the empty measurable set at inactive indices. Thus open sets are
measurable; complement and countable-union closure give closed sets and
every set-coded \(G_\delta\). This last assertion concerns internally
countable constructions; it does not presume an external list of a
model's rational numbers.

## 6. The universal-fiber envelope

Let \(A\subseteq[0,1]\), put \(B=b^{-1}[A]\), and take its exact Cantor witness
\(B\subseteq G=\bigcap_nO(g(n))\), with \(\operatorname{Null}_C(G\setminus B)\).
Set

\[
 F_n=C\setminus O(g(n)),\quad D_n=b[F_n],\quad
 K=[0,1]\setminus\bigcup_nD_n.
 \tag{10}
\]

Each \(D_n\) is real closed by (7). A real \(y\in[0,1]\) belongs to \(K\) exactly when its entire binary fiber is contained in \(G\). Since \(B\) contains every expansion of every point of \(A\), we have \(A\subseteq K\), including the dyadics.

For \(y\in K\setminus A\), its definable section \(c(y)\) lies in \(G\setminus B\). Thus
\(K\setminus A\subseteq b[G\setminus B]\), which is real-null by (8).

To give \(K\) an absolute real \(G_\delta\) code, use the opens

\[
 V_n=(\mathbb R\setminus D_n)\cap(-2^{-(n+1)},1+2^{-(n+1)}).
\]

Their intersection is \(K\). Each open has its canonical rational basis code, and Replacement forms the sequence of codes. Therefore \(A\) is the difference of the measurable \(K\) and its measurable null excess. This proves measurability of every subset of \([0,1]\) under \(\operatorname{ALL\_LM}_C\).

The construction uses images of closed sets. No step requires a continuous image of a \(G_\delta\) set to be \(G_\delta\).

## 7. Unbounded sets and one global envelope

Fix the integer enumeration \(z_{2k}=k\), \(z_{2k+1}=-k-1\). The intervals \([z_n,z_n+1]\) cover the real line, by the internal Archimedean property and integer-part construction. For arbitrary \(A\subseteq\mathbb R\), put \(A_n=A\cap[z_n,z_n+1]\). The translated set \(A_n-z_n\) lies in \([0,1]\), so Section 6 proves its measurability. Translation and countable-union closure prove that \(A\) is measurable. This argument does not need a simultaneous sequence of Cantor witnesses.

For any measurable \(A\), independently of the Cantor hypothesis, each \(A_n\) has measure at most one. Countable choice on \(\omega^2\) selects rational interval covers of \(A_n\) with costs below
\(\lambda^*(A_n)+2^{-(m+n+2)}\). Let their open unions be \(U_{mn}\). By (9),

\[
 A_n\subseteq U_{mn},\qquad
 \lambda^*(U_{mn}\setminus A_n)<2^{-(m+n+2)}.
\]

Let \(U_m=\bigcup_nU_{mn}\), and \(H=\bigcap_mU_m\). Each \(U_m\) contains \(A\), and

\[
 U_m\setminus A\subseteq\bigcup_n(U_{mn}\setminus A_n),\qquad
 \lambda^*(U_m\setminus A)\le2^{-(m+1)}.
\]

It follows that \(H\supseteq A\) is a real \(G_\delta\) and \(\lambda^*(H\setminus A)=0\). The proof never subtracts infinite measures. The global rational-open code for row \(m\) is the set of all endpoint pairs occurring in any chosen cover in that row. Conversely, any such envelope makes \(A\) measurable by the complete sigma-algebra result.

### 7.1 Witness construction and the finite-measure prerequisite

Exact interval normalization is not needed for this assembly: finiteness of
\(\lambda^*([z,z+1])\) suffices. For rational \(z\), the interval
\((z-1,z+2)\), followed by a genuine geometric filler sequence of total
length one, gives a total cover of cost four. Thus every slice \(A_n\)
above has finite outer measure without invoking the normalization argument
in Section 4. That normalization remains a separate identification of the
outer measure on intervals, not a premise needed to avoid infinite
subtraction in the envelope proof.

For completeness, let \(E\) be measurable with finite outer measure and
let \(d\) cover \(E\) with cost less than \(\lambda^*(E)+\eta\).
Its open union \(U\) is measurable, and
\(\lambda^*(U)\le\operatorname{cost}(d)<\infty\). Apply the criterion for
\(E\) to the test set \(U\). Since \(E\subseteq U\), it gives
\(\lambda^*(U)=\lambda^*(E)+\lambda^*(U\setminus E)\).
Both summands are finite by this equality, so ordinary finite cancellation
proves \(\lambda^*(U\setminus E)<\eta\). This proves (9) without assuming
outer regularity as a separate theorem.

For a measurable, possibly unbounded \(A\), its slices \(A_n\) are measurable
by finite intersection closure and have the preceding finite bound. For
each \((m,n)\), form the nonempty subset of \(\mathcal I^\omega\) consisting
of covers of \(A_n\) with cost less than
\(\lambda^*(A_n)+2^{-(m+n+2)}\). Replacement and the fixed pairing bijection
turn this into one sequence of nonempty sets, so one application of
countable choice selects the array \(d_{mn}\). There is no selection from
a proper class and no assumption that \(A\) itself has finite measure.

Define the rational open code
\[
 h(m)=\{(p,q)\in\mathcal I:\exists n\exists i\ d_{mn}(i)=(p,q)\}.
\]
Separation and Replacement form \(h\), and its open set is exactly
\(U_m=\bigcup_n U_{mn}\). Every \(x\in A\) lies in at least one slice
\(A_n\), hence belongs to every \(U_m\). If \(x\in U_m\setminus A\), a
witness \(n\) for membership in \(U_{mn}\) also witnesses
\(x\in U_{mn}\setminus A_n\). Countable subadditivity and the geometric
identity give
\[
 \lambda^*(U_m\setminus A)
 \le\sum_n\lambda^*(U_{mn}\setminus A_n)
 \le\sum_n2^{-(m+n+2)}=2^{-(m+1)}.
\]
For \(H=\bigcap_mU_m\), monotonicity gives the same bound on
\(\lambda^*(H\setminus A)\) for every \(m\). The Archimedean property
forces this value to be zero. Conversely, if \(H\) is a coded real
\(G_\delta\) containing \(A\) with null excess, then \(H\) is measurable,
its excess is measurable by completeness, and
\(A=H\setminus(H\setminus A)\) is measurable by finite algebra closure.
This proves both directions for unbounded sets.

## 8. Fixed formulas, witnesses and choice audit

Define \(\operatorname{RCov}(d,X,m)\) by requiring a total genuine rational-interval cover of \(X\) and
\(\sum_{i<k}|d(i)|\le2^{-m}\) for every internal \(k\). The infimum definition gives

\[
 \lambda^*(X)=0\iff\forall m\in\omega\ \exists d\ \operatorname{RCov}(d,X,m).
\]

From zero outer measure, take a genuine cover with total cost below \(2^{-m}\). Conversely, the finite partial-sum bounds give covers of total cost at most \(2^{-m}\) for every \(m\), so the outer measure is zero. Countable choice can package all these witnesses into one \(w:\omega^2\to\mathcal I\).

For \(h:\omega\to\mathcal P(\mathcal I)\), let
\(H_h=\{x\in\mathbb R:\forall n\ \exists(p,q)\in h(n)\ p<x<q\}\).
The resulting conclusion is the single first-order sentence

\[
 \forall A\subseteq\mathbb R\ \exists h\exists w\quad
 A\subseteq H_h\ \land\
 \forall m\in\omega\ \operatorname{RCov}(w(m,\cdot),H_h\setminus A,m).
\]

Finite sums, rational arithmetic, Dedekind cuts, function spaces, images and infima all have set-theoretic definitions. The cover space is a set, its cost range is a set, and its extended-real infimum is uniquely defined. Replacement therefore defines \(\lambda^*\) on \(\mathcal P(\mathbb R)\). Its Caratheodory sentence is likewise fixed first-order syntax.

Countable choice is used for the near-optimal covers proving subadditivity, the \(\omega^2\)-indexed covers producing the global envelope, and, if requested, the single array of all null-cover witnesses. All other infinite selections in the proof are uniquely defined internal recursions or applications of Replacement. The binary recursion uses its shrinking-interval invariant. The compactness recursion uses its explicit bad-prefix predicate. Counting, finite sorting, shadow refinement and measurable finite splitting use induction on internal naturals.

Accordingly the proof applies to any membership structure satisfying ZF + DC, including externally ill-founded structures and those with nonstandard internal naturals. It concludes measurability for every internal subset of the internal Dedekind real line. These arguments supply the mathematical proof required for R18; they do not yet supply its Lean source implementation.
