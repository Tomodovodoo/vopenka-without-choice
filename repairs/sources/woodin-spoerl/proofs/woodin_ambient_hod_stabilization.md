# Ambient HOD along the restoration iteration

This mathematical note is retained from proof development. Historical implementation labels are superseded by the [current repair summary](../README.md). The summary identifies the exact formalized scope.

This note develops the bounded stabilization argument proposed in the response supplied on 9 September 2026. It uses the canonical name presentation, the guarded quotient bounds, and the correctness and ordinal-capture lemmas established separately. The conclusion is a stabilization theorem for the HOD of full set-forcing extensions. It does not prove the HOD-preserving embedding assertion in Theorem 226.

Write \(P_\tau\) for the completed forcing at stage \(\tau\), \(c_\tau\) for its endpoint, \(\Omega\) for the final supercompact cutoff, and
\[
N_\tau=V[G_\tau],\qquad W=N_\Omega,
\qquad A_r^\tau=\mathrm{HOD}^{N_\tau}\cap V_{r+1}^V.
\]
The ground model satisfies ZF. All generics below are used through the set-forcing theorem; none is asserted to belong to the ground model.

## 1. Restarting a tail inside an intermediate extension

Fix completed stages \(\alpha<\tau\leq\Omega\). In \(N_\alpha\), start the restoration recursion at the ordinal endpoint \(c_\alpha\), retain the original stage labels above \(\alpha\), and run it to \(\tau\). The claimed forcing equivalence with the actual quotient requires both agreement of endpoint selection and a factorization lemma at limits.

### 1.1. The inaccessible candidates

The statement that an ordinal \(\xi>c_\alpha\) is strongly inaccessible is the same in \(V\) and \(N_\alpha\).

For preservation, an inaccessible candidate satisfies \(P_\alpha\in V_\xi\), by the rank bound \(\operatorname{rank}(P_\alpha)<c_\alpha+\omega\). The small-forcing name-pool argument therefore applies. Conversely, any ground map \(V_\beta^V\to\xi\), \(\beta<\xi\), with unbounded range extends in the forcing extension to \(V_\beta^{N_\alpha}\) by assigning zero on new arguments. Thus a ground failure of the defining inaccessibility property remains a failure. This also rules out a newly inaccessible ordinal which was not a ground cardinal.

### 1.2. The name translation used at a limit

Here is the factorization lemma in the form needed for this recursion. Suppose factorization into \(P_\alpha\) and the internally reconstructed tail has already been proved at every earlier stage below a limit \(\zeta\). Let \(\dot u\) be **one** ground \(P_\alpha\)-name and let
\[
p\Vdash_{P_\alpha}\dot u\text{ is a condition of the reconstructed tail through }\zeta.
\tag{1}
\]
There is a ground condition \(q\) of the original iteration through \(\zeta\), with initial prefix \(p\), whose image in the reconstructed tail is below \(\dot u\) in every initial generic containing \(p\). No sequence of independently chosen coordinate names is used.

We spell out the operations on names involved in this claim.

* Evaluation of a fixed coordinate of \(\dot u\) is a uniquely specified operation in a \(P_\alpha\)-extension. A name for it can be formed using all guarded local witnesses from bounded name pools. The same applies to every restriction of \(\dot u\). Such unique-value name formation in ZF does not require the maximum principle for arbitrary existential assertions.
* A \(P_\alpha\)-name for an \(R\)-name can be composed into a \(P_\alpha*\dot R\)-name. To see that this operation needs no Choice, bound the rank of the named inner name by the rank of the outer name. Recursively include every pair witnessed below an initial condition, using bounded pools for the possible inner subnames and conditions. Guard subnames outside their witnessing condition. At inner name rank \(\gamma\), use all smaller bounds \(\beta<\gamma\) and all conditions forcing a subname to have rank at most \(\beta\). The induction on \(\gamma\), and density of ordinal decisions, prove equality of evaluations. Each stage is a Separation construction from a supplied set of candidates.
* If \(i:T\to S\) is the previously constructed dense embedding of forcing preorders, pull an \(S\)-name back by the recursion
  \[
  i^*(\sigma)=\{(i^*(\nu),t):\exists(\nu,s)\in\sigma\ [i(t)\leq_S s]\}.
  \tag{2}
  \]
  Density proves the evaluation identity. Formula (2) chooses no preimage of a condition.

Recursively suppose \(q\restriction\xi\) has been formed. Compose the single initial name for the coordinate \(\dot u(\xi)\), and pull it back using the earlier factorization. This gives a name in the original prefix forcing for the requested collapse coordinate. Guard it by \(q\restriction\xi\), making it empty off that condition, and apply the canonical minimum-rank normalization. Under \(q\restriction\xi\), it has the required value; elsewhere it is a legal top collapse condition. The upper inaccessible cutoff bounds the normalized name's rank. Set this to be the coordinate of \(q\).

All operations in this recursion are specified from \(p,\dot u\) and the earlier factorization maps. The initial prefix remains \(p\) throughout. At inverse limits the resulting coherent sequence satisfies the terminal support rule. At direct limits one must make the following additional check.

### 1.3. Uniform support at every direct cut

A later direct-limit index \(\chi>\alpha\) is its inaccessible endpoint. Indeed, if the inaccessible supremum of the earlier endpoints were strictly larger than its index, the endpoint sequence would contradict that supremum's strong inaccessibility; and the increasing endpoint sequence is everywhere at least its index.

By (1), \(p\) forces that the support of \(\dot u\) below \(\chi\) is bounded. Below every condition extending \(p\), there is a condition deciding an ordinal bound. Let \(D\) be the set of such deciding conditions, and assign to each member the least bound it forces. Since
\[
P_\alpha\in V_\chi,
\]
strong inaccessibility in the ground model bounds this function by one \(b_\chi<\chi\). Density gives
\[
p\Vdash\operatorname{supp}(\dot u)\cap\chi\subseteq b_\chi.
\tag{3}
\]
At every coordinate at or above this bound and below \(\chi\), the translation in Section 1.2 is forced empty under its guard. It is also empty off the guard. Normalization consequently makes that coordinate literally empty. Thus \(q\restriction\chi\) has bounded support.

This argument applies separately at **every** direct cut. Each bound is a least definable ordinal or the supremum of a definable range, so the recursion does not choose a family of bounds from arbitrary sets. This completes the construction of a legal ground \(q\) from (1).

### 1.4. Order, density, and uniform prefixes

In the other direction, a ground thread gives an internally reconstructed thread by partial evaluation at \(G_\alpha\), translation of its remaining names, and normalization. This operation preserves support and order.

The preceding construction proves density: any named reconstructed tail condition below an initial condition has a ground thread below it. To check order reflection, consider two fixed ground threads whose reconstructed images are comparable in \(N_\alpha\). Their comparison is **one set-theoretic assertion about the whole threads**. The forcing truth lemma supplies one \(s\in G_\alpha\) forcing this entire assertion, strengthened to lie below both initial prefixes. The successor translation and its evaluation identity then imply the coordinate comparisons for the splice with this same \(s\). Therefore the actual quotient relation is precisely
\[
q\preccurlyeq_{G_\alpha} r
\quad\Longleftrightarrow\quad
\exists s\in G_\alpha\quad
\operatorname{splice}_s(q)\leq r.
\tag{4}
\]
The same prefix works at all coordinates. Inferring (4) from independently obtained prefixes at individual coordinates would be invalid.

Together these constructions give forcing equivalence, including at inverse limits. They do not identify a new thread in \(N_\alpha\) with a ground sequence of already evaluated coordinates. They represent it by a ground thread of names, as required by the original iteration.

### 1.5. The least successful endpoints

Assume inductively that the reconstructed tail through \(\beta\) is equivalent to the actual quotient, with endpoint \(c_\beta\). For each inaccessible candidate \(\xi>c_\beta\), the reconstructed test is
\[
N_\alpha\models
1_{R_\beta*C_{c_\beta}^{\xi}}\Vdash\mathrm{DC}_{<\xi}.
\tag{5}
\]
The reconstruction uses only ordinal parameters. Weak homogeneity of the OD forcing \(P_\alpha\) makes (5) a decided statement at its top. By the factorization already proved and the two-step forcing theorem, its positive value is equivalent to
\[
1_{P_\beta*C_{c_\beta}^{\xi}}\Vdash\mathrm{DC}_{<\xi}
\]
in the ground model. Thus the same candidates succeed and the least successful candidate agrees.

At an inverse limit, Section 1.2 identifies the full raw extensions. Their Hartogs successors therefore agree. The appended collapse and its least upper cutoff agree by the same argument. The limit suprema depend only on the cofinal tail of the endpoint sequence, so restarting after \(\alpha\) does not change them.

This simultaneous induction establishes the reconstruction. In \(N_\alpha\), its poset, order and homogeneity proof are definable from the ordinal parameters \(\alpha,c_\alpha,\tau\). Forcing equivalence with the actual quotient suffices; literal equality with a ground-coded quotient is unnecessary.

## 2. Monotonicity of ambient HOD

An OD weakly homogeneous forcing \(R\) over a ZF model \(N\) satisfies
\[
\mathrm{HOD}^{N[K]}\subseteq\mathrm{HOD}^N.
\tag{6}
\]
For an ordinal definition in the extension, homogeneity decides its statements about ground objects at the top. The forcing relation and the OD presentation convert the defining statement into an ordinal definition in \(N\). Applying this rank-recursively to the hereditary definition gives (6). This is the usual set-forcing proof and uses no maximal-antichain selection.

Apply (6) inside \(N_\alpha\) to the presentation from Section 1. It follows that
\[
\mathrm{HOD}^{N_\tau}\subseteq\mathrm{HOD}^{N_\alpha}
\quad(\alpha\leq\tau\leq\Omega).
\tag{7}
\]
Applying the same fact to every full prefix over \(V\) shows that these HOD classes consist of ground sets. Hence
\[
A_r^\tau
=\mathrm{HOD}^{N_\tau}\cap(N_\tau)_{r+1},
\qquad
A_r^\tau\subseteq A_r^\alpha\quad(\alpha\leq\tau).
\tag{8}
\]
Closure alone would not give (7); the ordinal-definable reconstruction is the reason it holds.

## 3. The complexity needed to reflect losses

Let \(\operatorname{Hist}(\tau,h)\) state that \(h\) is the canonical completed history through \(\tau\), including its forcing presentations and maps. A history is a set parameter, not a purported class truth predicate.

The canonical-presentation calculation gives
\[
\operatorname{Hist}(\tau,h)\in\Sigma_3.
\tag{9}
\]
In more detail, successful restoration tests have \(\Pi_2\) form. A failed earlier candidate has a \(\Sigma_2\) certificate. There are set-many tests in a supplied history, so Collection bounds the negative witnesses in one auxiliary set without choosing a witness function. Supremum, successor, forcing-name and presentation computations have the rank-code verification described in the presentation note. Thus one can put the entire assertion in the form \(\exists D\,\forall u\,\exists v\,\vartheta\) with bounded \(\vartheta\).

The relation \(\operatorname{It}(\tau,P)\) saying that some such history ends in forcing \(P\) is therefore \(\Sigma_3\). This formula refers to any existing history of the untruncated recursion. It asserts no existence of stages beyond \(\Omega\). Uniqueness makes any two valid histories agree on their common domain.

For fixed supplied set forcing \(P\),
\[
F(P,x)\iff 1_P\Vdash\check x\in\mathrm{HOD}
\]
has \(\Sigma_2\) complexity. HOD membership is \(\Sigma_2\), and the fixed-set-forcing complexity calculation uses density and Collection rather than the maximum principle. Consequently forcing its negation has \(\Pi_2\) form.

Define without an \(\Omega\) parameter
\[
L(x)\iff\exists\tau\,\exists P\,
\bigl(\operatorname{It}(\tau,P)\land
1_P\Vdash\check x\notin\mathrm{HOD}\bigr).
\tag{10}
\]
Then \(L\) is \(\Sigma_3\). Its definition includes a possible loss at the full set forcing \(P_\Omega\).

## 4. Strong HOD supercompactness supplies C_3 correctness

Let \(\delta\) be ground strongly-HOD-supercompact. The established ordinal-capture lemma permits Definition-223 embeddings with critical point above any prescribed \(\beta<\delta\), and with arbitrarily tall \(C_2\)-correct targets. Also \(\delta\in C_2\).

Suppose \(\exists y\,\psi(a,y)\) holds in \(V\), with \(a\in V_\delta\) and \(\psi\in\Pi_2\). Choose such a target containing a witness and an embedding whose critical point exceeds \(\operatorname{rank}(a)\). Target \(C_2\)-correctness verifies the witness there. Elementarity supplies a witness in the smaller source, with \(a\) fixed. Source \(C_2\)-correctness makes its \(\Pi_2\) matrix true globally. The witness lies below \(\delta\), and \(\delta\in C_2\) verifies the matrix in \(V_\delta\) as well.

This proves downward \(\Sigma_3\) reflection. Upward reflection follows by checking the \(\Pi_2\) matrix of a witness using \(\delta\in C_2\). Thus
\[
\delta\in C_3.
\tag{11}
\]

For \(x\in V_\delta\), reflection of (10) yields a witnessing history and forcing in \(V_\delta\). Since \(\delta\in C_3\), its assertion that this supplied history is valid is also correct in \(V\); the fixed-forcing \(\Pi_2\) assertion is correct by \(C_2\). Therefore
\[
x\in V_\delta\land L(x)
\quad\Longrightarrow\quad
\exists\tau<\delta\quad
1_{P_\tau}\Vdash\check x\notin\mathrm{HOD}.
\tag{12}
\]
It is necessary here to check the reflected **history**, not only the forcing statement about its last entry.

## 5. Bounded stabilization

Fix \(r<\delta\). Let \(L_r=\{x\in V_{r+1}:L(x)\}\). For \(x\in L_r\), define \(\ell(x)<\delta\) to be the least stage as in (12); assign zero on the remaining elements of \(V_{r+1}\). This is a definable function on one bounded ground rank. Strong inaccessibility of \(\delta\) gives
\[
\sup\{\ell(x)+1:x\in L_r\}<\delta.
\tag{13}
\]
Choose a completed stage \(b(r)<\delta\) above this bound. Monotonicity implies that every member of \(L_r\) is absent from \(A_r^\tau\) for all \(b(r)\leq\tau\leq\Omega\).

If \(x\notin L_r\), none of the actual prefix forcings forces its nonmembership. Homogeneity decides the ground statement, so each forces its membership. Hence
\[
\boxed{
\forall r<\delta\ \exists b(r)<\delta\
\forall\tau\in[b(r),\Omega]\quad
A_r^\tau=A_r^\Omega=V_{r+1}\setminus L_r.
}
\tag{14}
\]
There is no assumption of HOD continuity at direct limits. A purported first loss at \(\Omega\) is already a witness to (10), and (12) supplies an earlier one.

The rank-stabilization theorem permits increasing \(b(r)\) so that \(W_{r+1}\) itself has stabilized there. Thus both the underlying successor-rank structure and its predicate for **ambient** HOD stabilize before \(\delta\).

## 6. What this does not establish

Suppose a compatible cutoff-capturing embedding has
\[
k(\bar\Omega)=\Omega,\qquad k(\bar r)=r,
\qquad k(P_{\bar\Omega})=P_\Omega,
\]
and padded \(C_2\)-correct source and target. Correctness of the fixed-set-forcing formula gives
\[
k(A_{\bar r}^{\bar\Omega})=A_r^\Omega.
\tag{15}
\]
By (8), \(A_{\bar r}^\Omega\subseteq A_{\bar r}^{\bar\Omega}\), so this construction gives the forward inclusion
\[
k(A_{\bar r}^\Omega)\subseteq A_r^\Omega.
\tag{16}
\]
It gives equality precisely when
\[
A_{\bar r}^{\bar\Omega}=A_{\bar r}^\Omega.
\tag{17}
\]
Statement (14) alone does not select a capture with (17), since \(\bar r\) and \(\bar\Omega\) are outputs of the same embedding. Nor does (14) identify ambient HOD with the HOD internally computed by \(W_\delta\).

Finally, \(\delta\in C_3\) does not make a smaller Definition-223 source endpoint \(C_3\). Preservation of the required source \(C_2\) correctness under the iteration remains a separate obligation.

There is a useful refinement at the critical point: the reflection note proves that \(e=\operatorname{crit}(k)\) is itself ground \(C_3\), and gives \(W_e\prec_{\Sigma_2}W_\Omega\) when the actual iteration data are captured. The stabilization argument also applies below \(e\). The source rank in (17) is larger than \(e\), so this does not establish (17).
