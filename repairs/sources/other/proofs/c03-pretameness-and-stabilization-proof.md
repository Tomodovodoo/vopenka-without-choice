# C03: pretameness and subset stabilization in ZF

This mathematical note is retained from proof development. Historical implementation labels are superseded by the [current repair summary](../README.md). The summary identifies the exact formalized scope.

This note supplies the mathematical argument needed between the local Usuba collapse and the class extension. The hypothesis is a proper class of LS cardinals. VP is sufficient for that hypothesis, but is not used below. Section 7 records the checked implementation and the remaining independent correspondence review.

The forcing is the full inverse-limit tower used by `usubaForcingTower`. At a stage whose extension satisfies AC the next forcing is trivial. Otherwise let \(\kappa\) be the least ordinal at which dependent choice fails, and force with

\[
  \operatorname{Col}(\kappa,V_\lambda)
  =\{p:p\text{ is a partial function }\kappa\to V_\lambda,
            |p|<\kappa\},
\]

ordered by extension. Choose the least suitable singular LS target \(\lambda>\kappa\), satisfying \(\kappa<\operatorname{cf}(\lambda)\) and admitting a weakly LS \(\nu\) with \(\kappa\leq\nu\leq\operatorname{cf}(\lambda)\). These are the weak inequalities in the actual `IsUsubaTarget` predicate; the strict inequalities used below establish existence of a target but do not define its least value. Use the guarded, saturated name presentation already fixed for this tower. All limits in this note are full inverse limits. There is no direct-limit support restriction to check.

The local collapse inputs are Usuba's Proposition 3.6 for the initial \(\kappa=\omega\) case and Proposition 4.7 for uncountable \(\kappa\). They give the required DC gain; the latter preserves all earlier instances. These are set-forcing theorems over ZF. [Usuba, *A note on Löwenheim-Skolem cardinals*, Sections 3-4](https://arxiv.org/pdf/2004.01515).

We use the ordinary ZF set-forcing theorem, ordinal preservation, bounded name evaluation, and the factorization of a full-support iteration after an initial generic. They concern set stages only. No axiom of the final class extension is used to prove the assertions below.

## 1. The LS preservation input

The exact cited result is **Lemma 12** of Usuba's *Choiceless Löwenheim-Skolem property and uniform definability of grounds*: if \(\chi\) is a cardinal limit of LS cardinals and \(P\in V_\chi\), then \(\chi\) remains LS after forcing with \(P\). Its proof is on printed pages 13-14. [Primary source](https://arxiv.org/pdf/1904.00895#page=13).

Consequently, every set stage preserves the existence of a proper class of LS cardinals: above the rank of its poset there are arbitrarily large cardinal limits of ground LS cardinals, and the lemma applies to each of them. This is the general LS-only input. It does not assert preservation of every individual LS cardinal.

Suitable singular targets then exist in each set-stage extension. Choose a singular LS cardinal \(\nu>\kappa\); its successor is regular. A continuous increasing sequence of LS cardinals of length \(\nu^+\), starting above \(\nu^+\), has an LS supremum \(\lambda\) with cofinality \(\nu^+\). Thus \(\lambda\) is singular and satisfies the displayed target requirements. Least suitable targets are definable, so this selection does not require a choice function on a class.

When a ground predicate is needed inside a set-stage extension, it is available with a set parameter: under this same proper-class hypothesis the grounds are uniformly definable, by Corollaries 4-6 of the earlier Usuba paper. This is a convenience for applying ordinary first-order Reflection to the quotient dense classes. It is an explicit named input, not an implicit use of a truth predicate for the ground.

## 2. Coherent bounds through a full inverse limit

Fix a stage \(a\), work in its set-forcing extension \(M_a\), and suppose \(M_a\models\mathrm{DC}_\theta\), where \(\theta\) is infinite and regular. Factor the tower after \(a\). We prove simultaneously, by induction on the endpoint \(b\geq a\), that:

1. the separative order on the tail quotient to \(b\) is closed under descending sequences of every length \(\mu\leq\theta\);
2. that tail preserves \(\mathrm{DC}_\theta\).

The raw order on full conditions whose heads belong to the initial generic need not be closed: those heads need not have a common lower bound. We prove closure for its separative order directly. The ordinary set-stage quotient theorem then identifies forcing with this order with the extension from stage \(a\) to stage \(b\). Closure supplies distributivity after applying DC; distributivity alone is not being identified with closure.

Here is the bound construction in ground names. For a given separatively descending sequence in \(M_a\), choose a name \(\dot f\) and a head \(r\in G_a\) forcing that it is such a sequence of length \(\mu\) in \(P_b/G_a\). The ordinal length and the required base DC statement can be included in this condition. Set \(q_a=r\), and before \(a\) use the projections of \(r\). Construct one ground history of prefixes \(q_j\), for \(a\leq j\leq b\).

Suppose the prefix \(q_j\) is a condition and its quotient is separatively below all selected prefixes of \(\dot f\). In a \(P_j\)-generic through \(q_j\), those selected prefixes belong to the generic. The transported two-step comparison lemma makes their coordinate values descend in the separative order of the next collapse. Any two values therefore have a common extending partial function, so they agree on overlapping domains. This compatibility is sufficient for the union calculation. Write these values as \(p_\xi(j)\). If the iterand is trivial, use its top. Otherwise its least DC failure \(\kappa_j\) is strictly above \(\theta\): preservation of \(\mathrm{DC}_\theta\) up to \(j\) is the earlier endpoint induction hypothesis. Use the coordinate value

\[
             v_j=\bigcup_{\xi<\mu}p_\xi(j)
\]

inside that coordinate extension. The functions agree on overlaps. Each domain is a subset of the regular ordinal \(\kappa_j\) of size below \(\kappa_j\), hence is bounded there. Replacement forms their sequence of bounds, and regularity bounds its supremum because \(\mu\leq\theta<\kappa_j\). The union therefore has domain of size below \(\kappa_j\) and is an actual collapse condition extending every coordinate value. Its graph is well-orderable by its ordinal domain. No enumeration of the collapse range and no choice of coordinate lower bounds is made.

Translate \(\dot f\) to a \(P_j\)-name and apply the specified selected-union operation. Its value is \(v_j\). Apply the tower's guarded local normalization to this specified name. The successor prefix \(q_{j+1}\) is \(q_j\) followed by that coordinate name. The local lemmas give membership in the allowed name carrier and equality with the raw union below \(q_j\); they do not select an arbitrary equivalent representative. These are the statements represented by `transported_usuba_selected_union_member` and `transported_usuba_local_union_normalization`.

Here are the actual carrier and normalization, with their required membership proof. Fix a set forcing \((P,R)\) and its specified restoration-poset name \(Q\). Write \(\dot\bigcup Q\) for the ordinary union name, and set

\[
 A=\operatorname{dom}(\dot\bigcup Q),\qquad
 U=\mathcal P(A\times P).
\]

For any set \(D\) of possible member names define, using Separation,

\[
 \operatorname{Sat}_D(\sigma)=
 \{\langle\tau,t\rangle\in D\times P:
   \tau\text{ is a }P\text{-name and }t\Vdash\tau\in\sigma\}.
\]

The actual iterand name is \(Q^{\rm sat}=\operatorname{Sat}_U(Q)\). Its permitted coordinate-name set is

\[
 \operatorname{dom}(Q^{\rm sat})\cup\{\varnothing\},
\]

and a successor condition is a pair \(\langle q,n\rangle\) with \(q\in P\), \(n\) in this permitted set, and \(q\Vdash n\in Q^{\rm sat}\). These are the definitions of `usubaSaturatedPosetName`, `twoStepNames`, and `twoStepConditions`, rather than a new name presentation.

For \(p\in P\), let \(\operatorname{Res}_p(\tau)\) be the name whose pairs are

\[
 \langle\rho,t\rangle,
 \quad t\leq p,
 \quad \exists s\in P\ (\langle\rho,s\rangle\in\tau\ \land\ t\leq s).
\]

Define the single normalizing operation

\[
              N_p(\sigma)=\operatorname{Res}_p(\operatorname{Sat}_A(\sigma)).
\]

This is `forcingCarrierLocalNormalize P R Q p σ`. It is a name, is a subset of \(A\times P\), and therefore belongs to \(U\). All three sets and the operation are uniformly definable by their displayed bounded-set separations and the ordinary atomic forcing relation. The parameter \(Q\) can name different collapse targets in different generics.

Suppose \(q\leq p\) and \(q\Vdash\sigma\in Q\). Then

\[
                    q\Vdash N_p(\sigma)=\sigma.                 \tag{C03-N}
\]

To verify this at the same \(q\), consider a generic \(H\ni q\). Each element of \(\sigma[H]\) belongs to \((\dot\bigcup Q)[H]\), since \(\sigma[H]\in Q[H]\). The ordinary union-name membership lemma supplies a member name from \(A\) for this element. Atomic truth and a common strengthening of finitely many conditions place a corresponding pair in \(\operatorname{Sat}_A(\sigma)\). Conversely, every interpreted pair of this saturated name has its value in \(\sigma[H]\) by atomic soundness. Restriction below \(p\in H\) preserves that value, again using only finite directedness. Thus the names agree in every generic through the original \(q\). The atomic forcing theorem gives (C03-N) without strengthening \(q\). The existing proof first makes this calculation in countable grounds and then applies a fixed-formula elementary-submodel transfer, so `forcingCarrierLocalNormalize_forces_below` itself has no countability hypothesis.

Atomic substitution now gives \(q\Vdash N_p(\sigma)\in Q\). Together with \(N_p(\sigma)\in U\) and its name property, this places the literal pair \(\langle N_p(\sigma),q\rangle\) in \(Q^{\rm sat}\). Hence \(N_p(\sigma)\) belongs to the actual permitted coordinate-name set, and this very pair also gives \(q\Vdash N_p(\sigma)\in Q^{\rm sat}\). Therefore \(\langle q,N_p(\sigma)\rangle\) is an actual successor condition. This is the proof of `carrierSaturated_twoStep_localNormalize`. Membership in the larger pool \(U\) alone was not used as a substitute for membership in the actual carrier.

At stage \(j\), take \(\sigma\) to be the specified selected-union name and take \(p\) to be the section image of the original head \(r\). The already constructed \(q_j\) lies below that section image. The transported descending-sequence and earlier-endpoint DC/closure hypotheses prove \(q_j\Vdash\sigma\in Q\), by the union calculation above. Applying the preceding paragraph gives both successor membership and equality below \(q_j\). These are precisely `transported_usuba_local_union_pair_mem` and `transported_usuba_local_union_normalization`; their common input is `transported_usuba_selected_union_member`. Their proofs use DC and closure only at the preceding endpoint. No local \(\kappa_j\) or \(\lambda_j\) is decided in the ground. Every coordinate normalizer is the value of this one definable operation, so Replacement can form the ground history.

The definitions and proofs are in [ForcingSaturatedName.lean](../../../../ZFVP/SetTheory/ForcingSaturatedName.lean), [ForcingRestrictedName.lean](../../../../ZFVP/ModelTheory/ForcingRestrictedName.lean), [ForcingCarrierNormalization.lean](../../../../ZFVP/ModelTheory/ForcingCarrierNormalization.lean), and [UsubaTransportedLocalUnion.lean](../../../../ZFVP/ModelTheory/UsubaTransportedLocalUnion.lean). On a trivial generic branch the normalized coordinate is forced equal to the empty top. It is literally empty when the restriction head \(p\) itself forces the selected union empty, by `forcingCarrierLocalNormalize_empty`. Emptiness forced only at a stronger prefix \(q_j\leq p\) does not imply that literal identity.

At a limit \(d\leq b\), put

\[
 q_d=\langle q_j:j<d\rangle.
\]

Replacement makes this a set, including the fixed projections of \(r\) before \(a\). Its projection from \(j\) to \(i<j\) is the prefix already constructed at \(i\), because each successor appended a coordinate to that same history. It belongs to the full inverse limit. Membership alone is not yet the desired separative comparison. The following additional invariant supplies that comparison at successors and at limits of every cofinality.

For a full condition \(u\) and a stronger initial head \(s\leq u\mathbin{\upharpoonright}a\), define \(u[s]\) by replacing that head and retaining the later coordinate names. Recursion proves that this is a condition below \(u\): each retained name remains valid below the stronger prefix, and at a limit Replacement collects exactly those prefixes. This reheading operation is specified by \(u,s\); it does not choose coordinate extensions.

The structural conclusions needed here are

\[
 \begin{gathered}
 u[s]\mathbin{\upharpoonright}a=s,\qquad u[s]\leq u,\qquad
 u[s]\mathbin{\upharpoonright}j=(u\mathbin{\upharpoonright}j)[s]
       \quad(a\leq j),\\
 u[u\mathbin{\upharpoonright}a]=u,\qquad
 u\leq v\ \land\ s\leq u\mathbin{\upharpoonright}a
       \ \Longrightarrow\ u[s]\leq v[s].
 \end{gathered}
\]

At a successor, these are the pair equations with the retained tail name; monotonicity of forcing preserves both its membership and its order comparison. At a full inverse limit, every entry is the already constructed reheaded prefix, so extensionality and the coordinate definition of the inverse-limit order prove the equations and comparison. This uses the same history at all limits. `usubaTowerLift` implements the operation. Its `spec`, `commute`, and `successor_pair` theorems supply the projection, order and retained-coordinate facts used by the common-lift induction.

Alongside membership and coherence, prove the following invariant for the constructed prefixes \(q_j\):

\[
 \begin{gathered}
 h\in P_b,\quad s\leq r,h\mathbin{\upharpoonright}a,\quad
 s\Vdash_{P_a}\check h\in\operatorname{ran}(\dot f)
 \\
 \Longrightarrow\quad q_j[s]\leq h\mathbin{\upharpoonright}j
 \qquad(a\leq j\leq b).
 \end{gathered}
 \tag{C03-H}
\]

At the base this is the hypothesis on \(s\). At a successor, the earlier comparison puts the prefix of \(h\) into every generic under \(q_j[s]\). The initial generic contains \(s\), so the selected union contains the coordinate value of this same \(h\). Local normalization agrees with the union below \(q_j[s]\). Thus the next coordinate extends that of \(h\). At a limit, these are actual order comparisons of one coherent history, so the inverse-limit order gives the comparison at the limit. The single head \(s\) works at every coordinate; no later coordinate asks for a further choice of head.

Now fix an initial generic \(G_a\ni r\), a value \(h=\dot fG_a\), and a quotient condition \(u\leq q_b\). The set-forcing truth lemma and directedness of \(G_a\) give one \(s\in G_a\) below the heads of \(u,h,r\) which forces that \(h\) occurs in \(\dot f\). Then

\[
                    u[s]\leq q_b[s]\leq h,
\]

and \(u[s]\leq u\). This proves \(q_b/G_a\leq_{\rm sep}h/G_a\). To test the separative order it suffices to consider actual extensions \(u\leq q_b\) in the quotient. We have therefore obtained the required bound at the full endpoint. The same ground construction also returns a condition with the prescribed initial head from a named descending record. It removes the need to select unrelated names for the coordinates of an internal tail condition. Collection bounds the names used over the set of coordinates, while the recursion fixes their projections.

Finally, in ZF + \(\mathrm{DC}_\theta\), closure through \(\theta\) gives the usual decision construction of length at most \(\theta\), and preserves \(\mathrm{DC}_\theta\). To preserve DC, construct successively a descending condition and a name for the next value of a serial-history problem; at limit steps take a bound, and at length \(\theta\) take a final bound. The ground DC instance is applied to the set of pairs of conditions and names after Collection bounds the possible names. The final condition forces the entire selected sequence. This proves item 2 after item 1 at each endpoint, so preservation at the current limit is not a premise of its own closure proof.

A set sequence of conditions in the class tail has bounded support length. Choose a set endpoint containing all its conditions and apply the construction there. The class tail consequently has the same closure property. This uses a bound on the support of a **given set sequence**, not a bound on an entire dense class.

## 3. Reaching enough DC and a well-ordering

As long as AC fails, the successor collapse forces DC at the current least failure. Section 2 preserves every earlier gained DC instance at all subsequent set stages, including limit stages. The least failures therefore increase strictly at successor steps and cannot drop at a limit. If the construction has not stopped, their values are unbounded in the ordinals.

For a more local formulation, fix any set endpoint of length greater than an ordinal \(\rho\). Within that set iteration, either an earlier stage has AC, after which the tail is trivial, or ordinal induction makes the current least failure greater than \(\rho\). This observation avoids any appeal to Replacement in the final class extension.

Let \(x\in M_a\). A name for \(x\) gives a ground ordinal bound on its rank. At a sufficiently late nontrivial stage the target \(V_\lambda\) contains \(x\). The collapse supplies a surjection \(\kappa\twoheadrightarrow V_\lambda\), so \(x\) is well-orderable with size at most \(\kappa\). The same collapse supplies \(\mathrm{DC}_\kappa\), with \(\kappa\) regular; subsequent tails are closed through \(\kappa\) by Section 2. If a stage already has AC, use the trivial-tail case instead.

The regularity used in this sentence is preserved by the local collapse. For uncountable \(\kappa\), its no-new-sequences conclusion rules out a new cofinal map into \(\kappa\) of length below \(\kappa\). For \(\kappa=\omega\), regularity holds in ZF. Thus the ordinal at which DC has just been gained is a valid regular parameter for the following tail argument.

In particular this applies to any ground index set \(I\). It is **after this collapse** that we enumerate \(I\); no ground well-ordering of \(I\) is assumed.

## 4. The precise class selection lemma

In ZF + \(\mathrm{DC}_\theta\), for infinite regular \(\theta\), dependent recursion of length \(\theta\) may be used for a definable class relation on partial histories when the empty history is legal, every legal history of length below \(\theta\) has a legal next value, and unions of coherent legal initial histories remain legal. Here legality means satisfaction of the previously imposed step requirements, including all the descending-order and witness-record requirements. It has the required continuity at limits.

To reduce this to the set version of DC, apply Reflection to a finite, subformula-closed list containing the formulas for legal histories, extensions, and their existence, including the parameters. Choose a strictly increasing sequence of reflecting ordinals of length \(\theta\), starting above the parameters and \(\theta\), and take its supremum \(\chi\). Least further reflecting ordinals give this sequence by definable recursion. The reflecting class is closed, and \(\operatorname{cf}(\chi)=\theta\). Consequently every history of length below \(\theta\) with entries in \(V_\chi\) belongs to \(V_\chi\). Reflection makes its next-value relation total there. Separation turns it into a set relation, and \(\mathrm{DC}_\theta\) gives the required sequence. For illegal histories assign a fixed dummy value when putting the relation in the everywhere-total DC form. Legal prefixes remain legal by successor extension and limit continuity. The final history of length \(\theta\) is a set in \(M_a\); it need not belong to \(V_\chi\). The final lower bound uses closure through \(\theta\) in \(M_a\).

This is also why merely saying "choose successive stronger conditions" in the ground would be insufficient. Here the DC instance is the one proved in Section 3, and the relation to which it is applied is a set relation obtained by Reflection.

## 5. Ground-set predense refinements

Let \(\langle D_i:i\in I\rangle\) be a ground-set-indexed definable family of dense subclasses of the class forcing \(P\), and let \(p\in P\). We prove

\[
 \exists q\leq p\ \exists\langle F_i:i\in I\rangle\in M\quad
 F_i\subseteq D_i\quad\text{and}\quad F_i\text{ is predense below }q.
\tag{C03-P}
\]

For \(I=\varnothing\), take \(q=p\) and the empty family. Otherwise choose a sufficiently late successor stage \(a\), with its preceding index above the support of \(p\) and a ground rank bound for \(I\). By Section 3, either the iteration has reached AC, or the preceding least failure is above that rank bound and its collapse gives the desired properties of \(I\) at \(a\). Thus the stage can be fixed before enumerating \(I\). First work in an initial generic extension \(M_a\) through the head of \(p\). In the nontrivial case there is a surjection \(e:\theta\twoheadrightarrow I\), \(\theta\) is infinite regular, \(\mathrm{DC}_\theta\) holds, and the tail is closed through \(\theta\). When returning to names, strengthen the head to decide this one ordinal \(\theta\) and to force these properties.

The image of \(D_i\) is dense in the tail. Here is the verification that does not assume a class generic: for a ground representative \(u\), the heads of extensions \(d\leq u\) with \(d\in D_i\) form a ground **set** of initial conditions, by Separation on the initial poset. This set is dense below the head of \(u\), by amalgamating any stronger head with \(u\) and then using the ground density of \(D_i\). The initial generic meets it. Its witness gives the required tail extension. The ground definition of \(D\), the initial generic, and a parameter defining the ground make these quotient classes definable in \(M_a\).

Apply Section 4 to construct a descending tail sequence \(\langle t_\xi:\xi<\theta\rangle\), recording at step \(\xi\) an original ground witness \(d_\xi\in D_{e(\xi)}\) whose head belongs to the initial generic and whose tail lies above \(t_\xi\). At a limit step use the coherent bound from Section 2 before meeting the next dense class. Take a final tail bound \(t\) at length \(\theta\).

The recorded witnesses, \(t\), and \(p\) form a set of old full conditions. Choose an ordinal \(\rho\) above their ranks. Set forcing preserves ordinals and the ranks of old sets, so the ground set \(B=V_\rho^M\cap P\) contains all of them. This is a rank cover, with no claim about its cardinality and no selection of a value for each condition. When returning to names, strengthen the one initial head so that it forces the whole record and its bound to lie in \(\check B\). Replacement in the ground bounds the supports of every condition in \(B\) by a single set endpoint \(b\). This bounds all possible values allowed by the certificate, rather than only the supports seen in one generic.

Endpoint padding preserves and reflects separative comparison in the quotient. For \(a\leq b\leq c\), pad a \(b\)-condition using the specified section to \(c\). To prove preservation, project an extension below the padded condition back to \(b\), find a common \(b\)-extension using the original separative comparison, then lift it under the given \(c\)-condition. The lift has its initial head in \(G_a\) and is below the other padded condition. For reflection, project a common \(c\)-extension back to \(b\). The projection/section and lift laws prove both directions. The same argument works for any further set endpoint, so the comparisons in the next certificate can be made in the fixed set quotient to \(b\).

Return to the set-forcing relation. Strengthen the initial head to a condition \(r\) and take names for the descending record and its bound \(\dot t\), so that \(r\) forces:

\[
 \begin{split}
 &\dot t\text{ lies below the tail of }p;\\
 &\forall i\in\check I\ \exists d\in\check{(B\cap D_i)}\quad
    d\mathbin{\upharpoonright}a\in\dot G_a
       \ \land\ \dot t\leq_{\rm sep}d/G_a.
 \end{split}
\tag{C03-W}
\]

All classes have now been replaced in this displayed assertion by ground sets. The existence of one such strengthened condition and named record is the ordinary forcing witness lemma. It selects no family of names. Apply Section 2 to the named two-term descending sequence consisting of the ground condition \(p\) followed by the quotient representative \(\dot t\), at an endpoint containing both supports. This returns a ground condition \(q\) with head \(r\). Since \(r\) forces that \(p\) occurs in this record and \(r\leq p\mathbin{\upharpoonright}a\), (C03-H) gives the actual comparison \(q\leq p\). Its quotient is separatively below \(\dot t\).

Define in the ground, using Separation and Replacement,

\[
                         F_i=B\cap D_i\qquad(i\in I).
\]

To check predensity, fix \(u\leq q\) and \(i\in I\). Force with the initial poset below the head of \(u\). By (C03-W), some \(d\in F_i\) has its head in the initial generic and its quotient lies above \(\dot t\) in the separative order. The quotient of \(u\) is therefore compatible with the quotient of \(d\). The factorization compatibility lemma gives a common full extension after possibly strengthening the head. Thus \(u\) and some \(d\in F_i\) are compatible in the ground class forcing. Formally, if no member of the ground set \(F_i\) were compatible with \(u\), its head would force that same incompatibility in the quotient, contradicting (C03-W). This proves (C03-P).

If AC has already appeared, the tail is trivial on a stronger cone. That cone is equivalent to a set forcing. For a set forcing, Collection over \(I\times P_a\) supplies a set of dense witnesses, and intersecting with each \(D_i\) proves the same predensity assertion in ZF.

Thus the actual class tower is pretame for ground-set-indexed definable dense families. The three distinct operations are: a later collapse well-orders the index set; its internal DC instance builds the descending witness record; ground Collection converts that record into one bounded set of possible witnesses. None presupposes ground AC.

### 5A. The bounded witness argument used by the Lean implementation

The implementation proves (C03-P) by a second route that bounds the witness searches in the ground before applying DC. This route has the same conclusion and avoids the ground-definability and Reflection inputs used in Sections 4-5. The following is its actual sequence of constructions.

Work first in an externally countable ground and fix the initial class condition \(c\). A class generic through \(c\) exists by enumerating the definable dense classes. Only its set-stage generics and the already proved eventual-enumeration property are used here; no axiom of its class extension is assumed. `prepare_pretame_enumeration` gives a set stage \(i\), an ordinal \(\alpha\), and, in its extension \(A\), a surjection \(e:\alpha\twoheadrightarrow\check I\), the instance \(\mathrm{DC}_\alpha\), and quotient membership of \(\check c\). The later set quotients are closed through \(\alpha\).

For a ground ordinal \(j\geq i\), let \(B_j\) be the ground set of tagged conditions with stage at most \(j\). Ground Collection on the set of triples

\[
 (a,d,r)\in I\times B_j\times P_i
\]

gives a later ordinal \(k>j\) with the following property: whenever \(r\leq\pi_i(d)\), there is \(w\in B_k\cap D_a\) below both \(d\) and the tagged base condition \((i,r)\). The witness exists because one first lifts \(r\) below \(d\) and then meets \(D_a\). Collection supplies a set containing a witness for every applicable triple; its rank bounds their tagged stages. No witness function is chosen. Including **every** stronger base head \(r\) is essential: the projections of the bounded witnesses form a ground set dense below \(\pi_i(d)\), so each base generic containing that projection meets this set.

Choose the least such ordinal bound by a definable operation and iterate it internally, with unions at limits. This gives an increasing ground schedule \(F\) of length \(\alpha+1\), with \(F(0)=i\), and the displayed witness property from \(B_{F(\beta)}\) into \(B_{F(\beta+1)}\). Set \(K=F(\alpha)\). These are `denseClasses_projectedWitnessBound`, `witnessStageStep`, and `witnessStageSchedule`. Their transfinite inductions are inductions on definable predicates inside the ground model.

Inside \(A\), use the sets

\[
 X_\beta=\{\check d:d\in B_{F(\beta)},\ \pi_i(d)\in G_i\},
 \qquad
 E_\beta=\check{(B_K\cap D_{e(\beta)})},
\]

where the notation for \(E_\beta\) means evaluation of the checked ground family \(a\mapsto B_K\cap D_a\) at \(e(\beta)\). It does not apply a ground class predicate to new extension elements. All orders are restrictions of the separative order on the single set quotient \(X_\alpha\). Padding and reduction preserve and reflect that order. Consequently the earlier quotient-closure theorem gives closure at length \(\beta\) inside \(X_\beta\), with comparisons in this ambient order. The projected witness property gives, below every member of \(X_\beta\), a member of \(X_{\beta+1}\cap E_\beta\).

`stagedForcingDependentChoice` now applies to these set tables. At a history of length \(\beta\), each earlier selected value lies in some \(X_{\xi+1}\subseteq X_\beta\). Closure in \(X_\beta\) supplies a bound for that history and the initial condition before the next witness is taken in \(X_{\beta+1}\). Its conclusion is a sequence \(f\) meeting every \(E_\beta\) and one \(q\in X_\alpha\) separatively below both \(\check c\) and all entries of \(f\). This is `quotient_stagedChoices`; the entire DC application occurs in the ZF set-stage model \(A\).

The next step obtains an actual stronger ground condition. Since \(q\leq_{\rm sep}\check c\), they have a common extension in the raw quotient order. Every element of this quotient is a checked old tagged condition, so this common extension has a ground representative \(b\leq c\). Reduce \(b\) to stage \(K\), obtaining \(p\in P_K\) whose head belongs to \(G_i\). It remains separatively below the selected witnesses, and its tagged condition is literally below \(c\). Thus in \(A\), for every \(a\in\check I\), some member of the checked ground set \(B_K\cap D_a\) lies separatively above \(\check p\). This is `boundedQuotient_cover_from_enumerated_bounds`.

That cover assertion is one fixed first-order formula. Its parameters are the quotient carrier and order names and the check names for \(I\), the entire ground witness family, the reduction map, and \(p\). The set-forcing truth lemma gives one head \(u\in G_i\) that forces it. It therefore holds in every base generic through \(u\), with these same ground parameters. Strengthen the head of \(p\) together with \(u\) inside \(G_i\), and use the specified tower lift to obtain a ground \(r\leq p\) with that head. For any class condition below \((K,r)\), pass to a larger set endpoint containing it. The forced cover and the quotient compatibility/lift lemmas give compatibility with a member of each ground set \(B_K\cap D_a\). Hence this family is predense below \((K,r)\leq c\). These are `boundedDenseFamily_uniform_cover`, `boundedDenseFamily_refinement_of_cover`, and finally `isPretame_of_enumerations_and_closure`.

The bounded tables, the fixed forcing formula, and the final raw lift account for all selections in this implementation. In particular, the source does not rely on the Reflection reduction or on the two-term named-bound extraction described in Section 5. The unrestricted ground-theory conclusion is subsequently obtained by the fixed-formula transfer recorded in Section 7.

## 6. Eventual stabilization of all subsets of a fixed set

Fix \(x\in M_a\), and choose a later stage \(b\) as in Section 3. In \(M_b\), fix a well-ordering of \(x\) of length at most \(\theta\), where \(\mathrm{DC}_\theta\) holds and all later tails are closed through \(\theta\).

For every set endpoint \(c\geq b\), a name for a subset of \(x\) can be decided by a descending sequence of length at most \(\theta\): successively decide membership of the elements in the chosen enumeration and use closure for the final bound. DC is applied in \(M_b\), not in the class extension. The deciding sequence and its final bound belong to the set tail to \(c\). Therefore

\[
              \mathcal P(x)^{M_c}=\mathcal P(x)^{M_b}
                   \qquad(c\geq b).
\tag{C03-S}
\]

Every class-forcing set name has set-sized transitive closure; Replacement bounds the stages of all conditions in it. Hence its evaluation already belongs to some set-stage extension. Applying (C03-S) to that stage proves that \(\mathcal P(x)^{M_b}\) is the full powerset of \(x\) in the class extension. The stage \(b\) depends on \(x\), but works for **all** later subset names of \(x\); it is not a bound chosen separately for each subset.

## 7. Extension axioms and the checked implementation

Here are the extension-axiom arguments, including the order in which the forcing theorem and ZF schemes are obtained. They do not assume that the final quotient is already a ZF model.

Every set name has bounded hereditary stage support. At a stage containing two names and a condition, use ordinary set-forcing equality and membership. Completeness of the stage embeddings makes these atomic relations independent of a larger stage. The atomic forcing classes are regular: a failure to force an atomic assertion can be witnessed by a stronger condition forcing its negation at a common bounded stage, and later complete embeddings preserve that negation. The class model is the quotient of internal names; its bounded pieces are the set-stage models, with membership-preserving end-extension maps.

For each fixed standard formula, define forcing recursively by the regular forcing clauses. An existential is forced when conditions forcing a named witness are dense below the given condition. A universal is forced when every name instance is forced. Negation says that no stronger condition forces its argument. Regularity follows by induction. For the universal truth step, the union of the class forcing the universal and the class forcing a counterexample name is dense: if the universal is not forced, some name instance is not forced, and regularity supplies a stronger condition forcing its negation. A generic at which the universal is true must meet the first class. The existential step uses the dense witness class. This proves the forcing theorem before the extension axioms. In an externally countable arbitrary ground, generics through any condition exist by enumerating its definable dense classes; no external evaluation along a well-founded membership relation is required.

For Separation, let \(\sigma\) name a set and fix a formula \(\varphi(x,\nu)\). For each root pair \((\tau,r)\in\sigma\), use the ground-definable dense class

\[
 D_{\tau,r}=\{s:s\perp r\}\cup
 \{s:s\leq r\text{ and }s\text{ decides }\varphi(\tau,\nu)\}.
\]

Pretameness supplies a family of ground sets \(F_{\tau,r}\subseteq D_{\tau,r}\), all predense below one condition \(q\). Such conditions \(q\) are dense, so choose one in the generic. The pairs \((\tau,s)\) with \((\tau,r)\in\sigma\), \(s\in F_{\tau,r}\), \(s\leq r\), and \(s\Vdash\varphi(\tau,\nu)\) form a ground set name \(\zeta\). Soundness proves one inclusion in the required separated subset. For the other, take a root representation with \(r\) in the generic. Predensity below \(q\) ensures the generic meets the downward closure of \(F_{\tau,r}\), and hence contains a member of that set. That member cannot be incompatible with \(r\), and its decision must be positive by truth. Thus \(\zeta\) names exactly the separated subset.

For Collection, let \(p\) in the generic force that every member of \(\sigma\) has a witness to \(\psi(x,y,\nu)\). For each root pair \((\tau,r)\in\sigma\), the conditions below \(p\) that either are incompatible with \(r\), or strengthen \(r\) and force \(\psi(\tau,\eta,\nu)\) for some name \(\eta\), are dense in that cone. Pretameness also holds in a cone: adjoin the conditions incompatible with \(p\) to each dense class, apply global pretameness below \(p\), and discard the members incompatible with \(p\). The remaining sets are still predense below the resulting \(q\leq p\), because a common extension below \(q\) cannot witness compatibility with a discarded member. They consist of conditions below \(p\).

Choose such a \(q\) in the generic and the associated family \(F_{\tau,r}\). Ground Collection applied to the set of triples \((\tau,r,s)\) with \(s\in F_{\tau,r}\) compatible with \(r\) gives a set \(A\) of names containing at least one witness name for every triple. This collects witnesses without choosing one per triple. Form a set name from all \((\eta,s)\) with \(\eta\in A\), \(s\in F_{\tau,r}\), \(s\leq r\), and \(s\Vdash\psi(\tau,\eta,\nu)\) for some root pair. Predensity and soundness show that its value contains a witness for each member of \(\sigma\). Collection and Separation imply Replacement.

The source constructs Separation and functional Replacement directly. `ClassForcingSeparation` indexes by the ground set `domain σ` and uses dense classes deciding the relevant membership and formula conjunction. `ClassForcingImages` collects a ground set containing witnesses for all required condition/name pairs, retaining every valid witness instead of choosing one per pair. `ClassForcingReplacement` then uses functional uniqueness to identify the image. The forcing theorem used in these constructions is already available before the final structure is shown to satisfy ZF. Thus the source implements the same preservation conclusion through functional Replacement, while the preceding argument also explains the stronger Collection formulation.

Empty Set, Pairing, Union, Infinity, Extensionality and Foundation follow from the set-stage models and their end-extension maps. In particular, a Foundation witness stays a witness because old sets gain no members. Section 6 supplies Powerset. Every set in the extension has a well-ordering at a later set stage by Section 3, and that well-ordering persists. Hence Choice holds. The extension satisfies ZFC, establishing the general LS route for Corollary 4.5 of V13.

The following implementations have now been connected to the actual tower.

The last row closes the distinction between a countable-model realization and a ground-theory derivability statement. [UsubaIterationUniform.lean](../../../../ZFVP/ModelTheory/UsubaIterationUniform.lean) defines the actual initial, successor, inverse-limit and transfinite-recursion stages by fixed formulas. [ClassForcingFormulaCompiler.lean](../../../../ZFVP/ModelTheory/ClassForcingFormulaCompiler.lean) and [ClassForcingTowerDictionary.lean](../../../../ZFVP/ModelTheory/ClassForcingTowerDictionary.lean) prove that the resulting forcing formula agrees with `towerFormula` in every ZF model. No formula is chosen afresh inside an individual model. The project theorem `eval_of_countable_zf` transfers the fixed LS-to-forcing implication from countable elementary submodels, and first-order completeness gives its ZF derivability.

The four uniformity modules and the imported project root built on 2026-09-10. The compiler correctness theorem, tower dictionary, unrestricted LS and VP forcing theorems, and ZF derivability theorem each have exactly `propext`, `Classical.choice`, and `Quot.sound` in their exported axiom dependencies. These are metatheoretic logical axioms; the ground structure is assumed only to satisfy ZF and the stated LS hypothesis.

The primary source audit exposed a remaining export restriction in the singular weak-LS clause. `SingularWeaklyLSForcing.lean` now removes external countability from the forcing and generic-extension conclusions and proves one fixed forcing sentence in ZF. Its leaf build, five exported-result axiom checks and the project root build with 4375 jobs pass. Independent GPT-6 Pro review of the complete wrapper and countable-elementary transfer proof returned PASS and was read in full. The reviewer corrected one prose splice in the chat transmission; the corrected declaration matches the compiled local source exactly after whitespace normalization. All 28 declarations from the new module are registered in the checked dependency map. The stated C03 contract is complete; the full paper still has separate open obligations.
