# The nonzero convention for rank-Berkeley cardinals

This mathematical note is retained from proof development. Historical implementation labels are superseded by the [current repair summary](../README.md). The summary identifies the exact formalized scope.

10 September 2026. V13 now says "a nonzero cardinal" in its
rank-Berkeley definition.
The descent proof now explicitly takes \(\zeta=0<\delta\).

Write \(R(\delta)\) for the earlier literal definition. Its outer
bounded universal quantifier is \(\forall\zeta<\delta\).
Since zero is a cardinal and has no elements, ZF proves \(R(0)\).
Consequently ZF proves \(\exists\delta\,R(\delta)\), and the sentence
"there are no rank-Berkeley cardinals" under that literal convention
would contradict ZF. It cannot be the sentence used in the pruning
conclusion.

The corrected definition is
\[
R^+(\delta)\quad\Longleftrightarrow\quad
  \delta\ne0\ \land R(\delta).
\]
For every cardinal \(\delta\), elementary case distinction gives
\[
R(\delta)\quad\Longleftrightarrow\quad
  \delta=0\ \lor R^+(\delta).
\]
Thus the change removes exactly the vacuous zero case. From
\(R^+(\delta)\), choosing \(\zeta=0<\delta\) supplies the nontrivial
embedding with critical point below \(\delta\) needed at the start of
the descent proof. Removing zero also leaves every unboundedness
assertion about these cardinals unchanged.

The existing Lean file [RankBerkeley.lean](../../../../ZFVP/SetTheory/RankBerkeley.lean)
already proves `rankBerkeleyClause_zero`,
`zf_proves_literalRankBerkeleyExistence`, and
`rankBerkeleyClause_iff_zero_or_nonzero`.
Its `IsNonzeroRankBerkeley` is the corrected predicate.
The theorem `consistent_pruned_UE` in
[PrunedUnboundedExtendibility.lean](../../../../ZFVP/ModelTheory/PrunedUnboundedExtendibility.lean)
uses the negation of `nonzeroRankBerkeleyExistenceSentence`.
The manuscript now agrees with that statement; no Lean definition or
proof was changed in this correction.

[Mohammd, Definition 4.4](https://arxiv.org/html/2404.10455#S4)
gives the same embedding clause without explicitly spelling out this
boundary convention. V13 makes the nonzero convention explicit because
of the vacuity calculation above.
