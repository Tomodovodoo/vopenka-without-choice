# Remaining differences from V13

These are differences between exact manuscript clauses and available Lean exports. They are not consequences of stale completion labels. The main results have checked routes that do not require the unused stronger versions.

## W02: sharp Σ₃ for the specified sparse presentation

V13 Theorem 5.5, `thm:Woodin-forcing`, fixes a normalized sparse presentation. [WoodinEndpointInternalPresentation](../../ZFVP/ModelTheory/WoodinEndpointInternalPresentation.lean) proves `woodinEndpointStagePresentation_sigmaThree_uniform` for the stage-tagged raw presentation, `woodinStageCarrier` with `woodinLocalOrderOn`. [UniformWoodinSparseCompleteCode](../../ZFVP/ModelTheory/UniformWoodinSparseCompleteCode.lean) supplies a finite complexity bound for the sparse dictionary, not the asserted bound 3.

Forcing equivalence does not transfer definability complexity. Close the difference by proving a Σ₃ formula and readout for the exact sparse carrier and order. Alternatively, revise Theorem 5.5 to an effective finite bound and verify every later use against that replacement. The latter belongs in our paper and appears sufficient for the finite-restoration route; it is a proposed edit, not an edit already made to V13.

## W05: the full endpoint and generic quantifiers

V13 Lemma 5.7, `lem:Woodin-endpoint-forcing`, ranges over every marked inaccessible endpoint computing the prefixes and every generic over `(Vγ, Def(Vγ))`. [WoodinSparseCodedForcingEquality](../../ZFVP/ModelTheory/WoodinSparseCodedForcingEquality.lean) proves the coded readout with a Woodin-supercompact endpoint. [WoodinSparseEndpointTruth](../../ZFVP/ModelTheory/WoodinSparseEndpointTruth.lean) proves marked-stage truth for the prefix induced by an ambient V-generic. The implication from an ambient generic to a rank-class generic does not prove the converse.

Close the difference by specializing the class-forcing machinery to the full stated endpoint and generic range. Alternatively, narrow the lemma to the endpoints and ambient-induced generics actually used in the proof. This is an edit to our paper; there is no established counterexample here and no source-author repair request follows from the mismatch alone.

## Claims outside the current paper route

Prescribed-ground downward satisfiability, general standalone second incompleteness, and universal class Boolean completion remain optional extensions. The paper uses the proved transfer through a fresh coding ground, the Gödel-sentence pruning argument, and class-forcing truth through tower projections. They do not require those stronger replacements.

Woodin's full ambient-HOD clause is a separate unresolved source argument, described in [the source note](../sources/woodin-spoerl/README.md#ambient-hod-remains-separate). The paper's explicitly open questions remain open questions.
