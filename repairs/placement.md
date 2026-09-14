# Which paper should contain each repair?

The earlier index mixed the location of a defect with the location where we implemented its replacement. The main correction belongs where the defective definition or inference occurs. A downstream paper normally needs only an accurate citation and a check that the repaired result still supplies its input.

A valid application of a cited theorem is not an application error merely because a gap is later found in that theorem's proof. Once the gap is known, however, the dependent conclusion needs a repaired proof or another sufficient input. If the repair weakens the theorem, checking that implication is substantive work. Provenance alone does not establish that every line of either paper is correct.

The entries below distinguish demonstrated defects, missing justifications, and differences between our formalization and the manuscript. They are proposed placement decisions, not author-approved errata. Source numbering is specific to the versions linked in the source notes. The Lean links establish their stated formal propositions; they do not certify every broader claim in the cited publication.

## Woodin and Spoerl

### W1. Initial collapse

**Primary location:** Woodin, *Suitable extender models I*, proof of Theorem 226, p. 323.

The cutoff is selected using a collapse whose lower parameter is the least DC-failure ordinal, but the displayed initial forcing uses lower parameter omega. The stated selection criterion therefore does not itself verify the displayed seed's induction premise. Correct the convention or supply the missing implication in Woodin's construction. This is a mismatch requiring justification, not a counterexample to Theorem 226.

Our Theorem 5.5 should identify the convention it imports. It need not carry the entire source repair. The trivial-stage seed used in our development supplies a consistent alternative; adopting that presentation is separate from diagnosing the original notation.

[Source account and repair](sources/woodin-spoerl/README.md#iteration-seed) · [Lean construction](../ZFVP/ModelTheory/WoodinConstruction.lean).

### W2. Raw inverse stage, completed stage, and DC bound

**Primary location:** a comparative supplement to Woodin's Theorem 226, pp. 323–324, and Spoerl's Definition 43/Theorem 44, pp. 24–25.

Woodin appends a collapse after the raw inverse stage. Spoerl's displayed convention retains the raw stage with a successor cutoff. A premise about one object cannot be applied to the other just because both are denoted by a stage of Woodin forcing. The explanation belongs with those constructions: identify the raw forcing, compute its successor cutoff in its extension, establish the required DC, then identify any appended collapse.

Different conventions are not themselves errors in either paper. The comparison note must say which missing justification or mixed convention it repairs. Our paper should choose and cite one convention; it should not label a change of presentation as a correction to its main theorem.

[Detailed comparison and DC proof](sources/woodin-spoerl/proofs/woodin_inverse_limit_dependent_choice.md) · [Lean](../ZFVP/ModelTheory/WoodinRawInverseDC.lean).

### W3. Lifting to the final successor ranks

**Primary location:** Spoerl, Lemma 45, pp. 26–27. Woodin's Theorem 226(2), pp. 323, 325, is related but has different quantifiers.

A lift between prefix extensions, together with agreement at the final ranks below gamma, does not identify their power sets at rank gamma plus one. Later forcing can add subsets there. Thus Spoerl's assertion about lifting the specified embedding to both final successor ranks needs an additional argument. Replacing that assertion in our paper cannot repair the lemma for its other users.

Our proved replacement lifts to the marked final ranks and captures the complete forcing code. It is sufficient for finite restoration. Our Theorem 5.5 should cite and state this replacement accurately. It must not present it as a proof of the full source lemma. A taller embedding may repair an existential conclusion without proving the original same-embedding assertion. The remaining stronger assertion belongs in a source-author inquiry.

[Precise replacement](sources/woodin-spoerl/proofs/w04-restricted-lift-bridge.md) · [Lean lift](../ZFVP/ModelTheory/WoodinSparseActualCriticalLift.lean).

### W4. Ambient HOD and correctness transfer

**Primary location:** Woodin, proof of Theorem 226(3), p. 326.

The missing work concerns correctness after forcing and the identification of ambient HOD with the HOD computed at the selected ranks. A definability bound alone does not give that transfer; bounded stabilization alone does not ensure the chosen source rank is beyond the bound. These are obligations in the proof of the source clause, irrespective of our application.

Our records do not close the full clause and do not refute its statement. It belongs in a source-proof inquiry. Our current argument uses finite restoration instead, so it needs no weakened HOD conclusion added to the manuscript. The alternative proof should simply avoid claiming this clause as an established input.

[Unresolved obligations](sources/woodin-spoerl/proofs/woodin_ambient_hod_stabilization.md) · [Lean alternative, not the HOD clause](../ZFVP/ModelTheory/WoodinSparseRestorationTheorem.lean).

## Enayat

The primary repair document should be a supplement or proposed erratum to [*Models of Set Theory: Extensions and Dead-ends*, v7](https://arxiv.org/abs/2406.14790v7). These issues occur in that paper's definitions and Appendix, before our Proposition 9.7 is applied. The chain is Appendix construction → weakly Rubin existence → Theorem 5.18 → our end-extension application.

Our checked replacement supplies the ZF-model existence input used downstream. It should not be advertised as certification of every arbitrary-language formulation of Theorem 5.15. Naming Rubin, Shelah, or Schmerl in the construction does not establish that the same defect occurs in their original papers.

### E1. Coding a proper class by a member

**Primary location:** Definition 5.13(b), hence the literal Rubin-model assertion in Theorem 5.15.

Apply clause a to the ordinal order. Its whole domain is a maximal filter with the required cofinal chain, so literal member-coding in clause b yields a set of all ordinals. This contradicts ZF. The definition itself must change in the source paper; no change to our application can make that definition satisfiable.

Use parametric definability for class filters. On the internal set of finite partial functions, Separation recovers member-coding. This restores the input relevant to the later weakly Rubin construction. Our Proposition 9.7 needs the repaired existence theorem, not the inconsistent class-coding assertion.

[Argument](sources/enayat/proofs/enayat-internal-rubin-proof.md) · [Lean refutation and corrected predicates](../ZFVP/ModelTheory/RubinDefinableFilters.lean).

### E2. Maximal directed filter versus maximal compatibility

**Primary location:** Definition 5.10(c), footnote 30, and Appendix Stage 1's separating argument, p. 25.

The separation step needs a point outside the filter to be incompatible with some member. Inclusion-maximal directedness does not ensure this on an arbitrary poset. Correct the general assertion or restrict it to posets where the equivalence is proved. That is a repair to the source's definition-to-proof transition.

For internal finite partial functions the equivalence is proved, so the needed downstream application survives. Our paper should cite that version; it does not need to replace its end-extension conclusion.

[Lean definitions and special-case equivalence](../ZFVP/ModelTheory/MaximallyCompatibleFilters.lean).

### E3. The order of the bound and witness quantifiers

**Primary location:** Appendix Lemmas A.3 and A.4, p. 26.

Simultaneous realization above all prescribed bounds differs from a game in which a later bound is chosen after an earlier witness. For instance, with the requirement that the second witness be below the first, choosing both witnesses after both bounds can work, whereas a later bound above the first witness defeats the alternating form. This changes the asserted consistency equivalence in the source itself.

Use a block of universal bounds followed by a block of existential witnesses for consistency, and the dual blocks for consequence. Our Proposition 9.7 does not use these quantifiers directly; their correction belongs in the repaired construction it cites.

[Lean obstruction](../ZFVP/ModelTheory/AlternatingBlocks.lean) · [Correct block lemmas](../ZFVP/ModelTheory/RubinBlockLemmas.lean).

### E4. The separating-type argument

**Primary location:** Appendix Lemma A.5, pp. 26–27.

Bounds depending on a candidate tuple cannot contradict an assertion that may choose a different tuple later. Also, the two implications with antecedent theta only imply a contradiction under theta; the displayed final contradiction drops that antecedent. Correcting A.3–A.4 alone does not justify this step.

Repair the omitted-type argument over the full upper-bound theory, with a common witness tuple and theta retained. This is part of the source proof of its existence theorem. Our paper needs that theorem as input, not a repetition of its type-omission proof.

[Detailed argument](sources/enayat/proofs/enayat-internal-rubin-proof.md) · [Lean construction](../ZFVP/ModelTheory/SchmerlInternalRubinConstruction.lean).

### E5. Preservation of old branches

**Primary location:** Appendix Lemma A.7, p. 28.

Possible nodes forced by different extensions of one condition need not belong to one branch. The argument needs a condition below which the possibilities cannot split. Supply that in the source lemma, since the subsequent construction depends on preservation of the old branches.

The replacement uses ccc of the specific forcing's square to bound splitting pairs and obtains stabilization densely. The square-ccc hypothesis is proved for the specialization forcing used here. No general product-of-ccc assertion is needed. This is a proof repair, not a counterexample to the source lemma's conclusion.

[Repair](sources/enayat/proofs/e10-e12-schmerl-route-repair.md) · [Lean preservation](../ZFVP/ModelTheory/SchmerlBranchPreservation.lean) · [Product hypothesis](../ZFVP/ModelTheory/SchmerlSpecializationProducts.lean).

### E6. Returning to the membership language

**Primary location:** Appendix Stage 2, Step 2 and its extraction, p. 29.

A formula using a newly added coloring predicate does not by itself define the same class after that predicate is removed. Lemma A.6's statement about the expanded language need not be changed. The missing justification is the later passage to the membership reduct.

Retain original-language definitions and codes for the full generated filters before taking that reduct. The source construction should supply this transfer. Our application of the resulting membership-model theorem then needs only the corrected reference.

[Repair](sources/enayat/proofs/e10-e12-schmerl-route-repair.md) · [Lean realization](../ZFVP/ModelTheory/SchmerlCodedWeaklyRubinRealization.lean).

### E7. Coverage of internally finite domains

**Primary location:** Appendix Stage 2, Step 1, p. 27, and extraction on p. 29.

An internally finite domain may have infinitely many external members. Covering selected domains or individual members does not automatically place the entire internal domain below one branch node. The source's passage from its chosen trees to every relevant maximal filter needs this coverage argument.

Our replacement constructs FinSmall and the required Q-smallness internally to the model-existence proof. These are properties supplied by the construction, not new hypotheses to impose on our Proposition 9.7. The source supplement should explain the strengthened construction. This does not assert that FinSmall is the only possible repair.

[Coverage repair](sources/enayat/proofs/e05-finite-domain-coverage-repair.md) · [Lean existence theorem](../ZFVP/ModelTheory/SchmerlNamedConsistency.lean).

## Other source issues

### M1. The zero rank-Berkeley case

**Primary location:** Mohammd, [*Berkeley Cardinals and Vopěnka's Principle*, Definition 4.4](https://arxiv.org/html/2404.10455#S4), and any downstream definition that repeats its literal boundary convention.

The clause is universally quantified over ordinals below delta, so it holds vacuously at zero. Under that literal convention, existence is automatic and a no-rank-Berkeley assertion is impossible. A nonzero convention belongs at the source definition. This is a boundary correction, not a refutation of the intended positive-cardinal results.

Our paper also spells out the definition and uses its negation in pruning, so it must state the same convention. This is a justified change in both places. The reason is the shared predicate, not ownership of the later pruning proof.

[Exact calculation](sources/other/proofs/rank_berkeley_nonzero_correction.md) · [Lean](../ZFVP/SetTheory/RankBerkeley.lean).

### K1. Comparison generics must generate the same extension

**Primary location:** Karagila–Schilhan, [*Towards a theory of symmetric extensions*, Proposition 9.4, reverse inclusion](https://arxiv.org/html/2602.17338v1#S9), p. 33.

Lemma 9.3 requires equality of generic extensions. Membership of a comparison generic in the outer model does not provide that equality. The source proof must justify or restrict the quantifier at precisely this use of the lemma.

The proposed replacement defines the appropriate comparison generics using ground canonical names, without adding the chosen generic as a definition parameter. Our original Solovay application explicitly cites Proposition 9.4. It should cite the repaired argument; the defect is not created by that citation. The linked formalization covers the application used here, and should not be called a blanket verification of every class-name case in Proposition 9.4.

[Account and Lean links](sources/other/README.md#quantify-over-generics-giving-the-same-extension).

## Items that do not justify source-paper errata

| Item already in the records | Proper location and reason |
| --- | --- |
| Solovay parameters, full HOD, and ordinary-real transport | Our application note or formalization supplement. The records supply the parameter/closure and representation bridges used here; they do not identify a false statement in Solovay's paper. [Proof and Lean links](sources/other/README.md#spell-out-the-solovay-import). |
| Bagaria Theorem 4.11, complexity and parameters | Our application proof. Checking the complexity level and choosing a cardinal above the parameters verifies a theorem's hypotheses; it does not repair Bagaria's theorem. [Lean](../ZFVP/ModelTheory/WoodinSparseRestorationTheorem.lean). |
| Usuba Corollary 4.5, class restoration | Our construction supplement. The bridge from the cited input to this forcing construction needs pretameness and stabilization arguments. The records establish no error in Usuba's corollary. [Proof](sources/other/proofs/c03-pretameness-and-stabilization-proof.md). |
| Arbitrary-ground Cohen, unrestricted-ground PSP, and the ordinary-real bridge | Completed formalization work. Earlier countability or representation restrictions in our code are not evidence of paper defects. [Development classification](development/README.md). |
| V13's exact sparse Sigma-3 clause | Our manuscript/formalization correspondence. A raw presentation's complexity does not automatically transfer to our chosen sparse presentation. This does not refute the source's existence of a Sigma-3 presentation. [Exact difference](formalization/README.md#w02-sharp-σ₃-for-the-specified-sparse-presentation). |
| V13's full endpoint and class-generic range | Our manuscript/formalization correspondence. The exported specialization does not establish the entire quantified clause. No source theorem is refuted by that mismatch. [Exact difference](formalization/README.md#w05-the-full-endpoint-and-generic-quantifiers). |
| Other proof expansions in our paper | Decide each at its own locus; a longer Lean-compatible proof is not evidence the old theorem was false. [Individual placement arguments](our-paper/README.md). |
| Rejected local shortcuts | Our development record only. Each failed rank bound, support claim, cone isomorphism, or Q argument is listed with its replacement. None should be sent to an author as their error without finding it in their text. [Individual entries](development/README.md). |
| Stronger unused completeness or Boolean-completion routes | Optional formalization work. Their absence requires no paper repair when the actual dependency uses a proved weaker result. [Scope](formalization/README.md#claims-outside-the-current-paper-route). |

## Recommended publication arrangement

Keep one source supplement for Woodin/Spoerl and one for Enayat, with the exact corrected inputs and the limits of each repair. Treat the rank-Berkeley convention and the same-extension generic argument as short source corrections. Our manuscript should cite those notes and state any replacement input whose hypotheses or conclusion changed. Application details and implementation correspondence belong in our own supplement.

An author inquiry is still needed for the full same-embedding successor-rank lift and the ambient-HOD clause if those source assertions are to be claimed at their original strength. The available replacements suffice for the recorded main routes but do not settle those broader assertions. No author has been contacted as part of this revision.
