# Independent statement of Theorem A

[TheoremA.lean](TheoremA.lean) connects the explicit statement to the existing
symmetric-preservation theorem. It proves that the specified symmetric quotient
exists and that every presentation of it satisfies ZF plus the full VP scheme.
The generic is supplied. The ground need not be externally countable, transitive,
or well-founded.

## What specifies the extension

[Vocabulary.lean](Vocabulary.lean) supplies the poset, top condition, automorphism
group, normal subgroup filter, and external generic. Genericity means meeting
every dense subset coded in the ground model.

Names, their automorphism action, hereditary symmetry, and atomic forcing are
defined through internal set operations and recursion graphs. This retains the
construction in possibly nonstandard or externally ill-founded ground models.

`Presentation` specifies the quotient completely. Its valuation is surjective
on the hereditarily symmetric names. Two values are equal exactly when the
generic meets their atomic equality condition set. Their membership relation
holds exactly when the generic meets the atomic membership condition set.
It contains no ZF or VP assumption on the extension.

[Presentation.lean](Presentation.lean) proves that the existing symmetric model
has this presentation and that every such presentation is membership-isomorphic
to that model. Thus the universal preservation clause covers the specified
extension, rather than an arbitrary model chosen for its theory.

## Proof dependencies

1. The shared [membership vocabulary](../PalomarBridge/Vocabulary.lean) and its
   completed ZF/VP correspondence are reused without modification.
2. [Dictionary.lean](Dictionary.lean) identifies every forcing definition with
   its source definition and constructs the corresponding `SymmetricContext`.
3. [Presentation.lean](Presentation.lean) proves existence and uniqueness up to
   membership isomorphism of the specified quotient.
4. [TheoremA.lean](TheoremA.lean) applies the existing
   [preservation proof](../ZFVP/ModelTheory/SymmetricVopenkaPreservation.lean)
   and transfers the conclusion to every presentation.

For a Palomar Challenge, copy both vocabularies into one standalone module and
remove the local vocabulary import. The resulting statement imports only the
shared vocabulary's Mathlib dependency. Proof-side modules can retain their
ordinary imports. The parent repository supplies the final standalone modules
and Comparator configuration.
