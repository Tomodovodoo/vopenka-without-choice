# Dependent choice consistency

`Vocabulary.lean` defines DC through internal function graphs on the model's omega. Its sequence covers every internal natural number, including nonstandard ones. `FailureOfChoice` negates the explicit disjoint-family transversal axiom in `PalomarBridge/Vocabulary.lean`.

`Dictionary.lean` proves exact agreement with `ZFVP.InternalDependentChoice`, `ZFVP.InternalChoice`, and both sentences inserted in the source theory. These equivalences hold for arbitrary inhabited ZF membership models, without external countability or well-foundedness assumptions.

`TheoremDC.lean` identifies the full independent model statement with `ZFVP.zfVPDCNotChoiceTheory`. Completeness and equality normalization prove equivalence to its syntactic consistency. The final theorem composes the existing Woodin restoration consistency result with `consistent_zfVP_DC_notChoice`, exactly as the repository's `Solution.dependent_choice` does.

For a standalone Challenge, combine the shared `PalomarBridge/Vocabulary.lean` and this folder's `Vocabulary.lean`, dropping the latter's local import. The proof modules belong only in the Solution environment. The statement introduces no new predicate parameters or extra mathematical hypotheses.
