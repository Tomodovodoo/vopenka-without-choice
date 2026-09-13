/-! Retired: the top of Enayat's Theorem 5.17 chain under `◊`, in its first form.

This file used to state `RubinExtensionUnderDiamond`, which asked a countable model of `ZF` to have
an elementary extension of cardinality `ℵ₁` satisfying `IsRubin`, the literal reading of Enayat's
Definition 5.13. That reading is refutable in `ZF`: `ZFVP.not_isRubin` in
`ZFVP.ModelTheory.RubinDefinableFilters` applies clause (a) to the ordinals under inclusion and
then clause (b) to the maximal filter they form over themselves, and a code for that filter is a
set of all ordinals. So the hypothesis carried by every theorem here was false for every model, and
the structure `AlephOneRubinExtension`, the hypothesis `RubinExtensionUnderDiamond` and the five
results drawn from them have been removed.

The four conclusions are proved in `ZFVP.ModelTheory.RubinChainCountabilityEssential` from
`RubinChainUnderDiamond`, which asks instead for the object Stage 1 of Enayat's Appendix builds:
`exists_weaklyRubin_elementary_extension_of_rubinChain`, `rubinShelahSchmerl_of_rubinChain`,
`exists_zf_dead_end_of_countable_of_rubinChain` and `countability_essential_of_rubinChain`.

The file is kept so that the module stays in the build, and holds no declarations. -/
