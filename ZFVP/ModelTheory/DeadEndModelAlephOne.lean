import ZFVP.ModelTheory.CountabilityEssential
import ZFVP.ModelTheory.NoConservativeEndExtension

/-! The model-theoretic half of the paper's Proposition `prop:countability-essential`, with
Enayat's Theorem 5.1 discharged.

`ZFVP.ModelTheory.CountabilityEssential` proves its results from two named hypotheses, Enayat's
Theorem 5.17 and his Theorem 5.1. The second is now available as
`no_conservative_proper_end_extension`, so the theorems below repeat the two statements with that
hypothesis supplied. Enayat's Theorem 5.17 stays a hypothesis, and it is the only unproved input
that is left. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

/-- A countable model of `ZF` has an elementary extension of cardinality `ℵ₁` with no proper end
extension to a model of `ZF`.

This is part of the model-theoretic half of the paper's Proposition `prop:countability-essential`.
The only input it does not prove is `RubinShelahSchmerl`, Enayat's Theorem 5.17, the theorem of
Rubin, Shelah and Schmerl that every countable model of `ZF` has a weakly Rubin elementary
extension of cardinality `ℵ₁`.

The paper phrases the conclusion in terms of forcing rather than end extensions. The forcing half
of the argument, which is not in this file, turns `IsZFDeadEnd` into "no proper generic extension
satisfying `ZF`": a generic extension that adds a set is a proper end extension, so
`IsZFDeadEnd.false_of_new_element` applied to it gives a contradiction. -/
theorem exists_zf_dead_end_of_countable' (h517 : RubinShelahSchmerl.{u}) (M : Type u)
    [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M] :
    Nonempty (AlephOneDeadEndExtension M) :=
  exists_zf_dead_end_of_countable h517 no_conservative_proper_end_extension M

/-- The model-theoretic half of the paper's Proposition `prop:countability-essential`. From a
countable model of `ZF` satisfying every instance of the Vopenka scheme and failing internal
choice, we get a model of cardinality `ℵ₁` with the same two properties and with no proper end
extension to a model of `ZF`.

The only input this does not prove is `RubinShelahSchmerl`, Enayat's Theorem 5.17, the theorem of
Rubin, Shelah and Schmerl that every countable model of `ZF` has a weakly Rubin elementary
extension of cardinality `ℵ₁`.

The paper phrases the conclusion in terms of forcing rather than end extensions. The forcing half
of the argument, which is not in this file, turns `IsZFDeadEnd` into "no proper generic extension
satisfying `ZF`": a generic extension that adds a set is a proper end extension, so
`IsZFDeadEnd.false_of_new_element` applied to it gives a contradiction. -/
theorem countability_essential' (h517 : RubinShelahSchmerl.{u}) (M : Type u)
    [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := M) φ)
    (hAC : ¬ InternalChoice M) :
    ∃ E : AlephOneDeadEndExtension M,
      (∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := E.Model) φ) ∧
        ¬ InternalChoice E.Model :=
  countability_essential h517 no_conservative_proper_end_extension M hVP hAC

end ZFVP
