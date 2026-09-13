import ZFVP.ModelTheory.SchmerlNamedConsistency
import ZFVP.ModelTheory.DeadEndModelAlephOne

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The Rubin–Shelah–Schmerl theorem for set-sized models in Type. -/
theorem rubinShelahSchmerl : RubinShelahSchmerl.{0} :=
  Schmerl.exists_alephOneWeaklyRubinExtension

/-- Every countable ZF model has an elementary extension of size aleph-one
with no proper ZF end extension. Both formerly assumed construction inputs
are supplied by proved theorems. -/
theorem exists_zf_dead_end_of_countable_complete (M : Type)
    [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M] :
    Nonempty (AlephOneDeadEndExtension M) :=
  exists_zf_dead_end_of_countable' rubinShelahSchmerl M

/-- The whole VP scheme and failure of Choice survive in the dead-end model. -/
theorem countability_essential_complete (M : Type)
    [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := M) φ)
    (hAC : ¬InternalChoice M) :
    ∃ E : AlephOneDeadEndExtension M,
      (∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := E.Model) φ) ∧
        ¬InternalChoice E.Model :=
  countability_essential' rubinShelahSchmerl M hVP hAC

end ZFVP
