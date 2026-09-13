import ZFVP.ModelTheory.ForcingDCEnumerations
import ZFVP.ModelTheory.UsubaStageDependentChoice
import ZFVP.ModelTheory.ForcingPreorderVopenkaLS
import ZFVP.SetTheory.UsubaLeastTarget

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingContext.usuba_rank_target_bound (A : ForcingContext V)
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (hAC : ¬InternalChoice A.Model) (k : V) [IsOrdinal k]
    (hDC : ∀ β ∈ A.check k, InternalDependentChoiceAt β)
    {X : A.Model} (hX : rank X ⊆ A.check k) :
    X ⊆ hierarchy (usubaLeastTarget woodinSeedCardinal) := by
  have hle : A.check k ⊆ (woodinSeedCardinal : A.Model) := by
    rcases IsOrdinal.mem_trichotomy (A.check k) (woodinSeedCardinal : A.Model) with h | he | h
    · exact IsOrdinal.toIsTransitive.transitive _ h
    · exact he ▸ subset_refl _
    · exact False.elim ((woodinSeedCardinal_spec hAC).2.1 (hDC _ h))
  have htarget := usubaLeastTarget_spec
    (fun β hβ ↦ by let := hβ; exact A.lsCardinals_unbounded hVP β)
    (woodinSeedCardinal : A.Model)
  have hseed : (woodinSeedCardinal : A.Model) ∈ usubaLeastTarget woodinSeedCardinal :=
    IsOrdinal.toIsTransitive.mem_trans htarget.2.2.1 htarget.2.1
  have hm : X ∈ hierarchy (usubaLeastTarget woodinSeedCardinal) :=
    (mem_hierarchy_iff_rank_mem _ _).mpr
      (ordinal_mem_of_subset_mem (subset_trans hX hle) hseed)
  exact (hierarchy_transitive _).transitive _ hm

end ZFVP
