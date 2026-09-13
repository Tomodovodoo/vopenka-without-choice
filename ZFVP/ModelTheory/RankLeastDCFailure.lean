import ZFVP.ModelTheory.TransitiveZFDependentChoice
import ZFVP.SetTheory.WoodinSeedCardinal

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_leastDependentChoiceFailure (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (κ B : SetDomain (hierarchy ξ)) (hκ : IsLeastDependentChoiceFailure κ.val)
    (hf : IsBoundedDependentChoiceFailure κ.val B.val)
    (hclosed : ∀ A ∈ B.val, ∀ β ∈ succ κ.val, ∀ f ∈ A ^ β, f ∈ B.val) :
    IsLeastDependentChoiceFailure κ := by
  let := hierarchy_transitive ξ
  let := (TransitiveZF.ordinal_iff (hierarchy ξ) κ).mpr hκ.1
  refine ⟨inferInstance,
    TransitiveZF.not_dependentChoice_of_bounded_failure (hierarchy ξ) κ B hκ.1 hf hclosed, ?_⟩
  intro α hα hfail
  let := hα
  rcases IsOrdinal.mem_trichotomy κ α with hlt | he | hlt
  · exact IsOrdinal.toIsTransitive.transitive _ hlt
  · exact he ▸ subset_refl _
  · exact False.elim (hfail (rank_dependentChoice_of_ambient hs α
      ((TransitiveZF.ordinal_iff (hierarchy ξ) α).mp hα) (hκ.below hlt)))

theorem rank_woodinSeedCardinal_eq (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (κ B : SetDomain (hierarchy ξ)) (hκ : IsLeastDependentChoiceFailure κ.val)
    (hf : IsBoundedDependentChoiceFailure κ.val B.val)
    (hclosed : ∀ A ∈ B.val, ∀ β ∈ succ κ.val, ∀ f ∈ A ^ β, f ∈ B.val) :
    (woodinSeedCardinal : SetDomain (hierarchy ξ)).val = κ.val := by
  have hk := rank_leastDependentChoiceFailure hs κ B hκ hf hclosed
  let := hk.1
  have hn : ¬InternalChoice (SetDomain (hierarchy ξ)) :=
    fun hAC ↦ hk.2.1 (dependentChoiceAt_of_internalChoice hAC κ)
  have he : (woodinSeedCardinal : SetDomain (hierarchy ξ)) = κ :=
    (leastDependentChoiceFailure_existsUnique hn).unique (woodinSeedCardinal_spec hn) hk
  exact congrArg Subtype.val he

end ZFVP
