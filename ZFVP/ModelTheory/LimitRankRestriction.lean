import ZFVP.ModelTheory.LimitRankEmbeddingAction
import ZFVP.ModelTheory.TruthTableRestriction
import ZFVP.ModelTheory.TransitiveZFCoding
import ZFVP.SetTheory.CorrectDomainReflection

/-! Restriction to an inner transitive ZF model using a truth table in a limit rank segment. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem membershipModelTruthTable_mem_hierarchy_limit {κ a : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (hω : (ω : V) ∈ hierarchy κ)
    (ha : a ∈ hierarchy κ) (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy κ) :
    membershipModelTruthTable a ∈ hierarchy κ := by
  apply subset_mem_hierarchy_limit hκ
    (prod_mem_hierarchy_limit hκ hF (finiteSequences_mem_hierarchy_limit hκ hω ha))
  intro p hp
  exact (mem_sep_iff.mp hp).1

theorem TransitiveZF.identity_val (a : V) [IsTransitive a] [Nonempty (SetDomain a)]
    [(SetDomain a)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (x : SetDomain a) :
    (SetTheory.identity x).val = SetTheory.identity x.val :=
  (bounded_defined_absolute a boundedIdentityFormula_bounded
    (fun v ↦ v 0 = SetTheory.identity (v 1))
    (fun v ↦ v 0 = SetTheory.identity (v 1)) ![SetTheory.identity x, x]).mp rfl

theorem limitRankEmbedding_restrict_transitiveZF {δ B f a : V}
    [IsOrdinal δ] [IsTransitive B] [IsTransitive a] [Nonempty (SetDomain a)]
    [(SetDomain a)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hω : (ω : V) ∈ δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) B f) (ha : a ∈ hierarchy δ) :
    IsCodedMembershipEmbedding a (f ‘ a) (f ↾ a) := by
  let := hierarchy_isSequenceSupport hω hδ
  let := TransitiveZF.sequenceSupport a
  have hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ a := by
    simpa only [TransitiveZF.membershipFamily_val a] using
      (formulaFamily (membershipLanguageCode : SetDomain a) ∅).property
  have hiF : SetTheory.identity (formulaFamily membershipLanguageCode ∅ : V) ∈ a := by
    simpa only [TransitiveZF.identity_val a, TransitiveZF.membershipFamily_val a] using
      (SetTheory.identity (formulaFamily (membershipLanguageCode : SetDomain a) ∅)).property
  exact h.restrict_of_truthTable ha hF hiF
    (membershipModelTruthTable_mem_hierarchy_limit hδ (IsCodingSupport.omega_mem (U := hierarchy δ))
      ha ((hierarchy_transitive δ).mem_trans hF ha))
    (membershipModelTruthTable_correct a)

theorem limitRankEmbedding_restrict_rank {δ ε f θ : V} [IsOrdinal δ] [IsOrdinal ε]
    [IsOrdinal θ] [Nonempty (SetDomain (hierarchy θ))]
    [(SetDomain (hierarchy θ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hε : ∀ β ∈ ε, succ β ∈ ε) (hω : (ω : V) ∈ δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f) (hθ : θ ∈ δ) :
    IsCodedMembershipEmbedding (hierarchy θ) (hierarchy (f ‘ θ)) (f ↾ (hierarchy θ)) := by
  let := hierarchy_transitive θ
  let := hierarchy_transitive ε
  have he := limitRankEmbedding_restrict_transitiveZF hδ hω h (hierarchy_mem hθ)
  rw [(limitRankEmbedding_value_hierarchy hδ hε h inferInstance (ordinal_subset_hierarchy δ _ hθ)).2] at he
  exact he

theorem rankCriterionEmbedding_restrict {θ η f : V} (hθ : IsRankCriterionHeight θ)
    [IsOrdinal η]
    (h : IsCodedMembershipEmbedding (hierarchy (ordinalAdd θ ω)) (hierarchy (ordinalAdd η ω)) f)
    (hθη : f ‘ θ = η) :
    IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) (f ↾ (hierarchy θ)) := by
  let := hθ.1
  let := rankDomain_nonempty hθ.2.1
  let := hθ.models_zf
  have he := limitRankEmbedding_restrict_rank
    (fun _ hβ ↦ ordinalAdd_omega_succ_closed θ hβ)
    (fun _ hβ ↦ ordinalAdd_omega_succ_closed η hβ)
    (IsOrdinal.toIsTransitive.mem_trans hθ.2.1 (ordinalAdd_omega_gt θ)) h (ordinalAdd_omega_gt θ)
  simpa only [hθη] using he

end ZFVP
