import ZFVP.ModelTheory.EmbeddingSetOperations
import ZFVP.SetTheory.BoundedRestriction
import ZFVP.SetTheory.BoundedRelationDomain
import ZFVP.SetTheory.BoundedUnion
import ZFVP.SetTheory.SparseSplice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsCodedMembershipEmbedding
variable {A B f : V} [IsTransitive A] [IsTransitive B]

theorem value_restriction (he : IsCodedMembershipEmbedding A B f) {p a : V}
    (hp : p ∈ A) (ha : a ∈ A) (hr : p ↾ a ∈ A) :
    f ‘ (p ↾ a) = (f ‘ p) ↾ (f ‘ a) :=
  (he.bounded_defined_iff boundedRestrictFormula_bounded
    (fun v ↦ v 0 = (v 1) ↾ (v 2)) ![p ↾ a, p, a]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hp, ha, hr])).mp rfl

theorem value_relationDomain (he : IsCodedMembershipEmbedding A B f) {p : V}
    (hp : p ∈ A) (hd : domain p ∈ A) : f ‘ (domain p) = domain (f ‘ p) :=
  (he.bounded_defined_iff boundedRelationDomainFormula_bounded
    (fun v ↦ v 0 = domain (v 1)) ![domain p, p] (by simp [hp, hd])).mp rfl

theorem value_union (he : IsCodedMembershipEmbedding A B f) {p q : V}
    (hp : p ∈ A) (hq : q ∈ A) (hu : p ∪ q ∈ A) : f ‘ (p ∪ q) = (f ‘ p) ∪ (f ‘ q) :=
  (he.bounded_defined_iff boundedUnionFormula_bounded
    (fun v ↦ v 0 = v 1 ∪ v 2) ![p ∪ q, p, q]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hp, hq, hu])).mp rfl

end IsCodedMembershipEmbedding

theorem relationDomain_mem_hierarchy_limit {δ p : V} [IsOrdinal δ]
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hp : p ∈ hierarchy δ) : domain p ∈ hierarchy δ :=
  subset_mem_hierarchy_limit hδ (sUnion_mem_hierarchy_limit hδ (sUnion_mem_hierarchy_limit hδ hp))
    (fun _ hz ↦ (mem_sep_iff.mp hz).1)

theorem limitRankEmbedding_restriction {δ ε f p a : V} [IsOrdinal δ] [IsOrdinal ε]
    (hδ : ∀ β ∈ δ, succ β ∈ δ)
    (he : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hp : p ∈ hierarchy δ) (ha : a ∈ hierarchy δ) :
    f ‘ (p ↾ a) = (f ‘ p) ↾ (f ‘ a) := by
  let := hierarchy_transitive δ
  let := hierarchy_transitive ε
  exact he.value_restriction hp ha (subset_mem_hierarchy_limit hδ hp
    (fun _ hz ↦ (mem_restrict_iff.mp hz).1))

theorem limitRankEmbedding_sparsePrefixReplace {δ ε f a q p : V} [IsOrdinal δ] [IsOrdinal ε]
    (hδ : ∀ β ∈ δ, succ β ∈ δ)
    (he : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (ha : a ∈ hierarchy δ) (hq : q ∈ hierarchy δ) (hp : p ∈ hierarchy δ) :
    f ‘ (sparsePrefixReplace a q p) = sparsePrefixReplace (f ‘ a) (f ‘ q) (f ‘ p) := by
  let := hierarchy_transitive δ
  let := hierarchy_transitive ε
  have hd := relationDomain_mem_hierarchy_limit hδ hq
  have hc : domain q \ a ∈ hierarchy δ := subset_mem_hierarchy_limit hδ hd
    (fun _ hz ↦ (mem_sdiff_iff.mp hz).1)
  have ht : q ↾ (domain q \ a) ∈ hierarchy δ := subset_mem_hierarchy_limit hδ hq
    (fun _ hz ↦ (mem_restrict_iff.mp hz).1)
  have hu : p ∪ (q ↾ (domain q \ a)) ∈ hierarchy δ := by
    have hpair := pair_mem_hierarchy_limit hδ hp ht
    simpa only [pair_eq_doubleton, ← union_def] using sUnion_mem_hierarchy_limit hδ hpair
  unfold sparsePrefixReplace
  rw [he.value_union hp ht hu, limitRankEmbedding_restriction hδ he hq hc]
  have hcomp : f ‘ (domain q \ a) = (f ‘ (domain q)) \ (f ‘ a) :=
    he.value_relativeComplement hd ha hc
  rw [hcomp, he.value_relationDomain hq hd]

end ZFVP
