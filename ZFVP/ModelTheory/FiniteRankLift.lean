import ZFVP.ModelTheory.FiniteRankInternalForcing
import ZFVP.ModelTheory.SuccessorNameElementaryLift
import ZFVP.ModelTheory.WoodinSparseEndpointTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure FiniteRankLiftData (A B : ForcingContext V) (δ ε e : V) : Prop where
  source_inaccessible : IsChoicelessInaccessible δ
  target_inaccessible : IsChoicelessInaccessible ε
  embedding : IsCodedMembershipEmbedding (hierarchy (ordinalAdd δ (ω : V)))
    (hierarchy (ordinalAdd ε (ω : V))) e
  poset_subset : A.P ⊆ hierarchy δ
  target_poset_subset : B.P ⊆ hierarchy ε
  poset_image : e ‘ A.P = B.P
  relation_image : e ‘ A.R = B.R
  height_image : e ‘ δ = ε
  generic : ∀ p ∈ A.G, e ‘ p ∈ B.G
  source_coverage : ∀ x ∈ hierarchy (A.check δ), ∃ τ : ForcingName A.P,
    τ.val ∈ hierarchy δ ∧ x = A.ofName τ
  target_coverage : ∀ x ∈ hierarchy (B.check ε), ∃ τ : ForcingName B.P,
    τ.val ∈ hierarchy ε ∧ x = B.ofName τ

namespace FiniteRankLiftData
variable {A B : ForcingContext V} {δ ε e : V} (L : FiniteRankLiftData A B δ ε e)
include L

theorem low_mem_allowance {x : V} (hx : x ∈ hierarchy δ) :
    x ∈ hierarchy (ordinalAdd δ (ω : V)) := by
  let := L.source_inaccessible.1
  exact (hierarchy_transitive _).mem_trans hx (hierarchy_mem (ordinalAdd_omega_gt δ))

theorem subset_mem_allowance {x : V} (hx : x ⊆ hierarchy δ) :
    x ∈ hierarchy (ordinalAdd δ (ω : V)) := by
  let := L.source_inaccessible.1
  apply mem_hierarchy_of_mem_stage (ordinalAdd_omega_succ_closed δ (ordinalAdd_omega_gt δ))
  rwa [hierarchy_succ, mem_power_iff]

theorem relation_mem : A.R ∈ hierarchy (ordinalAdd δ (ω : V)) := by
  let := L.source_inaccessible.1
  have hs : ∀ β ∈ ordinalAdd δ (ω : V), succ β ∈ ordinalAdd δ (ω : V) :=
    fun _ ↦ ordinalAdd_omega_succ_closed δ
  have hP := L.subset_mem_allowance L.poset_subset
  exact subset_mem_hierarchy_limit hs (prod_mem_hierarchy_limit hs hP hP) A.order.1

theorem nameDomain_image : e ‘ (lowRankNameSet A.P δ) = lowRankNameSet B.P ε := by
  let := L.source_inaccessible.1
  let := L.target_inaccessible.1
  rw [limitRankEmbedding_value_lowRankNameSet
    (fun _ ↦ ordinalAdd_omega_succ_closed δ) (fun _ ↦ ordinalAdd_omega_succ_closed ε)
    L.embedding (L.subset_mem_allowance L.poset_subset) (ordinalAdd_omega_gt δ),
    L.poset_image, L.height_image]

theorem image_lowName {τ : V} (hτ : τ ∈ lowRankNameSet A.P δ) :
    e ‘ τ ∈ lowRankNameSet B.P ε := by
  let := L.source_inaccessible.1
  let := L.target_inaccessible.1
  let := hierarchy_transitive (ordinalAdd ε (ω : V))
  rw [← L.nameDomain_image]
  exact (L.embedding.value_mem_iff (L.low_mem_allowance ((mem_lowRankNameSet _ _ _).mp hτ).1)
    (L.subset_mem_allowance (lowRankNameSet_subset A.P δ))).mpr hτ

theorem image_name {τ : V} (hτ : τ ∈ hierarchy δ) (hn : IsForcingName A.P τ) :
    IsForcingName B.P (e ‘ τ) :=
  ((mem_lowRankNameSet _ _ _).mp (L.image_lowName ((mem_lowRankNameSet _ _ _).mpr ⟨hτ, hn⟩))).2

noncomputable def imageName (τ : ForcingName A.P) (hτ : τ.val ∈ hierarchy δ) : ForcingName B.P :=
  ⟨e ‘ τ.val, L.image_name hτ τ.property⟩

theorem imageName_rank (τ : ForcingName A.P) (hτ : τ.val ∈ hierarchy δ) :
    (L.imageName τ hτ).val ∈ hierarchy ε :=
  ((mem_lowRankNameSet _ _ _).mp (L.image_lowName ((mem_lowRankNameSet _ _ _).mpr ⟨hτ, τ.property⟩))).1

theorem image_eq_iff (σ τ : ForcingName A.P) (hσ : σ.val ∈ hierarchy δ) (hτ : τ.val ∈ hierarchy δ) :
    B.ofName (L.imageName σ hσ) = B.ofName (L.imageName τ hτ) ↔ A.ofName σ = A.ofName τ := by
  let := L.source_inaccessible.1
  let := L.target_inaccessible.1
  obtain ⟨j, hj⟩ := finiteRankEmbedding_successorNameLift A B
    L.source_inaccessible.rankCriterion.2.2.1 L.target_inaccessible.rankCriterion.2.2.1
    L.poset_subset L.target_poset_subset L.embedding L.poset_image L.relation_image L.height_image L.generic
  let s : {x : V // x ∈ successorLowNameSet A.P δ} :=
    ⟨σ.val, lowRankNameSet_subset_successor A.P δ _ ((mem_lowRankNameSet _ _ _).mpr ⟨hσ, σ.property⟩)⟩
  let t : {x : V // x ∈ successorLowNameSet A.P δ} :=
    ⟨τ.val, lowRankNameSet_subset_successor A.P δ _ ((mem_lowRankNameSet _ _ _).mpr ⟨hτ, τ.property⟩)⟩
  obtain ⟨s', hs', hjs⟩ := hj s
  obtain ⟨t', ht', hjt⟩ := hj t
  have hse : s' = L.imageName σ hσ := Subtype.ext hs'
  have hte : t' = L.imageName τ hτ := Subtype.ext ht'
  rw [hse] at hjs
  rw [hte] at hjt
  rw [← hjs, ← hjt]
  change (j (A.successorNameValue δ s)).val = (j (A.successorNameValue δ t)).val ↔
    (A.successorNameValue δ s).val = (A.successorNameValue δ t).val
  exact Subtype.val_injective.eq_iff.trans (j.injective.eq_iff.trans Subtype.val_injective.eq_iff.symm)

end FiniteRankLiftData
end ZFVP
