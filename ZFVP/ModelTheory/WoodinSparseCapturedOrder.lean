import ZFVP.ModelTheory.WoodinSparseCapturedProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem source_pair_second (γ : V) :
    kpair.π₂ (woodinSparseSourceStageCode γ) =
      ⟨forcingCodeR (woodinSparseSourceStageCode γ),
        kpair.π₂ (kpair.π₂ (woodinSparseSourceStageCode γ))⟩ₖ := by
  simp only [woodinSparseSourceStageCode, woodinSourceCode, forcingIterationCode,
    forcingCodeR, kpair.π₁_kpair, kpair.π₂_kpair]

theorem woodinSparseSourceStageCode_order_table_mem_of_code {A γ : V}
    [IsTransitive A] (hs : woodinSparseSourceStageCode γ ∈ A) :
    forcingCodeR (woodinSparseSourceStageCode γ) ∈ A := by
  have h1 : ⟨forcingCodeP (woodinSparseSourceStageCode γ),
      kpair.π₂ (woodinSparseSourceStageCode γ)⟩ₖ ∈ A :=
    woodinSparseSourceStageCode_pair_first γ ▸ hs
  have h2 := (kpair_components_mem_transitive h1).2
  rw [source_pair_second γ] at h2
  exact (kpair_components_mem_transitive h2).1

theorem woodinSparseSourceStageCode_capture_order_table {A B f γ ξ : V}
    [IsTransitive A] [IsTransitive B] (he : IsCodedMembershipEmbedding A B f)
    (hcode : ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ ∈ A)
    (hcap : f ‘ ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ =
      ⟨woodinSparseSourceStageCode ξ, woodinSparseSourceStageCardinals ξ⟩ₖ) :
    f ‘ (forcingCodeR (woodinSparseSourceStageCode γ)) =
      forcingCodeR (woodinSparseSourceStageCode ξ) := by
  have hs := (kpair_components_mem_transitive hcode).1
  have h1 : ⟨forcingCodeP (woodinSparseSourceStageCode γ),
      kpair.π₂ (woodinSparseSourceStageCode γ)⟩ₖ ∈ A :=
    woodinSparseSourceStageCode_pair_first γ ▸ hs
  have hh1 := kpair_components_mem_transitive h1
  have hv1 := he.value_pair hh1.1 hh1.2 h1
  rw [← woodinSparseSourceStageCode_pair_first γ,
    (woodinSparseSourceStageCode_capture_components he hcode hcap).1] at hv1
  have ht : f ‘ (kpair.π₂ (woodinSparseSourceStageCode γ)) =
      kpair.π₂ (woodinSparseSourceStageCode ξ) := by
    simpa only [kpair.π₂_kpair] using (congrArg kpair.π₂ hv1).symm
  have h2 : ⟨forcingCodeR (woodinSparseSourceStageCode γ),
      kpair.π₂ (kpair.π₂ (woodinSparseSourceStageCode γ))⟩ₖ ∈ A :=
    source_pair_second γ ▸ hh1.2
  have hh2 := kpair_components_mem_transitive h2
  have hv2 := he.value_pair hh2.1 hh2.2 h2
  rw [← source_pair_second γ, ht] at hv2
  simpa only [forcingCodeR, kpair.π₁_kpair] using (congrArg kpair.π₁ hv2).symm

theorem woodinSparseSourceStageCode_capture_order {Ω B f γ ξ i : V}
    [IsOrdinal γ] [IsTransitive B]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hγ : γ ⊆ Ω)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V))) B f)
    (hcode : ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ ∈
      hierarchy (ordinalAdd γ (ω : V)))
    (hcap : f ‘ ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ =
      ⟨woodinSparseSourceStageCode ξ, woodinSparseSourceStageCardinals ξ⟩ₖ)
    (hi : i ∈ succ (woodinSourceIndex γ)) :
    f ‘ ((forcingCodeR (woodinSparseSourceStageCode γ)) ‘ i) =
      (forcingCodeR (woodinSparseSourceStageCode ξ)) ‘ (f ‘ i) := by
  let := hierarchy_transitive (ordinalAdd γ (ω : V))
  have hR := woodinSparseSourceStageCode_order_table_mem_of_code (kpair_components_mem_transitive hcode).1
  have ht := (woodinSparseSourceStageCode_valid hΩ hAC hγ).tableR
  have hD : succ (woodinSourceIndex γ) ∈ hierarchy (ordinalAdd γ (ω : V)) := by
    simpa only [woodinSourceIndex_successor] using woodinSourceIndex_successor_finiteRank γ
  have hv := he.value_apply hR hD ht.function ht.domain_eq hi
  rw [woodinSparseSourceStageCode_capture_order_table he hcode hcap] at hv
  exact hv.symm

theorem woodinSparseSourceStageCode_capture_order_relation {Ω B f γ ξ p q : V}
    [IsOrdinal γ] [IsOrdinal ξ] [IsTransitive B]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hγ : γ ⊆ Ω)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V))) B f)
    (hcode : ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ ∈
      hierarchy (ordinalAdd γ (ω : V)))
    (hcap : f ‘ ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ =
      ⟨woodinSparseSourceStageCode ξ, woodinSparseSourceStageCardinals ξ⟩ₖ)
    (hγinf : γ ∉ (ω : V)) (hξinf : ξ ∉ (ω : V)) (himage : f ‘ γ = ξ)
    (hpq : ⟨p, q⟩ₖ ∈ (forcingCodeR (woodinSparseSourceStageCode γ)) ‘ (woodinSourceIndex γ)) :
    ⟨f ‘ p, f ‘ q⟩ₖ ∈ (forcingCodeR (woodinSparseSourceStageCode ξ)) ‘ (woodinSourceIndex ξ) := by
  let := hierarchy_transitive (ordinalAdd γ (ω : V))
  have hR := woodinSparseSourceStageCode_order_table_mem_of_code (kpair_components_mem_transitive hcode).1
  have ht := (woodinSparseSourceStageCode_valid hΩ hAC hγ).tableR
  let := ht.function
  have hrow := (IsCodedMembershipEmbedding.function_argument_mem hR
    (ht.domain_eq.symm ▸ mem_succ_self (woodinSourceIndex γ))).2
  have hpqA := (hierarchy_transitive (ordinalAdd γ (ω : V))).mem_trans hpq hrow
  have hparts := kpair_components_mem_transitive hpqA
  have hm := (he.value_mem_iff hpqA hrow).mpr hpq
  rw [he.value_pair hparts.1 hparts.2 hpqA,
    woodinSparseSourceStageCode_capture_order hΩ hAC hγ he hcode hcap (mem_succ_self _),
    woodinSourceIndex_infinite hγinf, himage] at hm
  simpa only [woodinSourceIndex_infinite hξinf] using hm

end ZFVP
