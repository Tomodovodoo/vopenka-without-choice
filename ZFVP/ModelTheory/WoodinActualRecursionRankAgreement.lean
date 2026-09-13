import ZFVP.ModelTheory.WoodinActualStageRuleRankAgreement
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_woodinIterationRec_val_of_thresholds {δ ξ ηS ηI : V} [IsOrdinal ξ]
    [Nonempty (SetDomain (hierarchy ξ))] [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hξ : IsChoicelessInaccessible ξ)
    (α : SetDomain (hierarchy ξ)) (hα : IsOrdinal α) (hαδ : α.val ∈ δ)
    (hinit : (woodinInitialCode : SetDomain (hierarchy ξ)).val = (woodinInitialCode : V) ∧
      (woodinInitialCardinals : SetDomain (hierarchy ξ)).val = (woodinInitialCardinals : V))
    (hS : ∀ k ∈ α.val, IsWoodinActualSuccessorRankThreshold k ηS)
    (hI : ∀ k ∈ α.val, IsWoodinActualInverseRankThreshold k ηI)
    (hSξ : ηS ∈ ξ) (hIξ : ηI ∈ ξ) :
    ∀ t ∈ α, (woodinIterationRec t).val = woodinIterationRec t.val := by
  let := hierarchy_transitive ξ
  let := hα
  let := (TransitiveZF.ordinal_iff (hierarchy ξ) α).mp hα
  let := hδ.inaccessible.1
  let f := woodinIterationHistory α
  have hvalue (t : SetDomain (hierarchy ξ)) (ht : t ∈ α) :
      (woodinIterationRec t).val = f.val ‘ t.val := by
    rw [← TransitiveZF.value_val_total (hierarchy ξ) f t]
    congr 1
    exact (value_definableGraph α woodinIterationRec woodinIterationRec_definable ht).symm
  have hall := transfinite_induction
    (fun β : V ↦ β ∈ α.val → f.val ‘ β = woodinIterationRec β) (by definability) ?_
  · intro t ht
    let := IsOrdinal.of_mem ht
    let := (TransitiveZF.ordinal_iff (hierarchy ξ) t).mp (inferInstance : IsOrdinal t)
    exact (hvalue t ht).trans (hall (IsOrdinal.toOrdinal t.val) ht)
  intro β ih hβα
  let b : SetDomain (hierarchy ξ) := ⟨β, (hierarchy_transitive ξ).mem_trans hβα α.property⟩
  have hb : IsOrdinal b := (TransitiveZF.ordinal_iff (hierarchy ξ) b).mpr inferInstance
  let := hb
  have hprev : ∀ i ∈ b, (woodinIterationRec i).val = woodinIterationRec i.val := by
    intro i hib
    have hiα : i ∈ α := IsOrdinal.toIsTransitive.mem_trans hib hβα
    let := IsOrdinal.of_mem hib
    let := (TransitiveZF.ordinal_iff (hierarchy ξ) i).mp (inferInstance : IsOrdinal i)
    exact (hvalue i hiα).trans (ih (IsOrdinal.toOrdinal i.val) hib hiα)
  have hp := TransitiveZF.woodinIterationPrefixes_val_of_previous (hierarchy ξ) b hprev
  have hstep := rank_woodinStageRule_val_of_actual hδ hAC hξ b
    (woodinIterationPrefix b) (woodinIterationCardinalPrefix b) hb
    (IsOrdinal.toIsTransitive.mem_trans hβα hαδ) hp.1 hp.2 hinit
    (fun k hk ↦ hS k (IsOrdinal.toIsTransitive.mem_trans hk hβα)) (hI _ hβα) hSξ hIξ
  rw [← hvalue b hβα, woodinIterationRec_rule b, hstep, hp.1, hp.2]
  exact (woodinIterationRec_rule (β : V)).symm

/-- One threshold gives agreement of the actual recursion at every earlier index.
Earlier histories and prefix containment are derived inside the proof. -/
theorem woodinIterationRec_eventually_rank_below {δ α : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hαδ : α ∈ δ) :
    ∃ η ∈ δ, α ∈ η ∧ ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ t : SetDomain (hierarchy ξ), t.val ∈ α →
        (woodinIterationRec t).val = woodinIterationRec t.val := by
  let := hδ.inaccessible.1
  let := IsOrdinal.of_mem hαδ
  obtain ⟨η0, h0δ, h0⟩ := hδ.eventually_rank_woodinInitialCode_eq hAC
  obtain ⟨ηS, hSδ, hS⟩ := woodinActualSuccessorRankThreshold_bounded hδ hAC hαδ
  obtain ⟨ηI, hIδ, hI⟩ := woodinActualInverseRankThreshold_bounded hδ hAC hαδ
  let b := ((α ∪ η0) ∪ ηS) ∪ ηI
  have hbδ : b ∈ δ := ordinal_union_mem (ordinal_union_mem (ordinal_union_mem hαδ h0δ) hSδ) hIδ
  let := IsOrdinal.of_mem hbδ
  let := IsOrdinal.of_mem h0δ
  let := IsOrdinal.of_mem hSδ
  let := IsOrdinal.of_mem hIδ
  let η := succ b
  have hηδ : η ∈ δ := regularCardinal_succ_closed hδ.inaccessible.regular hbδ
  have hαη : α ∈ η := by
    apply mem_succ_iff.mpr
    apply IsOrdinal.subset_iff.mp
    intro z hz
    exact mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inl hz)))))
  have h0η : η0 ∈ η := by
    apply mem_succ_iff.mpr
    apply IsOrdinal.subset_iff.mp
    intro z hz
    exact mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inr hz)))))
  have hSη : ηS ∈ η := by
    apply mem_succ_iff.mpr
    apply IsOrdinal.subset_iff.mp
    intro z hz
    exact mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inr hz)))
  have hIη : ηI ∈ η := by
    apply mem_succ_iff.mpr
    apply IsOrdinal.subset_iff.mp
    intro z hz
    exact mem_union_iff.mpr (Or.inr hz)
  refine ⟨η, hηδ, hαη, ?_⟩
  intro ξ hηξ hξ
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  have hαξ : α ∈ ξ := IsOrdinal.toIsTransitive.mem_trans hαη hηξ
  let A : SetDomain (hierarchy ξ) := ⟨α, ordinal_mem_hierarchy_iff.mpr hαξ⟩
  have hA : IsOrdinal A := (TransitiveZF.ordinal_iff (hierarchy ξ) A).mpr inferInstance
  exact rank_woodinIterationRec_val_of_thresholds hδ hAC hξ A hA hαδ
    (h0 ξ (IsOrdinal.toIsTransitive.mem_trans h0η hηξ) hξ) hS hI
    (IsOrdinal.toIsTransitive.mem_trans hSη hηξ) (IsOrdinal.toIsTransitive.mem_trans hIη hηξ)


theorem woodinIterationRec_eventually_rank_eq {δ θ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hθδ : θ ∈ δ) :
    ∃ η ∈ δ, θ ∈ η ∧ ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ t : SetDomain (hierarchy ξ), t.val = θ →
        (woodinIterationRec t).val = woodinIterationRec θ := by
  let := hδ.inaccessible.1
  let := IsOrdinal.of_mem hθδ
  obtain ⟨η, hηδ, hθη, hall⟩ := woodinIterationRec_eventually_rank_below hδ hAC
    (regularCardinal_succ_closed hδ.inaccessible.regular hθδ)
  let := IsOrdinal.of_mem hηδ
  refine ⟨η, hηδ, IsOrdinal.toIsTransitive.mem_trans (mem_succ_self θ) hθη, ?_⟩
  intro ξ hηξ hξ t ht
  have hh := hall ξ hηξ hξ t (ht ▸ mem_succ_self θ)
  simpa only [ht] using hh

theorem woodinIterationHistory_eventually_rank_eq {δ α : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hαδ : α ∈ δ) :
    ∃ η ∈ δ, α ∈ η ∧ ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ t : SetDomain (hierarchy ξ), t.val = α →
        (woodinIterationHistory t).val = woodinIterationHistory α ∧
        (woodinIterationPrefix t).val = woodinIterationPrefix α ∧
        (woodinIterationCardinalPrefix t).val = woodinIterationCardinalPrefix α := by
  obtain ⟨η, hηδ, hαη, hall⟩ := woodinIterationRec_eventually_rank_below hδ hAC hαδ
  refine ⟨η, hηδ, hαη, ?_⟩
  intro ξ hηξ hξ
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  intro t ht
  have hp : ∀ i ∈ t, (woodinIterationRec i).val = woodinIterationRec i.val := by
    intro i hi
    exact hall ξ hηξ hξ i (ht ▸ hi)
  have hh := TransitiveZF.woodinIterationHistory_val_of_previous (hierarchy ξ) t hp
  have hc := TransitiveZF.woodinIterationPrefixes_val_of_previous (hierarchy ξ) t hp
  simpa only [ht] using And.intro hh hc

end ZFVP
