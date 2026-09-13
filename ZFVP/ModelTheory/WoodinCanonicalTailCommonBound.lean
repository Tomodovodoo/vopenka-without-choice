import ZFVP.ModelTheory.WoodinCanonicalTailNameAction
import ZFVP.ModelTheory.NormalizedBinaryNameUnion
import ZFVP.ModelTheory.ForcedOrderLaws

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
set_option maxHeartbeats 800000
universe u
variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def canonicalTailUnionJoinedFormula : SetTheorySemisentence 10 :=
  (collapseDisplacementPreInputFormula.subst (fun i ↦ .bvar ((![0,1,2,3,4,5] : Fin 6 → Fin 10) i))).and
  ((collapseDisplacementOutputFormula.subst (fun i ↦ .bvar ((![0,1,2,3,4,5,6,7] : Fin 8 → Fin 10) i))).and
  ((functionValueFormula.subst (fun i ↦ .bvar ((![6,4,8] : Fin 3 → Fin 10) i))).and
  (binaryNameUnionFormula.subst (fun i ↦ .bvar ((![9,8,5] : Fin 3 → Fin 10) i)))))

def canonicalTailUnionBoundFormula : SetTheorySemisentence 10 :=
  (nameMemberFormula.subst (fun i ↦ .bvar ((![9,0] : Fin 2 → Fin 10) i))).and
  ((boundedPairMemberFormula.subst (fun i ↦ .bvar ((![1,9,8] : Fin 3 → Fin 10) i))).and
  (boundedPairMemberFormula.subst (fun i ↦ .bvar ((![1,9,5] : Fin 3 → Fin 10) i))))

theorem canonicalTailUnion_ground_bound (v : Fin 10 → V)
    (h : canonicalTailUnionJoinedFormula.Evalb v) : canonicalTailUnionBoundFormula.Evalb v := by
  have h₁ := (canonicalTail_eval_rename collapseDisplacementPreInputFormula
    (![0,1,2,3,4,5] : Fin 6 → Fin 10) v).mp h.1
  have h₂ := (canonicalTail_eval_rename collapseDisplacementOutputFormula
    (![0,1,2,3,4,5,6,7] : Fin 8 → Fin 10) v).mp h.2.1
  have h₃ := (canonicalTail_eval_rename functionValueFormula
    (![6,4,8] : Fin 3 → Fin 10) v).mp h.2.2.1
  have h₄ := (canonicalTail_eval_rename binaryNameUnionFormula
    (![9,8,5] : Fin 3 → Fin 10) v).mp h.2.2.2
  have hpre : IsRegularCardinal (v 2) ∧ IsOrdinal (v 3) ∧
      v 0 = totalWoodinCollapse (v 2) (v 3) ∧ v 1 = reverseInclusionOrder (v 0) ∧
      v 4 ∈ v 0 ∧ v 5 ∈ v 0 := by
    simpa using (eval_collapseDisplacementPreInputFormula _).mp h₁
  have hout := (eval_collapseDisplacementOutputFormula
    (fun i ↦ v ((![0,1,2,3,4,5,6,7] : Fin 8 → Fin 10) i))).mp h₂
  have hf : IsFunction (v 6) ∧ (v 6) ‘ (v 4) = v 8 := by
    simpa [Semiformula.eval_substs, functionValueFormula, Defined.eval_iff, Function.comp_def, eq_comm] using h₃
  have hu : v 9 = v 8 ∪ v 5 := by
    simpa [Semiformula.eval_substs, binaryNameUnionFormula, Function.comp_def] using h₄
  have hc : ForcingCompatible (v 0) (v 1) ((v 6) ‘ (v 4)) (v 5) := by
    exact hout.2.2.2.2.2.2
  obtain ⟨r, hr, hrp, hrq⟩ := hc
  rw [hpre.2.2.2.1, pair_mem_reverseInclusionOrder] at hrp hrq
  have hrp' : v 8 ⊆ r := hf.2 ▸ hrp.2.2
  have huQ : v 9 ∈ v 0 := by
    let := hpre.2.1
    have hQ := hpre.2.2.1
    rw [totalWoodinCollapse_eq] at hQ
    rw [hQ] at hr ⊢
    apply woodinCollapse_subset hr
    rw [hu]
    intro z hz
    rcases mem_union_iff.mp hz with hz | hz
    · exact hrp' z hz
    · exact hrq.2.2 z hz
  have hpQ : v 8 ∈ v 0 := hf.2 ▸ hrp.2.1
  have hνp : ⟨v 9, v 8⟩ₖ ∈ v 1 := by
    rw [hpre.2.2.2.1, pair_mem_reverseInclusionOrder]
    exact ⟨huQ, hpQ, fun z hz ↦ hu ▸ mem_union_iff.mpr (Or.inl hz)⟩
  have hνq : ⟨v 9, v 5⟩ₖ ∈ v 1 := by
    rw [hpre.2.2.2.1, pair_mem_reverseInclusionOrder]
    exact ⟨huQ, hpre.2.2.2.2.2, fun z hz ↦ hu ▸ mem_union_iff.mpr (Or.inr hz)⟩
  refine ⟨(canonicalTail_eval_rename nameMemberFormula (![9,0] : Fin 2 → Fin 10) v).mpr ?_,
    (canonicalTail_eval_rename boundedPairMemberFormula (![1,9,8] : Fin 3 → Fin 10) v).mpr ?_,
    (canonicalTail_eval_rename boundedPairMemberFormula (![1,9,5] : Fin 3 → Fin 10) v).mpr ?_⟩
  · simpa [nameMemberFormula] using huQ
  · simpa [Defined.eval_iff] using hνp
  · simpa [Defined.eval_iff] using hνq

theorem canonicalTailUnion_forces_bound {P R top : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (Q S k d p q f g σ ν : ForcingName P)
    (hpre : top ∈ forcingFormula P R collapseDisplacementPreInputFormula
      (standardTuple ![Q.val,S.val,k.val,d.val,p.val,q.val]))
    (hout : top ∈ forcingFormula P R collapseDisplacementOutputFormula
      (standardTuple ![Q.val,S.val,k.val,d.val,p.val,q.val,f.val,g.val]))
    (hf : top ∈ forcingFormula P R functionValueFormula (standardTuple ![f.val,p.val,σ.val]))
    (hu : top ∈ forcingFormula P R binaryNameUnionFormula (standardTuple ![ν.val,σ.val,q.val])) :
    top ∈ atomicMembership P R ν.val Q.val ∧
    top ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S.val,ν.val,σ.val]) ∧
    top ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S.val,ν.val,q.val]) := by
  have hj : top ∈ forcingFormula P R canonicalTailUnionJoinedFormula
      (standardTuple ![Q.val,S.val,k.val,d.val,p.val,q.val,f.val,g.val,σ.val,ν.val]) := by
    simp only [canonicalTailUnionJoinedFormula, forcingFormula_and, mem_inter_iff, forcingFormula_rename]
    exact ⟨hpre,hout,hf,hu⟩
  have hb := forcingFormula_entailment canonicalTailUnionJoinedFormula canonicalTailUnionBoundFormula
    (fun _ _ _ _ ↦ canonicalTailUnion_ground_bound) hR ht ht.1 ![Q,S,k,d,p,q,f,g,σ,ν] hj
  simp only [canonicalTailUnionBoundFormula, forcingFormula_and, mem_inter_iff, forcingFormula_rename] at hb
  change top ∈ forcingFormula P R nameMemberFormula (standardTuple ![ν.val,Q.val]) ∧ _ at hb
  rwa [forcingFormula_nameMember] at hb

noncomputable def canonicalTailCommonName (P R top f p q : V) : V :=
  normalizedBinaryNameUnion P R top (normalizedTailFunctionValueName P R top f p) q

theorem canonicalTailCommonName_spec_of_member_rank {P R top δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (Q S k d p q f g : ForcingName P)
    (hpre : top ∈ forcingFormula P R collapseDisplacementPreInputFormula
      (standardTuple ![Q.val,S.val,k.val,d.val,p.val,q.val]))
    (hout : top ∈ forcingFormula P R collapseDisplacementOutputFormula
      (standardTuple ![Q.val,S.val,k.val,d.val,p.val,q.val,f.val,g.val]))
    (hp : p.val ∈ normalizedNamePool P R top δ Q.val)
    (hq : q.val ∈ normalizedNamePool P R top δ Q.val)
    (hQr : ∀ τ : ForcingName P, top ∈ atomicMembership P R τ.val Q.val →
      top ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val,checkName top δ])) :
    let σ := normalizedTailFunctionValueName P R top f.val p.val
    let ν := canonicalTailCommonName P R top f.val p.val q.val
    ν ∈ normalizedNamePool P R top δ Q.val ∧
    top ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S.val,ν,σ]) ∧
    top ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S.val,ν,q.val]) := by
  let := hδ.1
  have hi := canonicalTailOutput_inverse hR ht ht.1 ![Q,S,k,d,p,q,f,g] hout
  have hf := canonicalTailOutput_function hR ht ht.1 ![Q,S,k,d,p,q,f,g] hout
  let σ : ForcingName P := ⟨normalizedTailFunctionValueName P R top f.val p.val,
    normalizedTailFunctionValueName_isName hR ht.1⟩
  let ν : ForcingName P := ⟨normalizedBinaryNameUnion P R top σ.val q.val,
    normalizedBinaryNameUnion_isName hR ht.1 σ.property q.property⟩
  have hσ : σ.val ∈ normalizedNamePool P R top δ Q.val :=
    normalizedTailFunctionValueName_mem_pool hR ht hδ hP Q S f g hi hf hp
      (tailFunctionValueName_forces_rank_of_member_rank hR ht Q S f g hi hf hQr hp)
  have hb := canonicalTailUnion_forces_bound hR ht Q S k d p q f g σ ν hpre hout
    (normalizedTailFunctionValueName_forces hR ht f p hf)
    (normalizedBinaryNameUnion_forces hR ht σ q)
  refine ⟨mem_sep_iff.mpr ⟨?_, ν.property, ?_, hb.1⟩, hb.2⟩
  · exact normalizedBinaryNameUnion_mem_hierarchy hR ht.1 σ.property q.property
      hδ.rankCriterion.2.2.1 (mem_sep_iff.mp hσ).1 (mem_sep_iff.mp hq).1
  · exact normalizedBinaryNameUnion_normalized hR ht.1 σ.property q.property

theorem canonicalPrefixTailCommonName_spec {P R top κ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (hκ : top ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName top κ]))
    (p q : ForcingName P)
    (hp : p.val ∈ normalizedNamePool P R top δ (saturatedWoodinPrefixPosetName P R top κ δ))
    (hq : q.val ∈ normalizedNamePool P R top δ (saturatedWoodinPrefixPosetName P R top κ δ)) :
    let Q := saturatedWoodinPrefixPosetName P R top κ δ
    let S := saturatedWoodinPrefixOrderName P R top κ δ
    let f := woodinCollapseDisplacementName P R (checkName top κ) (checkName top δ) p.val q.val
    let σ := normalizedTailFunctionValueName P R top f p.val
    let ν := canonicalTailCommonName P R top f p.val q.val
    ν ∈ normalizedNamePool P R top δ Q ∧
    top ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S,ν,σ]) ∧
    top ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S,ν,q.val]) := by
  let Q : ForcingName P := ⟨_, saturatedWoodinPrefixPosetName_isName P R top κ δ⟩
  let S : ForcingName P := ⟨_, saturatedWoodinPrefixOrderName_isName P R top κ δ⟩
  let k : ForcingName P := ⟨_, checkName_isName ht.1 κ⟩
  let d : ForcingName P := ⟨_, checkName_isName ht.1 δ⟩
  let f : ForcingName P := ⟨_, woodinCollapseDisplacementName_isName P R k.val d.val p.val q.val⟩
  let g : ForcingName P := ⟨_, collapseConverseName_isName P R f.val⟩
  have hpQ := (mem_sep_iff.mp hp).2.2.2
  have hqQ := (mem_sep_iff.mp hq).2.2.2
  have hpre := collapseDisplacement_forces_preInput hR ht ht.1 Q S k d p q hκ
    (forces_checked_ordinal hR ht hδ.1 ht.1)
    (saturatedWoodinPrefixPosetName_forces hR ht hδ hP hκδ ht.1)
    (reverseInclusionOrderName_forces hR ht ht.1 Q) hpQ hqQ
  have hout := saturatedPrefix_displacementName_forces_output hR ht hδ hP hκδ hκ p q hpQ hqQ
  exact canonicalTailCommonName_spec_of_member_rank hR ht hδ hP Q S k d p q f g hpre hout hp hq
    (fun τ hτ ↦ saturatedWoodinPrefix_member_forces_rank hR ht hδ hP hκδ τ hτ)

theorem canonicalHartogsTailCommonName_spec {P R top γ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hγδ : γ ∈ δ)
    (hγ : top ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![hartogsNumberName P R (checkName top γ)]))
    (p q : ForcingName P)
    (hp : p.val ∈ normalizedNamePool P R top δ (saturatedHartogsPosetName P R top γ δ))
    (hq : q.val ∈ normalizedNamePool P R top δ (saturatedHartogsPosetName P R top γ δ)) :
    let Q := saturatedHartogsPosetName P R top γ δ
    let S := saturatedHartogsOrderName P R top γ δ
    let f := woodinCollapseDisplacementName P R (hartogsNumberName P R (checkName top γ))
      (checkName top δ) p.val q.val
    let σ := normalizedTailFunctionValueName P R top f p.val
    let ν := canonicalTailCommonName P R top f p.val q.val
    ν ∈ normalizedNamePool P R top δ Q ∧
    top ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S,ν,σ]) ∧
    top ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S,ν,q.val]) := by
  let Q : ForcingName P := ⟨_, saturatedHartogsPosetName_isName P R top γ δ⟩
  let S : ForcingName P := ⟨_, reverseInclusionOrderName_isName P R Q.val⟩
  let k : ForcingName P := ⟨_, hartogsNumberName_isName P R (checkName top γ)⟩
  let d : ForcingName P := ⟨_, checkName_isName ht.1 δ⟩
  let f : ForcingName P := ⟨_, woodinCollapseDisplacementName_isName P R k.val d.val p.val q.val⟩
  let g : ForcingName P := ⟨_, collapseConverseName_isName P R f.val⟩
  have hpQ := (mem_sep_iff.mp hp).2.2.2
  have hqQ := (mem_sep_iff.mp hq).2.2.2
  have hpre := collapseDisplacement_forces_preInput hR ht ht.1 Q S k d p q hγ
    (forces_checked_ordinal hR ht hδ.1 ht.1)
    (saturatedHartogsPosetName_forces hR ht hδ hP hγδ ht.1)
    (reverseInclusionOrderName_forces hR ht ht.1 Q) hpQ hqQ
  have hout := saturatedHartogs_displacementName_forces_output hR ht hδ hP hγδ hγ p q hpQ hqQ
  exact canonicalTailCommonName_spec_of_member_rank hR ht hδ hP Q S k d p q f g hpre hout hp hq
    (fun τ hτ ↦ saturatedHartogs_member_forces_rank hR ht hδ hP hγδ τ hτ)

end ZFVP
