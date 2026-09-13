import ZFVP.ModelTheory.ForcingStarDCFailure
import ZFVP.ModelTheory.RankDependentChoiceProxy
import ZFVP.ModelTheory.SuccessorRankLiftChecks
import ZFVP.ModelTheory.SuccessorRankDependentChoice
import ZFVP.ModelTheory.SuccessorRankCriticalPoint
import ZFVP.ModelTheory.SuccessorRankLiftElementarity

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def rankDCBelowProxyFormula : SetTheorySemisentence 2 :=
  “κ D. ∀ η ∈ κ, !rankDCProxyFormula η D”

theorem rankDCBelowProxy_rank_iff {γ : V} (hγ : Cn 1 γ)
    (κ D : SetDomain (hierarchy γ)) :
    rankDCBelowProxyFormula.Evalb ![κ, D] ↔
      boundedStarDCBelowFormula.Evalb ![κ.val, D.val, hierarchy γ] := by
  let := hγ.ordinal
  have he : rankDCBelowProxyFormula.Evalb ![κ, D] ↔
      ∀ η : SetDomain (hierarchy γ), η ∈ κ → rankDCProxyFormula.Evalb ![η, D] := by
    simp [rankDCBelowProxyFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  rw [he, eval_boundedStarDCBelowFormula]
  constructor
  · intro h η hη
    let η' : SetDomain (hierarchy γ) := ⟨η, (hierarchy_transitive γ).mem_trans hη κ.property⟩
    exact (rankDCProxy_rank_iff hγ η' D).mp (h η' hη)
  · intro h η hη
    exact (rankDCProxy_rank_iff hγ η D).mpr (h η.val hη)

namespace SuccessorRankLiftData
variable {A B : ForcingContext V} {ρ γ e : V} (L : SuccessorRankLiftData A B ρ γ e)

noncomputable def rankCheck (x : V) (hx : x ∈ hierarchy ρ) : SetDomain (hierarchy (A.check ρ)) :=
  L.sourceRankValue ⟨checkName A.one x, checkName_isName A.top.1 x⟩ (L.checkName_mem_source hx)

theorem rankLiftFun_rankCheck (heone : e ‘ A.one = B.one) (x : V) (hx : x ∈ hierarchy ρ) :
    (L.rankLiftFun (L.rankCheck x hx)).val = B.check (e ‘ x) := by
  rw [rankCheck, L.rankLiftFun_sourceRankValue]
  change B.ofName ⟨e ‘ (checkName A.one x), _⟩ = B.ofName ⟨checkName B.one (e ‘ x), _⟩
  congr 1
  apply Subtype.ext
  change e ‘ (checkName A.one x) = checkName B.one (e ‘ x)
  rw [successorRankEmbedding_value_checkName L.source_correct L.target_correct L.embedding
    L.one_mem_source hx, heone]

theorem rankLiftFun_hierarchy (a D : SetDomain (hierarchy (A.check ρ)))
    (ha : IsOrdinal a.val) (hD : D.val = hierarchy a.val) :
    (L.rankLiftFun D).val = hierarchy (L.rankLiftFun a).val := by
  have hA := A.cn_one_check L.source_correct L.poset_mem
  have hB := B.cn_one_check L.target_correct L.target_poset_mem
  have hs := (hA.hierarchy_formula_correct D a).mpr ⟨ha, hD⟩
  have ht := (L.rankLiftFun_formula_iff piOneHierarchyFormula ![D, a]).mp hs
  have hv : L.rankLiftFun ∘ ![D, a] = ![L.rankLiftFun D, L.rankLiftFun a] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [hv] at ht
  exact ((hB.hierarchy_formula_correct _ _).mp ht).2

theorem rankDCBelowProxy_iff (κ D : SetDomain (hierarchy (A.check ρ))) :
    boundedStarDCBelowFormula.Evalb ![κ.val, D.val, hierarchy (A.check ρ)] ↔
      boundedStarDCBelowFormula.Evalb
        ![(L.rankLiftFun κ).val, (L.rankLiftFun D).val, hierarchy (B.check γ)] := by
  have hh := L.rankLiftFun_formula_iff rankDCBelowProxyFormula ![κ, D]
  have hv : L.rankLiftFun ∘ ![κ, D] = ![L.rankLiftFun κ, L.rankLiftFun D] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [hv] at hh
  exact (rankDCBelowProxy_rank_iff (A.cn_one_check L.source_correct L.poset_mem) κ D).symm.trans
    (hh.trans (rankDCBelowProxy_rank_iff (B.cn_one_check L.target_correct L.target_poset_mem) _ _))

include L in
theorem dependentChoice_iff {δ κ α : V} (hδ : IsWoodinSupercompact δ)
    (hρ : IsSigmaOneStarCorrect ρ) (hγ : IsSigmaOneStarCorrect γ)
    (heone : e ‘ A.one = B.one) (hα : α ∈ ρ) (hκ : κ ∈ α) :
    InternalDependentChoiceAt (A.check κ) ↔ InternalDependentChoiceAt (B.check (e ‘ κ)) := by
  let := hρ.1.ordinal
  let := hγ.1.ordinal
  let := IsOrdinal.of_mem hα
  let := IsOrdinal.of_mem hκ
  have hκρ : κ ∈ ρ := IsOrdinal.toIsTransitive.mem_trans hκ hα
  have hαV : α ∈ hierarchy ρ := ordinal_mem_hierarchy_iff.mpr hα
  have hκV : κ ∈ hierarchy ρ := ordinal_mem_hierarchy_iff.mpr hκρ
  have hαi := successorRankEmbedding_ordinal_bounds hρ.1 hγ.1 L.embedding hα
  let := hαi.1
  have hκi : e ‘ κ ∈ e ‘ α := by
    exact (successorRankElementaryMap L.embedding).map_mem_iff ⟨κ, hκV⟩ ⟨α, hαV⟩ |>.mpr hκ
  have hA := A.cn_one_check L.source_correct L.poset_mem
  let a := L.rankCheck α hαV
  let k := L.rankCheck κ hκV
  let D : SetDomain (hierarchy (A.check ρ)) := ⟨hierarchy (A.check α),
    hA.hierarchy_closed inferInstance (ordinal_mem_hierarchy_iff.mpr ((A.check_mem_iff _ _).mpr hα))⟩
  have heD : (L.rankLiftFun D).val = hierarchy (B.check (e ‘ α)) := by
    rw [L.rankLiftFun_hierarchy a D (by change IsOrdinal (A.check α); infer_instance) rfl,
      L.rankLiftFun_rankCheck heone α hαV]
  have heκ : (L.rankLiftFun k).val = B.check (e ‘ κ) := L.rankLiftFun_rankCheck heone κ hκV
  have hp := L.rankDCProxy_iff k D
  change boundedStarDCFormula.Evalb ![A.check κ, hierarchy (A.check α), hierarchy (A.check ρ)] ↔ _ at hp
  rw [heκ, heD] at hp
  exact (A.boundedStarDC_iff_at hδ hρ L.poset_mem hα hκ).symm.trans
    (hp.trans (B.boundedStarDC_iff_at hδ hγ L.target_poset_mem hαi.2 hκi))

include L in
theorem dependentChoiceBelow_iff {δ κ α : V} (hδ : IsWoodinSupercompact δ)
    (hρ : IsSigmaOneStarCorrect ρ) (hγ : IsSigmaOneStarCorrect γ)
    (heone : e ‘ A.one = B.one) (hα : α ∈ ρ) (hκ : κ ∈ α) :
    (∀ η ∈ A.check κ, InternalDependentChoiceAt η) ↔
      ∀ η ∈ B.check (e ‘ κ), InternalDependentChoiceAt η := by
  let := hρ.1.ordinal
  let := hγ.1.ordinal
  let := IsOrdinal.of_mem hα
  let := IsOrdinal.of_mem hκ
  have hκρ : κ ∈ ρ := IsOrdinal.toIsTransitive.mem_trans hκ hα
  have hαV : α ∈ hierarchy ρ := ordinal_mem_hierarchy_iff.mpr hα
  have hκV : κ ∈ hierarchy ρ := ordinal_mem_hierarchy_iff.mpr hκρ
  have hαi := successorRankEmbedding_ordinal_bounds hρ.1 hγ.1 L.embedding hα
  let := hαi.1
  have hκi : e ‘ κ ∈ e ‘ α :=
    (successorRankElementaryMap L.embedding).map_mem_iff ⟨κ, hκV⟩ ⟨α, hαV⟩ |>.mpr hκ
  have hA := A.cn_one_check L.source_correct L.poset_mem
  let a := L.rankCheck α hαV
  let k := L.rankCheck κ hκV
  let D : SetDomain (hierarchy (A.check ρ)) := ⟨hierarchy (A.check α),
    hA.hierarchy_closed inferInstance (ordinal_mem_hierarchy_iff.mpr ((A.check_mem_iff _ _).mpr hα))⟩
  have heD : (L.rankLiftFun D).val = hierarchy (B.check (e ‘ α)) := by
    rw [L.rankLiftFun_hierarchy a D (by change IsOrdinal (A.check α); infer_instance) rfl,
      L.rankLiftFun_rankCheck heone α hαV]
  have heκ : (L.rankLiftFun k).val = B.check (e ‘ κ) := L.rankLiftFun_rankCheck heone κ hκV
  have hp := L.rankDCBelowProxy_iff k D
  change boundedStarDCBelowFormula.Evalb ![A.check κ, hierarchy (A.check α), hierarchy (A.check ρ)] ↔ _ at hp
  rw [heκ, heD] at hp
  exact (A.boundedStarDCBelow_iff_at hδ hρ L.poset_mem hα hκ).symm.trans
    (hp.trans (B.boundedStarDCBelow_iff_at hδ hγ L.target_poset_mem hαi.2 hκi))

end SuccessorRankLiftData

namespace ForcingContext

theorem selfGeneric (A : ForcingContext V) : ∀ p, p ∈ A.G ↔ p ∈ A.G ∧ p ∈ A.P :=
  fun p ↦ ⟨fun hp ↦ ⟨hp, A.generic.1.1 p hp⟩, fun hp ↦ hp.1⟩

theorem identityRetraction (A : ForcingContext V) :
    IsForcingRetraction A.P A.R A.P A.R (definableGraph A.P id (by definability)) := by
  have hv (p : V) (hp : p ∈ A.P) : (definableGraph A.P id (by definability)) ‘ p = p :=
    value_definableGraph _ _ _ hp
  refine ⟨definableGraph_mem_function_of_mapsTo A.P A.P id (by definability) (fun _ h ↦ h),
    fun _ h ↦ h, hv, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rwa [hv p hp, hv q hq]
  · intro q hq p _
    rw [hv q hq]
  · intro q hq p hp hpq
    exact ⟨p, hp, (hv q hq) ▸ hpq, hv p hp⟩

theorem smallForcing_liftData (A : ForcingContext V) {ρ γ e c : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hc : IsCriticalPoint (hierarchy (succ ρ)) e c) (hcρ : c ∈ ρ)
    (hP : A.P ∈ hierarchy c) (hR : A.R ∈ hierarchy c) :
    SuccessorRankLiftData A A ρ γ e := by
  let := hρ.ordinal
  let := hc.ordinal
  have hsub : hierarchy c ⊆ hierarchy ρ :=
    hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hcρ)
  have hfix := successorRankEmbedding_fixed_below_criticalPoint hρ hγ he hc hcρ
  refine ⟨hρ, hγ, he, hsub _ hP, hsub _ hR, hfix _ hP, hfix _ hR, ?_⟩
  intro p hpG
  rw [hfix p ((hierarchy_transitive c).mem_trans (A.generic.1.1 p hpG) hP)]
  exact hpG

theorem smallForcing_dependentChoiceBelow_iff (A : ForcingContext V) {δ ρ γ e c : V}
    (hδ : IsWoodinSupercompact δ) (hρ : IsSigmaOneStarCorrect ρ) (hγ : IsSigmaOneStarCorrect γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hc : IsCriticalPoint (hierarchy (succ ρ)) e c) (hcρ : c ∈ ρ) (hec : e ‘ c = δ)
    (hP : A.P ∈ hierarchy c) (hR : A.R ∈ hierarchy c) :
    (∀ η ∈ A.check c, InternalDependentChoiceAt η) ↔
      ∀ η ∈ A.check δ, InternalDependentChoiceAt η := by
  let := hρ.1.ordinal
  let := hc.ordinal
  let L := A.smallForcing_liftData hρ.1 hγ.1 he hc hcρ hP hR
  have heone : e ‘ A.one = A.one := successorRankEmbedding_fixed_below_criticalPoint
    hρ.1 hγ.1 he hc hcρ A.one ((hierarchy_transitive c).mem_trans A.top.1 hP)
  have hh := L.dependentChoiceBelow_iff hδ hρ hγ heone
    (hρ.1.successor_closed c hcρ) (mem_succ_self c)
  rwa [hec] at hh

end ForcingContext

namespace SuccessorRankLiftData
variable {A : ForcingContext V} {ρ γ e : V} (L : SuccessorRankLiftData A A ρ γ e)

noncomputable def selfGraph : A.Model := L.graph A.identityRetraction

theorem selfGraph_domain : domain L.selfGraph = hierarchy (A.check ρ) := by
  rw [selfGraph, L.graph_domain_eq_rank_image A.identityRetraction A.selfGeneric]
  obtain ⟨τ, hτ⟩ := A.ofName_surjective (hierarchy (A.check ρ))
  rw [← hτ, ForcingContext.retractionInclusion_ofName]

theorem selfGraph_codedElementary :
    IsCodedMembershipEmbedding (hierarchy (A.check ρ)) (hierarchy (A.check γ)) L.selfGraph := by
  have hh := L.graph_codedElementary A.identityRetraction A.selfGeneric rfl
  change IsCodedMembershipEmbedding (domain L.selfGraph) _ L.selfGraph at hh
  rwa [L.selfGraph_domain] at hh

theorem selfGraph_check (heone : e ‘ A.one = A.one) {x : V} (hx : x ∈ hierarchy ρ) :
    L.selfGraph ‘ (A.check x) = A.check (e ‘ x) :=
  L.graph_check A.identityRetraction A.selfGeneric rfl heone hx

theorem selfGraph_criticalPoint {c : V} (hc : IsCriticalPoint (hierarchy (succ ρ)) e c)
    (hcρ : c ∈ ρ) (heone : e ‘ A.one = A.one) :
    IsCriticalPoint (hierarchy (A.check ρ)) L.selfGraph (A.check c) := by
  let := L.source_correct.ordinal
  let := hc.ordinal
  let := hierarchy_transitive (succ ρ)
  have hcV : c ∈ hierarchy ρ := ordinal_mem_hierarchy_iff.mpr hcρ
  have hcv : A.check c ∈ hierarchy (A.check ρ) :=
    ordinal_mem_hierarchy_iff.mpr ((A.check_mem_iff _ _).mpr hcρ)
  have hmove : L.selfGraph ‘ (A.check c) ≠ A.check c := by
    rw [L.selfGraph_check heone hcV]
    exact fun h ↦ hc.moved ((A.check_eq_iff _ _).mp h)
  refine ⟨inferInstance, ⟨hcv, hmove⟩, ?_⟩
  intro α hα hαmove
  let := hα
  rcases IsOrdinal.mem_trichotomy (A.check c) α with hlt | heq | hgt
  · exact IsOrdinal.toIsTransitive.transitive _ hlt
  · rw [heq]
  · obtain ⟨a, ha, rfl⟩ := (A.mem_check_iff c α).mp hgt
    have haV := (hierarchy_transitive ρ).mem_trans ha hcV
    exact False.elim (hαmove.2 (by rw [L.selfGraph_check heone haV, hc.fixed_below ha]))

end SuccessorRankLiftData

theorem ForcingContext.smallForcing_rankWitness (A : ForcingContext V) {δ γ η : V}
    (hδ : IsWoodinSupercompact δ) (hγ : IsSigmaOneStarCorrect γ) (hδγ : δ ∈ γ)
    (hP : A.P ∈ hierarchy δ) (hR : A.R ∈ hierarchy δ) (hη : η ∈ δ)
    (τ : ForcingName A.P) (hτ : τ.val ∈ hierarchy γ) :
    ∃ ρ ∈ δ, IsSigmaOneStarCorrect ρ ∧ ∃ c ∈ ρ, η ∈ c ∧ c ∈ δ ∧
      A.P ∈ hierarchy c ∧ A.R ∈ hierarchy c ∧
      ∃ j : A.Model,
        IsCodedMembershipEmbedding (hierarchy (A.check ρ)) (hierarchy (A.check γ)) j ∧
        IsCriticalPoint (hierarchy (A.check ρ)) j (A.check c) ∧
        j ‘ (A.check c) = A.check δ ∧
        ∃ x ∈ hierarchy (A.check ρ), j ‘ x = A.ofName τ := by
  let := hδ.1.1
  let := hγ.1.ordinal
  let := IsOrdinal.of_mem hη
  let d := ⟨A.P, ⟨A.R, η⟩ₖ⟩ₖ
  have hd : d ∈ hierarchy δ := kpair_mem_hierarchy_limit hδ.inaccessible.rankCriterion.2.2.1 hP
    (kpair_mem_hierarchy_limit hδ.inaccessible.rankCriterion.2.2.1 hR
      (ordinal_mem_hierarchy_iff.mpr hη))
  obtain ⟨_, ρ, hρδ, hρ, u, hu, e, he, c, hc, hec, heu, hdc⟩ :=
    hδ.highCritical.2.2 γ hδγ hγ τ.val hτ (rank d) ((mem_hierarchy_iff_rank_mem _ _).mp hd)
  let := hρ.1.ordinal
  let := hc.ordinal
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ γ)
  let := hierarchy_transitive c
  have hcρ := successorRankEmbedding_criticalPoint_lt_height he hc (hec.symm ▸ hδγ)
  have hdc' : d ∈ hierarchy c := (mem_hierarchy_iff_rank_mem _ _).mpr hdc
  obtain ⟨hPc, hpair⟩ := kpair_components_mem_transitive hdc'
  obtain ⟨hRc, hηc⟩ := kpair_components_mem_transitive hpair
  let L := A.smallForcing_liftData hρ.1 hγ.1 he hc hcρ hPc hRc
  have heone : e ‘ A.one = A.one := successorRankEmbedding_fixed_below_criticalPoint
    hρ.1 hγ.1 he hc hcρ A.one ((hierarchy_transitive c).mem_trans A.top.1 hPc)
  have huN : IsForcingName A.P u := by
    apply (successorRankEmbedding_forcingName_iff hρ.1 hγ.1 he L.poset_mem hu).mpr
    rw [L.poset_image, heu]
    exact τ.property
  let ν : ForcingName A.P := ⟨u, huN⟩
  refine ⟨ρ, hρδ, hρ, c, hcρ, ordinal_mem_hierarchy_iff.mp hηc, hec ▸ hc.lt_value he,
    hPc, hRc, L.selfGraph, L.selfGraph_codedElementary, L.selfGraph_criticalPoint hc hcρ heone, ?_,
    A.ofName ν, (L.sourceRankValue ν hu).property, ?_⟩
  · rw [L.selfGraph_check heone (ordinal_mem_hierarchy_iff.mpr hcρ), hec]
  · have hv := L.graph_value A.identityRetraction A.selfGeneric ν hu
    change L.selfGraph ‘ (A.ofName ν) = A.ofName (L.imageName ν hu) at hv
    exact hv.trans (congrArg A.ofName (Subtype.ext heu))

end ZFVP
