import ZFVP.ModelTheory.SaturatedUnionBounds
import ZFVP.ModelTheory.ForcingReverseOrderName
import ZFVP.SetTheory.TwoStepForcing

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def twoStepTailSequenceFormula : SetTheorySemisentence 3 :=
  f“s I f. ∀ z, z ∈ s ↔ ∃ i ∈ I, z = !kpair.dfn i (!kpair.π₂.dfn (!value.dfn f i))”

def twoStepUnionBoundFormula : SetTheorySemisentence 4 :=
  f“b I p f. b = !kpair.dfn p (!sUnion.dfn (!range.dfn (!twoStepTailSequenceFormula I f)))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def twoStepTailSequence (I f : V) : V :=
  definableGraph I (fun i ↦ kpair.π₂ (f ‘ i)) (by definability)

instance twoStepTailSequenceFormula_defined :
    ℒₛₑₜ-function₂[V] twoStepTailSequence via twoStepTailSequenceFormula :=
  ⟨fun v ↦ by
    change twoStepTailSequenceFormula.Evalb v ↔ v 0 = twoStepTailSequence (v 1) (v 2)
    rw [mem_ext_iff]
    simp [twoStepTailSequenceFormula, twoStepTailSequence, mem_definableGraph_iff]⟩

instance twoStepTailSequence_definable : ℒₛₑₜ-function₂[V] twoStepTailSequence :=
  twoStepTailSequenceFormula_defined.to_definable

noncomputable def twoStepUnionBound (I p f : V) : V := ⟨p, ⋃ˢ range (twoStepTailSequence I f)⟩ₖ

instance twoStepUnionBoundFormula_defined :
    ℒₛₑₜ-function₃[V] twoStepUnionBound via twoStepUnionBoundFormula :=
  ⟨fun v ↦ by simp [twoStepUnionBoundFormula, twoStepUnionBound]⟩

instance twoStepUnionBound_definable : ℒₛₑₜ-function₃[V] twoStepUnionBound :=
  twoStepUnionBoundFormula_defined.to_definable

theorem saturated_twoStep_union_bound_countable [Countable V] {P R one δ α p t f : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (Q S : ForcingName P)
    (hα : α ∈ internalCofinality δ) (ht : t ∈ forcingNameHierarchy P δ) (hp : p ∈ P)
    (hclosed : p ∈ forcingFormula P R forcingUnionClosedAtFormula (standardTuple ![Q.val, checkName one α]))
    (hS : p ∈ forcingFormula P R piOneReverseInclusionOrderFormula
      (standardTuple ![S.val, forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val]))
    (hf : IsForcingDirectedFamily
      (twoStepConditions P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val) t)
      (twoStepOrder P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val) S.val t) α f)
    (hpbelow : ∀ i ∈ α, ⟨p, kpair.π₁ (f ‘ i)⟩ₖ ∈ R) :
    twoStepUnionBound α p f ∈ twoStepConditions P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val) t ∧
      ∀ i ∈ α, ⟨twoStepUnionBound α p f, f ‘ i⟩ₖ ∈
        twoStepOrder P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val) S.val t := by
  let Q' : ForcingName P := ⟨forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val,
    forcingSaturatedName_isName _ _ _ _⟩
  let s := twoStepTailSequence α f
  have hd : domain s = α := domain_definableGraph _ _ _
  have hs (i : V) (hi : i ∈ α) : s ‘ i = kpair.π₂ (f ‘ i) := value_definableGraph _ _ _ hi
  have hfi (i : V) (hi : i ∈ α) := function_value_mem hf.1 hi
  have hpi (i : V) (hi : i ∈ α) : kpair.π₁ (f ‘ i) ∈ P := by
    obtain ⟨a, ha, c, _, he⟩ := mem_prod_iff.mp (mem_sep_iff.mp (hfi i hi)).1
    simpa only [he, kpair.π₁_kpair] using ha
  have hsi (i : V) (hi : i ∈ α) : kpair.π₂ (f ‘ i) ∈ forcingNameHierarchy P δ := by
    obtain ⟨a, _, c, hc, he⟩ := mem_prod_iff.mp (mem_sep_iff.mp (hfi i hi)).1
    have hc' : kpair.π₂ (f ‘ i) ∈ twoStepNames Q'.val t := by simpa only [he, kpair.π₂_kpair] using hc
    rcases mem_union_iff.mp hc' with hc' | hc'
    · exact forcingSaturatedName_domain_subset _ _ _ _ _ hc'
    · exact (mem_singleton_iff.mp hc').symm ▸ ht
  have hsN : s ∈ (forcingNameHierarchy P δ) ^ α :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ hsi
  let := IsFunction.of_mem hsN
  have hsn : IsNameSequence P s := by
    intro i hi
    exact forcingNameHierarchy_names P δ _ (function_value_mem hsN (hd ▸ hi))
  let τ : ForcingName P := ⟨⋃ˢ range s, hsn.union_isName⟩
  have hτN : τ.val ∈ forcingNameHierarchy P δ := forcingNameHierarchy_sequence_union hα hsN
  have hgeneric (G : Set V) (hG : IsExternalForcingGeneric P R G) (hpG : p ∈ G) :
      let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
      A.ofName τ ∈ A.ofName Q' ∧ ∀ i, ∀ hi : i ∈ domain s,
        ⟨A.ofName τ, A.ofName ⟨s ‘ i, hsn i hi⟩⟩ₖ ∈ A.ofName S := by
    let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
    let c : ForcingName P := ⟨checkName one α, checkName_isName htop.1 _⟩
    have hc : IsForcingUnionClosedAt (A.ofName Q) (A.check α) :=
      (Defined.eval_iff _).mp ((A.formula_truth forcingUnionClosedAtFormula ![Q, c]).mpr ⟨p, hpG, hclosed⟩)
    have heS : A.ofName S = reverseInclusionOrder (A.ofName Q') :=
      (Defined.eval_iff _).mp ((A.formula_truth piOneReverseInclusionOrderFormula ![S, Q']).mpr ⟨p, hpG, hS⟩)
    have hfirst (i : V) (hi : i ∈ α) : kpair.π₁ (f ‘ i) ∈ G :=
      hG.1.2.2.1 p hpG _ (hpi i hi) (hpbelow i hi)
    have hm (i : V) (hi : i ∈ domain s) : A.ofName ⟨s ‘ i, hsn i hi⟩ ∈ A.ofName Q' := by
      have hiα : i ∈ α := hd ▸ hi
      have hfmem : kpair.π₁ (f ‘ i) ∈ atomicMembership P R (s ‘ i) Q'.val := by
        rw [hs i hiα]
        exact (mem_sep_iff.mp (hfi i hiα)).2
      have htmem : kpair.π₁ (f ‘ i) ∈ forcingFormula P R nameMemberFormula
          (standardTuple ![s ‘ i, Q'.val]) := by rwa [forcingFormula_nameMember]
      have he := (A.formula_truth nameMemberFormula ![⟨s ‘ i, hsn i hi⟩, Q']).mpr
        ⟨kpair.π₁ (f ‘ i), hfirst i hiα, htmem⟩
      simpa [nameMemberFormula] using he
    have hdir : IsForcingDirectedFamily (A.ofName Q') (reverseInclusionOrder (A.ofName Q'))
        (A.check α) (A.sequenceValue s hsn) := by
      refine ⟨by simpa only [hd] using A.sequenceValue_mem_function s hsn hm, ?_⟩
      intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := (A.mem_check_iff α x).mp hx
      obtain ⟨j, hj, rfl⟩ := (A.mem_check_iff α y).mp hy
      obtain ⟨k, hk, hki, hkj⟩ := hf.2 i hi j hj
      refine ⟨A.check k, (A.check_mem_iff _ _).mpr hk, ?_, ?_⟩
      all_goals rw [← heS, A.sequenceValue_value s hsn (hd.symm ▸ hk), A.sequenceValue_value s hsn (hd.symm ▸ ‹_ ∈ α›)]
      · have ho := ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hki).2.2.2
        have ho' : kpair.π₁ (f ‘ k) ∈ forcingFormula P R boundedPairMemberFormula
            (standardTuple ![S.val, s ‘ k, s ‘ i]) := by simpa only [hs k hk, hs i hi] using ho
        exact (Defined.eval_iff _).mp ((A.formula_truth boundedPairMemberFormula
          ![S, ⟨s ‘ k, hsn k (hd.symm ▸ hk)⟩, ⟨s ‘ i, hsn i (hd.symm ▸ hi)⟩]).mpr
          ⟨kpair.π₁ (f ‘ k), hfirst k hk, ho'⟩)
      · have ho := ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hkj).2.2.2
        have ho' : kpair.π₁ (f ‘ k) ∈ forcingFormula P R boundedPairMemberFormula
            (standardTuple ![S.val, s ‘ k, s ‘ j]) := by simpa only [hs k hk, hs j hj] using ho
        exact (Defined.eval_iff _).mp ((A.formula_truth boundedPairMemberFormula
          ![S, ⟨s ‘ k, hsn k (hd.symm ▸ hk)⟩, ⟨s ‘ j, hsn j (hd.symm ▸ hj)⟩]).mpr
          ⟨kpair.π₁ (f ‘ k), hfirst k hk, ho'⟩)
    have hu := A.saturated_sequence_union_bound hα hsn hsN Q hc hdir
    exact ⟨hu.1, fun i hi ↦ heS.symm ▸ hu.2 i hi⟩
  have hτQ : p ∈ atomicMembership P R τ.val Q.val := by
    rw [← forcingFormula_nameMember]
    apply forcingFormula_of_all_generics hR htop hp nameMemberFormula ![τ, Q]
    intro G hG hpG
    let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
    have hm := ((A.mem_saturatedName_iff _ Q _).mp (hgeneric G hG hpG).1).1
    simpa [nameMemberFormula] using hm
  have hcond : ⟨p, τ.val⟩ₖ ∈ twoStepConditions P R Q'.val t :=
    (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hp,
      mem_union_iff.mpr (Or.inl (forcingSaturatedName_mem_domain hτN hp τ.property hτQ)),
      forcingSaturatedName_forces_member hR hτN hp τ.property hτQ⟩
  refine ⟨hcond, fun i hi ↦ ?_⟩
  apply (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mpr
  refine ⟨hcond, hfi i hi, ?_, ?_⟩
  · simpa only [twoStepUnionBound, kpair.π₁_kpair] using hpbelow i hi
  · simp only [twoStepUnionBound, kpair.π₁_kpair, kpair.π₂_kpair]
    change p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S.val, τ.val, kpair.π₂ (f ‘ i)])
    rw [← hs i hi]
    apply forcingFormula_of_all_generics hR htop hp boundedPairMemberFormula ![S, τ, ⟨s ‘ i, hsn i (hd.symm ▸ hi)⟩]
    intro G hG hpG
    exact (Defined.eval_iff _).mpr ((hgeneric G hG hpG).2 i (hd.symm ▸ hi))

end ZFVP
