import ZFVP.ModelTheory.PrefixRestorationForcingThreshold
import ZFVP.ModelTheory.RankWoodinPrefixCutoff
import ZFVP.ModelTheory.WoodinStrictPrefixCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsPrefixRestorationForcingThreshold.rank_cutoff_iff {ξ β : V}
    (hξ : IsChoicelessInaccessible ξ) (hβξ : β ∈ ξ) :
    letI := hξ.1
    letI := rankDomain_nonempty hξ.2.1
    letI := hξ.rankCriterion.models_zf
    ∀ P R one κ γ : SetDomain (hierarchy ξ),
      IsPrefixRestorationForcingThreshold P.val R.val one.val κ.val γ.val β →
      (IsWoodinPrefixCutoff P R one κ γ ↔ IsWoodinPrefixCutoff P.val R.val one.val κ.val γ.val) := by
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  intro P R one κ γ h
  have hk : checkName one.val κ.val ∈ hierarchy ξ := by
    have he := TransitiveZF.checkName_val (hierarchy ξ) one κ
    exact he ▸ (checkName one κ).property
  have hg : checkName one.val γ.val ∈ hierarchy ξ := by
    have he := TransitiveZF.checkName_val (hierarchy ξ) one γ
    exact he ▸ (checkName one γ).property
  exact rank_woodinPrefixCutoff_iff_of_forcing_eq
    (fun _ hb ↦ regularCardinal_succ_closed hξ.regular hb) P R one κ γ
    (h.forcing_eq hβξ hξ P.property hk hg)

theorem IsWoodinSupercompact.eventually_rank_woodinPrefixCutoff_eq {δ P R one κ : V}
    (hδ : IsWoodinSupercompact δ) (hord : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hP : P ∈ hierarchy δ) (hR : R ∈ hierarchy δ) (hκδ : κ ∈ δ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
    (hDC : ∀ p ∈ P, p ∈ forcingFormula P R dependentChoiceBelowFormula (standardTuple ![checkName one κ])) :
    ∃ η ∈ δ, κ ∈ η ∧ ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ p r o k : SetDomain (hierarchy ξ), p.val = P → r.val = R → o.val = one → k.val = κ →
        (woodinPrefixCutoff p r o k).val = woodinPrefixCutoff P R one κ := by
  let := hδ.1.1
  let c := woodinPrefixCutoff P R one κ
  have hcδ : c ∈ δ := woodinPrefixCutoff_lt_supercompact hδ hord htop hP hR hκδ hκ hDC
  obtain ⟨a, _, ha⟩ := hδ.strictPrefixCutoff hord htop hP hR hκδ hκ hDC
  have hc := woodinPrefixCutoff_spec ha
  let : IsOrdinal c := hc.1
  obtain ⟨η, hηδ, hall⟩ := hδ.bounded_prefixRestorationForcingThreshold hP hκδ
    (regularCardinal_succ_closed hδ.inaccessible.regular hcδ) hord htop hκ
  have htc := hall c (mem_succ_self c)
  let := IsOrdinal.of_mem hηδ
  refine ⟨η, hηδ, IsOrdinal.toIsTransitive.mem_trans hc.2.1.1 htc.1, ?_⟩
  intro ξ hηξ hξ
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  intro p r o k hp hr ho hk
  have hcξ : c ∈ ξ := IsOrdinal.toIsTransitive.mem_trans htc.1 hηξ
  let d : SetDomain (hierarchy ξ) := ⟨c, ordinal_mem_hierarchy_iff.mpr hcξ⟩
  have hdord : IsOrdinal d := (TransitiveZF.ordinal_iff (hierarchy ξ) d).mpr inferInstance
  let := hdord
  have hagree (b : SetDomain (hierarchy ξ)) (hb : b.val ∈ succ c) :
      IsWoodinPrefixCutoff p r o k b ↔ IsWoodinPrefixCutoff P R one κ b.val := by
    have ht : IsPrefixRestorationForcingThreshold p.val r.val o.val k.val b.val η := by
      simpa only [hp, hr, ho, hk] using hall b.val hb
    have he := ht.rank_cutoff_iff hξ hηξ p r o k b
    simpa only [hp, hr, ho, hk] using he
  have hd : IsWoodinPrefixCutoff p r o k d := (hagree d (mem_succ_self c)).mpr hc.2.1
  have hleast : IsLeastOrdinal (IsWoodinPrefixCutoff p r o k) d := by
    refine ⟨hdord, hd, ?_⟩
    intro b hb hbrest
    let := hb
    rcases IsOrdinal.mem_trichotomy d b with hdb | he | hbd
    · exact IsOrdinal.toIsTransitive.transitive _ hdb
    · exact he ▸ subset_refl _
    · have hbc : b.val ∈ c := hbd
      have hbc' : b.val ∈ succ c := mem_succ_iff.mpr (Or.inr hbc)
      have hbrest' := (hagree b hbc').mp hbrest
      have hbOrd := (TransitiveZF.ordinal_iff (hierarchy ξ) b).mp hb
      have hcb := hc.2.2 b.val hbOrd hbrest'
      exact False.elim (mem_irrefl b.val (hcb b.val hbc))
  have hi := woodinPrefixCutoff_spec hd
  have he : woodinPrefixCutoff p r o k = d := subset_antisymm
    (hi.2.2 d hdord hd) (hleast.2.2 _ hi.1 hi.2.1)
  exact congrArg Subtype.val he

end ZFVP
