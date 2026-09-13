import ZFVP.ModelTheory.RankHartogsRestorationThreshold
import ZFVP.ModelTheory.StrictHartogsCutoffTransfer

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.eventually_rank_hartogsPrefixCutoff_eq {δ P R one κ : V}
    (hδ : IsWoodinSupercompact δ) (hord : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hP : P ∈ hierarchy δ) (hR : R ∈ hierarchy δ) (hκδ : κ ∈ δ)
    (hsmall : ∀ γ : V, IsChoicelessInaccessible γ → κ ∈ γ → P ∈ hierarchy γ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![hartogsNumberName P R (checkName one κ)]))
    (hDC : ∀ p ∈ P, p ∈ forcingFormula P R dependentChoiceBelowFormula
      (standardTuple ![hartogsNumberName P R (checkName one κ)])) :
    ∃ η ∈ δ, κ ∈ η ∧ ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ p r o k : SetDomain (hierarchy ξ), p.val = P → r.val = R → o.val = one → k.val = κ →
        (woodinNamedPrefixCutoff p r o k (hartogsNumberName p r (checkName o k))).val =
          woodinNamedPrefixCutoff P R one κ (hartogsNumberName P R (checkName one κ)) := by
  let := hδ.1.1
  let c := woodinNamedPrefixCutoff P R one κ (hartogsNumberName P R (checkName one κ))
  obtain ⟨a, haδ, ha⟩ := hδ.strictHartogsPrefixCutoff hord htop hP hR hκδ hκ hDC
  have hc := woodinNamedPrefixCutoff_spec ha
  let : IsOrdinal c := hc.1
  let := IsOrdinal.of_mem haδ
  have hcδ : c ∈ δ := ordinal_mem_of_subset_mem (woodinNamedPrefixCutoff_le ha) haδ
  obtain ⟨η, hηδ, hall⟩ := hδ.bounded_hartogsRestorationRankThreshold hP
    (regularCardinal_succ_closed hδ.inaccessible.regular hcδ) hord htop hκ
  have htc := hall c (mem_succ_self c) hc.2.1.1 hc.2.1.2.1
    (hsmall c hc.2.1.2.1 hc.2.1.1)
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
      IsWoodinNamedPrefixCutoff p r o k (hartogsNumberName p r (checkName o k)) b ↔
        IsWoodinNamedPrefixCutoff P R one κ (hartogsNumberName P R (checkName one κ)) b.val := by
    by_cases hgood : κ ∈ b.val ∧ IsChoicelessInaccessible b.val
    · have ht : IsHartogsRestorationRankThreshold p.val r.val o.val k.val b.val η := by
        simpa only [hp, hr, ho, hk] using
          hall b.val hb hgood.1 hgood.2 (hsmall b.val hgood.2 hgood.1)
      have he := ht.rank_cutoff_iff hξ hηξ p r o k b
      simpa only [hp, hr, ho, hk] using he
    · constructor
      · intro hh
        have hbκ : κ ∈ b.val := hk ▸ hh.1
        have hbi := (rank_choicelessInaccessible_iff
          (fun _ hc ↦ regularCardinal_succ_closed hξ.regular hc) b).mp hh.2.1
        exact False.elim (hgood ⟨hbκ, hbi⟩)
      · intro hh
        exact False.elim (hgood ⟨hh.1, hh.2.1⟩)
  have hd : IsWoodinNamedPrefixCutoff p r o k (hartogsNumberName p r (checkName o k)) d :=
    (hagree d (mem_succ_self c)).mpr hc.2.1
  have hleast : IsLeastOrdinal
      (IsWoodinNamedPrefixCutoff p r o k (hartogsNumberName p r (checkName o k))) d := by
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
  have hi := woodinNamedPrefixCutoff_spec hd
  have he : woodinNamedPrefixCutoff p r o k (hartogsNumberName p r (checkName o k)) = d := subset_antisymm
    (hi.2.2 d hdord hd) (hleast.2.2 _ hi.1 hi.2.1)
  exact congrArg Subtype.val he

end ZFVP

