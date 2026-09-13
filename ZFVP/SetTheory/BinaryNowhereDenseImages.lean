import ZFVP.SetTheory.BinaryClosedImages
import ZFVP.SetTheory.BinaryCylinderIntervals
import ZFVP.SetTheory.CantorInfiniteOnes

/-! Closed nowhere dense binary tree bodies have nowhere dense real images. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem realInterval_strict_refinement {a b u v : V}
    (ha : a ∈ internalRationals V) (hb : b ∈ internalRationals V)
    (hu : u ∈ internalRationals V) (hv : v ∈ internalRationals V)
    (huv : InternalRationalLT u v) (hsub : realInterval u v ⊆ realInterval a b) :
    ∃ r ∈ internalRationals V, ∃ t ∈ internalRationals V,
      InternalRationalLT a r ∧ InternalRationalLT r t ∧ InternalRationalLT t b ∧
        realInterval r t ⊆ realInterval u v := by
  obtain ⟨r, hr, hur, hrv⟩ := internalRational_dense hu hv huv
  obtain ⟨t, ht, hrt, htv⟩ := internalRational_dense hr hv hrv
  have hut := internalRationalLT_trans hu hr ht hur hrt
  have hri : rationalCut r ∈ realInterval u v := (mem_realInterval_iff _ _ _).mpr
    ⟨rationalCut_isCut hr, (rationalCut_lt_iff hu hr).mpr hur, (rationalCut_lt_iff hr hv).mpr hrv⟩
  have hti : rationalCut t ∈ realInterval u v := (mem_realInterval_iff _ _ _).mpr
    ⟨rationalCut_isCut ht, (rationalCut_lt_iff hu ht).mpr hut, (rationalCut_lt_iff ht hv).mpr htv⟩
  have har := (rationalCut_lt_iff ha hr).mp ((mem_realInterval_iff _ _ _).mp (hsub _ hri)).2.1
  have htb := (rationalCut_lt_iff ht hb).mp ((mem_realInterval_iff _ _ _).mp (hsub _ hti)).2.2
  exact ⟨r, hr, t, ht, har, hrt, htb,
    realInterval_mono (⟨r, hr⟩ : InternalRational V) ⟨t, ht⟩ ⟨u, hu⟩ ⟨v, hv⟩
      (le_of_lt hur) (le_of_lt htv)⟩

def IsRealNowhereDense (P : V) : Prop := P ⊆ dedekindReals V ∧
  ∀ a ∈ internalRationals V, ∀ b ∈ internalRationals V, InternalRationalLT a b →
    ∃ r ∈ internalRationals V, ∃ t ∈ internalRationals V,
      InternalRationalLT a r ∧ InternalRationalLT r t ∧ InternalRationalLT t b ∧
        ∀ x ∈ realInterval r t, x ∉ P

instance isRealNowhereDense_definable : ℒₛₑₜ-predicate[V] IsRealNowhereDense := by
  unfold IsRealNowhereDense
  definability

theorem binaryNowhereDenseImage_interval {T a b : V} (hT : IsNowhereDenseTree T)
    (ha : a ∈ internalRationals V) (hb : b ∈ internalRationals V) (hab : InternalRationalLT a b) :
    ∃ u ∈ internalRationals V, ∃ v ∈ internalRationals V, InternalRationalLT u v ∧
      realInterval u v ⊆ realInterval a b ∧ ∀ x ∈ realInterval u v, x ∉ binaryImage (treeBody T) := by
  by_cases h : ∃ x ∈ realInterval a b, x ∈ binaryImage (treeBody T)
  · obtain ⟨x, hxi, hxI⟩ := h
    obtain ⟨c, hc, rfl⟩ := (mem_binaryImage_iff _ _).mp hxI
    have hcC := treeBody_subset_cantorSpace T c hc
    obtain ⟨n, hn, hlo, hup⟩ := binaryPrefixEnds_inside hcC ha hb hxi
    have hs := restrict_mem_binarySequences hcC hn
    obtain ⟨t, ht, hst, htT⟩ := hT.2 _ hs
    let d := cantorOneTail t
    have hd : d ∈ cantorSpace V := cantorOneTail_mem t
    have htd : t ⊆ d := cantorOneTail_extends ht
    have hm : domain t ∈ (ω : V) := binarySequence_domain_mem ht
    have heq : d ↾ (domain t) = t := (subset_iff_restrict_eq hd ht).mp htd
    refine ⟨binaryValue d (domain t), binaryValue_mem hd hm,
      binaryUpper d (domain t), binaryUpper_mem hd hm, binaryValue_lt_upper hd hm hm, ?_, ?_⟩
    · intro z hzi
      obtain ⟨e, he, rfl, hde⟩ := binaryInterval_surjective_prefix hd hm hzi
      rw [heq] at hde
      exact binaryReal_interval_of_prefix hcC he hn ha hb hlo hup (subset_trans hst hde)
    · intro z hzi hzI
      obtain ⟨e, he, rfl⟩ := (mem_binaryImage_iff _ _).mp hzI
      have heC := treeBody_subset_cantorSpace T e he
      have hpref := binaryInterval_preimage_prefix hd heC hm hzi
      rw [heq] at hpref
      exact htT (hpref ▸ ((mem_treeBody_iff _ _).mp he).2 _ hm)
  · exact ⟨a, ha, b, hb, hab, subset_refl _, fun x hxi hxI ↦ h ⟨x, hxi, hxI⟩⟩

theorem binaryNowhereDenseImage_nowhereDense {T : V} (hT : IsNowhereDenseTree T) :
    IsRealNowhereDense (binaryImage (treeBody T)) := by
  refine ⟨binaryImage_subset_reals (treeBody_subset_cantorSpace T), ?_⟩
  intro a ha b hb hab
  obtain ⟨u, hu, v, hv, huv, hsub, havoid⟩ := binaryNowhereDenseImage_interval hT ha hb hab
  obtain ⟨r, hr, t, ht, har, hrt, htb, hrtuv⟩ := realInterval_strict_refinement ha hb hu hv huv hsub
  exact ⟨r, hr, t, ht, har, hrt, htb, fun x hx ↦ havoid x (hrtuv x hx)⟩

end ZFVP
