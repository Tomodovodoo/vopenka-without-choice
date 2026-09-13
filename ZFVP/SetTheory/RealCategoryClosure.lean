import ZFVP.SetTheory.RealCategoryCodes

/-! Finite category operations on actual internal real sets and their codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem realInterval_isOpen {a b : V} (ha : a ∈ internalRationals V) (hb : b ∈ internalRationals V) :
    IsRealOpen (realInterval a b) :=
  realOpen_of_neighborhoods (fun _ hx ↦ ⟨a, ha, b, hb, realInterval_order ha hb hx, hx, subset_refl _⟩)

theorem isRealOpen_inter {U W : V} (hU : IsRealOpen U) (hW : IsRealOpen W) : IsRealOpen (U ∩ W) := by
  apply realOpen_of_neighborhoods
  intro x hx
  obtain ⟨hxU, hxW⟩ := mem_inter_iff.mp hx
  obtain ⟨a, ha, b, hb, _, hxi, hiU⟩ := realOpen_neighborhood hU hxU
  obtain ⟨c, hc, d, hd, _, hxj, hjW⟩ := realOpen_neighborhood hW hxW
  obtain ⟨r, hr, t, ht, hxrt, hri, hrj⟩ := realInterval_refine_inter ha hb hc hd hxi hxj
  exact ⟨r, hr, t, ht, realInterval_order hr ht hxrt, hxrt,
    fun z hz ↦ mem_inter_iff.mpr ⟨hiU z (hri z hz), hjW z (hrj z hz)⟩⟩

theorem realComplement_union_open {P Q : V}
    (hP : IsRealOpen ((dedekindReals V) \ P)) (hQ : IsRealOpen ((dedekindReals V) \ Q)) :
    IsRealOpen ((dedekindReals V) \ (P ∪ Q)) := by
  have he : ((dedekindReals V) \ (P ∪ Q)) =
      ((dedekindReals V) \ P) ∩ ((dedekindReals V) \ Q) := by
    apply mem_ext
    intro x
    simp only [mem_sdiff_iff, mem_union_iff, mem_inter_iff]
    tauto
  rw [he]
  exact isRealOpen_inter hP hQ

theorem realNowhereDense_union {P Q : V} (hP : IsRealNowhereDense P) (hQ : IsRealNowhereDense Q) :
    IsRealNowhereDense (P ∪ Q) := by
  refine ⟨fun x hx ↦ (mem_union_iff.mp hx).elim (hP.1 x) (hQ.1 x), ?_⟩
  intro a ha b hb hab
  obtain ⟨r, hr, t, ht, har, hrt, htb, havoidP⟩ := hP.2 a ha b hb hab
  obtain ⟨u, hu, v, hv, hru, huv, hvt, havoidQ⟩ := hQ.2 r hr t ht hrt
  have hsub := realInterval_mono (⟨u, hu⟩ : InternalRational V) ⟨v, hv⟩ ⟨r, hr⟩ ⟨t, ht⟩
    (le_of_lt hru) (le_of_lt hvt)
  refine ⟨u, hu, v, hv, internalRationalLT_trans ha hr hu har hru, huv,
    internalRationalLT_trans hv ht hb hvt htb, ?_⟩
  intro x hx hxPQ
  exact (mem_union_iff.mp hxPQ).elim (havoidP x (hsub x hx)) (havoidQ x hx)

theorem realSingleton_complement_open {p : V} (hp : IsDedekindCut p) :
    IsRealOpen ((dedekindReals V) \ {p}) := by
  apply realOpen_of_neighborhoods
  intro x hx
  obtain ⟨hxR, hxp⟩ := mem_sdiff_iff.mp hx
  have hxCut := (mem_dedekindReals_iff _).mp hxR
  have hne : x ≠ p := fun he ↦ hxp (mem_singleton_iff.mpr he)
  obtain ⟨a, ha, b, hb, u, _, v, _, hxi, hpi, hdis⟩ := realIntervals_separate hxCut hp hne
  exact ⟨a, ha, b, hb, realInterval_order ha hb hxi, hxi, fun z hz ↦
    mem_sdiff_iff.mpr ⟨realInterval_subset_reals _ _ z hz,
      fun hzp ↦ hdis p hpi ((mem_singleton_iff.mp hzp) ▸ hz)⟩⟩

theorem realSingleton_nowhereDense {p : V} (hp : IsDedekindCut p) : IsRealNowhereDense ({p} : V) := by
  refine ⟨fun x hx ↦ (mem_singleton_iff.mp hx).symm ▸ (mem_dedekindReals_iff _).mpr hp, ?_⟩
  intro a ha b hb hab
  obtain ⟨q, hq, haq, hqb⟩ := internalRational_dense ha hb hab
  have hex : ∃ u ∈ internalRationals V, ∃ v ∈ internalRationals V, InternalRationalLT u v ∧
      realInterval u v ⊆ realInterval a b ∧ p ∉ realInterval u v := by
    by_cases hpq : p ⊆ rationalCut q
    · refine ⟨q, hq, b, hb, hqb,
        realInterval_mono ⟨q, hq⟩ ⟨b, hb⟩ ⟨a, ha⟩ ⟨b, hb⟩ (le_of_lt haq) (le_refl _), ?_⟩
      intro hpi
      have hlt := ((mem_realInterval_iff _ _ _).mp hpi).2.1
      exact dedekindLT_irrefl _ (dedekindLT_of_lt_of_subset hlt hpq)
    · have hqp := (dedekindCuts_comparable hp (rationalCut_isCut hq)).resolve_left hpq
      refine ⟨a, ha, q, hq, haq,
        realInterval_mono ⟨a, ha⟩ ⟨q, hq⟩ ⟨a, ha⟩ ⟨b, hb⟩ (le_refl _) (le_of_lt hqb), ?_⟩
      intro hpi
      have hlt := ((mem_realInterval_iff _ _ _).mp hpi).2.2
      exact dedekindLT_irrefl _ (dedekindLT_of_lt_of_subset hlt hqp)
  obtain ⟨u, hu, v, hv, huv, hsub, hpI⟩ := hex
  obtain ⟨r, hr, t, ht, har, hrt, htb, hrtuv⟩ := realInterval_strict_refinement ha hb hu hv huv hsub
  exact ⟨r, hr, t, ht, har, hrt, htb, fun x hx hxp ↦ hpI
    ((mem_singleton_iff.mp hxp) ▸ hrtuv x hx)⟩

theorem realClosedFrom_complement_open {S : V} (hS : S ⊆ realBasicCodes V) :
    IsRealOpen ((dedekindReals V) \ realClosedFrom S) := by
  have he : ((dedekindReals V) \ realClosedFrom S) = realOpenFrom S := by
    apply mem_ext
    intro x
    simp only [mem_sdiff_iff, mem_realClosedFrom_iff, mem_dedekindReals_iff]
    have hcut : x ∈ realOpenFrom S → IsDedekindCut x := fun hx ↦ ((mem_realOpenFrom_iff _ _).mp hx).1
    tauto
  rw [he]
  exact realOpenFrom_isOpen hS

theorem isRealMeagre_union_closed_nowhereDense {A P : V} (hA : IsRealMeagre A)
    (hP : IsRealNowhereDense P) (hPo : IsRealOpen ((dedekindReals V) \ P)) : IsRealMeagre (A ∪ P) := by
  obtain ⟨f, hf, hfn, hcover⟩ := hA
  let F : V → V := fun n ↦ realClosedCode (realClosedFrom (f ‘ n) ∪ P)
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  have hspec : ∀ n ∈ (ω : V), realClosedFrom (F n) = realClosedFrom (f ‘ n) ∪ P := by
    intro n hn
    apply realClosedCode_spec (realNowhereDense_union (hfn n hn) hP).1
    exact realComplement_union_open
      (realClosedFrom_complement_open (mem_power_iff.mp (function_value_mem hf hn))) hPo
  refine ⟨definableGraph (ω : V) F hF,
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ _ ↦ mem_power_iff.mpr (realClosedCode_subset _)), ?_, ?_⟩
  · intro n hn
    rw [value_definableGraph _ _ _ hn, hspec n hn]
    exact realNowhereDense_union (hfn n hn) hP
  · intro x hx
    rcases mem_union_iff.mp hx with hxA | hxP
    · obtain ⟨n, hn, hxn⟩ := hcover x hxA
      refine ⟨n, hn, ?_⟩
      rw [value_definableGraph _ _ _ hn, hspec n hn]
      exact mem_union_iff.mpr (Or.inl hxn)
    · refine ⟨0, by simp, ?_⟩
      rw [value_definableGraph _ _ _ (show (0 : V) ∈ ω by simp), hspec 0 (by simp)]
      exact mem_union_iff.mpr (Or.inr hxP)

end ZFVP
