import ZFVP.ModelTheory.WoodinBoundedLocalRestorationAgreement
import ZFVP.ModelTheory.TransitiveZFInaccessible
import ZFVP.ModelTheory.WoodinStrictRestoration

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinRestorationCutoff_iff_local (κ γ : V) :
    IsWoodinRestorationCutoff κ γ ↔ κ ∈ γ ∧ IsChoicelessInaccessible γ ∧ IsWoodinLocalRestoration κ γ := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.1.1, h.2.2⟩
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.2⟩

theorem rank_restorationCutoff_iff {ξ : V} [IsOrdinal ξ]
    [Nonempty (SetDomain (hierarchy ξ))] [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hs : ∀ β ∈ ξ, succ β ∈ ξ) (k d : SetDomain (hierarchy ξ))
    (hlocal : IsWoodinLocalRestoration k d ↔ IsWoodinLocalRestoration k.val d.val) :
    IsWoodinRestorationCutoff k d ↔ IsWoodinRestorationCutoff k.val d.val := by
  rw [woodinRestorationCutoff_iff_local, woodinRestorationCutoff_iff_local]
  exact and_congr Iff.rfl (and_congr (rank_choicelessInaccessible_iff hs d) hlocal)

theorem IsWoodinSupercompact.eventually_rank_woodinRestorationCutoff_eq {δ κ : V}
    (hδ : IsWoodinSupercompact δ) (hκ : IsRegularCardinal κ) (hκδ : κ ∈ δ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α) :
    ∃ η ∈ δ, κ ∈ η ∧ ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ k : SetDomain (hierarchy ξ), k.val = κ →
        (woodinRestorationCutoff k).val = woodinRestorationCutoff κ := by
  let := hδ.1.1
  let c := woodinRestorationCutoff κ
  have hcδ : c ∈ δ := woodinRestorationCutoff_lt_supercompact hκ hδ hκδ hDC
  have hc := woodinRestorationCutoff_spec (hδ.restorationCutoff hκ hκδ hDC)
  obtain ⟨η, hηδ, hall⟩ := hδ.bounded_localRestorationRankThreshold hκ hκδ
    (regularCardinal_succ_closed hδ.inaccessible.regular hcδ)
  have htc := hall c (mem_succ_self c)
  refine ⟨η, hηδ, htc.1, ?_⟩
  intro ξ hηξ hξ
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  intro k hk
  have hs : ∀ β ∈ ξ, succ β ∈ ξ := fun _ hβ ↦ regularCardinal_succ_closed hξ.regular hβ
  have hcξ : c ∈ ξ := IsOrdinal.toIsTransitive.mem_trans htc.2.1 hηξ
  let d : SetDomain (hierarchy ξ) := ⟨c, ordinal_mem_hierarchy_iff.mpr hcξ⟩
  have hdord : IsOrdinal d := (TransitiveZF.ordinal_iff (hierarchy ξ) d).mpr inferInstance
  let := hdord
  have hagree (b : SetDomain (hierarchy ξ)) (hb : b.val ∈ succ c) :
      IsWoodinRestorationCutoff k b ↔ IsWoodinRestorationCutoff κ b.val := by
    have hl := ((localRestorationRankThreshold_iff κ b.val η).mp (hall b.val hb)).2.2
      ξ hηξ hξ k b hk rfl
    have he := rank_restorationCutoff_iff hs k b (by simpa only [hk] using hl)
    simpa only [hk] using he
  have hd : IsWoodinRestorationCutoff k d := (hagree d (mem_succ_self c)).mpr hc.2.1
  have hleast : IsLeastOrdinal (IsWoodinRestorationCutoff k) d := by
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
  have hi := woodinRestorationCutoff_spec hd
  have he : woodinRestorationCutoff k = d := subset_antisymm
    (hi.2.2 d hdord hd) (hleast.2.2 _ hi.1 hi.2.1)
  exact congrArg Subtype.val he

end ZFVP
