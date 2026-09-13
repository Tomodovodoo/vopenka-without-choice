import ZFVP.SetTheory.LevyCollapseSupport
import ZFVP.ModelTheory.ForcingModel

/-! The subcollapse `Coll(ω, <β)` inside `Coll(ω, <κ)`: cutting a generic filter below `β`
gives a generic filter for the subcollapse, so both collapses provide forcing contexts over
the same ground. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem levyCut_mono {β p q : V} (h : p ⊆ q) : levyCut β p ⊆ levyCut β q := by
  intro z hz
  obtain ⟨hzp, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
  exact mem_restrict_iff.mpr ⟨h _ hzp, x, hx, y, rfl⟩

theorem levyCut_eq_self {β p : V} (hp : p ∈ levyCollapse β) : levyCut β p = p :=
  levyCut_eq_of_support hp (ordinalSupport_subset hp)

theorem levyCut_le {κ β p : V} (hp : p ∈ levyCollapse κ) : ⟨p, levyCut β p⟩ₖ ∈ levyOrder κ :=
  (pair_mem_reverseInclusionOrder _ _ _).mpr
    ⟨hp, levyCollapse_subset hp (levyCut_subset β p), levyCut_subset β p⟩

/-- The part of a generic filter lying in the subcollapse. -/
def levySubGeneric (β : V) (G : Set V) : Set V := {p | p ∈ G ∧ p ∈ levyCollapse β}

theorem levySubGeneric_generic {κ β : V} [IsOrdinal β] (hβ : β ⊆ κ) {G : Set V}
    (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G) :
    IsExternalForcingGeneric (levyCollapse β) (levyOrder β) (levySubGeneric β G) := by
  have hup : ∀ p ∈ G, ∀ q ∈ levyCollapse κ, q ⊆ p → q ∈ G := fun p hp q hq hqp ↦
    hG.1.2.2.1 p hp q hq ((pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hG.1.1 p hp, hq, hqp⟩)
  refine ⟨⟨fun p hp ↦ hp.2, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨p, hp⟩ := hG.1.2.1
    exact ⟨∅, hup p hp ∅ (empty_mem_levyCollapse κ) (empty_subset _), empty_mem_levyCollapse β⟩
  · intro p hp q hq hpq
    exact ⟨hup p hp.1 q (levyCollapse_mono hβ _ hq) ((pair_mem_reverseInclusionOrder _ _ _).mp hpq).2.2, hq⟩
  · intro p hp q hq
    obtain ⟨r, hr, hrp, hrq⟩ := hG.1.2.2.2 p hp.1 q hq.1
    have hrκ := hG.1.1 r hr
    have hcut : levyCut β r ∈ levyCollapse β := levyCut_mem hrκ
    refine ⟨levyCut β r, ⟨hup r hr _ (levyCollapse_mono hβ _ hcut) (levyCut_subset β r), hcut⟩, ?_, ?_⟩
    · refine (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hcut, hp.2, ?_⟩
      rw [← levyCut_eq_self hp.2]
      exact levyCut_mono ((pair_mem_reverseInclusionOrder _ _ _).mp hrp).2.2
    · refine (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hcut, hq.2, ?_⟩
      rw [← levyCut_eq_self hq.2]
      exact levyCut_mono ((pair_mem_reverseInclusionOrder _ _ _).mp hrq).2.2
  · intro D hD
    have hE : ForcingDense (levyCollapse κ) (levyOrder κ) {r ∈ levyCollapse κ ; ∃ d ∈ D, d ⊆ r} := by
      refine ⟨sep_subset, fun p hp ↦ ?_⟩
      obtain ⟨d, hd, hdp⟩ := hD.2 (levyCut β p) (levyCut_mem hp)
      have hdβ : d ∈ levyCollapse β := hD.1 d hd
      have hdκ : d ∈ levyCollapse κ := levyCollapse_mono hβ _ hdβ
      have hcd : levyCut β p ⊆ d := ((pair_mem_reverseInclusionOrder _ _ _).mp hdp).2.2
      have hdfun : IsFunction d :=
        ((mem_finitePartialFunctions _ _ d).mp (levyCollapse_finitePartialFunction hdβ)).2.1
      have hu : d ∪ p ∈ levyCollapse κ := by
        apply levyCollapse_union hdκ hp
        intro x y z hxy hxz
        have hsub := ((mem_finitePartialFunctions _ _ d).mp (levyCollapse_finitePartialFunction hdβ)).1
        have hxβ : x ∈ (ω : V) ×ˢ β := (kpair_mem_iff.mp (hsub _ hxy)).1
        have hxz' : ⟨x, z⟩ₖ ∈ d := hcd _ ((kpair_mem_levyCut_iff β p x z).mpr ⟨hxz, hxβ⟩)
        exact IsFunction.unique (hf := hdfun) hxy hxz'
      exact ⟨d ∪ p, mem_sep_iff.mpr ⟨hu, d, hd, subset_union_left d p⟩,
        (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hu, hp, subset_union_right d p⟩⟩
    obtain ⟨r, hr, hrE⟩ := hG.2 _ hE
    obtain ⟨_, d, hd, hdr⟩ := mem_sep_iff.mp hrE
    have hdβ : d ∈ levyCollapse β := hD.1 d hd
    exact ⟨d, ⟨hup r hr d (levyCollapse_mono hβ _ hdβ) hdr, hdβ⟩, hd⟩

/-- The forcing context of the Levy collapse with an external generic. -/
noncomputable def levyContext (κ : V) {G : Set V}
    (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G) : ForcingContext V where
  P := levyCollapse κ
  R := levyOrder κ
  one := ∅
  G := G
  order := (levyCollapse_poset κ).1
  top := levyCollapse_top κ
  generic := hG

/-- The forcing context of the subcollapse below `β` with the cut generic. -/
noncomputable def levySubContext {κ : V} (β : V) [IsOrdinal β] (hβ : β ⊆ κ) {G : Set V}
    (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G) : ForcingContext V where
  P := levyCollapse β
  R := levyOrder β
  one := ∅
  G := levySubGeneric β G
  order := (levyCollapse_poset β).1
  top := levyCollapse_top β
  generic := levySubGeneric_generic hβ hG

end ZFVP
