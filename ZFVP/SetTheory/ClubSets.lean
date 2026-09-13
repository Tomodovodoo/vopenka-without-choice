import ZFVP.SetTheory.FiniteCofinality
import ZFVP.SetTheory.NaturalIteration

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsUnboundedIn (C κ : V) : Prop := C ⊆ κ ∧ ∀ ξ ∈ κ, ∃ η ∈ C, ξ ∈ η

def IsClosedIn (C κ : V) : Prop := C ⊆ κ ∧
  ∀ δ ∈ κ, δ ≠ 0 → (∀ ξ ∈ δ, ∃ η ∈ C, η ∈ δ ∧ ξ ∈ η) → δ ∈ C

def IsClubIn (C κ : V) : Prop := IsClosedIn C κ ∧ IsUnboundedIn C κ

instance isUnboundedIn_definable : ℒₛₑₜ-relation[V] IsUnboundedIn := by
  unfold IsUnboundedIn
  definability

instance isClosedIn_definable : ℒₛₑₜ-relation[V] IsClosedIn := by
  unfold IsClosedIn
  definability

instance isClubIn_definable : ℒₛₑₜ-relation[V] IsClubIn := by
  unfold IsClubIn
  definability

theorem closed_inter {C D κ : V} (hC : IsClosedIn C κ) (hD : IsClosedIn D κ) :
    IsClosedIn (C ∩ D) κ := by
  refine ⟨fun x hx ↦ hC.1 x (mem_inter_iff.mp hx).1, ?_⟩
  intro δ hδ hn hcof
  apply mem_inter_iff.mpr
  constructor
  · apply hC.2 δ hδ hn
    intro ξ hξ
    obtain ⟨η, hη, hηδ, hξη⟩ := hcof ξ hξ
    exact ⟨η, (mem_inter_iff.mp hη).1, hηδ, hξη⟩
  · apply hD.2 δ hδ hn
    intro ξ hξ
    obtain ⟨η, hη, hηδ, hξη⟩ := hcof ξ hξ
    exact ⟨η, (mem_inter_iff.mp hη).2, hηδ, hξη⟩

noncomputable def nextIn (C ξ : V) : V := ⋂ˢ {η ∈ C ; ξ ∈ η}

instance nextIn_definable : ℒₛₑₜ-function₂[V] nextIn := by
  have h : ℒₛₑₜ-function₂[V] (fun C ξ ↦ {η ∈ C ; ξ ∈ η}) := by
    apply Language.Definable.of_iff (show ℒₛₑₜ-relation₃[V]
      (fun X C ξ ↦ ∀ η, η ∈ X ↔ η ∈ C ∧ ξ ∈ η) from by definability)
    intro v
    rw [mem_ext_iff]
    simp
  unfold nextIn
  definability

theorem nextIn_spec {C κ ξ : V} [IsOrdinal κ] (hC : IsUnboundedIn C κ) (hξ : ξ ∈ κ) :
    nextIn C ξ ∈ C ∧ ξ ∈ nextIn C ξ := by
  obtain ⟨η, hη, hξη⟩ := hC.2 ξ hξ
  let S : V := {η ∈ C ; ξ ∈ η}
  have : IsNonempty S := ⟨η, by simp [S, hη, hξη]⟩
  have h := IsOrdinal.sInter_mem (X := S)
    (fun η hη ↦ IsOrdinal.of_mem (hC.1 η (mem_sep_iff.mp hη).1))
  exact mem_sep_iff.mp h

theorem club_inter {C D κ : V} (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hC : IsClubIn C κ) (hD : IsClubIn D κ) : IsClubIn (C ∩ D) κ := by
  have : IsOrdinal κ := hκ.1.1
  refine ⟨closed_inter hC.1 hD.1, ⟨fun x hx ↦ hC.1.1 x (mem_inter_iff.mp hx).1, ?_⟩⟩
  intro ξ hξ
  let F : V → V := fun x ↦ nextIn D (nextIn C x)
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  have hstep (x : V) (hx : x ∈ κ) : F x ∈ κ ∧ x ∈ F x := by
    have hc := nextIn_spec hC.2 hx
    have hd := nextIn_spec hD.2 (hC.2.1 _ hc.1)
    have hfκ := hD.2.1 _ hd.1
    have : IsOrdinal (F x) := IsOrdinal.of_mem hfκ
    exact ⟨hfκ, IsOrdinal.toIsTransitive.transitive _ hd.2 x hc.2⟩
  let a := naturalIteration F hF ξ
  have ha (n : V) (hn : n ∈ (ω : V)) : a n ∈ κ :=
    naturalIteration_invariant F hF ξ (fun x ↦ x ∈ κ) (by definability) hξ
      (fun x hx ↦ (hstep x hx).1) n hn
  have hsucc (n : V) (hn : n ∈ (ω : V)) : a (succ n) = F (a n) := naturalIteration_succ F hF ξ hn
  have hinc (n : V) (hn : n ∈ (ω : V)) : a n ∈ a (succ n) := by
    rw [hsucc n hn]
    exact (hstep _ (ha n hn)).2
  let f := naturalIterationGraph F hF ξ
  have hf : f ∈ κ ^ (ω : V) := definableGraph_mem_function_of_mapsTo _ _ _ _ ha
  have hval (n : V) (hn : n ∈ (ω : V)) : f ‘ n = a n := naturalIterationGraph_value F hF ξ hn
  let δ := ⋃ˢ range f
  have hord : IsOrdinal δ := IsOrdinal.sUnion (fun x hx ↦ IsOrdinal.of_mem (range_subset_of_mem_function hf x hx))
  obtain ⟨ζ, hζ, hbound⟩ := regularCardinal_maps_bounded hκ hω hf
  have hδζ : δ ⊆ ζ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    obtain ⟨n, hny⟩ := mem_range_iff.mp hy
    have hn : n ∈ (ω : V) := domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem hny
    have hyζ : y ∈ ζ := value_eq_of_kpair_mem hny ▸ hbound n hn
    have : IsOrdinal ζ := IsOrdinal.of_mem hζ
    exact IsOrdinal.toIsTransitive.transitive y hyζ x hxy
  have hδ : δ ∈ κ := by
    have : IsOrdinal ζ := IsOrdinal.of_mem hζ
    rcases IsOrdinal.subset_iff.mp hδζ with heq | hlt
    · exact heq ▸ hζ
    · exact IsOrdinal.toIsTransitive.transitive ζ hζ δ hlt
  have harange (n : V) (hn : n ∈ (ω : V)) : a n ∈ range f := by
    rw [← hval n hn]
    exact mem_range_of_kpair_mem (kpair_value_mem (by simpa only [domain_eq_of_mem_function hf] using hn))
  have haδ (n : V) (hn : n ∈ (ω : V)) : a n ∈ δ :=
    mem_sUnion_iff.mpr ⟨a (succ n), harange _ (ω_succ_closed hn), hinc n hn⟩
  have hξδ : ξ ∈ δ := by simpa only [a, naturalIteration_zero] using haδ 0 (by simp)
  have hne : δ ≠ 0 := fun heq ↦ not_mem_empty (heq ▸ hξδ)
  have hcof (x : V) (hx : x ∈ δ) : ∃ n ∈ (ω : V), x ∈ a n := by
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    obtain ⟨n, hny⟩ := mem_range_iff.mp hy
    have hn : n ∈ (ω : V) := domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem hny
    exact ⟨n, hn, by rw [← hval n hn, value_eq_of_kpair_mem hny]; exact hxy⟩
  refine ⟨δ, mem_inter_iff.mpr ⟨?_, ?_⟩, hξδ⟩
  · apply hC.1.2 δ hδ hne
    intro x hx
    obtain ⟨n, hn, hxn⟩ := hcof x hx
    have hc := nextIn_spec hC.2 (ha n hn)
    have hd := nextIn_spec hD.2 (hC.2.1 _ hc.1)
    have hcδ : nextIn C (a n) ∈ δ := by
      apply IsOrdinal.toIsTransitive.transitive (a (succ n)) (haδ _ (ω_succ_closed hn))
      simpa only [hsucc n hn, F] using hd.2
    have : IsOrdinal (nextIn C (a n)) := IsOrdinal.of_mem (hC.2.1 _ hc.1)
    exact ⟨nextIn C (a n), hc.1, hcδ, IsOrdinal.toIsTransitive.transitive _ hc.2 x hxn⟩
  · apply hD.1.2 δ hδ hne
    intro x hx
    obtain ⟨n, hn, hxn⟩ := hcof x hx
    have hc := nextIn_spec hC.2 (ha n hn)
    have hd := nextIn_spec hD.2 (hC.2.1 _ hc.1)
    have hsD : a (succ n) ∈ D := by simpa only [hsucc n hn, F] using hd.1
    have : IsOrdinal (a (succ n)) := IsOrdinal.of_mem (ha _ (ω_succ_closed hn))
    exact ⟨a (succ n), hsD, haδ _ (ω_succ_closed hn),
      IsOrdinal.toIsTransitive.transitive _ (hinc n hn) x hxn⟩

end ZFVP
