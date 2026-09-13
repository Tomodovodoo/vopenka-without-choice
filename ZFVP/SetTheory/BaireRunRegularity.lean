import ZFVP.SetTheory.BaireRunTrees
import ZFVP.SetTheory.CountableSets

/-! Transfer of category regularity from Cantor space to the manuscript's Baire space. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def baireRunImage (A : V) : V := repl baireRunCode (by definability) A

theorem mem_baireRunImage_iff (A x : V) :
    x ∈ baireRunImage A ↔ ∃ a ∈ A, x = baireRunCode a := repl_spec (by definability)

instance baireRunImage_definable : ℒₛₑₜ-function₁[V] baireRunImage := by
  have h : ℒₛₑₜ-relation (fun B A : V ↦ ∀ x, x ∈ B ↔ ∃ a ∈ A, x = baireRunCode a) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [mem_baireRunImage_iff]

theorem baireRunImage_subset_infiniteOnes {A : V} (hA : A ⊆ baireSpace V) :
    baireRunImage A ⊆ cantorInfiniteOnes V := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (mem_baireRunImage_iff A x).mp hx
  exact baireRunCode_infiniteOnes (hA a ha)

theorem baireRunImage_subset_cantor {A : V} (hA : A ⊆ baireSpace V) :
    baireRunImage A ⊆ cantorSpace V :=
  fun x hx ↦ ((mem_cantorInfiniteOnes_iff x).mp (baireRunImage_subset_infiniteOnes hA x hx)).1

theorem baireRunCode_mem_image_iff {A a : V} (hA : A ⊆ baireSpace V) (ha : a ∈ baireSpace V) :
    baireRunCode a ∈ baireRunImage A ↔ a ∈ A := by
  constructor
  · intro h
    obtain ⟨b, hb, he⟩ := (mem_baireRunImage_iff A _).mp h
    exact baireRunCode_injective ha (hA b hb) he ▸ hb
  · intro h
    exact (mem_baireRunImage_iff A _).mpr ⟨a, h, rfl⟩

theorem baireRunImage_countable_iff {A : V} (hA : A ⊆ baireSpace V) :
    IsInternallyCountable (baireRunImage A) ↔ IsInternallyCountable A := by
  constructor
  · intro h
    have hle : A ≤# baireRunImage A := cardLE_of_injective_map baireRunCode (by definability)
      (fun a ha ↦ (mem_baireRunImage_iff A _).mpr ⟨a, ha, rfl⟩)
      (fun a ha b hb he ↦ baireRunCode_injective (hA a ha) (hA b hb) he)
    exact hle.trans h
  · exact internallyCountable_repl baireRunCode (by definability)

noncomputable def baireRunPreimage (A : V) : V := {a ∈ baireSpace V ; baireRunCode a ∈ A}

theorem mem_baireRunPreimage_iff (A a : V) :
    a ∈ baireRunPreimage A ↔ a ∈ baireSpace V ∧ baireRunCode a ∈ A := by
  simp [baireRunPreimage]

instance baireRunPreimage_definable : ℒₛₑₜ-function₁[V] baireRunPreimage := by
  have h : ℒₛₑₜ-relation (fun B A : V ↦ ∀ a, a ∈ B ↔ a ∈ baireSpace V ∧ baireRunCode a ∈ A) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [mem_baireRunPreimage_iff]

theorem isBaireMeagre_subset {A B : V} (hB : IsBaireMeagre B) (hAB : A ⊆ B) : IsBaireMeagre A := by
  obtain ⟨f, hf, hfn, hcover⟩ := hB
  exact ⟨f, hf, hfn, fun a ha ↦ hcover a (hAB a ha)⟩

theorem baireRunPreimage_meagre {A : V} (hA : IsMeagre A) : IsBaireMeagre (baireRunPreimage A) := by
  obtain ⟨f, _, hfn, hcover⟩ := hA
  let F : V → V := fun n ↦ baireRunTreePreimage (f ‘ n)
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let g := definableGraph (ω : V) F hF
  refine ⟨g, definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun n _ ↦ mem_power_iff.mpr (baireRunTreePreimage_subset _)), ?_, ?_⟩
  · intro n hn
    rw [value_definableGraph _ _ _ hn]
    exact baireRunTreePreimage_nowhereDense (hfn n hn)
  · intro a ha
    obtain ⟨hab, hac⟩ := (mem_baireRunPreimage_iff A a).mp ha
    obtain ⟨n, hn, han⟩ := hcover _ hac
    refine ⟨n, hn, ?_⟩
    rw [value_definableGraph _ _ _ hn]
    exact (baireRunTreePreimage_body_iff (hfn n hn).1 hab).mpr han

theorem baireSpaceProperty_of_image {A : V} (hA : A ⊆ baireSpace V)
    (hBP : BaireProperty (baireRunImage A)) : BaireSpaceProperty A := by
  obtain ⟨_, ⟨S, hS, rfl⟩, hmeagre⟩ := hBP
  let W := baireOpenFrom (baireRunPreimageBasis S)
  refine ⟨W, ⟨baireRunPreimageBasis S, baireRunPreimageBasis_subset S, rfl⟩, ?_⟩
  apply isBaireMeagre_subset (baireRunPreimage_meagre hmeagre)
  intro a ha
  have hab : a ∈ baireSpace V := by
    rcases mem_union_iff.mp ha with h | h
    · exact hA a (mem_sdiff_iff.mp h).1
    · exact ((mem_baireOpenFrom_iff _ _).mp (mem_sdiff_iff.mp h).1).1
  refine (mem_baireRunPreimage_iff _ a).mpr ⟨hab, ?_⟩
  have hi := baireRunCode_mem_image_iff hA hab
  have ho := baireRunCode_mem_open_iff hab hS
  simpa only [mem_union_iff, mem_sdiff_iff, hi, ho] using ha

theorem allBaireSpaceProperty_of_cantor (h : AllBaireProperty V) :
    ∀ A : V, A ⊆ baireSpace V → BaireSpaceProperty A :=
  fun _ hA ↦ baireSpaceProperty_of_image hA (h _ (baireRunImage_subset_cantor hA))

end ZFVP
