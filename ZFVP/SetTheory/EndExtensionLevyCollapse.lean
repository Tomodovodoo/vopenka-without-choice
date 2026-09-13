import ZFVP.SetTheory.EndExtensionCoding
import ZFVP.SetTheory.EndExtensionRelations
import ZFVP.SetTheory.EndExtensionFinite
import ZFVP.SetTheory.EndExtensionSets
import ZFVP.SetTheory.EndExtensionWellOrdering
import ZFVP.SetTheory.EndExtensionNameValue
import ZFVP.SetTheory.FiniteSequences
import ZFVP.SetTheory.LevyCollapseUpper

/-! Absoluteness of finiteness, finite partial functions and the Levy collapse for membership end
extensions: `j (Coll(ω,<κ)) = Coll(ω,<j κ)`, and likewise for its order, cuts and upper parts. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem finiteSequences_mono {A B : V} (h : A ⊆ B) : finiteSequences A ⊆ finiteSequences B := by
  intro s hs
  obtain ⟨n, hn, hsn⟩ := (mem_finiteSequences_iff A s).mp hs
  exact (mem_finiteSequences_iff B s).mpr ⟨n, hn, mem_function_of_mem_function_of_subset hsn h⟩

theorem range_insert_kpair (f x y : V) : range (insert ⟨x, y⟩ₖ f) = insert y (range f) := by
  ext z
  rw [mem_range_iff, mem_insert, mem_range_iff]
  constructor
  · rintro ⟨w, hw⟩
    rcases mem_insert.mp hw with h | h
    · exact Or.inl (kpair_iff.mp h).2
    · exact Or.inr ⟨w, h⟩
  · rintro (rfl | ⟨w, hw⟩)
    · exact ⟨x, mem_insert.mpr (Or.inl rfl)⟩
    · exact ⟨w, mem_insert.mpr (Or.inr hw)⟩

theorem range_empty_eq : range (∅ : V) = ∅ := by
  ext z
  rw [mem_range_iff]
  simp only [not_mem_empty, iff_false, not_exists, not_false_eq_true, implies_true]

/-- A finite set is the range of a finite sequence in it. -/
theorem exists_finiteSequence_range {X : V} (hX : IsInternallyFinite X) :
    ∃ s ∈ finiteSequences X, range s = X := by
  revert X
  apply internallyFinite_induction (fun A ↦ ∃ s ∈ finiteSequences A, range s = A) (by definability)
  · exact ⟨∅, empty_mem_finiteSequences ∅, range_empty_eq⟩
  · rintro A a ⟨s, hs, hr⟩
    refine ⟨insert ⟨domain s, a⟩ₖ s, ?_, ?_⟩
    · exact finiteSequence_append (finiteSequences_mono (fun z hz ↦ mem_insert.mpr (Or.inr hz)) s hs)
        (mem_insert.mpr (Or.inl rfl))
    · rw [range_insert_kpair, hr]

/-- The range of a finite sequence is finite. -/
theorem internallyFinite_of_finiteSequence_range {X s : V} (hs : s ∈ finiteSequences X)
    (hr : range s = X) : IsInternallyFinite X := by
  obtain ⟨n, hn, hsn⟩ := (mem_finiteSequences_iff X s).mp hs
  haveI : IsFunction s := IsFunction.of_mem hsn
  have hd : domain s = n := domain_eq_of_mem_function hsn
  have hnfin : IsInternallyFinite n := ⟨n, hn, CardLE.refl n, CardLE.refl n⟩
  rw [← hr]
  exact internallyFinite_range (internallyFinite_function (by rw [hd]; exact hnfin))

theorem range_subset_of_mem_finiteSequences {A s : V} (hs : s ∈ finiteSequences A) : range s ⊆ A := by
  obtain ⟨n, _, hsn⟩ := (mem_finiteSequences_iff A s).mp hs
  intro y hy
  obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
  exact (kpair_mem_iff.mp ((mem_function_iff.mp hsn).1 _ hxy)).2

namespace MembershipEndExtension

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

/-- Finiteness is absolute for end extensions. -/
theorem internallyFinite_iff (X : V) : IsInternallyFinite (j X) ↔ IsInternallyFinite X := by
  constructor
  · intro h
    obtain ⟨s, hs, hr⟩ := exists_finiteSequence_range h
    rw [← j.map_finiteSequences] at hs
    obtain ⟨s', hs', rfl⟩ := j.endExtension _ _ hs
    rw [← j.map_range] at hr
    exact internallyFinite_of_finiteSequence_range hs' (j.injective hr)
  · exact j.map_internallyFinite

/-- Finite subsets of the image of a set are images of subsets. -/
theorem exists_eq_map_of_finite_subset {Y : V} {q : W} (hq : q ⊆ j Y) (hfin : IsInternallyFinite q) :
    ∃ p, p ⊆ Y ∧ q = j p := by
  obtain ⟨s, hs, hr⟩ := exists_finiteSequence_range hfin
  have hs' : s ∈ finiteSequences (j Y) := finiteSequences_mono hq s hs
  rw [← j.map_finiteSequences] at hs'
  obtain ⟨s', hs'', rfl⟩ := j.endExtension _ _ hs'
  exact ⟨range s', range_subset_of_mem_finiteSequences hs'', by rw [← hr, j.map_range]⟩

/-- A function whose image is a function. -/
theorem isFunction_of_map {p : V} (h : IsFunction (j p)) : IsFunction p := by
  have h1 := isFunction_iff.mp h
  rw [← j.map_range, ← j.map_relationDomain, j.function_iff] at h1
  exact isFunction_iff.mpr h1

theorem map_finitePartialFunctions (D B : V) :
    j (finitePartialFunctions D B) = finitePartialFunctions (j D) (j B) := by
  apply mem_ext
  intro q
  constructor
  · intro hq
    obtain ⟨p, hp, rfl⟩ := j.endExtension _ _ hq
    obtain ⟨hsub, hfun, hfin⟩ := (mem_finitePartialFunctions _ _ _).mp hp
    haveI := hfun
    refine (mem_finitePartialFunctions _ _ _).mpr ⟨?_, j.map_function p, ?_⟩
    · rw [← j.map_prod]
      exact (j.subset_iff _ _).mpr hsub
    · rw [← j.map_domain]
      exact j.map_internallyFinite hfin
  · intro hq
    obtain ⟨hsub, hfun, hfin⟩ := (mem_finitePartialFunctions _ _ _).mp hq
    haveI := hfun
    have hqfin : IsInternallyFinite q := internallyFinite_function hfin
    rw [← j.map_prod] at hsub
    obtain ⟨p, hpsub, rfl⟩ := j.exists_eq_map_of_finite_subset hsub hqfin
    have hpf : IsFunction p := j.isFunction_of_map hfun
    refine (j.mem_iff _ _).mpr ((mem_finitePartialFunctions _ _ _).mpr ⟨hpsub, hpf, ?_⟩)
    rw [← j.map_relationDomain] at hfin
    exact (j.internallyFinite_iff _).mp hfin

theorem map_levyCollapse (κ : V) : j (levyCollapse κ) = levyCollapse (j κ) := by
  unfold levyCollapse
  rw [j.map_separation _ (fun p ↦ ∀ z ∈ p, kpair.π₂ z ∈ kpair.π₂ (kpair.π₁ z))
    (fun p ↦ ∀ z ∈ p, kpair.π₂ z ∈ kpair.π₂ (kpair.π₁ z)) (by definability) (by definability) ?_,
    j.map_finitePartialFunctions, j.map_prod, j.map_omega]
  intro p _
  rw [j.forall_mem_iff]
  constructor
  · intro h z hz
    rw [← j.map_first, ← j.map_second, ← j.map_second, j.mem_iff]
    exact h z hz
  · intro h z hz
    have := h z hz
    rwa [← j.map_first, ← j.map_second, ← j.map_second, j.mem_iff] at this

theorem map_reverseInclusionOrder (P : V) :
    j (reverseInclusionOrder P) = reverseInclusionOrder (j P) := by
  unfold reverseInclusionOrder
  rw [j.map_separation _ (fun z ↦ kpair.π₂ z ⊆ kpair.π₁ z) (fun z ↦ kpair.π₂ z ⊆ kpair.π₁ z)
    (by definability) (by definability) ?_, j.map_prod]
  intro z _
  rw [← j.map_first, ← j.map_second, j.subset_iff]

theorem map_levyOrder (κ : V) : j (levyOrder κ) = levyOrder (j κ) := by
  unfold levyOrder
  rw [j.map_reverseInclusionOrder, j.map_levyCollapse]

theorem map_levyCut (β p : V) : j (levyCut β p) = levyCut (j β) (j p) := by
  unfold levyCut
  rw [j.map_restrict, j.map_prod, j.map_omega]

theorem map_sdiff (x y : V) : j (x \ y) = j x \ j y := by
  change j (SetTheory.sdiff x y) = SetTheory.sdiff (j x) (j y)
  unfold SetTheory.sdiff
  rw [j.map_separation _ (fun z ↦ z ∉ y) (fun z ↦ z ∉ j y) (by definability) (by definability)]
  intro z _
  rw [j.mem_iff]

theorem map_levyUpper (β p : V) : j (levyUpper β p) = levyUpper (j β) (j p) := by
  unfold levyUpper
  rw [j.map_sdiff, j.map_levyCut]

theorem map_levyCollapseAbove (κ β : V) :
    j (levyCollapseAbove κ β) = levyCollapseAbove (j κ) (j β) := by
  unfold levyCollapseAbove
  rw [j.map_separation _ (fun p ↦ levyCut β p = ∅) (fun p ↦ levyCut (j β) p = ∅)
    (by definability) (by definability) ?_, j.map_levyCollapse]
  intro p _
  rw [← j.map_levyCut]
  constructor
  · intro h
    rw [h, j.map_empty]
  · intro h
    rw [← j.map_empty] at h
    exact j.injective h

end MembershipEndExtension

end ZFVP
