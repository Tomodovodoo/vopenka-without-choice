import ZFVP.SetTheory.InfiniteDependentChoice

/-! Finite-set induction and closure inside arbitrary ZF models. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem cardLE_insert_fresh {A B a b : V} (h : A ≤# B)
    (ha : a ∉ A) (hb : b ∉ B) : insert a A ≤# insert b B := by
  obtain ⟨f, hf, hi⟩ := h
  have : IsFunction f := IsFunction.of_mem hf
  have : IsFunction (insert ⟨a, b⟩ₖ f) :=
    IsFunction.insert f a b (by simpa only [domain_eq_of_mem_function hf] using ha)
  refine ⟨insert ⟨a, b⟩ₖ f, ?_, injective_append_fresh hi
    (fun hh ↦ hb (range_subset_of_mem_function hf _ hh))⟩
  have hd : domain (insert ⟨a, b⟩ₖ f) = insert a A := by
    simp [domain_eq_of_mem_function hf]
  have hr : range (insert ⟨a, b⟩ₖ f) ⊆ insert b B := by
    intro y hy
    rcases show y = b ∨ y ∈ range f from by simpa using hy with rfl | hy
    · simp
    · exact mem_insert.mpr (Or.inr (range_subset_of_mem_function hf _ hy))
  simpa only [hd] using mem_function_of_mem_function_of_subset
    (IsFunction.mem_function (insert ⟨a, b⟩ₖ f)) hr

theorem internallyFinite_empty : IsInternallyFinite (∅ : V) :=
  ⟨∅, empty_mem_ω, CardEQ.refl _⟩

theorem internallyFinite_insert {A : V} (h : IsInternallyFinite A) (a : V) :
    IsInternallyFinite (insert a A) := by
  classical
  by_cases ha : a ∈ A
  · have he : insert a A = A := by ext x; simp only [mem_insert]; grind
    rwa [he]
  · obtain ⟨n, hn, hAn, hnA⟩ := h
    refine ⟨succ n, ω_succ_closed hn, ?_, ?_⟩
    · simpa only [succ] using cardLE_insert_fresh hAn ha (mem_irrefl n)
    · simpa only [succ] using cardLE_insert_fresh hnA (mem_irrefl n) ha

theorem property_of_cardLE_natural (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (he : P ∅) (hi : ∀ A a, P A → P (insert a A)) :
    ∀ n ∈ (ω : V), ∀ A, A ≤# n → P A := by
  classical
  apply naturalNumber_induction (fun n ↦ ∀ A, A ≤# n → P A) (by definability)
  · intro A hA
    obtain ⟨f, hf, _⟩ := hA
    have hzero : A = ∅ := by
      apply mem_ext
      intro x
      simp only [not_mem_empty, iff_false]
      exact fun hx ↦ not_mem_empty (function_value_mem hf hx)
    simpa only [hzero] using he
  · intro n hn ih A hA
    obtain ⟨f, hf, hinj⟩ := hA
    have : IsFunction f := IsFunction.of_mem hf
    let B := {x ∈ A ; f ‘ x ≠ n}
    have hBA : B ⊆ A := fun x hx ↦ (mem_sep_iff.mp hx).1
    have hfB : f ↾ B ∈ n ^ B := by
      have hd : domain (f ↾ B) = B := by
        rw [domain_restrict_eq, domain_eq_of_mem_function hf, inter_eq_right_of_subset hBA]
      have hr : range (f ↾ B) ⊆ n := by
        intro y hy
        obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
        obtain ⟨hxy, hx⟩ := kpair_mem_restrict_iff.mp hxy
        have hxB : x ∈ A ∧ f ‘ x ≠ n := mem_sep_iff.mp hx
        have hyfn : f ‘ x = y := value_eq_of_kpair_mem hxy
        rw [← hyfn]
        exact (mem_succ_iff.mp (function_value_mem hf hxB.1)).resolve_left hxB.2
      simpa only [hd] using mem_function_of_mem_function_of_subset
        (IsFunction.mem_function (f ↾ B)) hr
    have hBi : Injective (f ↾ B) := fun x y z hx hy ↦
      hinj x y z (kpair_mem_restrict_iff.mp hx).1 (kpair_mem_restrict_iff.mp hy).1
    have hPB := ih B ⟨f ↾ B, hfB, hBi⟩
    by_cases hex : ∃ a ∈ A, f ‘ a = n
    · obtain ⟨a, ha, hfa⟩ := hex
      have hAB : A = insert a B := by
        apply mem_ext
        intro x
        simp only [mem_insert]
        constructor
        · intro hx
          by_cases hfx : f ‘ x = n
          · exact Or.inl (injective_value_eq hf hinj hx ha (hfx.trans hfa.symm))
          · exact Or.inr (mem_sep_iff.mpr ⟨hx, hfx⟩)
        · rintro (rfl | hx)
          · exact ha
          · exact hBA x hx
      rw [hAB]
      exact hi B a hPB
    · have hAB : A = B := by
        apply SetTheory.subset_antisymm
        · intro x hx
          exact mem_sep_iff.mpr ⟨hx, fun hh ↦ hex ⟨x, hx, hh⟩⟩
        · exact hBA
      rwa [hAB]

/-- Internal finite-set induction includes internally finite sets of nonstandard size. -/
theorem internallyFinite_induction (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (he : P ∅) (hi : ∀ A a, P A → P (insert a A)) :
    ∀ A, IsInternallyFinite A → P A := by
  intro A hA
  obtain ⟨n, hn, hAn, _⟩ := hA
  exact property_of_cardLE_natural P hP he hi n hn A hAn

theorem internallyFinite_of_cardLE_natural {A n : V} (hn : n ∈ (ω : V))
    (h : A ≤# n) : IsInternallyFinite A :=
  property_of_cardLE_natural IsInternallyFinite (by definability) internallyFinite_empty
    (fun _ a hA ↦ internallyFinite_insert hA a) n hn A h

theorem internallyFinite_of_cardLE {A B : V} (hB : IsInternallyFinite B)
    (h : A ≤# B) : IsInternallyFinite A := by
  obtain ⟨n, hn, hBn, _⟩ := hB
  exact internallyFinite_of_cardLE_natural hn (h.trans hBn)

theorem internallyFinite_subset {A B : V} (hB : IsInternallyFinite B)
    (h : A ⊆ B) : IsInternallyFinite A :=
  internallyFinite_of_cardLE hB (cardLE_of_subset h)

theorem internallyFinite_union {A B : V} (hA : IsInternallyFinite A)
    (hB : IsInternallyFinite B) : IsInternallyFinite (A ∪ B) := by
  apply internallyFinite_induction (fun A ↦ IsInternallyFinite (A ∪ B))
    (by definability) ?_ ?_ A hA
  · simpa using hB
  · intro C c ih
    have he : insert c C ∪ B = insert c (C ∪ B) := by ext x; simp
    rw [he]
    exact internallyFinite_insert ih c

theorem internallyFinite_repl (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    {A : V} (hA : IsInternallyFinite A) : IsInternallyFinite (repl F hF A) := by
  apply internallyFinite_induction (fun A ↦ IsInternallyFinite (repl F hF A))
    (by have := hF; definability) ?_ ?_ A hA
  · have he : repl F hF ∅ = (∅ : V) := by ext x; simp only [repl_spec, not_mem_empty, false_and, exists_false]
    rw [he]
    exact internallyFinite_empty
  · intro B b ih
    have he : repl F hF (insert b B) = insert (F b) (repl F hF B) := by
      ext x
      simp only [repl_spec, mem_insert]
      constructor
      · rintro ⟨y, rfl | hy, he⟩
        · exact Or.inl he
        · exact Or.inr ⟨y, hy, he⟩
      · rintro (he | ⟨y, hy, he⟩)
        · exact ⟨b, Or.inl rfl, he⟩
        · exact ⟨y, Or.inr hy, he⟩
    rw [he]
    exact internallyFinite_insert ih (F b)

theorem internallyFinite_domain {f : V} (hf : IsInternallyFinite f) :
    IsInternallyFinite (domain f) := by
  apply internallyFinite_subset (internallyFinite_repl kpair.π₁ (by definability) hf)
  intro x hx
  obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
  exact (repl_spec (by definability)).mpr ⟨⟨x, y⟩ₖ, hxy, by simp⟩

theorem internallyFinite_range {f : V} (hf : IsInternallyFinite f) :
    IsInternallyFinite (range f) := by
  apply internallyFinite_subset (internallyFinite_repl kpair.π₂ (by definability) hf)
  intro y hy
  obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
  exact (repl_spec (by definability)).mpr ⟨⟨x, y⟩ₖ, hxy, by simp⟩

theorem internallyFinite_function {f : V} [IsFunction f]
    (hf : IsInternallyFinite (domain f)) : IsInternallyFinite f := by
  have he : f = repl (fun x ↦ ⟨x, f ‘ x⟩ₖ) (by definability) (domain f) := by
    ext p
    rw [repl_spec]
    constructor
    · intro hp
      obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hp
      exact ⟨x, mem_domain_of_kpair_mem hp, by rw [value_eq_of_kpair_mem hp]⟩
    · rintro ⟨x, hx, rfl⟩
      exact kpair_value_mem hx
  rw [he]
  exact internallyFinite_repl _ _ hf

theorem internallyFinite_function_iff {f : V} [IsFunction f] :
    IsInternallyFinite f ↔ IsInternallyFinite (domain f) :=
  ⟨internallyFinite_domain, internallyFinite_function⟩

end ZFVP
