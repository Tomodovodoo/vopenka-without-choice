import ZFVP.SetTheory.CountableUnions
import ZFVP.SetTheory.FiniteSets
import ZFVP.SetTheory.WellOrderedSurjection

/-! Closure properties of internally countable sets without any choice principle,
and fresh elements of the first uncountable ordinal. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internallyCountable_of_cardLE {A B : V} (hB : IsInternallyCountable B) (h : A ≤# B) :
    IsInternallyCountable A := h.trans hB

theorem internallyCountable_subset {A B : V} (hB : IsInternallyCountable B) (h : A ⊆ B) :
    IsInternallyCountable A := internallyCountable_of_cardLE hB (cardLE_of_subset h)

theorem internallyCountable_empty : IsInternallyCountable (∅ : V) := cardLE_empty _

theorem internallyCountable_omega : IsInternallyCountable (ω : V) := CardLE.refl _

theorem internallyCountable_of_finite {A : V} (h : IsInternallyFinite A) : IsInternallyCountable A := by
  obtain ⟨n, hn, hAn, _⟩ := h
  have ht : IsTransitive (ω : V) := IsOrdinal.toIsTransitive
  exact hAn.trans (cardLE_of_subset (ht.transitive n hn))

theorem internallyCountable_singleton (a : V) : IsInternallyCountable ({a} : V) :=
  internallyCountable_of_finite (by simpa using internallyFinite_insert internallyFinite_empty a)

theorem IsInternallyCountable.wellOrderable {A : V} (h : IsInternallyCountable A) : IsWellOrderable A :=
  (wellOrderable_iff_cardLE_ordinal A).mpr ⟨ω, inferInstance, h⟩

theorem internallyCountable_of_surjection {A B f : V} (hA : IsInternallyCountable A)
    (hf : f ∈ B ^ A) (hr : range f = B) : IsInternallyCountable B :=
  (cardLE_of_surjective_function hA.wellOrderable hf hr).trans hA

theorem internallyCountable_repl (F : V → V) (hF : ℒₛₑₜ-function₁ F) {A : V}
    (hA : IsInternallyCountable A) : IsInternallyCountable (repl F hF A) :=
  internallyCountable_of_surjection hA (definableGraph_mem_function A F hF) (range_definableGraph A F hF)

theorem internallyCountable_domain {f : V} (hf : IsInternallyCountable f) :
    IsInternallyCountable (domain f) := by
  apply internallyCountable_subset (internallyCountable_repl kpair.π₁ (by definability) hf)
  intro x hx
  obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
  exact (repl_spec _).mpr ⟨⟨x, y⟩ₖ, hxy, by simp⟩

theorem internallyCountable_range {f : V} (hf : IsInternallyCountable f) :
    IsInternallyCountable (range f) := by
  apply internallyCountable_subset (internallyCountable_repl kpair.π₂ (by definability) hf)
  intro y hy
  obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
  exact (repl_spec _).mpr ⟨⟨x, y⟩ₖ, hxy, by simp⟩

theorem internallyCountable_function {f : V} [IsFunction f]
    (hf : IsInternallyCountable (domain f)) : IsInternallyCountable f := by
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
  exact internallyCountable_repl _ _ hf

theorem internallyCountable_function_iff {f : V} [IsFunction f] :
    IsInternallyCountable f ↔ IsInternallyCountable (domain f) :=
  ⟨internallyCountable_domain, internallyCountable_function⟩

/-- Two countable sets have countable union; the tags separate the two injections. -/
theorem internallyCountable_union {A B : V} (hA : IsInternallyCountable A)
    (hB : IsInternallyCountable B) : IsInternallyCountable (A ∪ B) := by
  classical
  obtain ⟨f, hf, hfi⟩ := hA
  obtain ⟨g, hg, hgi⟩ := hB
  let := IsFunction.of_mem hf
  let := IsFunction.of_mem hg
  let F : V → V := fun x ↦ if x ∈ A then ⟨(0 : V), f ‘ x⟩ₖ else ⟨(1 : V), g ‘ x⟩ₖ
  have hF : ℒₛₑₜ-function₁ F := by
    have h : ℒₛₑₜ-relation (fun y x : V ↦
        (x ∈ A ∧ y = ⟨(0 : V), f ‘ x⟩ₖ) ∨ (x ∉ A ∧ y = ⟨(1 : V), g ‘ x⟩ₖ)) := by definability
    apply Language.Definable.of_iff h
    intro v
    change v 0 = F (v 1) ↔ _
    unfold F
    split <;> simp_all
  let h := definableGraph (A ∪ B) F hF
  have hh : h ∈ ((ω : V) ×ˢ (ω : V)) ^ (A ∪ B) := by
    apply definableGraph_mem_function_of_mapsTo
    intro x hx
    dsimp only [F]
    split_ifs with hxA
    · exact kpair_mem_iff.mpr ⟨by simp, function_value_mem hf hxA⟩
    · have hxB : x ∈ B := (mem_union_iff.mp hx).resolve_left hxA
      exact kpair_mem_iff.mpr ⟨by simp, function_value_mem hg hxB⟩
  have hinj : Injective h := by
    intro x y z hx hy
    obtain ⟨hxU, rfl⟩ := (pair_mem_definableGraph_iff _ _ _ x z).mp hx
    obtain ⟨hyU, he⟩ := (pair_mem_definableGraph_iff _ _ _ y _).mp hy
    dsimp only [F] at he
    split_ifs at he with hxA hyA hyA
    · exact injective_value_eq hf hfi hxA hyA (kpair_iff.mp he).2
    · exact absurd (kpair_iff.mp he).1 zero_ne_one
    · exact absurd (kpair_iff.mp he).1 one_ne_zero
    · exact injective_value_eq hg hgi ((mem_union_iff.mp hxU).resolve_left hxA)
        ((mem_union_iff.mp hyU).resolve_left hyA) (kpair_iff.mp he).2
  exact (show A ∪ B ≤# ((ω : V) ×ˢ (ω : V)) from ⟨h, hh, hinj⟩).trans omega_prod_cardLE_omega

theorem internallyCountable_insert {A : V} (h : IsInternallyCountable A) (a : V) :
    IsInternallyCountable (insert a A) := by
  have he : insert a A = ({a} : V) ∪ A := by
    ext x
    simp
  rw [he]
  exact internallyCountable_union (internallyCountable_singleton a) h

theorem countable_of_mem_hartogs_omega {α : V} (hα : α ∈ hartogsNumber (ω : V)) :
    IsInternallyCountable α := cardLE_of_mem_hartogsNumber hα

theorem hartogs_omega_not_countable : ¬IsInternallyCountable (hartogsNumber (ω : V)) :=
  not_hartogsNumber_cardLE (ω : V)

theorem omega_mem_hartogs_omega : (ω : V) ∈ hartogsNumber (ω : V) :=
  ordinal_cardLE_iff_mem_hartogsNumber.mp (CardLE.refl _)

/-- Every countable set misses some element of the first uncountable ordinal. -/
theorem exists_fresh_of_countable {E : V} (hE : IsInternallyCountable E) :
    ∃ ξ ∈ hartogsNumber (ω : V), ξ ∉ E := by
  by_contra hall
  have hsub : hartogsNumber (ω : V) ⊆ E := fun ξ hξ ↦ by_contra (fun hn ↦ hall ⟨ξ, hξ, hn⟩)
  exact hartogs_omega_not_countable (internallyCountable_subset hE hsub)

end ZFVP
