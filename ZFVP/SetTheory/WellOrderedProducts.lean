import ZFVP.SetTheory.WellOrderingChoice

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def lexicographicRelation (A B R S : V) : V :=
  {z ∈ (A ×ˢ B) ×ˢ (A ×ˢ B) ;
    ⟨kpair.π₁ (kpair.π₁ z), kpair.π₁ (kpair.π₂ z)⟩ₖ ∈ R ∨
    kpair.π₁ (kpair.π₁ z) = kpair.π₁ (kpair.π₂ z) ∧
      ⟨kpair.π₂ (kpair.π₁ z), kpair.π₂ (kpair.π₂ z)⟩ₖ ∈ S}

theorem pair_mem_lexicographicRelation (A B R S x y : V) :
    ⟨x, y⟩ₖ ∈ lexicographicRelation A B R S ↔
      x ∈ A ×ˢ B ∧ y ∈ A ×ˢ B ∧
      (⟨kpair.π₁ x, kpair.π₁ y⟩ₖ ∈ R ∨
        kpair.π₁ x = kpair.π₁ y ∧ ⟨kpair.π₂ x, kpair.π₂ y⟩ₖ ∈ S) := by
  simp only [lexicographicRelation, mem_sep_iff, kpair_mem_iff,
    kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

theorem lexicographicRelation_wellOrder {A B R S : V}
    (hR : IsInternalWellOrder R A) (hS : IsInternalWellOrder S B) :
    IsInternalWellOrder (lexicographicRelation A B R S) (A ×ˢ B) := by
  refine ⟨fun _ h ↦ (mem_sep_iff.mp h).1, ?_, ?_, ?_⟩
  · intro X hX hn
    have hd : domain X ⊆ A := by
      intro a ha
      obtain ⟨b, hb⟩ := mem_domain_iff.mp ha
      exact (kpair_mem_iff.mp (hX _ hb)).1
    obtain ⟨z, hz⟩ := hn.nonempty
    obtain ⟨a, _, b, _, he⟩ := mem_prod_iff.mp (hX _ hz)
    subst z
    obtain ⟨a, ha, hamin⟩ := hR.2.1 (domain X) hd
      ⟨a, mem_domain_of_kpair_mem hz⟩
    let Y : V := {b ∈ B ; ⟨a, b⟩ₖ ∈ X}
    obtain ⟨b, hb⟩ := mem_domain_iff.mp ha
    have hnY : IsNonempty Y := ⟨b, mem_sep_iff.mpr
      ⟨(kpair_mem_iff.mp (hX _ hb)).2, hb⟩⟩
    obtain ⟨b, hb, hbmin⟩ := hS.2.1 Y (fun _ h ↦ (mem_sep_iff.mp h).1) hnY
    have hbX := (mem_sep_iff.mp hb).2
    refine ⟨⟨a, b⟩ₖ, hbX, ?_⟩
    intro y hy hlt
    obtain ⟨c, _, d, _, rfl⟩ := mem_prod_iff.mp (hX _ hy)
    have hh := ((pair_mem_lexicographicRelation A B R S _ _).mp hlt).2.2
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hh
    rcases hh with hh | ⟨rfl, hh⟩
    · exact hamin c (mem_domain_of_kpair_mem hy) hh
    · exact hbmin d (mem_sep_iff.mpr ⟨(kpair_mem_iff.mp (hX _ hy)).2, hy⟩) hh
  · intro x hx y hy z hz hxy hyz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hx
    obtain ⟨c, hc, d, hd, rfl⟩ := mem_prod_iff.mp hy
    obtain ⟨e, he, f, hf, rfl⟩ := mem_prod_iff.mp hz
    rw [pair_mem_lexicographicRelation] at hxy hyz ⊢
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hxy hyz ⊢
    refine ⟨hxy.1, hyz.2.1, ?_⟩
    rcases hxy.2.2 with h | ⟨rfl, h⟩ <;>
      rcases hyz.2.2 with k | ⟨rfl, k⟩
    · exact Or.inl (hR.2.2.1 a ha c hc e he h k)
    · exact Or.inl h
    · exact Or.inl k
    · exact Or.inr ⟨rfl, hS.2.2.1 b hb d hd f hf h k⟩
  · intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hx
    obtain ⟨c, hc, d, hd, rfl⟩ := mem_prod_iff.mp hy
    have hp := kpair_mem_iff.mpr ⟨ha, hb⟩
    have hq := kpair_mem_iff.mpr ⟨hc, hd⟩
    simp only [pair_mem_lexicographicRelation, kpair.π₁_kpair, kpair.π₂_kpair]
    rcases hR.2.2.2 a ha c hc with h | rfl | h
    · exact Or.inl ⟨hp, hq, Or.inl h⟩
    · rcases hS.2.2.2 b hb d hd with h | rfl | h
      · exact Or.inl ⟨hp, hq, Or.inr ⟨rfl, h⟩⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨hq, hp, Or.inr ⟨rfl, h⟩⟩)
    · exact Or.inr (Or.inr ⟨hq, hp, Or.inl h⟩)

theorem wellOrderable_prod {A B : V} (hA : IsWellOrderable A) (hB : IsWellOrderable B) :
    IsWellOrderable (A ×ˢ B) := by
  obtain ⟨R, hR⟩ := hA
  obtain ⟨S, hS⟩ := hB
  exact ⟨lexicographicRelation A B R S, lexicographicRelation_wellOrder hR hS⟩

end ZFVP
