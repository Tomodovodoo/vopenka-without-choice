import ZFVP.SetTheory.EndExtensionCoding

/-! Set operations used in arbitrary language and structure codes are absolute under end extensions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]

theorem forall_mem_iff (j : MembershipEndExtension V W) (A : V) (P : W → Prop) :
    (∀ y ∈ j A, P y) ↔ ∀ x ∈ A, P (j x) := by
  constructor
  · intro h x hx; exact h (j x) ((j.mem_iff _ _).mpr hx)
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := j.endExtension A y hy
    exact h x hx

theorem exists_mem_iff (j : MembershipEndExtension V W) (A : V) (P : W → Prop) :
    (∃ y ∈ j A, P y) ↔ ∃ x ∈ A, P (j x) := by
  constructor
  · rintro ⟨y, hy, hp⟩
    obtain ⟨x, hx, rfl⟩ := j.endExtension A y hy
    exact ⟨x, hx, hp⟩
  · rintro ⟨x, hx, hp⟩
    exact ⟨j x, (j.mem_iff _ _).mpr hx, hp⟩

variable [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_sUnion (j : MembershipEndExtension V W) (A : V) : j (⋃ˢ A) = ⋃ˢ j A := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := j.endExtension _ y hy
    obtain ⟨a, ha, hx⟩ := mem_sUnion_iff.mp hx
    exact mem_sUnion_iff.mpr ⟨j a, (j.mem_iff _ _).mpr ha, (j.mem_iff _ _).mpr hx⟩
  · intro hy
    obtain ⟨b, hb, hy⟩ := mem_sUnion_iff.mp hy
    obtain ⟨a, ha, rfl⟩ := j.endExtension A b hb
    obtain ⟨x, hx, rfl⟩ := j.endExtension a y hy
    exact (j.mem_iff _ _).mpr (mem_sUnion_iff.mpr ⟨a, ha, hx⟩)

theorem map_separation (j : MembershipEndExtension V W) (A : V)
    (P : V → Prop) (Q : W → Prop) (hP : ℒₛₑₜ-predicate P) (hQ : ℒₛₑₜ-predicate Q)
    (he : ∀ x ∈ A, P x ↔ Q (j x)) :
    j {x ∈ A ; P x} = {x ∈ j A ; Q x} := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := j.endExtension _ y hy
    obtain ⟨hx, hp⟩ := mem_sep_iff.mp hx
    exact mem_sep_iff.mpr ⟨(j.mem_iff _ _).mpr hx, (he x hx).mp hp⟩
  · intro hy
    obtain ⟨hy, hq⟩ := mem_sep_iff.mp hy
    obtain ⟨x, hx, rfl⟩ := j.endExtension A y hy
    exact (j.mem_iff _ _).mpr (mem_sep_iff.mpr ⟨hx, (he x hx).mpr hq⟩)

omit [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem nonempty_iff (j : MembershipEndExtension V W) (A : V) : IsNonempty (j A) ↔ IsNonempty A := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, _⟩ := j.endExtension A y hy
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨j x, (j.mem_iff _ _).mpr hx⟩

theorem map_sInter (j : MembershipEndExtension V W) (A : V) : j (⋂ˢ A) = ⋂ˢ j A := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := j.endExtension _ y hy
    rw [mem_sInter_iff] at hx ⊢
    refine ⟨?_, ?_⟩
    · exact (j.nonempty_iff A).mpr hx.1
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := j.endExtension A b hb
      exact (j.mem_iff _ _).mpr (hx.2 a ha)
  · intro hy
    rw [mem_sInter_iff] at hy
    obtain ⟨b, hb⟩ := hy.1
    obtain ⟨a, ha, rfl⟩ := j.endExtension A b hb
    obtain ⟨x, _, rfl⟩ := j.endExtension a y (hy.2 (j a) hb)
    apply (j.mem_iff _ _).mpr
    rw [mem_sInter_iff]
    refine ⟨(j.nonempty_iff A).mp hy.1, ?_⟩
    intro a ha
    exact (j.mem_iff _ _).mp (hy.2 (j a) ((j.mem_iff _ _).mpr ha))

theorem map_first (j : MembershipEndExtension V W) (p : V) : j (kpair.π₁ p) = kpair.π₁ (j p) := by
  rw [kpair.π₁, j.map_sUnion, j.map_sInter]
  rfl

theorem map_second (j : MembershipEndExtension V W) (p : V) : j (kpair.π₂ p) = kpair.π₂ (j p) := by
  unfold kpair.π₂
  rw [j.map_sUnion]
  congr 1
  have he := j.map_separation (⋃ˢ p) (fun x ↦ x ∈ ⋂ˢ p → ⋃ˢ p = ⋂ˢ p)
    (fun x ↦ x ∈ ⋂ˢ j p → ⋃ˢ j p = ⋂ˢ j p) (by definability) (by definability) (by
      intro x _
      rw [← j.map_sUnion, ← j.map_sInter, j.mem_iff, j.injective.eq_iff])
  simpa only [j.map_sUnion] using he

theorem pair_mem_image_left_iff (j : MembershipEndExtension V W) (A x : V) (y : W) :
    ⟨j x, y⟩ₖ ∈ j A ↔ ∃ z : V, ⟨x, z⟩ₖ ∈ A ∧ y = j z := by
  constructor
  · intro h
    obtain ⟨p, _, hp⟩ := j.endExtension A _ h
    have hy : y = j (kpair.π₂ p) := by
      rw [j.map_second, ← hp, kpair.π₂_kpair]
    refine ⟨kpair.π₂ p, ?_, hy⟩
    apply (j.mem_iff _ _).mp
    rwa [j.map_kpair, ← hy]
  · rintro ⟨z, hz, rfl⟩
    rw [← j.map_kpair]
    exact (j.mem_iff _ _).mpr hz


end MembershipEndExtension
end ZFVP
