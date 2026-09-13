import ZFVP.SetTheory.EndExtensionSets
import ZFVP.SetTheory.FunctionComposition
import ZFVP.SetTheory.FunctionUnion

/-! Relations, composition, restriction, and total graph evaluation under end extensions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem pair_mem_image_iff (j : MembershipEndExtension V W) (A : V) (x y : W) :
    ⟨x, y⟩ₖ ∈ j A ↔ ∃ a b : V, ⟨a, b⟩ₖ ∈ A ∧ x = j a ∧ y = j b := by
  constructor
  · intro h
    obtain ⟨p, _, hp⟩ := j.endExtension A _ h
    have hx : x = j (kpair.π₁ p) := by rw [j.map_first, ← hp, kpair.π₁_kpair]
    have hy : y = j (kpair.π₂ p) := by rw [j.map_second, ← hp, kpair.π₂_kpair]
    refine ⟨kpair.π₁ p, kpair.π₂ p, ?_, hx, hy⟩
    apply (j.mem_iff _ _).mp
    rwa [j.map_kpair, ← hx, ← hy]
  · rintro ⟨a, b, hab, rfl, rfl⟩
    rw [← j.map_kpair]
    exact (j.mem_iff _ _).mpr hab

theorem map_range (j : MembershipEndExtension V W) (f : V) : j (range f) = range (j f) := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨b, hb, rfl⟩ := j.endExtension _ y hy
    obtain ⟨a, hab⟩ := mem_range_iff.mp hb
    exact mem_range_iff.mpr ⟨j a, by rw [← j.map_kpair]; exact (j.mem_iff _ _).mpr hab⟩
  · intro hy
    obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
    obtain ⟨a, b, hab, _, rfl⟩ := (j.pair_mem_image_iff f x y).mp hxy
    exact (j.mem_iff _ _).mpr (mem_range_iff.mpr ⟨a, hab⟩)

theorem map_compose (j : MembershipEndExtension V W) (f g : V) :
    j (compose f g) = compose (j f) (j g) := by
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := j.endExtension _ p hp
    obtain ⟨a, b, c, hab, hbc, rfl⟩ := mem_compose_iff.mp hq
    exact mem_compose_iff.mpr ⟨j a, j b, j c,
      by rw [← j.map_kpair]; exact (j.mem_iff _ _).mpr hab,
      by rw [← j.map_kpair]; exact (j.mem_iff _ _).mpr hbc, j.map_kpair a c⟩
  · intro hp
    obtain ⟨x, y, z, hxy, hyz, rfl⟩ := mem_compose_iff.mp hp
    obtain ⟨a, b, hab, rfl, rfl⟩ := (j.pair_mem_image_iff f x y).mp hxy
    obtain ⟨c, hbc, rfl⟩ := (j.pair_mem_image_left_iff g b z).mp hyz
    rw [← j.map_kpair]
    exact (j.mem_iff _ _).mpr (mem_compose_iff.mpr ⟨a, b, c, hab, hbc, rfl⟩)

theorem map_restrict (j : MembershipEndExtension V W) (f A : V) : j (f ↾ A) = (j f) ↾ (j A) := by
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := j.endExtension _ p hp
    obtain ⟨hq, x, hx, y, rfl⟩ := mem_restrict_iff.mp hq
    rw [j.map_kpair, kpair_mem_restrict_iff, ← j.map_kpair, j.mem_iff, j.mem_iff]
    exact ⟨hq, hx⟩
  · intro hp
    obtain ⟨hp, x, hx, y, rfl⟩ := mem_restrict_iff.mp hp
    obtain ⟨a, b, hab, rfl, rfl⟩ := (j.pair_mem_image_iff f x y).mp hp
    rw [← j.map_kpair, j.mem_iff, kpair_mem_restrict_iff]
    exact ⟨hab, (j.mem_iff _ _).mp hx⟩

theorem map_value_total (j : MembershipEndExtension V W) (f x : V) :
    j (f ‘ x) = (j f) ‘ (j x) := by
  unfold SetTheory.value
  have he := j.map_separation (⋃ˢ range f)
    (fun z ↦ ∃ y, z ∈ y ∧ ⟨x, y⟩ₖ ∈ f)
    (fun z ↦ ∃ y, z ∈ y ∧ ⟨j x, y⟩ₖ ∈ j f) (by definability) (by definability) (by
      intro z _
      constructor
      · rintro ⟨y, hzy, hxy⟩
        exact ⟨j y, (j.mem_iff _ _).mpr hzy, by rw [← j.map_kpair]; exact (j.mem_iff _ _).mpr hxy⟩
      · rintro ⟨y, hzy, hxy⟩
        obtain ⟨a, ha, rfl⟩ := (j.pair_mem_image_left_iff f x y).mp hxy
        exact ⟨a, (j.mem_iff _ _).mp hzy, ha⟩)
  simpa only [j.map_sUnion, j.map_range] using he

theorem map_definableGraph (j : MembershipEndExtension V W) (A : V) (F : V → V) (Q : W → W)
    (hF : ℒₛₑₜ-function₁ F) (hQ : ℒₛₑₜ-function₁ Q) (he : ∀ x ∈ A, j (F x) = Q (j x)) :
    j (definableGraph A F hF) = definableGraph (j A) Q hQ := by
  let := j.map_function (definableGraph A F hF)
  apply functions_eq_of_domain_values
  · rw [← j.map_domain, domain_definableGraph, domain_definableGraph]
  · intro y hy
    rw [← j.map_domain, domain_definableGraph] at hy
    obtain ⟨x, hx, rfl⟩ := j.endExtension A y hy
    rw [← j.map_value_total, value_definableGraph _ _ _ hx,
      value_definableGraph _ _ _ ((j.mem_iff _ _).mpr hx), he x hx]

end MembershipEndExtension
end ZFVP
