import ZFVP.SetTheory.EndExtensionRelations

set_option maxHeartbeats 400000

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Recover subsets from their two-valued characteristic functions. -/
theorem subset_of_function_closed (j : MembershipEndExtension V W) {X : V}
    (hc : ∀ f ∈ j (doubleton ∅ (doubleton ∅ ∅) : V) ^ j X,
      ∃ g ∈ (doubleton ∅ (doubleton ∅ ∅) : V) ^ X, j g = f)
    {Y : W} (hY : Y ⊆ j X) : ∃ Z, Z ⊆ X ∧ j Z = Y := by
  classical
  let F : W → W := fun x ↦ if x ∈ Y then doubleton ∅ ∅ else ∅
  have hF : ℒₛₑₜ-function₁ F := by
    have hd : ℒₛₑₜ-relation (fun z x : W ↦
        (x ∈ Y ∧ z = doubleton ∅ ∅) ∨ (x ∉ Y ∧ z = ∅)) := by definability
    apply Language.Definable.of_iff hd
    intro v
    change v 0 = F (v 1) ↔ _
    by_cases hv : v 1 ∈ Y <;> simp [F, hv]
  let f := definableGraph (j X) F hF
  have hf : f ∈ j (doubleton ∅ (doubleton ∅ ∅) : V) ^ j X := by
    apply definableGraph_mem_function_of_mapsTo
    intro x _
    simp only [F, j.map_doubleton, j.map_empty]
    split_ifs <;> simp
  obtain ⟨g, hg, he⟩ := hc f hf
  change j g = definableGraph (j X) F hF at he
  let Z := {x ∈ X ; g ‘ x = doubleton ∅ ∅}
  refine ⟨Z, fun x hx ↦ (mem_sep_iff.mp hx).1, ?_⟩
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := j.endExtension Z y hy
    obtain ⟨hxX, hxg⟩ := mem_sep_iff.mp hx
    have hval : F (j x) = (doubleton ∅ ∅ : W) := by
      rw [← value_definableGraph (j X) F hF ((j.mem_iff _ _).mpr hxX), ← he,
        ← j.map_value_total, hxg]
      simp only [j.map_doubleton, j.map_empty]
    by_contra hn
    have hbad : (∅ : W) = doubleton ∅ ∅ := by simpa [F, hn] using hval
    have hm : (∅ : W) ∈ (doubleton ∅ ∅ : W) := by simp
    rw [← hbad] at hm
    exact not_mem_empty hm
  · intro hy
    obtain ⟨x, hx, rfl⟩ := j.endExtension X y (hY y hy)
    apply (j.mem_iff _ _).mpr
    apply mem_sep_iff.mpr
    refine ⟨hx, j.injective ?_⟩
    rw [j.map_value_total, he, value_definableGraph _ _ _ ((j.mem_iff _ _).mpr hx)]
    simp [F, hy, j.map_doubleton, j.map_empty]

/-- An enumeration transfers binary-function closure to subsets of its range. -/
theorem subset_of_surjection_function_closed (j : MembershipEndExtension V W) {X D e : V}
    (he : e ∈ X ^ D) (hr : range e = X)
    (hc : ∀ f ∈ j (doubleton ∅ (doubleton ∅ ∅) : V) ^ j D,
      ∃ g ∈ (doubleton ∅ (doubleton ∅ ∅) : V) ^ D, j g = f)
    {Y : W} (hY : Y ⊆ j X) : ∃ Z, Z ⊆ X ∧ j Z = Y := by
  let := IsFunction.of_mem he
  let T := {a ∈ j D ; (j e) ‘ a ∈ Y}
  obtain ⟨Z, hZ, hZT⟩ := j.subset_of_function_closed hc
    (show T ⊆ j D from fun _ ha ↦ (mem_sep_iff.mp ha).1)
  let S := {x ∈ X ; ∃ a ∈ Z, e ‘ a = x}
  refine ⟨S, fun _ hx ↦ (mem_sep_iff.mp hx).1, ?_⟩
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := j.endExtension S y hy
    obtain ⟨_, a, ha, hax⟩ := mem_sep_iff.mp hx
    have haT : j a ∈ T := hZT ▸ (j.mem_iff _ _).mpr ha
    have hav := (mem_sep_iff.mp haT).2
    rwa [← j.map_value_total, hax] at hav
  · intro hy
    obtain ⟨x, hx, rfl⟩ := j.endExtension X y (hY y hy)
    obtain ⟨a, ha⟩ := mem_range_iff.mp (hr.symm ▸ hx)
    have haD : a ∈ D := domain_eq_of_mem_function he ▸ mem_domain_of_kpair_mem ha
    have hax := value_eq_of_kpair_mem ha
    have haT : j a ∈ T := mem_sep_iff.mpr ⟨(j.mem_iff _ _).mpr haD, by
      rw [← j.map_value_total, hax]
      exact hy⟩
    have haZ : a ∈ Z := (j.mem_iff _ _).mp (hZT.symm ▸ haT)
    exact (j.mem_iff _ _).mpr (mem_sep_iff.mpr ⟨hx, a, haZ, hax⟩)

/-- Binary-function closure on an enumerating domain preserves the whole powerset. -/
theorem map_power_of_surjection_function_closed (j : MembershipEndExtension V W) {X D e : V}
    (he : e ∈ X ^ D) (hr : range e = X)
    (hc : ∀ f ∈ j (doubleton ∅ (doubleton ∅ ∅) : V) ^ j D,
      ∃ g ∈ (doubleton ∅ (doubleton ∅ ∅) : V) ^ D, j g = f) :
    j (℘ X) = ℘ (j X) := by
  apply mem_ext
  intro Y
  constructor
  · intro hY
    obtain ⟨Z, hZ, rfl⟩ := j.endExtension _ Y hY
    exact mem_power_iff.mpr ((j.subset_iff _ _).mpr (mem_power_iff.mp hZ))
  · intro hY
    obtain ⟨Z, hZ, rfl⟩ := j.subset_of_surjection_function_closed he hr hc (mem_power_iff.mp hY)
    exact (j.mem_iff _ _).mpr (mem_power_iff.mpr hZ)

end MembershipEndExtension
end ZFVP
