import ZFVP.SetTheory.ForcingNameUnions
import ZFVP.ModelTheory.ForcingModelSequences

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem mem_nameUnion_iff (A : ForcingContext V) (B : V) (hB : ∀ τ ∈ B, IsForcingName A.P τ)
    (x : A.Model) : x ∈ A.ofName ⟨⋃ˢ B, forcingName_sUnion hB⟩ ↔
      ∃ τ : ForcingName A.P, τ.val ∈ B ∧ x ∈ A.ofName τ := by
  rw [A.mem_ofName_iff]
  constructor
  · rintro ⟨ν, p, hpG, hpair, rfl⟩
    obtain ⟨τ, hτ, hpair⟩ := mem_sUnion_iff.mp hpair
    exact ⟨⟨τ, hB τ hτ⟩, hτ, (A.mem_ofName_iff _ _).mpr ⟨ν, p, hpG, hpair, rfl⟩⟩
  · rintro ⟨τ, hτ, hx⟩
    obtain ⟨ν, p, hpG, hpair, rfl⟩ := (A.mem_ofName_iff τ x).mp hx
    exact ⟨ν, p, hpG, mem_sUnion_iff.mpr ⟨τ.val, hτ, hpair⟩, rfl⟩

theorem sequenceNameUnion_value (A : ForcingContext V) (s : V) [IsFunction s]
    (hs : IsNameSequence A.P s) :
    A.ofName ⟨⋃ˢ range s, hs.union_isName⟩ = ⋃ˢ range (A.sequenceValue s hs) := by
  have hB : ∀ τ ∈ range s, IsForcingName A.P τ := by
    intro τ hτ
    obtain ⟨i, hiτ⟩ := mem_range_iff.mp hτ
    rw [← value_eq_of_kpair_mem hiτ]
    exact hs i (mem_domain_of_kpair_mem hiτ)
  apply mem_ext
  intro x
  rw [A.mem_nameUnion_iff _ hB x, mem_sUnion_iff]
  constructor
  · rintro ⟨τ, hτ, hxτ⟩
    obtain ⟨i, hiτ⟩ := mem_range_iff.mp hτ
    have hi := mem_domain_of_kpair_mem hiτ
    have he : A.ofName τ = (A.sequenceValue s hs) ‘ (A.check i) := by
      rw [A.sequenceValue_value s hs hi]
      exact congrArg A.ofName (Subtype.ext (value_eq_of_kpair_mem hiτ).symm)
    exact ⟨A.ofName τ, he.symm ▸ mem_range_of_kpair_mem
      (kpair_value_mem (by rw [A.sequenceValue_domain]; exact (A.check_mem_iff _ _).mpr hi)), hxτ⟩
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨i, hiy⟩ := mem_range_iff.mp hy
    obtain ⟨j, hj, he⟩ := (A.mem_sequenceValue s hs _).mp hiy
    obtain ⟨_, rfl⟩ := kpair_iff.mp he
    exact ⟨⟨s ‘ j, hs j hj⟩, mem_range_of_kpair_mem (kpair_value_mem hj), hxy⟩

end ForcingContext
end ZFVP
