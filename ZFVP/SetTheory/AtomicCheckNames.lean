import ZFVP.SetTheory.AtomicMembership
import ZFVP.SetTheory.CheckNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem atomicEquality_checkName_injective {P R one : V} (hR : IsForcingPreorder P R)
    (hone : IsForcingTop P R one) (x y p : V)
    (hp : p ∈ atomicEquality P R (checkName one x) (checkName one y)) : x = y := by
  have h := set_induction (fun x : V ↦ ∀ y p,
      p ∈ atomicEquality P R (checkName one x) (checkName one y) → x = y) (by definability) ?_ x
  · exact h y p hp
  intro x ih y p hp
  obtain ⟨hpP, hl, hr⟩ := (mem_atomicEquality_iff _ _ _ _ _).mp hp
  apply SetTheory.mem_ext_iff.mpr
  intro z
  constructor
  · intro hz
    have hpair := (mem_checkName_iff one x _).mpr ⟨z, hz, rfl⟩
    obtain ⟨r, _, _, ν, t, hνt, _, he⟩ := hl (checkName one z) one hpair p hpP
      (hR.2.1 p hpP) (hone.2 p hpP)
    obtain ⟨w, hw, hpair'⟩ := (mem_checkName_iff one y _).mp hνt
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp hpair'
    have hzw := ih z hz w r he
    simpa only [hzw] using hw
  · intro hz
    have hpair := (mem_checkName_iff one y _).mpr ⟨z, hz, rfl⟩
    obtain ⟨r, _, _, ν, t, hνt, _, he⟩ := hr (checkName one z) one hpair p hpP
      (hR.2.1 p hpP) (hone.2 p hpP)
    obtain ⟨w, hw, hpair'⟩ := (mem_checkName_iff one x _).mp hνt
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp hpair'
    have hwz := ih w hw z r he
    exact hwz ▸ hw

theorem mem_atomicEquality_checkName_iff {P R one : V} (hR : IsForcingPreorder P R)
    (hone : IsForcingTop P R one) (x y p : V) :
    p ∈ atomicEquality P R (checkName one x) (checkName one y) ↔ p ∈ P ∧ x = y := by
  constructor
  · intro hp
    exact ⟨atomicEquality_subset _ _ _ _ p hp, atomicEquality_checkName_injective hR hone x y p hp⟩
  · rintro ⟨hp, rfl⟩
    exact (atomicEquality_refl hR _).symm ▸ hp

theorem mem_atomicMembership_checkName_iff {P R one : V} (hR : IsForcingPreorder P R)
    (hone : IsForcingTop P R one) (x y p : V) :
    p ∈ atomicMembership P R (checkName one x) (checkName one y) ↔ p ∈ P ∧ x ∈ y := by
  constructor
  · intro hp
    obtain ⟨hpP, hh⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hp
    obtain ⟨r, _, _, ν, s, hνs, _, he⟩ := hh p hpP (hR.2.1 p hpP)
    obtain ⟨z, hz, hpair⟩ := (mem_checkName_iff one y _).mp hνs
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp hpair
    have hxz := atomicEquality_checkName_injective hR hone x z r he
    exact ⟨hpP, by simpa only [hxz] using hz⟩
  · rintro ⟨hp, hx⟩
    have hpair := (mem_checkName_iff one y _).mpr ⟨x, hx, rfl⟩
    exact atomicMembership_mono hR (atomicMembership_of_pair hR hone.1 hpair) hp (hone.2 p hp)

end ZFVP
