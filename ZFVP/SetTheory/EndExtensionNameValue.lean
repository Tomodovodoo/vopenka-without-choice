import ZFVP.SetTheory.EndExtensionAtomicForcing
import ZFVP.SetTheory.NameValue

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_relationDomain (j : MembershipEndExtension V W) (r : V) :
    j (domain r) = domain (j r) := by
  apply mem_ext
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := j.endExtension _ x hx
    obtain ⟨b, hab⟩ := mem_domain_iff.mp ha
    exact mem_domain_iff.mpr ⟨j b, by rw [← j.map_kpair, j.mem_iff]; exact hab⟩
  · intro hx
    obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
    obtain ⟨a, b, hab, rfl, rfl⟩ := (j.pair_mem_image_iff r x y).mp hxy
    exact (j.mem_iff _ _).mpr (mem_domain_of_kpair_mem hab)

theorem map_nameValueStep (j : MembershipEndExtension V W) (G τ f : V) :
    j (nameValueStep G τ f) = nameValueStep (j G) (j τ) (j f) := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := j.endExtension _ y hy
    obtain ⟨σ, p, hp, hσp, rfl⟩ := (mem_nameValueStep_iff _ _ _ _).mp hx
    exact (mem_nameValueStep_iff _ _ _ _).mpr ⟨j σ, j p, (j.mem_iff _ _).mpr hp,
      by rw [← j.map_kpair, j.mem_iff]; exact hσp, j.map_value_total f σ⟩
  · intro hy
    obtain ⟨σ, p, hp, hσp, he⟩ := (mem_nameValueStep_iff _ _ _ _).mp hy
    obtain ⟨ν, q, hνq, rfl, rfl⟩ := (j.pair_mem_image_iff τ σ p).mp hσp
    rw [← j.map_value_total] at he
    rw [he, j.mem_iff]
    exact (mem_nameValueStep_iff _ _ _ _).mpr ⟨ν, q, (j.mem_iff _ _).mp hp, hνq, rfl⟩

theorem map_nameValueRecursion (j : MembershipEndExtension V W) {G N f : V}
    (hf : IsSubnameRecursion N (nameValueStep G) f) :
    IsSubnameRecursion (j N) (nameValueStep (j G)) (j f) := by
  letI : IsFunction f := hf.1
  refine ⟨j.map_function f, ?_, ?_⟩
  · rw [← j.map_relationDomain, hf.2.1]
  · intro x hx
    obtain ⟨τ, hτ, rfl⟩ := j.endExtension N x hx
    rw [← j.map_value_total, hf.2.2 τ hτ, j.map_nameValueStep,
      j.map_restrict, j.map_relationDomain]

theorem map_nameValue (j : MembershipEndExtension V W) (G τ : V) :
    j (nameValue G τ) = nameValue (j G) (j τ) := by
  let f := subnameRecursionTable (nameValueStep G) (by definability) τ
  have hf : IsSubnameRecursion (nameClosure τ) (nameValueStep G) f :=
    subnameRecursionTable_spec _ _ _
  have hg := j.map_nameValueRecursion hf
  have hτ : j τ ∈ j (nameClosure τ) := (j.mem_iff _ _).mpr (mem_nameClosure_self τ)
  have he := subnameRecursion_coherent (j.map_subnameClosed (nameClosure_closed τ))
    (nameClosure_closed (j τ)) hg (subnameRecursionTable_spec (nameValueStep (j G)) (by definability) (j τ))
    (j τ) hτ (mem_nameClosure_self (j τ))
  change j (f ‘ τ) = _
  rw [j.map_value_total]
  exact he

end MembershipEndExtension
end ZFVP
