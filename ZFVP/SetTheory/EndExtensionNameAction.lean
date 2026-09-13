import ZFVP.SetTheory.EndExtensionNameValue
import ZFVP.SetTheory.NameValueAction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameValue_nameAction_of_membership {P π G H τ : V}
    (hτ : IsForcingName P τ) (hGH : ∀ p ∈ P, π ‘ p ∈ H ↔ p ∈ G) :
    nameValue H (nameAction π τ) = nameValue G τ := by
  apply forcingName_induction P
    (fun τ ↦ nameValue H (nameAction π τ) = nameValue G τ) (by definability) ?_ τ hτ
  intro σ hσ ih
  apply mem_ext
  intro z
  rw [mem_nameValue_iff, mem_nameValue_iff]
  constructor
  · rintro ⟨υ, q, hq, hυq, hz⟩
    obtain ⟨ν, p, hp, he⟩ := (mem_nameAction_iff hσ π _).mp hυq
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact ⟨ν, p, (hGH p (forcingName_condition hσ hp)).mp hq, hp,
      hz.trans (ih ν p hp)⟩
  · rintro ⟨ν, p, hpG, hp, hz⟩
    exact ⟨nameAction π ν, π ‘ p, (hGH p (forcingName_condition hσ hp)).mpr hpG,
      (mem_nameAction_iff hσ π _).mpr ⟨ν, p, hp, rfl⟩, hz.trans (ih ν p hp).symm⟩

namespace MembershipEndExtension
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_nameActionStep (j : MembershipEndExtension V W) (π τ f : V) :
    j (nameActionStep π τ f) = nameActionStep (j π) (j τ) (j f) := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := j.endExtension _ y hy
    rw [nameActionStep, repl_spec] at hx ⊢
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨j z, (j.mem_iff _ _).mpr hz, ?_⟩
    rw [j.map_kpair, j.map_value_total, j.map_value_total, j.map_first, j.map_second]
  · intro hy
    rw [nameActionStep, repl_spec] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨x, hx, rfl⟩ := j.endExtension τ z hz
    rw [← j.map_first, ← j.map_second, ← j.map_value_total, ← j.map_value_total,
      ← j.map_kpair, j.mem_iff]
    rw [nameActionStep, repl_spec]
    exact ⟨x, hx, rfl⟩

theorem map_nameActionRecursion (j : MembershipEndExtension V W) {π N f : V}
    (hf : IsSubnameRecursion N (nameActionStep π) f) :
    IsSubnameRecursion (j N) (nameActionStep (j π)) (j f) := by
  let := hf.1
  refine ⟨j.map_function f, ?_, ?_⟩
  · rw [← j.map_relationDomain, hf.2.1]
  · intro x hx
    obtain ⟨τ, hτ, rfl⟩ := j.endExtension N x hx
    rw [← j.map_value_total, hf.2.2 τ hτ, j.map_nameActionStep,
      j.map_restrict, j.map_relationDomain]

theorem map_nameAction (j : MembershipEndExtension V W) (π τ : V) :
    j (nameAction π τ) = nameAction (j π) (j τ) := by
  let f := subnameRecursionTable (nameActionStep π) (by definability) τ
  have hf : IsSubnameRecursion (nameClosure τ) (nameActionStep π) f :=
    subnameRecursionTable_spec _ _ _
  have hg := j.map_nameActionRecursion hf
  have hτ : j τ ∈ j (nameClosure τ) := (j.mem_iff _ _).mpr (mem_nameClosure_self τ)
  have he := subnameRecursion_coherent (j.map_subnameClosed (nameClosure_closed τ))
    (nameClosure_closed (j τ)) hg (subnameRecursionTable_spec (nameActionStep (j π))
      (by definability) (j τ)) (j τ) hτ (mem_nameClosure_self (j τ))
  change j (f ‘ τ) = _
  rw [j.map_value_total]
  exact he

end MembershipEndExtension
end ZFVP
