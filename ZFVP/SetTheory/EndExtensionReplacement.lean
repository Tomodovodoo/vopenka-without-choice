import ZFVP.SetTheory.EndExtensionSets

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_repl (j : MembershipEndExtension V W) (A : V) (F : V → V) (Q : W → W)
    (hF : ℒₛₑₜ-function₁ F) (hQ : ℒₛₑₜ-function₁ Q)
    (hmap : ∀ x ∈ A, j (F x) = Q (j x)) :
    j (repl F hF A) = repl Q hQ (j A) := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := j.endExtension _ y hy
    obtain ⟨x, hx, rfl⟩ := (repl_spec hF).mp hz
    exact (repl_spec hQ).mpr ⟨j x, (j.mem_iff _ _).mpr hx, hmap x hx⟩
  · intro hy
    obtain ⟨z, hz, he⟩ := (repl_spec hQ).mp hy
    obtain ⟨x, hx, rfl⟩ := j.endExtension A z hz
    rw [← hmap x hx] at he
    rw [he, j.mem_iff]
    exact (repl_spec hF).mpr ⟨x, hx, rfl⟩

end MembershipEndExtension
end ZFVP
