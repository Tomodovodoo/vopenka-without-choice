import ZFVP.Syntax.EndExtensionMembershipSyntax

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem membershipFormulaCode_preimage_at (j : MembershipEndExtension V W) {n : V} {φ : W}
    (hφ : IsMembershipFormulaCode (j n) φ) :
    ∃ ψ : V, φ = j ψ ∧ IsMembershipFormulaCode n ψ := by
  obtain ⟨m, ψ, hm, rfl, hψ⟩ := j.membershipFormulaCode_preimages hφ
  obtain rfl := j.injective hm
  exact ⟨ψ, rfl, hψ⟩

theorem membershipAtomic_preimages (j : MembershipEndExtension V W) {n : V} (hn : n ∈ (ω : V))
    {r args : W} (ha : IsAtomicArguments membershipLanguageCode ∅ (j n) r args) :
    ∃ s bs : V, r = j s ∧ args = j bs ∧ IsAtomicArguments membershipLanguageCode ∅ n s bs := by
  rw [← j.map_membershipLanguageCode, ← j.map_empty] at ha
  exact j.atomicArguments_preimages membershipLanguageCode_valid hn ha

end MembershipEndExtension
end ZFVP
