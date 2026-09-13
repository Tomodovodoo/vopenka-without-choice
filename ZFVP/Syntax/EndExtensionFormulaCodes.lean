import ZFVP.Syntax.EndExtensionTerms
import ZFVP.Syntax.FormulaCodes

/-! Formula constructors and arbitrary atomic arguments under ZF end extensions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_equalityToken (j : MembershipEndExtension V W) : j equalityToken = equalityToken := j.map_empty

theorem map_relationToken (j : MembershipEndExtension V W) (r : V) :
    j (relationToken r) = relationToken (j r) := by
  unfold relationToken
  rw [j.map_kpair, show j (1 : V) = (1 : W) from j.map_numeral 1]

theorem map_truthCode (j : MembershipEndExtension V W) : j truthCode = truthCode := by
  unfold truthCode
  rw [j.map_kpair, j.map_empty, show j (0 : V) = (0 : W) from j.map_numeral 0]

theorem map_falsityCode (j : MembershipEndExtension V W) : j falsityCode = falsityCode := by
  unfold falsityCode
  rw [j.map_kpair, j.map_empty, show j (1 : V) = (1 : W) from j.map_numeral 1]

theorem map_atomCode (j : MembershipEndExtension V W) (r args : V) :
    j (atomCode r args) = atomCode (j r) (j args) := j.map_functionTermCode r args

theorem map_negAtomCode (j : MembershipEndExtension V W) (r args : V) :
    j (negAtomCode r args) = negAtomCode (j r) (j args) := by
  unfold negAtomCode
  rw [j.map_kpair, j.map_kpair, show j (3 : V) = (3 : W) from j.map_numeral 3]

theorem map_andCode (j : MembershipEndExtension V W) (φ ψ : V) :
    j (andCode φ ψ) = andCode (j φ) (j ψ) := by
  unfold andCode
  rw [j.map_kpair, j.map_kpair, show j (4 : V) = (4 : W) from j.map_numeral 4]

theorem map_orCode (j : MembershipEndExtension V W) (φ ψ : V) :
    j (orCode φ ψ) = orCode (j φ) (j ψ) := by
  unfold orCode
  rw [j.map_kpair, j.map_kpair, show j (5 : V) = (5 : W) from j.map_numeral 5]

theorem map_allCode (j : MembershipEndExtension V W) (φ : V) : j (allCode φ) = allCode (j φ) := by
  unfold allCode
  rw [j.map_kpair, show j (6 : V) = (6 : W) from j.map_numeral 6]

theorem map_existsCode (j : MembershipEndExtension V W) (φ : V) : j (existsCode φ) = existsCode (j φ) := by
  unfold existsCode
  rw [j.map_kpair, show j (7 : V) = (7 : W) from j.map_numeral 7]

theorem atomicArguments_map (j : MembershipEndExtension V W) {L Γ n r args : V}
    (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) (ha : IsAtomicArguments L Γ n r args) :
    IsAtomicArguments (j L) (j Γ) (j n) (j r) (j args) := by
  rcases ha with ⟨rfl, ha⟩ | ⟨s, hs, rfl, ha⟩
  · refine Or.inl ⟨j.map_equalityToken, ?_⟩
    rw [← j.map_termSet hL hn Γ, ← show j (2 : V) = (2 : W) from j.map_numeral 2]
    exact (j.function_iff _ _ _).mpr ha
  · refine Or.inr ⟨j s, ?_, j.map_relationToken s, ?_⟩
    · rw [← j.map_relationSymbols]; exact (j.mem_iff _ _).mpr hs
    · rw [← j.map_termSet hL hn Γ, ← j.map_relationArity hL hs]
      exact (j.function_iff _ _ _).mpr ha

theorem atomicArguments_preimages (j : MembershipEndExtension V W) {L Γ n : V}
    (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) {r args : W}
    (ha : IsAtomicArguments (j L) (j Γ) (j n) r args) :
    ∃ s bs : V, r = j s ∧ args = j bs ∧ IsAtomicArguments L Γ n s bs := by
  rcases ha with ⟨rfl, ha⟩ | ⟨t, ht, rfl, ha⟩
  · rw [← j.map_termSet hL hn Γ, ← show j (2 : V) = (2 : W) from j.map_numeral 2,
      ← j.map_finiteFunctionSet _ (show (2 : V) ∈ (ω : V) by simp)] at ha
    obtain ⟨bs, hbs, rfl⟩ := j.endExtension _ args ha
    exact ⟨equalityToken, bs, j.map_equalityToken.symm, rfl, Or.inl ⟨rfl, hbs⟩⟩
  · rw [← j.map_relationSymbols] at ht
    obtain ⟨s, hs, rfl⟩ := j.endExtension _ t ht
    rw [← j.map_termSet hL hn Γ, ← j.map_relationArity hL hs,
      ← j.map_finiteFunctionSet _ (hL.relation_arity_natural hs)] at ha
    obtain ⟨bs, hbs, rfl⟩ := j.endExtension _ args ha
    exact ⟨relationToken s, bs, (j.map_relationToken s).symm, rfl, Or.inr ⟨s, hs, rfl, hbs⟩⟩

end MembershipEndExtension
end ZFVP
