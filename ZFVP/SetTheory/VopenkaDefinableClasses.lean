import ZFVP.SetTheory.VopenkaScheme
import ZFVP.Syntax.PackFiniteParameters

/-! The two-variable Vopenka scheme applies to every class definable with
finitely many set parameters. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem vopenka_definable_class
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (L : V) (P : V → Prop) (hP : ℒₛₑₜ-predicate P) (hp : IsProperClass P)
    (hs : ∀ M, P M → IsStructureCode L M) :
    ∃ M N f : V, M ≠ N ∧ P M ∧ P N ∧ IsCodedElementaryEmbedding L M N f := by
  obtain ⟨φ, p, he⟩ := definable_predicate_one_parameter P hP
  have hp' : IsProperClass (fun M ↦ φ.Evalb ![M, p]) := by
    intro A
    obtain ⟨M, hM, hn⟩ := hp A
    exact ⟨M, (he M).mpr hM, hn⟩
  obtain ⟨M, N, f, hne, hM, hN, hf⟩ := hVP φ L p hp'
    (fun M hM ↦ hs M ((he M).mp hM))
  exact ⟨M, N, f, hne, (he M).mp hM, (he N).mp hN, hf⟩

end ZFVP
