import ZFVP.SetTheory.VopenkaScheme
import ZFVP.Syntax.LevyPackParameters

/-! Restricted Vopenka applies to classes with finitely many parameters at the same positive level. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem vopenka_levy_class {pol k n} (hk : 0 < k)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsLevyFormula pol k φ → VopenkaInstance (V := V) φ)
    (L : V) (φ : SetTheorySemisentence (n + 1)) (hφ : IsLevyFormula pol k φ) (v : Fin n → V)
    (hp : IsProperClass (fun M ↦ φ.Evalb (M :> v)))
    (hs : ∀ M, φ.Evalb (M :> v) → IsStructureCode L M) :
    ∃ M N f : V, M ≠ N ∧ φ.Evalb (M :> v) ∧ φ.Evalb (N :> v) ∧
      IsCodedElementaryEmbedding L M N f := by
  have he (M : V) := eval_levyPackParameters pol φ M v
  have hp' : IsProperClass (fun M ↦ (levyPackParameters pol φ).Evalb ![M, standardTuple v]) := by
    intro A
    obtain ⟨M, hM, hn⟩ := hp A
    exact ⟨M, (he M).mpr hM, hn⟩
  obtain ⟨M, N, f, hne, hM, hN, hf⟩ :=
    hVP (levyPackParameters pol φ) (levyPackParameters_levy hφ hk) L (standardTuple v) hp'
      (fun M hM ↦ hs M ((he M).mp hM))
  exact ⟨M, N, f, hne, (he M).mp hM, (he N).mp hN, hf⟩

theorem vopenka_levy_definable_class {pol k n} (hk : 0 < k)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsLevyFormula pol k φ → VopenkaInstance (V := V) φ)
    (L : V) (P : V → Prop) (φ : SetTheorySemisentence (n + 1))
    (hφ : IsLevyFormula pol k φ) (v : Fin n → V) (he : ∀ M, φ.Evalb (M :> v) ↔ P M)
    (hp : IsProperClass P) (hs : ∀ M, P M → IsStructureCode L M) :
    ∃ M N f : V, M ≠ N ∧ P M ∧ P N ∧ IsCodedElementaryEmbedding L M N f := by
  have hp' : IsProperClass (fun M ↦ φ.Evalb (M :> v)) := by
    intro A
    obtain ⟨M, hM, hn⟩ := hp A
    exact ⟨M, (he M).mpr hM, hn⟩
  obtain ⟨M, N, f, hne, hM, hN, hf⟩ := vopenka_levy_class hk hVP L φ hφ v hp'
    (fun M hM ↦ hs M ((he M).mp hM))
  exact ⟨M, N, f, hne, (he M).mp hM, (he N).mp hN, hf⟩

end ZFVP
