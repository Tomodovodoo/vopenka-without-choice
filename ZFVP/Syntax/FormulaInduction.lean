import ZFVP.Syntax.Formulas

/-! Definable induction over the internally finite formula family. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem formulaFamily_induction {L : V} (hL : IsLanguageCode L) (Γ : V)
    (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (hc : ∀ n ∈ (ω : V), P ⟨n, truthCode⟩ₖ ∧ P ⟨n, falsityCode⟩ₖ)
    (ha : ∀ n ∈ (ω : V), ∀ r args, IsAtomicArguments L Γ n r args →
      P ⟨n, atomCode r args⟩ₖ ∧ P ⟨n, negAtomCode r args⟩ₖ)
    (hb : ∀ n ∈ (ω : V), ∀ φ ψ, ⟨n, φ⟩ₖ ∈ formulaFamily L Γ →
      ⟨n, ψ⟩ₖ ∈ formulaFamily L Γ → P ⟨n, φ⟩ₖ → P ⟨n, ψ⟩ₖ →
      P ⟨n, andCode φ ψ⟩ₖ ∧ P ⟨n, orCode φ ψ⟩ₖ)
    (hq : ∀ n ∈ (ω : V), ∀ φ, ⟨succ n, φ⟩ₖ ∈ formulaFamily L Γ →
      P ⟨succ n, φ⟩ₖ → P ⟨n, allCode φ⟩ₖ ∧ P ⟨n, existsCode φ⟩ₖ) :
    ∀ p ∈ formulaFamily L Γ, P p := by
  let S : V := {p ∈ formulaFamily L Γ ; P p}
  have hS : IsFormulaClosed L Γ S := by
    intro n hn
    have hf := formulaFamily_closed hL Γ n hn
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ⟨mem_sep_iff.mpr ⟨hf.1.1, (hc n hn).1⟩,
        mem_sep_iff.mpr ⟨hf.1.2, (hc n hn).2⟩⟩
    · intro r args hargs
      exact ⟨mem_sep_iff.mpr ⟨(hf.2.1 r args hargs).1, (ha n hn r args hargs).1⟩,
        mem_sep_iff.mpr ⟨(hf.2.1 r args hargs).2, (ha n hn r args hargs).2⟩⟩
    · intro φ ψ hφ hψ
      obtain ⟨hφf, hφP⟩ := mem_sep_iff.mp hφ
      obtain ⟨hψf, hψP⟩ := mem_sep_iff.mp hψ
      exact ⟨mem_sep_iff.mpr ⟨(hf.2.2.1 φ ψ hφf hψf).1, (hb n hn φ ψ hφf hψf hφP hψP).1⟩,
        mem_sep_iff.mpr ⟨(hf.2.2.1 φ ψ hφf hψf).2, (hb n hn φ ψ hφf hψf hφP hψP).2⟩⟩
    · intro φ hφ
      obtain ⟨hφf, hφP⟩ := mem_sep_iff.mp hφ
      exact ⟨mem_sep_iff.mpr ⟨(hf.2.2.2 φ hφf).1, (hq n hn φ hφf hφP).1⟩,
        mem_sep_iff.mpr ⟨(hf.2.2.2 φ hφf).2, (hq n hn φ hφf hφP).2⟩⟩
  intro p hp
  exact (mem_sep_iff.mp (formulaFamily_minimal hS p hp)).2

theorem formulaFamily_context {L p : V} (hL : IsLanguageCode L) (Γ : V)
    (hp : p ∈ formulaFamily L Γ) : ∃ n ∈ (ω : V), ∃ φ, p = ⟨n, φ⟩ₖ := by
  apply formulaFamily_induction hL Γ (fun p ↦ ∃ n ∈ (ω : V), ∃ φ, p = ⟨n, φ⟩ₖ)
    (by definability) ?_ ?_ ?_ ?_ p hp
  · intro n hn
    exact ⟨⟨n, hn, _, rfl⟩, ⟨n, hn, _, rfl⟩⟩
  · intro n hn r args _
    exact ⟨⟨n, hn, _, rfl⟩, ⟨n, hn, _, rfl⟩⟩
  · intro n hn φ ψ _ _ _ _
    exact ⟨⟨n, hn, _, rfl⟩, ⟨n, hn, _, rfl⟩⟩
  · intro n hn φ _ _
    exact ⟨⟨n, hn, _, rfl⟩, ⟨n, hn, _, rfl⟩⟩

theorem formulaSet_context {L Γ n φ : V} (hL : IsLanguageCode L)
    (hφ : φ ∈ formulaSet L Γ n) : n ∈ (ω : V) := by
  obtain ⟨m, hm, ψ, heq⟩ := formulaFamily_context hL Γ ((mem_formulaSet_iff _ _ _ _).mp hφ)
  exact (kpair_inj heq).1 ▸ hm

theorem formulaSet_constants {L n : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) (Γ : V) :
    truthCode ∈ formulaSet L Γ n ∧ falsityCode ∈ formulaSet L Γ n :=
  ⟨(mem_formulaSet_iff _ _ _ _).mpr (formulaFamily_closed hL Γ n hn).1.1,
    (mem_formulaSet_iff _ _ _ _).mpr (formulaFamily_closed hL Γ n hn).1.2⟩

theorem formulaSet_atoms {L Γ n r args : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments L Γ n r args) :
    atomCode r args ∈ formulaSet L Γ n ∧ negAtomCode r args ∈ formulaSet L Γ n :=
  ⟨(mem_formulaSet_iff _ _ _ _).mpr ((formulaFamily_closed hL Γ n hn).2.1 r args ha).1,
    (mem_formulaSet_iff _ _ _ _).mpr ((formulaFamily_closed hL Γ n hn).2.1 r args ha).2⟩

theorem formulaSet_binary {L Γ n φ ψ : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L Γ n) (hψ : ψ ∈ formulaSet L Γ n) :
    andCode φ ψ ∈ formulaSet L Γ n ∧ orCode φ ψ ∈ formulaSet L Γ n := by
  have h := (formulaFamily_closed hL Γ n hn).2.2.1 φ ψ
    ((mem_formulaSet_iff _ _ _ _).mp hφ) ((mem_formulaSet_iff _ _ _ _).mp hψ)
  exact ⟨(mem_formulaSet_iff _ _ _ _).mpr h.1, (mem_formulaSet_iff _ _ _ _).mpr h.2⟩

theorem formulaSet_quantifiers {L Γ n φ : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L Γ (succ n)) :
    allCode φ ∈ formulaSet L Γ n ∧ existsCode φ ∈ formulaSet L Γ n := by
  have h := (formulaFamily_closed hL Γ n hn).2.2.2 φ ((mem_formulaSet_iff _ _ _ _).mp hφ)
  exact ⟨(mem_formulaSet_iff _ _ _ _).mpr h.1, (mem_formulaSet_iff _ _ _ _).mpr h.2⟩

theorem formulaSet_induction {L : V} (hL : IsLanguageCode L) (Γ : V)
    (P : V → V → Prop) (hP : ℒₛₑₜ-relation P)
    (hc : ∀ n ∈ (ω : V), P n truthCode ∧ P n falsityCode)
    (ha : ∀ n ∈ (ω : V), ∀ r args, IsAtomicArguments L Γ n r args →
      P n (atomCode r args) ∧ P n (negAtomCode r args))
    (hb : ∀ n ∈ (ω : V), ∀ φ ψ, φ ∈ formulaSet L Γ n → ψ ∈ formulaSet L Γ n →
      P n φ → P n ψ → P n (andCode φ ψ) ∧ P n (orCode φ ψ))
    (hq : ∀ n ∈ (ω : V), ∀ φ, φ ∈ formulaSet L Γ (succ n) → P (succ n) φ →
      P n (allCode φ) ∧ P n (existsCode φ)) :
    ∀ n φ, φ ∈ formulaSet L Γ n → P n φ := by
  have h : ∀ p ∈ formulaFamily L Γ, P (kpair.π₁ p) (kpair.π₂ p) := by
    apply formulaFamily_induction hL Γ (fun p ↦ P (kpair.π₁ p) (kpair.π₂ p)) (by definability)
    · intro n hn
      simpa using hc n hn
    · intro n hn r args hargs
      simpa using ha n hn r args hargs
    · intro n hn φ ψ hφ hψ ihφ ihψ
      simpa using hb n hn φ ψ ((mem_formulaSet_iff _ _ _ _).mpr hφ)
        ((mem_formulaSet_iff _ _ _ _).mpr hψ) (by simpa using ihφ) (by simpa using ihψ)
    · intro n hn φ hφ ihφ
      simpa using hq n hn φ ((mem_formulaSet_iff _ _ _ _).mpr hφ) (by simpa using ihφ)
  intro n φ hφ
  simpa using h ⟨n, φ⟩ₖ ((mem_formulaSet_iff _ _ _ _).mp hφ)

end ZFVP
