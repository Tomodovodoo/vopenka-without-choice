import ZFVP.Syntax.Terms
import ZFVP.SetTheory.StandardNaturals

/-! Definable induction and constructor inversion for internal terms. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem termSet_induction {L n : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (Γ : V) (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (hb : ∀ i ∈ n, P (boundVarCode i)) (hf : ∀ x ∈ Γ, P (freeVarCode x))
    (happ : ∀ f ∈ functionSymbols L, ∀ args ∈ termSet L Γ n ^ ((functionArities L) ‘ f),
      (∀ t ∈ range args, P t) → P (functionTermCode f args)) :
    ∀ t ∈ termSet L Γ n, P t := by
  let S : V := {t ∈ termSet L Γ n ; P t}
  have hSsub : S ⊆ termSet L Γ n := by
    intro t ht
    exact (show t ∈ termSet L Γ n ∧ P t from by simpa [S] using ht).1
  have hclosed := termSet_closed hL hn Γ
  have hS : IsTermClosed L Γ n S := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simpa [S] using And.intro (hclosed.1 i hi) (hb i hi)
    · intro x hx
      simpa [S] using And.intro (hclosed.2.1 x hx) (hf x hx)
    · intro f hf args ha
      have haT := mem_function_of_mem_function_of_subset ha hSsub
      have hall : ∀ t ∈ range args, P t := by
        intro t ht
        have htS := range_subset_of_mem_function ha t ht
        exact (show t ∈ termSet L Γ n ∧ P t from by simpa [S] using htS).2
      simpa [S] using And.intro (hclosed.2.2 f hf args haT) (happ f hf args haT hall)
  intro t ht
  have htS := termSet_minimal hS t ht
  exact (show t ∈ termSet L Γ n ∧ P t from by simpa [S] using htS).2

theorem termSet_cases {L n t : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (Γ : V) (ht : t ∈ termSet L Γ n) :
    (∃ i ∈ n, t = boundVarCode i) ∨ (∃ x ∈ Γ, t = freeVarCode x) ∨
      ∃ f ∈ functionSymbols L, ∃ args ∈ termSet L Γ n ^ ((functionArities L) ‘ f),
        t = functionTermCode f args := by
  apply termSet_induction hL hn Γ
    (fun t ↦ (∃ i ∈ n, t = boundVarCode i) ∨ (∃ x ∈ Γ, t = freeVarCode x) ∨
      ∃ f ∈ functionSymbols L, ∃ args ∈ termSet L Γ n ^ ((functionArities L) ‘ f),
        t = functionTermCode f args) (by definability) ?_ ?_ ?_ t ht
  · intro i hi
    exact Or.inl ⟨i, hi, rfl⟩
  · intro x hx
    exact Or.inr (Or.inl ⟨x, hx, rfl⟩)
  · intro f hf args ha _
    exact Or.inr (Or.inr ⟨f, hf, args, ha, rfl⟩)

@[simp] theorem boundVarCode_inj (i j : V) : boundVarCode i = boundVarCode j ↔ i = j := by
  simp [boundVarCode]
@[simp] theorem freeVarCode_inj (x y : V) : freeVarCode x = freeVarCode y ↔ x = y := by
  simp [freeVarCode]
@[simp] theorem functionTermCode_inj (f args g bs : V) :
    functionTermCode f args = functionTermCode g bs ↔ f = g ∧ args = bs := by
  simp [functionTermCode]

@[simp] theorem boundVarCode_ne_freeVarCode (i x : V) : boundVarCode i ≠ freeVarCode x := by
  simp [boundVarCode, freeVarCode]

@[simp] theorem boundVarCode_ne_functionTermCode (i f args : V) :
    boundVarCode i ≠ functionTermCode f args := by
  intro h
  have htag : (0 : V) = (2 : V) := (kpair_inj h).1
  have hnat : (0 : ℕ) = 2 := (natCast_eq_iff (V := V) 0 2).mp htag
  contradiction

@[simp] theorem freeVarCode_ne_functionTermCode (x f args : V) :
    freeVarCode x ≠ functionTermCode f args := by
  intro h
  have htag : (1 : V) = (2 : V) := (kpair_inj h).1
  have hnat : (1 : ℕ) = 2 := (natCast_eq_iff (V := V) 1 2).mp htag
  contradiction

theorem functionTermCode_mem_iff {L n : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (Γ f args : V) : functionTermCode f args ∈ termSet L Γ n ↔
      f ∈ functionSymbols L ∧ args ∈ termSet L Γ n ^ ((functionArities L) ‘ f) := by
  constructor
  · intro ht
    rcases termSet_cases hL hn Γ ht with ⟨i, _, heq⟩ | ⟨x, _, heq⟩ | ⟨g, hg, bs, hbs, heq⟩
    · exact False.elim (boundVarCode_ne_functionTermCode i f args heq.symm)
    · exact False.elim (freeVarCode_ne_functionTermCode x f args heq.symm)
    · obtain ⟨rfl, rfl⟩ := (functionTermCode_inj f args g bs).mp heq
      exact ⟨hg, hbs⟩
  · rintro ⟨hf, ha⟩
    exact (termSet_closed hL hn Γ).2.2 f hf args ha

theorem boundVarCode_mem_iff {L n : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (Γ i : V) : boundVarCode i ∈ termSet L Γ n ↔ i ∈ n := by
  constructor
  · intro ht
    rcases termSet_cases hL hn Γ ht with ⟨j, hj, heq⟩ | ⟨x, _, heq⟩ | ⟨f, _, args, _, heq⟩
    · exact (boundVarCode_inj i j).mp heq ▸ hj
    · exact False.elim (boundVarCode_ne_freeVarCode i x heq)
    · exact False.elim (boundVarCode_ne_functionTermCode i f args heq)
  · exact (termSet_closed hL hn Γ).1 i

theorem freeVarCode_mem_iff {L n : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (Γ x : V) : freeVarCode x ∈ termSet L Γ n ↔ x ∈ Γ := by
  constructor
  · intro ht
    rcases termSet_cases hL hn Γ ht with ⟨i, _, heq⟩ | ⟨y, hy, heq⟩ | ⟨f, _, args, _, heq⟩
    · exact False.elim (boundVarCode_ne_freeVarCode i x heq.symm)
    · exact (freeVarCode_inj x y).mp heq ▸ hy
    · exact False.elim (freeVarCode_ne_functionTermCode x f args heq)
  · exact (termSet_closed hL hn Γ).2.1 x

end ZFVP
