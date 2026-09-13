import ZFVP.Syntax.Subterms
import ZFVP.SetTheory.WellFoundedRecursion

/-! Recursion on internal term codes, including nonstandard finite terms. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem predecessors_boundVarCode (T i : V) :
    predecessors (subtermRelation T) T (boundVarCode i) = ∅ := by
  apply mem_ext
  intro s
  simp [kpair_mem_subtermRelation_iff]

@[simp] theorem predecessors_freeVarCode (T x : V) :
    predecessors (subtermRelation T) T (freeVarCode x) = ∅ := by
  apply mem_ext
  intro s
  simp [kpair_mem_subtermRelation_iff]

theorem predecessors_functionTermCode {L n f args : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (Γ : V) (ht : functionTermCode f args ∈ termSet L Γ n) :
    predecessors (subtermRelation (termSet L Γ n)) (termSet L Γ n)
      (functionTermCode f args) = range args := by
  apply mem_ext
  intro s
  constructor
  · intro hs
    obtain ⟨_, hr⟩ := (mem_predecessors_iff _ _ _ _).mp hs
    obtain ⟨_, _, g, bs, heq, hbs⟩ := (kpair_mem_subtermRelation_iff _ _ _).mp hr
    obtain ⟨rfl, rfl⟩ := (functionTermCode_inj f args g bs).mp heq
    exact hbs
  · intro hs
    exact (mem_predecessors_iff _ _ _ _).mpr
      ⟨immediate_subterm_mem hL hn Γ ht hs, immediate_subterm_relation hL hn Γ ht hs⟩

noncomputable def termRecursion (L Γ n : V) (F : V → V → V)
    (hF : ℒₛₑₜ-function₂ F) : V :=
  wellFoundedRecursion (subtermRelation_wellFounded (termSet L Γ n)) F hF

instance termRecursion_isFunction (L Γ n : V) (F : V → V → V)
    (hF : ℒₛₑₜ-function₂ F) : IsFunction (termRecursion L Γ n F hF) :=
  wellFoundedRecursion_isFunction _ F hF

@[simp] theorem domain_termRecursion (L Γ n : V) (F : V → V → V)
    (hF : ℒₛₑₜ-function₂ F) : domain (termRecursion L Γ n F hF) = termSet L Γ n :=
  domain_wellFoundedRecursion _ F hF

theorem termRecursion_boundVar {L n i : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (Γ : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F)
    (hi : i ∈ n) :
    (termRecursion L Γ n F hF) ‘ (boundVarCode i) = F (boundVarCode i) ∅ := by
  have h := wellFoundedRecursion_value (subtermRelation_wellFounded (termSet L Γ n)) F hF
    ((boundVarCode_mem_iff hL hn Γ i).mpr hi)
  simpa [termRecursion] using h

theorem termRecursion_freeVar {L n x : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (Γ : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F)
    (hx : x ∈ Γ) :
    (termRecursion L Γ n F hF) ‘ (freeVarCode x) = F (freeVarCode x) ∅ := by
  have h := wellFoundedRecursion_value (subtermRelation_wellFounded (termSet L Γ n)) F hF
    ((freeVarCode_mem_iff hL hn Γ x).mpr hx)
  simpa [termRecursion] using h

theorem termRecursion_function {L n f args : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (Γ : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F)
    (ht : functionTermCode f args ∈ termSet L Γ n) :
    (termRecursion L Γ n F hF) ‘ (functionTermCode f args) =
      F (functionTermCode f args) ((termRecursion L Γ n F hF) ↾ (range args)) := by
  have h := wellFoundedRecursion_value (subtermRelation_wellFounded (termSet L Γ n)) F hF ht
  rw [predecessors_functionTermCode hL hn Γ ht] at h
  exact h

end ZFVP
