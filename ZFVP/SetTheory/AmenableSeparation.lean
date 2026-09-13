import ZFVP.ModelTheory.FaithfulExtension
import ZFVP.SetTheory.NaturalPredecessor

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

instance PredicateExpansion.eq {V : Type*} [SetStructure V] (X : V → Prop) :
    @Language.DefinableRel predicateLanguage V (predicateExpansion X) Eq :=
  PredicateExpansion.base X _
instance PredicateExpansion.mem {V : Type*} [SetStructure V] (X : V → Prop) :
    @Language.DefinableRel predicateLanguage V (predicateExpansion X) Membership.mem :=
  PredicateExpansion.base X _


theorem PredicateExpansion.graph_comp {V : Type*} [SetStructure V]
    {X : V → Prop} {F : V → V} (hF : PredicateExpansion.Fun X F)
    {n : ℕ} {g h : (Fin n → V) → V}
    (hg : Language.DefinableFunction ℒₛₑₜ g) (hh : Language.DefinableFunction ℒₛₑₜ h) :
    PredicateExpansion.Definable X (fun v ↦ g v = F (h v)) := by
  let : Structure predicateLanguage V := predicateExpansion X
  exact Language.DefinableRel.comp (P := fun y x : V ↦ y = F x) (hP := hF)
    (@PredicateExpansion.base V _ X _ _ hg) (@PredicateExpansion.base V _ X _ _ hh)
syntax "relative_definability" term : tactic
macro_rules
  | `(tactic| relative_definability $X:term) =>
  `(tactic| solve
    | assumption
    | (refine PredicateExpansion.graph_comp (by assumption) ?_ ?_ <;> definability)
    | (apply Language.Definable.and <;> relative_definability $X)
    | (apply Language.Definable.or <;> relative_definability $X)
    | (apply Language.Definable.not <;> relative_definability $X)
    | (apply Language.Definable.imp <;> relative_definability $X)
    | (apply Language.Definable.biconditional <;> relative_definability $X)
    | (apply Language.Definable.all <;> relative_definability $X)
    | (apply Language.Definable.exs <;> relative_definability $X)
    | (refine @PredicateExpansion.base _ _ $X _ _ ?_; definability)
    | (apply Language.DefinablePred.comp <;> relative_definability $X)
    | (apply Language.DefinableRel.comp <;> relative_definability $X)
    | (apply Language.DefinableFunction₁.comp <;> relative_definability $X)
    | (apply Language.DefinableFunction₂.comp <;> relative_definability $X))
namespace IsAmenablePredicate
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  {X : V → Prop} (hX : IsAmenablePredicate X)
include hX

/-- Separation in the expanded language supplies ordinal minimization. -/
theorem leastOrdinal (P : V → Prop) (hP : PredicateExpansion.Pred X P)
    (hex : ∃ α : V, IsOrdinal α ∧ P α) : ∃! α, IsLeastOrdinal P α := by
  obtain ⟨α, hα, hPα⟩ := hex
  have : IsOrdinal α := hα
  obtain ⟨A, hA⟩ := hX.separation P hP (succ α)
  obtain ⟨β, hβ, _⟩ := leastOrdinal_existsUnique (fun z : V ↦ z ∈ A) (by clear hA; definability)
    ⟨α, hα, (hA α).mpr ⟨by simp, hPα⟩⟩
  have hβP := ((hA β).mp hβ.2.1).2
  have hmin : ∀ γ : V, IsOrdinal γ → P γ → β ⊆ γ := by
    intro γ hγ hPγ
    have : IsOrdinal γ := hγ
    by_cases hγα : γ ∈ succ α
    · exact hβ.2.2 γ hγ ((hA γ).mpr ⟨hγα, hPγ⟩)
    · have hαγ : α ⊆ γ := by
        rcases IsOrdinal.mem_trichotomy α γ with hh | hh | hh
        · exact IsOrdinal.toIsTransitive.transitive α hh
        · rw [hh]
        · exact False.elim (hγα (mem_succ_iff.mpr (Or.inr hh)))
      exact subset_trans (hβ.2.2 α hα ((hA α).mpr ⟨by simp, hPα⟩)) hαγ
  refine ⟨β, ⟨hβ.1, hβP, hmin⟩, ?_⟩
  intro γ hγ
  exact subset_antisymm (hγ.2.2 β hβ.1 hβP) (hmin γ hγ.1 hγ.2.1)

/-- Induction for every predicate definable in the expansion, including
formulas with arbitrary set parameters. -/
theorem naturalInduction (P : V → Prop) (hP : PredicateExpansion.Pred X P)
    (hzero : P 0) (hstep : ∀ n ∈ (ω : V), P n → P (succ n)) :
    ∀ n ∈ (ω : V), P n := by
  let : Structure predicateLanguage V := predicateExpansion X
  have : Language.DefinablePred predicateLanguage P := hP
  have hnP : PredicateExpansion.Pred X (fun n ↦ n ∈ (ω : V) ∧ ¬ P n) := by
    change Language.DefinablePred predicateLanguage (fun n : V ↦ n ∈ (ω : V) ∧ ¬ P n)
    relative_definability X
  intro n hn
  by_contra hpn
  obtain ⟨k, hk, _⟩ := hX.leastOrdinal _ hnP ⟨n, IsOrdinal.of_mem hn, hn, hpn⟩
  rcases internalNatural_cases hk.2.1.1 with rfl | ⟨i, hi, rfl⟩
  · exact hk.2.1.2 hzero
  · have hPi : P i := by
      by_contra hpi
      have hs := hk.2.2 i (IsOrdinal.of_mem hi) ⟨hi, hpi⟩
      exact mem_irrefl i (hs i (by simp))
    exact hk.2.1.2 (hstep i hi hPi)

end IsAmenablePredicate
end ZFVP
