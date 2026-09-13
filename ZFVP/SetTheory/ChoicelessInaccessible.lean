import ZFVP.ModelTheory.CriticalPointCofinality
import ZFVP.SetTheory.CnExtendible
import ZFVP.SetTheory.CnCofinalUnbounded

/-! The rank-map definition of inaccessibility in ZF, as in Spoerl Definition 19. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def choicelessInaccessibleFormula : SetTheorySemisentence 1 :=
  f“κ. !IsOrdinal.dfn κ ∧ !isω ∈ κ ∧ ∀ α ∈ κ, ∀ g,
    ¬!boundedCofinalMapFormula κ (!hierarchyFormula α) g”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsChoicelessInaccessible (κ : V) : Prop :=
  IsOrdinal κ ∧ (ω : V) ∈ κ ∧ ∀ α ∈ κ, ∀ g, ¬IsCofinalMap κ (hierarchy α) g

instance choicelessInaccessibleFormula_defined :
    ℒₛₑₜ-predicate[V] IsChoicelessInaccessible via choicelessInaccessibleFormula :=
  ⟨fun v ↦ by simp [choicelessInaccessibleFormula, IsChoicelessInaccessible]⟩

instance choicelessInaccessible_definable : ℒₛₑₜ-predicate[V] IsChoicelessInaccessible :=
  choicelessInaccessibleFormula_defined.to_definable

theorem rankEmbedding_criticalPoint_inaccessible {k l : ℕ} {δ ε f κ : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) : IsChoicelessInaccessible κ := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hκ.ordinal
  let := hierarchy_transitive ε
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff k δ).mp hδ).2.support
  exact ⟨hκ.ordinal, hκ.omega_lt h, fun α hα _ ↦
    rankEmbedding_criticalPoint_no_cofinalMap hδ hε h hκ (hierarchy_mem hα)⟩

theorem IsCnExtendible.inaccessible {n : ℕ} {κ : V} (hκ : IsCnExtendible (n + 1) κ) :
    IsChoicelessInaccessible κ := by
  let := hκ.1.1
  obtain ⟨δ, hκδ, hδ⟩ := cn_unbounded (n + 1) κ
  obtain ⟨ε, f, _, hε, hf, hc, _⟩ := hκ.2 δ hδ hκδ
  exact rankEmbedding_criticalPoint_inaccessible hδ hε hf hc

theorem IsCnExtendible.regular {n : ℕ} {κ : V} (hκ : IsCnExtendible (n + 1) κ) :
    IsRegularCardinal κ := by
  let := hκ.1.1
  obtain ⟨δ, hκδ, hδ⟩ := cn_unbounded (n + 1) κ
  obtain ⟨ε, f, _, hε, hf, hc, _⟩ := hκ.2 δ hδ hκδ
  exact rankEmbedding_criticalPoint_regular hδ hε hf hc

end ZFVP
