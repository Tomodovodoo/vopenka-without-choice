import ZFVP.ModelTheory.CriticalPointCardinal
import ZFVP.SetTheory.Cofinality

/-! Cofinal graphs transfer by a bounded formula, even for arbitrary set domains. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedCofinalMapFormula : SetTheorySemisentence 3 :=
  “Y X g. !boundedFunctionFormula g X Y ∧ ∀ z ∈ Y, ∃ i ∈ X, ∃ y ∈ Y,
    !boundedPairMemberFormula g i y ∧ !isSubsetOf z y”

theorem boundedCofinalMapFormula_bounded : IsBoundedSetFormula boundedCofinalMapFormula :=
  .and (boundedFunctionFormula_bounded.subst ![.bvar 2, .bvar 1, .bvar 0])
    (.all (.bvar 0) (.exs (.bvar 2) (.exs (.bvar 2) (.and
      (boundedPairMemberFormula_bounded.subst ![.bvar 5, .bvar 1, .bvar 0])
      (isSubsetOf_bounded.subst ![.bvar 2, .bvar 0])))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedCofinalMapFormula_defined :
    ℒₛₑₜ-relation₃[V] IsCofinalMap via boundedCofinalMapFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [boundedCofinalMapFormula, IsCofinalMap]
  intro hf
  let := IsFunction.of_mem hf
  constructor
  · intro hc z hz
    obtain ⟨i, hi, y, _, hiy, hzy⟩ := hc z hz
    exact ⟨i, hi, (value_eq_of_kpair_mem hiy).symm ▸ hzy⟩
  · intro hc z hz
    obtain ⟨i, hi, hzi⟩ := hc z hz
    exact ⟨i, hi, (v 2) ‘ i, function_value_mem hf hi,
      kpair_value_mem (domain_eq_of_mem_function hf |>.symm ▸ hi), hzi⟩

theorem IsCodedMembershipEmbedding.value_cofinalMap {A B f g X Y : V}
    [IsTransitive A] [IsTransitive B] (h : IsCodedMembershipEmbedding A B f)
    (hg : g ∈ A) (hX : X ∈ A) (hY : Y ∈ A) (hf : IsCofinalMap Y X g) :
    IsCofinalMap (f ‘ Y) (f ‘ X) (f ‘ g) :=
  (h.bounded_defined_iff boundedCofinalMapFormula_bounded
    (fun v ↦ IsCofinalMap (v 0) (v 1) (v 2)) ![Y, X, g]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hg, hX, hY])).mp hf

theorem rankEmbedding_criticalPoint_no_cofinalMap {k l : ℕ} {δ ε f κ a g : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) (ha : a ∈ hierarchy κ) :
    ¬IsCofinalMap κ a g := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hκ.ordinal
  let := hierarchy_transitive δ
  let := hierarchy_transitive ε
  intro hg
  have haδ := (hierarchy_transitive δ).mem_trans ha (hδ.hierarchy_closed hκ.ordinal hκ.mem_domain)
  have hgδ := (hierarchy_transitive δ).mem_trans hg.1
    (function_mem_hierarchy_limit hδ.successor_closed haδ hκ.mem_domain)
  have hmap := h.value_cofinalMap hgδ haδ hκ.mem_domain hg
  have hfa := rankEmbedding_fixed_below_criticalPoint hδ hε h hκ a ha
  rw [hfa] at hmap
  obtain ⟨i, hi, hle⟩ := hmap.2 κ (hκ.lt_value h)
  have hik := (hierarchy_transitive κ).mem_trans hi ha
  have hfi := rankEmbedding_fixed_below_criticalPoint hδ hε h hκ i hik
  have hgi := function_value_mem hg.1 hi
  have hv := h.value_apply hgδ haδ (IsFunction.of_mem hg.1) (domain_eq_of_mem_function hg.1) hi
  rw [hfi, hκ.fixed_below hgi] at hv
  rw [hv] at hle
  exact mem_irrefl (g ‘ i) (hle _ hgi)

end ZFVP
