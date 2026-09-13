import ZFVP.ModelTheory.CriticalPoint
import ZFVP.SetTheory.InjectionRetraction
import ZFVP.SetTheory.Hartogs
import ZFVP.SetTheory.RankBounds

/-! Critical points are uncountable initial ordinals in the ambient ZF model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedSurjectionFormula : SetTheorySemisentence 3 :=
  “g X Y. !boundedFunctionFormula g X Y ∧
    ∀ y ∈ Y, ∃ x ∈ X, !boundedPairMemberFormula g x y”

theorem boundedSurjectionFormula_bounded : IsBoundedSetFormula boundedSurjectionFormula :=
  .and (boundedFunctionFormula_bounded.subst ![.bvar 0, .bvar 1, .bvar 2])
    (.all (.bvar 2) (.exs (.bvar 2)
      (boundedPairMemberFormula_bounded.subst ![.bvar 2, .bvar 0, .bvar 1])))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedSurjectionFormula_defined :
    Defined (fun v : Fin 3 → V ↦ v 0 ∈ v 2 ^ v 1 ∧ range (v 0) = v 2) boundedSurjectionFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [boundedSurjectionFormula]
  intro hf
  constructor
  · intro hs
    apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
    intro y hy
    obtain ⟨x, _, hxy⟩ := hs y hy
    exact mem_range_of_kpair_mem hxy
  · intro hr y hy
    obtain ⟨x, hxy⟩ := mem_range_iff.mp (hr.symm ▸ hy)
    exact ⟨x, (mem_of_mem_functions hf hxy).1, hxy⟩

theorem IsCodedMembershipEmbedding.value_surjection {A B f g X Y : V}
    [IsTransitive A] [IsTransitive B] (h : IsCodedMembershipEmbedding A B f)
    (hg : g ∈ A) (hX : X ∈ A) (hY : Y ∈ A) (hf : g ∈ Y ^ X) (hr : range g = Y) :
    f ‘ g ∈ (f ‘ Y) ^ (f ‘ X) ∧ range (f ‘ g) = f ‘ Y :=
  (h.bounded_defined_iff boundedSurjectionFormula_bounded
    (fun v ↦ v 0 ∈ v 2 ^ v 1 ∧ range (v 0) = v 2) ![g, X, Y]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hg, hX, hY])).mp ⟨hf, hr⟩

theorem rankEmbedding_criticalPoint_no_surjection {k l : ℕ} {δ ε f κ α g : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) (hα : α ∈ κ) (hg : g ∈ κ ^ α) :
    range g ≠ κ := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hκ.ordinal
  let := hierarchy_transitive δ
  let := hierarchy_transitive ε
  let := IsFunction.of_mem hg
  intro hr
  have hαδ := (hierarchy_transitive δ).mem_trans hα hκ.mem_domain
  have hgδ := (hierarchy_transitive δ).mem_trans hg
    (function_mem_hierarchy_limit hδ.successor_closed hαδ hκ.mem_domain)
  have hmap := h.value_surjection hgδ hαδ hκ.mem_domain hg hr
  rw [hκ.fixed_below hα] at hmap
  let := IsFunction.of_mem hmap.1
  have hκr : κ ∈ range (f ‘ g) := hmap.2.symm ▸ hκ.lt_value h
  obtain ⟨x, hxp⟩ := mem_range_iff.mp hκr
  have hxα := (mem_of_mem_functions hmap.1 hxp).1
  have hxκ := IsOrdinal.toIsTransitive.mem_trans hxα hα
  have hgxκ := function_value_mem hg hxα
  have hv := h.value_apply hgδ hαδ (IsFunction.of_mem hg) (domain_eq_of_mem_function hg) hxα
  rw [hκ.fixed_below hxκ, hκ.fixed_below hgxκ] at hv
  have he : κ = g ‘ x := (value_eq_of_kpair_mem hxp).symm.trans hv
  exact mem_irrefl κ (he.symm ▸ hgxκ)

theorem rankEmbedding_criticalPoint_initial {k l : ℕ} {δ ε f κ : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) : IsInitialOrdinal κ := by
  refine ⟨hκ.ordinal, ?_⟩
  intro α hα hbad
  obtain ⟨g, hg, hr⟩ := surjection_of_injection hbad ⟨α, hα⟩
  exact rankEmbedding_criticalPoint_no_surjection hδ hε h hκ hα hg hr

end ZFVP
