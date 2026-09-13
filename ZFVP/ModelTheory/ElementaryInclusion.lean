import ZFVP.ModelTheory.CriticalSequenceZF
import ZFVP.SetTheory.BoundedIdentity

/-! Internal elementary inclusions and the successive critical rank segments. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsElementaryInclusion (A B : V) : Prop := IsCodedMembershipEmbedding A B (identity A)

instance isElementaryInclusion_definable : ℒₛₑₜ-relation[V] IsElementaryInclusion := by
  unfold IsElementaryInclusion
  definability

theorem IsElementaryInclusion.subset {A B : V} (h : IsElementaryInclusion A B) : A ⊆ B := by
  intro x hx
  have hv : (identity A) ‘ x = x := value_eq_of_kpair_mem (by simp [hx])
  exact hv ▸ function_value_mem h.function hx

theorem IsCodedMembershipEmbedding.value_identity {A B f a : V} [IsTransitive A] [IsTransitive B]
    (h : IsCodedMembershipEmbedding A B f) (ha : a ∈ A) (hi : SetTheory.identity a ∈ A) :
    f ‘ (SetTheory.identity a) = SetTheory.identity (f ‘ a) :=
  (h.bounded_defined_iff boundedIdentityFormula_bounded (fun v ↦ v 0 = SetTheory.identity (v 1))
    ![SetTheory.identity a, a] (by simp [ha, hi])).mp rfl

theorem rankEmbedding_elementaryInclusion_iff {k l : ℕ} {δ ε f A B : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hA : A ∈ hierarchy δ) (hB : B ∈ hierarchy δ) :
    IsElementaryInclusion A B ↔ IsElementaryInclusion (f ‘ A) (f ‘ B) := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hierarchy_transitive δ
  let := hierarchy_transitive ε
  have hi := (hierarchy_transitive δ).mem_trans (identity_mem_function A)
    (function_mem_hierarchy_limit hδ.successor_closed hA hA)
  have he := rankElementaryMap_preserves_codedEmbedding hδ hε h.toElementaryMap
    ⟨A, hA⟩ ⟨B, hB⟩ ⟨identity A, hi⟩
  change IsCodedMembershipEmbedding (f ‘ A) (f ‘ B) (f ‘ (identity A)) ↔ IsElementaryInclusion A B at he
  rw [h.value_identity hA hi] at he
  exact he.symm

theorem rankEmbedding_criticalPoint_elementaryInclusion {k l : ℕ} {δ ε f κ : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) :
    IsElementaryInclusion (hierarchy κ) (hierarchy (f ‘ κ)) := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hκ.ordinal
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff k δ).mp hδ).2.support
  let : IsSequenceSupport (hierarchy ε) := ((cn_successor_iff l ε).mp hε).2.support
  let := IsFunction.of_mem h.function
  have hVκ := hδ.hierarchy_closed hκ.ordinal hκ.mem_domain
  have hne : IsNonempty (hierarchy κ) := ⟨ω, ordinal_subset_hierarchy κ _ (hκ.omega_lt h)⟩
  have hr := rankEmbedding_restrict hδ hε h hVκ hne
  have hgraph : f ↾ (hierarchy κ) = identity (hierarchy κ) := by
    let := IsFunction.of_mem hr.function
    apply functions_eq_of_domain_values
    · rw [domain_eq_of_mem_function hr.function, domain_eq_of_mem_function (identity_mem_function (hierarchy κ))]
    · intro x hx
      have hxκ : x ∈ hierarchy κ := domain_eq_of_mem_function hr.function ▸ hx
      have hxδ := (hierarchy_transitive δ).mem_trans hxκ hVκ
      rw [value_restrict (domain_eq_of_mem_function h.function |>.symm ▸ hxδ) hxκ,
        rankEmbedding_fixed_below_criticalPoint hδ hε h hκ x hxκ]
      exact (value_eq_of_kpair_mem (f := identity (hierarchy κ)) (by simp [hxκ])).symm
  rw [hgraph, (rankEmbedding_value_hierarchy hδ hε h hκ.ordinal hκ.mem_domain).2] at hr
  exact hr

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem successive_elementaryInclusion {n : V} (hn : n ∈ (ω : V)) :
    IsElementaryInclusion (hierarchy (criticalIterate f κ n)) (hierarchy (criticalIterate f κ (succ n))) := by
  have hall : ∀ n ∈ (ω : V), IsElementaryInclusion
      (hierarchy (criticalIterate f κ n)) (hierarchy (criticalIterate f κ (succ n))) := by
    apply naturalNumber_induction (fun n ↦ IsElementaryInclusion
      (hierarchy (criticalIterate f κ n)) (hierarchy (criticalIterate f κ (succ n)))) (by definability)
    · simpa [criticalIterate_succ f κ (by simp : (0 : V) ∈ ω)] using
        rankEmbedding_criticalPoint_elementaryInclusion hδ hδ h hκ
    · intro n hn ih
      have hn' := ω_succ_closed hn
      have ha := iterate_spec hδ h hκ hn
      have hb := iterate_spec hδ h hκ hn'
      have he := (rankEmbedding_elementaryInclusion_iff hδ hδ h
        (hδ.hierarchy_closed ha.1 ha.2.1) (hδ.hierarchy_closed hb.1 hb.2.1)).mp ih
      rw [(rankEmbedding_value_hierarchy hδ hδ h ha.1 ha.2.1).2,
        (rankEmbedding_value_hierarchy hδ hδ h hb.1 hb.2.1).2,
        ← criticalIterate_succ f κ hn, ← criticalIterate_succ f κ hn'] at he
      exact he
  exact hall n hn

end CriticalSequence

end ZFVP
