import ZFVP.ModelTheory.LimitCriticalPoint
import ZFVP.ModelTheory.EmbeddingOmegaFixation
import ZFVP.SetTheory.ClosedRankStages

/-! # Successor closure and the critical point of a rank-stage embedding

A coded elementary embedding `e : V_lb → V_gam` carries successor closure of `gam` back to `lb`,
because "every ordinal lies in a larger ordinal" is a first-order sentence. Once `lb` is closed
under successor and carries an embedding with a critical point, the critical point is above `ω`,
and so is `lb` itself.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The sentence "every ordinal is a member of some ordinal". -/
def ordinalUnboundedFormula : SetTheorySemisentence 0 :=
  “∀ x, !IsOrdinal.dfn x → ∃ y, !IsOrdinal.dfn y ∧ x ∈ y”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
/-- Being an ordinal is absolute between a transitive set and the ambient model. -/
theorem setDomain_isOrdinal_iff (A : V) [IsTransitive A] (x : SetDomain A) :
    IsOrdinal (x : SetDomain A) ↔ IsOrdinal x.val := by
  simpa using bounded_formula_absolute A isOrdinalFormula_bounded ![x]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
/-- What `ordinalUnboundedFormula` says in a transitive set. -/
theorem eval_ordinalUnboundedFormula (A : V) [IsTransitive A] :
    ordinalUnboundedFormula.Evalb (![] : Fin 0 → SetDomain A) ↔
      ∀ x ∈ A, IsOrdinal x → ∃ y ∈ A, IsOrdinal y ∧ x ∈ y := by
  simp only [ordinalUnboundedFormula]
  simp [setDomain_isOrdinal_iff]
  constructor
  · intro h x hx hxo
    obtain ⟨y, hyo, hm⟩ := h ⟨x, hx⟩ hxo
    exact ⟨y.val, y.property, hyo, hm⟩
  · intro h x hxo
    obtain ⟨y, hy, hyo, hm⟩ := h x.val x.property hxo
    exact ⟨⟨y, hy⟩, hyo, hm⟩

/-- If the target rank stage is closed under successor, so is the source. The sentence
"every ordinal is a member of a larger ordinal" holds in `V_gam` and transfers back along `e`. -/
theorem successorClosed_of_embedding {lb gam e : V} [IsOrdinal lb] [IsOrdinal gam]
    (hgam : ∀ ξ ∈ gam, succ ξ ∈ gam)
    (he : IsCodedMembershipEmbedding (hierarchy lb) (hierarchy gam) e) :
    ∀ ξ ∈ lb, succ ξ ∈ lb := by
  let := hierarchy_transitive lb
  let := hierarchy_transitive gam
  have htarget : ordinalUnboundedFormula.Evalb (![] : Fin 0 → SetDomain (hierarchy gam)) := by
    rw [eval_ordinalUnboundedFormula]
    intro x hx hxo
    let := hxo
    have hs : succ x ∈ gam := hgam x (ordinal_mem_hierarchy_iff.mp hx)
    let : IsOrdinal (succ x) := IsOrdinal.succ
    exact ⟨succ x, ordinal_mem_hierarchy_iff.mpr hs, inferInstance, mem_succ_self x⟩
  have hvec : he.toFunction ∘ (![] : Fin 0 → SetDomain (hierarchy lb)) = ![] := by
    funext i; exact Fin.elim0 i
  have hsource : ordinalUnboundedFormula.Evalb (![] : Fin 0 → SetDomain (hierarchy lb)) := by
    rw [he.eval_semisentence ordinalUnboundedFormula ![], hvec]
    exact htarget
  rw [eval_ordinalUnboundedFormula] at hsource
  intro ξ hξ
  let : IsOrdinal ξ := IsOrdinal.of_mem hξ
  obtain ⟨y, hy, hyo, hm⟩ := hsource ξ (ordinal_mem_hierarchy_iff.mpr hξ) inferInstance
  let := hyo
  have hyl : y ∈ lb := ordinal_mem_hierarchy_iff.mp hy
  have hsub : succ ξ ⊆ y := by
    intro z hz
    rcases mem_succ_iff.mp hz with rfl | hz
    · exact hm
    · exact IsOrdinal.toIsTransitive.mem_trans hz hm
  have : IsOrdinal (succ ξ) := IsOrdinal.succ
  rcases IsOrdinal.subset_iff.mp hsub with hq | hlt
  · exact hq ▸ hyl
  · exact IsOrdinal.toIsTransitive.mem_trans hlt hyl

/-- A coded embedding fixes every natural number as soon as all of them lie in the source. -/
theorem value_natural_of_omega_subset {A B e n : V} [IsTransitive A] [IsTransitive B]
    (h : IsCodedMembershipEmbedding A B e) (hω : ∀ i ∈ (ω : V), i ∈ A) (hn : n ∈ (ω : V)) :
    e ‘ n = n := by
  apply naturalNumber_induction (fun n ↦ e ‘ n = n) (by definability)
    (h.value_empty (hω _ empty_mem_ω)) ?_ n hn
  intro i hi ih
  rw [h.value_succ (hω _ hi) (hω _ (ω_succ_closed hi)), ih]

/-- `ω` is a member of a successor-closed rank stage index carrying an embedding with a
critical point. -/
theorem omega_mem_of_criticalPoint {lb gam e ab : V} [IsOrdinal lb] [IsOrdinal gam]
    (hlb : ∀ ξ ∈ lb, succ ξ ∈ lb)
    (he : IsCodedMembershipEmbedding (hierarchy lb) (hierarchy gam) e)
    (hc : IsCriticalPoint (hierarchy lb) e ab) : (ω : V) ∈ lb := by
  let := hierarchy_transitive lb
  let := hierarchy_transitive gam
  let := hc.ordinal
  have hab : ab ∈ lb := ordinal_mem_hierarchy_iff.mp hc.mem_domain
  have hne : IsNonempty lb := ⟨ab, hab⟩
  have h0 : (∅ : V) ∈ lb := IsOrdinal.empty_mem_iff_nonempty.mpr hne
  have hsub : (ω : V) ⊆ lb := by
    intro n hn
    exact naturalNumber_induction (fun n ↦ n ∈ lb) (by definability) h0
      (fun i hi ih ↦ hlb i ih) n hn
  have hmem : ∀ i ∈ (ω : V), i ∈ hierarchy lb := by
    intro i hi
    let : IsOrdinal i := IsOrdinal.of_mem hi
    exact ordinal_mem_hierarchy_iff.mpr (hsub i hi)
  rcases IsOrdinal.subset_iff.mp hsub with hq | hlt
  · exact absurd (value_natural_of_omega_subset he hmem (hq ▸ hab)) hc.moved
  · exact hlt

/-- The critical point of an embedding of a successor-closed rank stage lies above `ω`. -/
theorem omega_mem_criticalPoint {lb gam e ab : V} [IsOrdinal lb] [IsOrdinal gam]
    (hlb : ∀ ξ ∈ lb, succ ξ ∈ lb)
    (he : IsCodedMembershipEmbedding (hierarchy lb) (hierarchy gam) e)
    (hc : IsCriticalPoint (hierarchy lb) e ab) : (ω : V) ∈ ab := by
  let := hierarchy_transitive lb
  let := hierarchy_transitive gam
  exact hc.omega_lt_of_omega_mem he
    (ordinal_mem_hierarchy_iff.mpr (omega_mem_of_criticalPoint hlb he hc))

end ZFVP
