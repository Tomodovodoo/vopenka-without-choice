import ZFVP.SetTheory.CohenFreshPermutation
import ZFVP.SetTheory.CohenConditionTransport
import ZFVP.SetTheory.CohenAmalgamation
import ZFVP.SetTheory.AtomicForcingSubstitution

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A forced member can be moved to have support fresh outside the overlap, while retaining
a common extension of the equality condition and the transported membership condition. -/
theorem cohen_fresh_reverse_transfer {E F D τ σ μ p t : V}
    (hτ : IsForcingName (cohenConditions (ω : V)) τ)
    (hσ : IsForcingName (cohenConditions (ω : V)) σ)
    (hμ : IsForcingName (cohenConditions (ω : V)) μ)
    (hE : IsCohenNameSupport τ E) (hF : IsCohenNameSupport σ F)
    (hD : IsCohenNameSupport μ D)
    (hp : p ∈ atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) τ σ)
    (hsupp : cohenSupport p ⊆ E ∪ F)
    (htp : ⟨t, p⟩ₖ ∈ cohenOrder (ω : V))
    (htμ : t ∈ atomicMembership (cohenConditions (ω : V)) (cohenOrder (ω : V)) μ τ) :
    ∃ b v, IsInternalPermutation (ω : V) b ∧ (∀ i ∈ E ∩ F, b ‘ i = i) ∧
      (∀ i ∈ repl (fun j ↦ b ‘ j) (by definability) D, i ∈ E ∪ F → i ∈ E ∩ F) ∧
      v ∈ cohenConditions (ω : V) ∧ ⟨v, p⟩ₖ ∈ cohenOrder (ω : V) ∧
      ⟨v, cohenConditionAction (ω : V) b t⟩ₖ ∈ cohenOrder (ω : V) ∧
      v ∈ atomicMembership (cohenConditions (ω : V)) (cohenOrder (ω : V))
        (nameAction (cohenPermutation (ω : V) b) μ) τ := by
  have hR := (cohen_poset (ω : V)).1
  have hpP := atomicEquality_subset _ _ _ _ p hp
  have ht := atomicMembership_subset _ _ _ _ t htμ
  have hpt : p ⊆ t := ((pair_mem_cohenOrder _ _ _).mp htp).2.2
  let B := E ∪ F
  let C := E ∩ F
  have hB : IsInternallyFinite B := internallyFinite_union hE.2.1 hF.2.1
  have hBω : B ⊆ (ω : V) :=
    fun i hi ↦ (mem_union_iff.mp hi).elim (hE.1 i) (hF.1 i)
  have hC : IsInternallyFinite C :=
    internallyFinite_subset hE.2.1 (fun _ hi ↦ (mem_inter_iff.mp hi).1)
  have hCω : C ⊆ (ω : V) := fun i hi ↦ hE.1 i (mem_inter_iff.mp hi).1
  obtain ⟨b, hb, hbfix, hbfixout, hbmove⟩ := finite_permutation_move_fresh_fixing_complement
    hB hBω hC hCω hD.2.1 hD.1 (cohenSupport_finite ht) (cohenSupport_subset ht)
  have hbD : ∀ i ∈ repl (fun j ↦ b ‘ j) (by definability) D, i ∈ B → i ∈ C := by
    intro i hi hiB
    obtain ⟨j, hj, rfl⟩ := (repl_spec _).mp hi
    by_cases hjC : j ∈ C
    · rw [hbfix j hjC]
      exact hjC
    · exact (hbmove j hj hjC (mem_union_iff.mpr (Or.inl hiB))).elim
  have hbt := cohenConditionAction_condition hb ht
  have hcompat : ForcingCompatible (cohenConditions (ω : V)) (cohenOrder (ω : V))
      p (cohenConditionAction (ω : V) b t) := by
    have : IsFunction t := ((mem_finitePartialFunctions _ _ _).mp ht).2.1
    apply (finitePartialFunctions_compatible_iff hpP hbt).mpr
    intro x y z hxy hxz
    obtain ⟨i, hi, n, hn, rfl⟩ := mem_prod_iff.mp
      (finitePartialFunction_domain hpP _ (mem_domain_of_kpair_mem hxy))
    have hiB : i ∈ B := hsupp i ((mem_cohenSupport p i).mpr ⟨n, y, hxy⟩)
    obtain ⟨j, hj, hij⟩ := (cohenConditionAction_pair_iff ht).mp hxz
    have hjs : j ∈ cohenSupport t := (mem_cohenSupport t j).mpr ⟨n, z, hj⟩
    have hbj : b ‘ j = j := by
      by_cases hjC : j ∈ C
      · exact hbfix j hjC
      · by_cases hjD : j ∈ D
        · exact (hbmove j hjD hjC (mem_union_iff.mpr (Or.inl (hij ▸ hiB)))).elim
        · exact hbfixout j (mem_union_iff.mpr (Or.inr hjs)) hjD
    have hij' : i = j := hij.trans hbj
    exact IsFunction.unique (hpt _ hxy) (hij'.symm ▸ hj)
  obtain ⟨v, hv, hvp, hvbt⟩ := hcompat
  have hvbp : ⟨v, cohenConditionAction (ω : V) b p⟩ₖ ∈ cohenOrder (ω : V) := by
    apply (pair_mem_cohenOrder _ _ _).mpr
    exact ⟨hv, cohenConditionAction_condition hb hpP, fun z hz ↦
      ((pair_mem_cohenOrder _ _ _).mp hvbt).2.2 z (cohenConditionAction_mono hpt z hz)⟩
  have havoid : ∀ i ∈ E, i ∉ F → b ‘ i ∉ F := by
    intro i hiE hiF hin
    have hiB : i ∈ B := mem_union_iff.mpr (Or.inl hiE)
    by_cases hiD : i ∈ D
    · exact hbmove i hiD (fun hiC ↦ hiF (mem_inter_iff.mp hiC).2)
        (mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inr hin))))
    · rw [hbfixout i (mem_union_iff.mpr (Or.inl hiB)) hiD] at hin
      exact hiF hin
  have hveq := cohen_atomicEquality_amalgamation hτ hσ hE hF hp hsupp hb hbfix havoid hv hvp hvbp
  have hbtμ := atomicMembership_nameAction_forward (cohenPermutation_automorphism hb) hμ hτ htμ
  rw [cohenPermutation_value ht] at hbtμ
  have hvμ := atomicMembership_mono hR hbtμ hv hvbt
  refine ⟨b, v, hb, hbfix, hbD, hv, hvp, hvbt, ?_⟩
  exact (atomicEquality_membership_iff hR hveq (nameAction (cohenPermutation (ω : V) b) μ)).2.mpr hvμ

end ZFVP
