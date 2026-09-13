import ZFVP.SetTheory.ChoicelessExtendibleWitness
import ZFVP.ModelTheory.EmbeddingCnTransfer
import ZFVP.ModelTheory.RankEmbeddingRestriction
import ZFVP.ModelTheory.RankEmbeddingDictionary
import ZFVP.ModelTheory.CriticalPointRestriction

/-! Bagaria-Poveda Corollary 2.7, the direction used by finite restoration:
the small-embedding criterion at C(n+1) stages gives C(n)-extendibility. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def cnExtendibleWitnessBody (C : SetTheorySemisentence 1) : SetTheorySemisentence 2 :=
  “κ μ. ∃ ν A B e y, μ ∈ ν ∧ !C ν ∧ !piOneHierarchyFormula A μ ∧ !piOneHierarchyFormula B ν ∧
    !piOneMembershipEmbeddingFormula A B e ∧ !boundedCriticalPointFormula A e κ ∧
    !boundedPairMemberFormula e κ y ∧ μ ∈ y”

def positiveCnExtendibleWitnessFormula (k : ℕ) : SetTheorySemisentence 2 :=
  cnExtendibleWitnessBody (positiveCnWitnessFormula k)

theorem positiveCnExtendibleWitnessFormula_sigma (k : ℕ) :
    IsSigmaFormula (k + 2) (positiveCnExtendibleWitnessFormula k) := by
  unfold positiveCnExtendibleWitnessFormula cnExtendibleWitnessBody
  repeat' apply IsLevyFormula.exs
  exact .and (.bounded (.rel _ _))
    (.and ((positiveCnWitnessFormula_sigma k).subst _)
      (.and ((piOneHierarchyFormula_piOne.raise.mono (by omega)).subst _)
        (.and ((piOneHierarchyFormula_piOne.raise.mono (by omega)).subst _)
          (.and ((piOneMembershipEmbeddingFormula_piOne.raise.mono (by omega)).subst _)
            (.and (.bounded (boundedCriticalPointFormula_bounded.subst _))
              (.and (.bounded (boundedPairMemberFormula_bounded.subst _)) (.bounded (.rel _ _))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The body of `IsCnExtendible n κ` at one source rank `μ`. -/
def CnExtendibleWitness (n : ℕ) (κ μ : V) : Prop :=
  IsOrdinal μ ∧ ∃ ν e, μ ∈ ν ∧ Cn n ν ∧
    IsCodedMembershipEmbedding (hierarchy μ) (hierarchy ν) e ∧
    IsCriticalPoint (hierarchy μ) e κ ∧ μ ∈ e ‘ κ

theorem eval_positiveCnExtendibleWitnessFormula (k : ℕ) (κ μ : V) :
    (positiveCnExtendibleWitnessFormula k).Evalb ![κ, μ] ↔ CnExtendibleWitness (k + 1) κ μ := by
  simp [positiveCnExtendibleWitnessFormula, cnExtendibleWitnessBody, CnExtendibleWitness]
  constructor
  · rintro ⟨ν, hμν, hν, A, ⟨hμ, rfl⟩, B, ⟨_, rfl⟩, e, he, hc, y, hp, hμy⟩
    let := hμ
    let := hierarchy_transitive μ
    let := IsFunction.of_mem he.function
    refine ⟨hμ, ν, hμν, hν, e, he, (criticalPoint_iff_graphSpec he.function).mpr hc, ?_⟩
    rwa [value_eq_of_kpair_mem hp]
  · rintro ⟨hμ, ν, hμν, hν, e, he, hc, hm⟩
    let := hμ
    let := hierarchy_transitive μ
    let := IsFunction.of_mem he.function
    refine ⟨ν, hμν, hν, hierarchy μ, ⟨hμ, rfl⟩, hierarchy ν, ⟨hν.ordinal, rfl⟩,
      e, he, (criticalPoint_iff_graphSpec he.function).mp hc, e ‘ κ, ?_, hm⟩
    exact kpair_value_mem (by rw [domain_eq_of_mem_function he.function]; exact hc.mem_domain)

instance positiveCnExtendibleWitnessFormula_defined (k : ℕ) :
    ℒₛₑₜ-relation[V] (CnExtendibleWitness (k + 1)) via positiveCnExtendibleWitnessFormula k :=
  ⟨fun v ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
    change (positiveCnExtendibleWitnessFormula k).Evalb v ↔
      CnExtendibleWitness (k + 1) (v 0) (v 1)
    rw [← hv]
    exact eval_positiveCnExtendibleWitnessFormula _ _ _⟩

theorem IsCnExtendible.witness {n : ℕ} {κ : V} (h : IsCnExtendible n κ) {μ : V}
    (hμ : Cn n μ) (hκμ : κ ∈ μ) : CnExtendibleWitness n κ μ :=
  ⟨hμ.ordinal, h.2 μ hμ hκμ⟩

/-- Bagaria-Poveda's small-embedding criterion for `δ` at level `n`: unboundedly many
`C(n+1)` stages `θ` such that every `α ∈ θ` is the image of some `α' ∈ θ'` under an elementary
`e : V_θ' → V_θ` with `θ' ∈ C(n+1)`, `θ' ∈ δ`, critical point `δ'` and `e(δ') = δ`. -/
def SmallEmbeddingCriterion (n : ℕ) (δ : V) : Prop :=
  ∀ η : V, IsOrdinal η → ∃ θ : V, η ∈ θ ∧ Cn (n + 1) θ ∧ ∀ α ∈ θ, ∃ δ' θ' α' e : V,
    δ' ∈ θ' ∧ θ' ∈ δ ∧ α' ∈ θ' ∧ Cn (n + 1) θ' ∧
    IsCodedMembershipEmbedding (hierarchy θ') (hierarchy θ) e ∧
    IsCriticalPoint (hierarchy θ') e δ' ∧ e ‘ δ' = δ ∧ e ‘ α' = α

theorem IsCnExtendible.of_smallEmbeddingCriterion {k : ℕ} {δ : V} (hδ : IsInitialOrdinal δ)
    (hcrit : SmallEmbeddingCriterion (k + 1) δ) : IsCnExtendible (k + 1) δ := by
  refine ⟨hδ, ?_⟩
  intro μ hμ hδμ
  let := hδ.1
  let := hμ.ordinal
  obtain ⟨θ, hμθ, hθ, hall⟩ := hcrit μ hμ.ordinal
  let := hθ.ordinal
  obtain ⟨δ', θ', μ', e, _, hθ'δ, hμ'θ', hθ', he, hc, heδ, heμ⟩ := hall μ hμθ
  let := hθ'.ordinal
  let := hierarchy_transitive θ'
  let := hierarchy_transitive θ
  let := hc.ordinal
  let := IsFunction.of_mem he.function
  let : IsOrdinal μ' := IsOrdinal.of_mem hμ'θ'
  let := hierarchy_transitive μ'
  have hμ'V : μ' ∈ hierarchy θ' := ordinal_subset_hierarchy θ' μ' hμ'θ'
  have hδ'V : δ' ∈ hierarchy θ' := hc.mem_domain
  have hCμ' : Cn (k + 1) μ' := by
    have hiff := rankEmbedding_cn_iff hθ' hθ he hμ'V
    rw [heμ] at hiff
    exact hiff.mpr hμ
  have hδ'μ' : δ' ∈ μ' := (he.value_mem_iff hδ'V hμ'V).mp (by rw [heδ, heμ]; exact hδμ)
  have hμ'δ : μ' ∈ δ := IsOrdinal.toIsTransitive.mem_trans hμ'θ' hθ'δ
  have hμ'μ : μ' ∈ μ := IsOrdinal.toIsTransitive.mem_trans hμ'δ hδμ
  have hr := rankEmbedding_restrict hθ' hθ he (hierarchy_mem hμ'θ')
    ⟨ω, ordinal_subset_hierarchy μ' _ hCμ'.omega_lt⟩
  rw [(rankEmbedding_value_hierarchy hθ' hθ he hCμ'.ordinal hμ'V).2, heμ] at hr
  have hcr := hc.restrict he.function
    ((hierarchy_transitive θ').transitive _ (hierarchy_mem hμ'θ')) (ordinal_subset_hierarchy μ' δ' hδ'μ')
  have hlocal : CnExtendibleWitness (k + 1) δ' μ' := by
    refine ⟨hCμ'.ordinal, μ, e ↾ (hierarchy μ'), hμ'μ, hμ, hr, hcr, ?_⟩
    rw [value_restrict (by rw [domain_eq_of_mem_function he.function]; exact hδ'V)
      (ordinal_subset_hierarchy μ' δ' hδ'μ'), heδ]
    exact hμ'δ
  have htransfer := rankEmbedding_defined_iff hθ' hθ he
    (positiveCnExtendibleWitnessFormula_sigma k)
    (fun v ↦ CnExtendibleWitness (k + 1) (v 0) (v 1)) ![δ', μ']
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hδ'V, hμ'V])
  have ht : CnExtendibleWitness (k + 1) (e ‘ δ') (e ‘ μ') := htransfer.mp hlocal
  rw [heδ, heμ] at ht
  exact ht.2

end ZFVP
