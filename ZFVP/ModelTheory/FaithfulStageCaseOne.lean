import ZFVP.ModelTheory.FaithfulRankExtension
import ZFVP.ModelTheory.ElementaryStageCaseOne

/-! Enayat Theorem 4.4, Case I, before specializing to conservative
extensions. Powerset preservation suffices for the least-stage argument. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W] [Nonempty V] [Nonempty W]
  [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
theorem exists_old_polar_witness_of_powersetPreserving {j : MembershipEndExtension V W} (hc : j.IsPowersetPreserving)
    {δ θ δ₀ : W} [IsOrdinal δ] [IsOrdinal θ] (hδθ : δ ∈ θ) (hrefl : ReflectsCaseOne θ)
    (hleast : IsLeastStageDefinableParamNew j δ θ δ₀) (pos : Bool) (n φ b : V) {x : W}
    (hx : x ∈ hierarchy δ₀) (hsat : polarStage pos δ₀ (j n) (j φ) (j b) x) :
    ∃ y : V, polarStage pos δ₀ (j n) (j φ) (j b) (j y) := by
  have hδ₀ord : IsOrdinal δ₀ := hleast.1
  have hnew : ∀ α : V, j α ≠ δ₀ := hleast.2.1.2
  obtain ⟨m₀, hm₀⟩ := hleast.2.1.1.2
  -- containments
  have hδ₀δ : δ₀ ⊆ δ := subset_of_leastParam hleast
  have hδmem : δ ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr hδθ
  have hδθsub : δ ⊆ θ := IsOrdinal.toIsTransitive.transitive δ hδθ
  have hδ₀θ : δ₀ ∈ θ := by
    rcases mem_succ_iff.mp hleast.2.1.1.1 with rfl | hlt
    · exact hδθ
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hδθ
  have hδ₀mem : δ₀ ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr hδ₀θ
  have hδ₀sub : δ₀ ⊆ θ := IsOrdinal.toIsTransitive.transitive δ₀ hδ₀θ
  have hmemδ₀ : ∀ m : V, j m ∈ hierarchy δ₀ := fun m ↦ hc.map_mem_hierarchy_of_new hnew m
  have hmemθ : ∀ m : V, j m ∈ hierarchy θ := fun m ↦ hierarchy_mono hδ₀sub _ (hmemδ₀ m)
  -- the single old parameter
  set M : V := ⟨m₀, ⟨n, ⟨φ, b⟩ₖ⟩ₖ⟩ₖ with hMdef
  set Q : W := j M with hQdef
  have hQ : Q = ⟨j m₀, ⟨j n, ⟨j φ, j b⟩ₖ⟩ₖ⟩ₖ := by
    rw [hQdef, hMdef, j.map_kpair, j.map_kpair, j.map_kpair]
  have hpolar : ∀ y : W, polarSat pos y δ₀ Q ↔ polarStage pos δ₀ (j n) (j φ) (j b) y := by
    intro y
    rw [hQ]
    exact polarSat_kpair pos δ₀ (j m₀) (j n) (j φ) (j b) y
  have hQmem : Q ∈ hierarchy θ := hmemθ M
  -- the least stage holding a witness
  obtain ⟨ξ, hξ⟩ := exists_isLeastPolarWitness pos δ₀ Q x ((hpolar x).mpr hsat)
  have hξord : IsOrdinal ξ := hξ.1
  -- it is below `δ₀`
  have hlim : IsLimitOrdinal δ₀ := isLimitOrdinal_of_leastParam hδθ hmemθ hleast
  have hrankx : rank x ∈ δ₀ := (mem_hierarchy_iff_rank_mem x δ₀).mp hx
  have hsuccmem : succ (rank x) ∈ δ₀ := succ_mem_of_isLimitOrdinal hlim hrankx
  have hxstage : x ∈ hierarchy (succ (rank x)) := by
    rw [hierarchy_succ, mem_power_iff]
    exact subset_hierarchy_rank x
  have hξδ₀ : ξ ∈ δ₀ := by
    rcases hξ.le hxstage ((hpolar x).mpr hsat) with hlt | heq
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hsuccmem
    · exact heq ▸ hsuccmem
  have hξmem : ξ ∈ hierarchy θ :=
    ordinal_mem_hierarchy_iff.mpr (IsOrdinal.toIsTransitive.mem_trans hξδ₀ hδ₀θ)
  -- `ξ` is definable in the stage from `δ₀` and `Q`
  have hξdef : IsStageDefinable θ δ₀ Q ξ := by
    refine isStageDefinable_of_reflect hrefl (ψ := leastPolarWitnessFormula pos) ?_
      hξmem hδ₀mem hQmem (fun z hz ↦ ?_)
    · cases pos <;> simp [caseOneCodes]
    · have he : (leastPolarWitnessFormula pos).Evalb ![z, δ₀, Q] ↔
          IsLeastPolarWitness pos z δ₀ Q :=
        (leastPolarWitnessFormula_defined (V := W) pos).iff ![z, δ₀, Q]
      rw [he]
      exact ⟨fun h ↦ h.unique hξ, fun h ↦ h ▸ hξ⟩
  -- `δ₀` is definable in the stage from `δ` and `Q`
  have hπ : IsStageDefinable θ δ Q (j m₀) := by
    refine isStageDefinable_of_reflect hrefl (ψ := kpairFirstFormula) (by simp [caseOneCodes])
      (hmemθ m₀) hδmem hQmem (fun z hz ↦ ?_)
    have he : kpairFirstFormula.Evalb ![z, δ, Q] ↔ z = kpair.π₁ Q :=
      (kpairFirstFormula_defined (V := W)).iff ![z, δ, Q]
    rw [he, hQ]
    simp
  have hδ₀def : IsStageDefinable θ δ Q δ₀ := isStageDefinable_trans_param hδmem hQmem hπ hm₀
  -- so `ξ` lies in `O`
  have hcore : stageDefinableParamCore j δ θ ξ :=
    ⟨mem_succ_iff.mpr (Or.inr (hδ₀δ ξ hξδ₀)), M,
      isStageDefinable_trans hδmem hQmem hδ₀def hξdef⟩
  -- and is old, by minimality of `δ₀`
  have hold : ∃ α : V, j α = ξ := by
    by_contra hno
    exact hleast.2.2 ξ hξδ₀ ⟨hcore, fun α hα ↦ hno ⟨α, hα⟩⟩
  obtain ⟨α, hα⟩ := hold
  have hαord : IsOrdinal α := (j.ordinal_iff α).mp (hα ▸ hξord)
  obtain ⟨y, hy, hpy⟩ := hξ.2.1
  have hyj : y ∈ j (hierarchy α) := by
    rw [hc.map_hierarchy α, hα]
    exact hy
  obtain ⟨y₀, -, rfl⟩ := (j.mem_map_iff (hierarchy α) y).mp hyj
  exact ⟨y₀, (hpolar (j y₀)).mp hpy⟩

/-- Enayat's Case I, second half: the image of the smaller model passes the Tarski test in the
stage `V_{δ₀}`. This is exactly the `helem` hypothesis of
`stageSatisfaction_isFullSatisfactionClass`. -/
theorem elementary_of_least_of_powersetPreserving {j : MembershipEndExtension V W} (hc : j.IsPowersetPreserving)
    {δ θ δ₀ : W} [IsOrdinal δ] [IsOrdinal θ] (hδθ : δ ∈ θ) (hrefl : ReflectsCaseOne θ)
    (hleast : IsLeastStageDefinableParamNew j δ θ δ₀) :
    ∀ n φ b : V, IsMembershipFormulaCode (succ n) φ → IsFunction b → domain b = n →
      ((∀ y : V, MembershipSatisfies (hierarchy δ₀) (succ (j n)) (j φ)
            (assignmentPrepend (j n) (j b) (j y))) →
          ∀ x : W, x ∈ hierarchy δ₀ →
            MembershipSatisfies (hierarchy δ₀) (succ (j n)) (j φ)
              (assignmentPrepend (j n) (j b) x)) ∧
      ((∃ x : W, x ∈ hierarchy δ₀ ∧
            MembershipSatisfies (hierarchy δ₀) (succ (j n)) (j φ)
              (assignmentPrepend (j n) (j b) x)) →
          ∃ y : V, MembershipSatisfies (hierarchy δ₀) (succ (j n)) (j φ)
            (assignmentPrepend (j n) (j b) (j y))) := by
  intro n φ b _ _ _
  constructor
  · intro hall x hx
    by_contra hxs
    obtain ⟨y, hy⟩ := exists_old_polar_witness_of_powersetPreserving hc hδθ hrefl hleast false n φ b hx
      ((polarStage_false δ₀ (j n) (j φ) (j b) x).mpr hxs)
    exact (polarStage_false δ₀ (j n) (j φ) (j b) (j y)).mp hy (hall y)
  · rintro ⟨x, hx, hsat⟩
    obtain ⟨y, hy⟩ := exists_old_polar_witness_of_powersetPreserving hc hδθ hrefl hleast true n φ b hx
      ((polarStage_true δ₀ (j n) (j φ) (j b) x).mpr hsat)
    exact ⟨y, (polarStage_true δ₀ (j n) (j φ) (j b) (j y)).mp hy⟩


end MembershipEndExtension
end ZFVP
