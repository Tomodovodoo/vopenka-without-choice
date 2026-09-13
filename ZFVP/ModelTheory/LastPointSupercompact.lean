import ZFVP.ModelTheory.LastPointCn
import ZFVP.ModelTheory.EmbeddingSupercompactBase
import ZFVP.SetTheory.ChoicelessSupercompactBelow
import ZFVP.SetTheory.ChoicelessSupercompactDownward

/-! Mohammd Lemma 6.4 at positive lower levels. A least failing target
replaces the induction along the last sequence; downward restriction
also handles a target equal to the image of the last point. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_lastPoint_supercompactBelow {n : ℕ} {θ η f κ α : V}
    (hθ : Cn (n + 2) θ) (hη : Cn (n + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hc : IsCriticalPoint (hierarchy θ) f κ) (hακ : α ∈ κ)
    (hlim : CnCofinal (n + 2) θ) (hγθ : lastPoint θ f ∈ θ) :
    ChoicelessSupercompactBelow (n + 2) α (lastPoint θ f) θ := by
  classical
  let := hθ.ordinal
  let := hη.ordinal
  let := hc.ordinal
  let : IsOrdinal α := IsOrdinal.of_mem hακ
  let := hierarchy_transitive θ
  let := hierarchy_transitive η
  let γ := lastPoint θ f
  let := lastPoint_ordinal θ f
  have hκγ : κ ⊆ γ := hc.subset_lastPoint hθ hη hf
  have hγV := ordinal_subset_hierarchy θ γ hγθ
  have hαV := (hierarchy_transitive θ).mem_trans hακ hc.mem_domain
  let := hf.value_ordinal (lastPoint_ordinal θ f) hγV
  have hγimage : γ ∈ f ‘ γ := rankEmbedding_lastPoint_lt_image hθ hη hf hγθ
  have hbase : ∀ μ, Cn (n + 2) μ → γ ∈ μ → μ ∈ f ‘ γ → μ ∈ θ →
      ∀ a ∈ hierarchy μ, ChoicelessSupercompactWitness (n + 2) α γ μ a := by
    intro μ hμ hγμ hμim hμθ a ha
    exact rankEmbedding_supercompactWitness_below_image hθ hη hf hc hακ hκγ
      hγμ hμim hμθ hμ ha
  intro μ hμ hγμ hμθ a ha
  by_contra hfail
  let P : V → Prop := fun ν ↦ Cn (n + 2) ν ∧ γ ∈ ν ∧ ν ∈ θ ∧
    ¬∀ b ∈ hierarchy ν, ChoicelessSupercompactWitness (n + 2) α γ ν b
  have hP : ℒₛₑₜ-predicate[V] P := by unfold P; definability
  obtain ⟨ν, hνleast, _⟩ := leastOrdinal_existsUnique P hP
    ⟨μ, hμ.ordinal, hμ, hγμ, hμθ, fun hall ↦ hfail (hall a ha)⟩
  obtain ⟨hν, hγν, hνθ, hνfail⟩ := hνleast.2.1
  let := hν.ordinal
  have hsmall : ChoicelessSupercompactBelow (n + 2) α γ ν := by
    intro ρ hρ hγρ hρν
    by_contra hn
    have hρP : P ρ := ⟨hρ, hγρ, IsOrdinal.toIsTransitive.mem_trans hρν hνθ, hn⟩
    have hle := hνleast.2.2 ρ hρ.ordinal hρP
    exact mem_irrefl ρ (hle ρ hρν)
  have himageν : f ‘ γ ⊆ ν := by
    rcases IsOrdinal.mem_trichotomy ν (f ‘ γ) with hl | he | hg
    · exact False.elim (hνfail (hbase ν hν hγν hl hνθ))
    · exact subset_of_eq he.symm
    · exact IsOrdinal.toIsTransitive.transitive _ hg
  have himageθ := ordinal_mem_of_subset_mem himageν hνθ
  have hγcof : CnCofinal (n + 2) γ := rankEmbedding_lastPoint_cnCofinal hθ hη hf hlim
  have himagecof : CnCofinal (n + 2) (f ‘ γ) :=
    rankEmbedding_cnCofinal_image hθ hη hf hlim hγθ hγcof himageθ
  have hgap : ∃ ζ, γ ∈ ζ ∧ ζ ∈ f ‘ γ ∧ Cn (n + 2) ζ := by
    obtain ⟨ζ, hζ, hγζ, hCζ⟩ := himagecof γ hγimage
    exact ⟨ζ, hγζ, hζ, hCζ⟩
  have hbaseBelow : ChoicelessSupercompactBelow (n + 2) α γ (f ‘ γ) := by
    intro ρ hρ hγρ hρim
    exact hbase ρ hρ hγρ hρim (IsOrdinal.toIsTransitive.mem_trans hρim himageθ)
  have htransfer := rankEmbedding_supercompactBelow hθ hη hf hαV hγV
    (ordinal_subset_hierarchy θ ν hνθ) hsmall
  rw [hc.fixed_below hακ] at htransfer
  have hνimage : ν ∈ f ‘ ν := rankEmbedding_above_lastPoint_lt_image hθ hη hf hνθ
    (IsOrdinal.toIsTransitive.transitive _ hγν)
  rcases IsOrdinal.subset_iff.mp himageν with heq | hlt
  · have hνcof : CnCofinal (n + 2) ν := heq ▸ himagecof
    have hνV := ordinal_subset_hierarchy θ ν hνθ
    let := hf.value_ordinal hν.ordinal hνV
    have hbetween : ∃ ρ, ρ ∈ θ ∧ ρ ∈ f ‘ ν ∧ ν ∈ ρ ∧ Cn (n + 2) ρ := by
      rcases IsOrdinal.mem_trichotomy (f ‘ ν) θ with hi | he | hg
      · obtain ⟨ρ, hρ, hνρ, hCρ⟩ :=
          rankEmbedding_cnCofinal_image hθ hη hf hlim hνθ hνcof hi ν hνimage
        exact ⟨ρ, IsOrdinal.toIsTransitive.mem_trans hρ hi, hρ, hνρ, hCρ⟩
      · obtain ⟨ρ, hρθ, hνρ, hCρ⟩ := hlim ν hνθ
        exact ⟨ρ, hρθ, he.symm ▸ hρθ, hνρ, hCρ⟩
      · obtain ⟨ρ, hρθ, hνρ, hCρ⟩ := hlim ν hνθ
        exact ⟨ρ, hρθ, IsOrdinal.toIsTransitive.mem_trans hρθ hg, hνρ, hCρ⟩
    obtain ⟨ρ, _, hρim, hνρ, hρ⟩ := hbetween
    have hρall : ∀ b ∈ hierarchy ρ, ChoicelessSupercompactWitness (n + 2) α γ ρ b := by
      intro b hb
      exact choicelessSupercompactWitness_interpolate hbaseBelow hgap
        (htransfer ρ hρ (heq.symm ▸ hνρ) hρim b hb)
    exact hνfail (choicelessSupercompactAt_downward hν hρ hγν hνρ hρall)
  · apply hνfail
    intro b hb
    exact choicelessSupercompactWitness_interpolate hbaseBelow hgap
      (htransfer ν hν hlt hνimage b hb)

end ZFVP
