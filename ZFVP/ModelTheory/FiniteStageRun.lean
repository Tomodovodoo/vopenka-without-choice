import ZFVP.ModelTheory.StageRunConstruction
import ZFVP.SetTheory.FiniteDictionary

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u
variable {Ω : Type u}

theorem StagePreservesFinite.refl (S : StageModel Ω) : StagePreservesFinite S S := by
  intro _ _ hsub a ha b hb
  exact ⟨b, hb, rfl⟩

/-- Preservation composes along elementary stage inclusions. -/
theorem StagePreservesFinite.trans {S T U : StageModel Ω}
    (hST : StageLe S T) (hTU : StageLe T U)
    (h₁ : StagePreservesFinite S T) (h₂ : StagePreservesFinite T U) :
    StagePreservesFinite S U := by
  intro _ _
  have : Nonempty ↥T.carrier := Nonempty.map hST.map inferInstance
  have : (↥T.carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := models_zf_of_map hST.map
  intro hsub a ha b hb
  have haT : IsInternallyFinite (StageModel.incl hST.subset a) := by
    rw [← hST.map_apply]
    exact (hST.map.map_internallyFinite_iff a).mpr ha
  obtain ⟨t, ht, htb⟩ := h₂ hTU.subset _ haT b hb
  obtain ⟨m, hm, hmt⟩ := h₁ hST.subset a ha t ht
  refine ⟨m, hm, ?_⟩
  have heq := congrArg (StageModel.incl hTU.subset) hmt
  exact heq.trans htb

/-- If every member of the upper stage appears at an earlier stage, finite preservation
from a fixed stage to those earlier stages gives finite preservation to the upper stage. -/
theorem stagePreservesFinite_of_covered {J : Type*} (S T : StageModel Ω)
    (F : J → StageModel Ω)
    (hSF : ∀ i, StageLe S (F i)) (hFT : ∀ i, StageLe (F i) T)
    (hfinite : ∀ i, StagePreservesFinite S (F i))
    (hcover : ∀ b ∈ T.carrier, ∃ i, b ∈ (F i).carrier) : StagePreservesFinite S T := by
  intro _ _ hsub a ha b hb
  obtain ⟨i, hi⟩ := hcover b b.property
  let b' : ↥(F i).carrier := ⟨b, hi⟩
  have hb' : b' ∈ StageModel.incl (hSF i).subset a := by
    apply ((hFT i).mem_iff _ _).mpr
    exact hb
  obtain ⟨m, hm, heq⟩ := hfinite i (hSF i).subset a ha b' hb'
  refine ⟨m, hm, ?_⟩
  exact Subtype.ext (congrArg (fun x : ↥(F i).carrier ↦ (x : Ω)) heq)

/-- Old internally finite sets acquire no new members at any later recursive stage. -/
theorem stageRunRec_preservesFinite (base : StageModel Ω) (code : OmegaOne ≃ Ω)
    (guess : OmegaOne → Set Ω) (hΩ : Cardinal.mk Ω = Cardinal.aleph 1)
    (hbc : base.carrier.Countable) (hbne : Nonempty ↥base.carrier) (hbzf : StageZF base)
    (α : OmegaOne) : ∀ β, β ≤ α →
      StagePreservesFinite (stageRunRec base code guess β) (stageRunRec base code guess α) := by
  let R := stageRunRec base code guess
  have hinv := stageRunRec_inv base code guess hΩ hbc hbne hbzf
  have hle : ∀ β α, β ≤ α → StageLe (R β) (R α) :=
    fun β α h ↦ (hinv α).2.2.2.1 β h
  change ∀ β, β ≤ α → StagePreservesFinite (R β) (R α)
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    intro β hβα
    rcases lt_or_eq_of_le hβα with hβα | rfl
    · by_cases hp : ∃ p, IsPredIndex p α
      · obtain ⟨p, hp⟩ := hp
        apply StagePreservesFinite.trans (hle β p (hp.2 β hβα)) (hle p α hp.1.le)
          (ih p hp.1 β (hp.2 β hβα))
        change StagePreservesFinite (stageRunRec base code guess p) (stageRunRec base code guess α)
        rw [stageRunRec_succ base code guess hp]
        exact stagePreservesFinite_succStage _ _ _
      · have hlim : IsLimitIndex α := by
          refine ⟨⟨β, hβα⟩, fun γ hγ ↦ ?_⟩
          by_contra hc
          push_neg at hc
          exact hp ⟨γ, hγ, fun δ hδ ↦ not_lt.mp fun hlt ↦
            absurd hδ (not_lt.mpr (hc δ hlt))⟩
        let F : ↥(Set.Iio α) → StageModel Ω := fun γ ↦ R (max β γ.val)
        have hm : ∀ γ : ↥(Set.Iio α), max β γ.val < α :=
          fun γ ↦ max_lt hβα γ.property
        apply stagePreservesFinite_of_covered (R β) (R α) F
          (fun γ ↦ hle β _ (le_max_left _ _))
          (fun γ ↦ hle _ α (hm γ).le)
          (fun γ ↦ ih _ (hm γ) β (le_max_left _ _))
        intro b hb
        have hc : b ∈ (limitStage fun γ : ↥(Set.Iio α) ↦ R γ.val).carrier := by
          change b ∈ (stageRunRec base code guess α).carrier at hb
          rwa [stageRunRec_limit base code guess hlim] at hb
        obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp hc
        exact ⟨γ, (hle γ.val _ (le_max_right _ _)).subset hγ⟩
    · exact StagePreservesFinite.refl _

/-- A union of countable elementary stages has countable finite extensions when
old internally finite sets gain no new members. -/
theorem internallyFinite_members_countable_of_stage_cover {J : Type*}
    (T : StageModel Ω) (F : J → StageModel Ω)
    [Nonempty ↥T.carrier] [(↥T.carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hcount : ∀ i, (F i).carrier.Countable)
    (hne : ∀ i, Nonempty ↥(F i).carrier) (hzf : ∀ i, StageZF (F i))
    (hle : ∀ i, StageLe (F i) T)
    (hfinite : ∀ i, StagePreservesFinite (F i) T)
    (hcover : ∀ b ∈ T.carrier, ∃ i, b ∈ (F i).carrier)
    (a : ↥T.carrier) (ha : IsInternallyFinite a) :
    {b : ↥T.carrier | b ∈ a}.Countable := by
  obtain ⟨i, hi⟩ := hcover a a.property
  have : Nonempty ↥(F i).carrier := hne i
  have : (↥(F i).carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := hzf i
  have : Countable ↥(F i).carrier := (hcount i).to_subtype
  let a' : ↥(F i).carrier := ⟨a, hi⟩
  have heq : (hle i).map a' = a := by
    rw [(hle i).map_apply]
    rfl
  have ha' : IsInternallyFinite a' := ( (hle i).map.map_internallyFinite_iff a').mp (heq.symm ▸ ha)
  apply (Set.countable_range (StageModel.incl (hle i).subset)).mono
  intro b hb
  obtain ⟨m, hm, he⟩ := hfinite i (hle i).subset a' ha' b hb
  exact ⟨m, he⟩

/-- The union of the strengthened recursion satisfies the semantic FinSmall clause. -/
theorem stageRunRec_union_finSmall (base : StageModel Ω) (code : OmegaOne ≃ Ω)
    (guess : OmegaOne → Set Ω) (hΩ : Cardinal.mk Ω = Cardinal.aleph 1)
    (hbc : base.carrier.Countable) (hbne : Nonempty ↥base.carrier) (hbzf : StageZF base) :
    let T := limitStage (stageRunRec base code guess)
    ∃ (_ : Nonempty ↥T.carrier) (_ : (↥T.carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙),
      ∀ a : ↥T.carrier, IsInternallyFinite a → {b : ↥T.carrier | b ∈ a}.Countable := by
  let R := stageRunRec base code guess
  have hinv := stageRunRec_inv base code guess hΩ hbc hbne hbzf
  have hle : ∀ β α, β ≤ α → StageLe (R β) (R α) :=
    fun β α h ↦ (hinv α).2.2.2.1 β h
  let F : StageFamily Ω OmegaOne :=
    { stage := R
      inc := fun i k h ↦ (hle i k h).subset
      agree := fun i k h x y _ _ ↦ (hle i k h).mem_iff x y
      step := fun {i k} h ↦ (hle i k h).map
      step_apply := fun {i k} h x ↦ (hle i k h).map_apply x }
  have hFT : ∀ i, StageLe (R i) (limitStage R) := fun i ↦
    ⟨subset_limitStage R i, limitStage_mem_iff F.inc F.agree i,
      F.embedding i, fun _ ↦ rfl⟩
  have hf : ∀ i, StagePreservesFinite (R i) (limitStage R) := by
    intro i
    apply stagePreservesFinite_of_covered (R i) (limitStage R) (fun j : OmegaOne ↦ R (max i j))
      (fun j ↦ hle i _ (le_max_left _ _)) (fun j ↦ hFT (max i j))
      (fun j ↦ stageRunRec_preservesFinite base code guess hΩ hbc hbne hbzf _ i (le_max_left _ _))
    intro b hb
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
    exact ⟨j, (hle j _ (le_max_right _ _)).subset hj⟩
  have hn : Nonempty ↥(limitStage R).carrier := limitStage_nonempty R leastIndex (hinv _).2.1
  have hn0 : Nonempty ↥(R leastIndex).carrier := (hinv _).2.1
  have hz : (↥(limitStage R).carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := F.models_zf leastIndex (hinv _).2.2.1
  refine ⟨hn, hz, ?_⟩
  exact internallyFinite_members_countable_of_stage_cover (limitStage R) R
    (fun i ↦ (hinv i).1) (fun i ↦ (hinv i).2.1) (fun i ↦ (hinv i).2.2.1)
    hFT hf (fun _ hb ↦ Set.mem_iUnion.mp hb)

/-- The actual StageRun can be chosen to preserve old finite sets at every later stage. -/
theorem exists_finite_stageRun_of_base {M : Type u} [SetStructure M]
    (base : StageModel Ω) (code : OmegaOne ≃ Ω) (guess : OmegaOne → Set Ω)
    (hΩ : Cardinal.mk Ω = Cardinal.aleph 1) (hbc : base.carrier.Countable)
    (hbne : Nonempty ↥base.carrier) (hbzf : StageZF base)
    (bmap : ElementaryMap M ↥base.carrier) :
    ∃ (inst : SetStructure Ω) (R : @StageRun M _ Ω inst),
      R.code = code ∧ R.guess = guess ∧
      ∀ β α, β ≤ α → StagePreservesFinite (R.stage β) (R.stage α) := by
  obtain ⟨inst, R, hc, hg, hs⟩ :=
    exists_stageRun_of_base_with_stages base code guess hΩ hbc hbne hbzf bmap
  refine ⟨inst, R, hc, hg, ?_⟩
  rw [hs]
  exact fun β α h ↦ stageRunRec_preservesFinite base code guess hΩ hbc hbne hbzf α β h

/-- The finite-preserving StageRun over any countable model of ZF. -/
theorem exists_finite_stageRun {M : Type u} [SetStructure M] [Nonempty M] [Countable M]
    [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (hΩ : Cardinal.mk Ω = Cardinal.aleph 1)
    (code : OmegaOne ≃ Ω) (guess : OmegaOne → Set Ω) :
    ∃ (inst : SetStructure Ω) (R : @StageRun M _ Ω inst),
      R.code = code ∧ R.guess = guess ∧
      ∀ β α, β ≤ α → StagePreservesFinite (R.stage β) (R.stage α) := by
  obtain ⟨B, e, hBc⟩ := exists_carrier_embedding (Ω := Ω) hΩ M
  have hbne : Nonempty ↥(StageModel.ofEquiv B e).carrier :=
    Nonempty.map (e.symm : M → ↥B) inferInstance
  refine exists_finite_stageRun_of_base (StageModel.ofEquiv B e) code guess hΩ hBc hbne ?_
    (StageModel.ofEquivSymmMap B e)
  intro _
  exact models_zf_of_map (StageModel.ofEquivSymmMap B e)

end ZFVP

