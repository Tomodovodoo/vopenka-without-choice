import ZFVP.ModelTheory.SchmerlInternalBranchNames

/-! Separated branch markers constructed as an internal function. All initial
families, choices, rank bounds, and recursion histories are internal sets. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsInternalCofinalBranch.comparable_of_rank_subset
    {D S κ rank B x y : V} (hT : InternalRankedTree D S κ rank)
    (hord : IsForcingPoset D S) [IsOrdinal κ]
    (hinj : ∀ x ∈ D, ∀ y ∈ D, ⟨x, y⟩ₖ ∈ S → rank ‘ x = rank ‘ y → x = y)
    (hB : IsInternalCofinalBranch D S κ rank B)
    (hx : x ∈ B) (hy : y ∈ B) (hxy : (rank ‘ x) ⊆ (rank ‘ y)) :
    ⟨x, y⟩ₖ ∈ S := by
  rcases hB.2.1 x hx y hy with h | h
  · exact h
  · have he : rank ‘ y = rank ‘ x := SetTheory.subset_antisymm
      (hT.rank_monotone y (hB.1 y hy) x (hB.1 x hx) h) hxy
    have hexy := hinj y (hB.1 y hy) x (hB.1 x hx) h he
    subst y
    exact hord.1.2.1 x (hB.1 x hx)

theorem IsInternalCofinalBranch.eq_of_subset
    {D S κ rank B C : V} (hT : InternalRankedTree D S κ rank)
    (hord : IsForcingPoset D S) [IsOrdinal κ]
    (hinj : ∀ x ∈ D, ∀ y ∈ D, ⟨x, y⟩ₖ ∈ S → rank ‘ x = rank ‘ y → x = y)
    (hB : IsInternalCofinalBranch D S κ rank B)
    (hC : IsInternalCofinalBranch D S κ rank C) (hBC : B ⊆ C) : B = C := by
  apply SetTheory.subset_antisymm hBC
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hB.2.2.1 (rank ‘ x) (function_value_mem hT.rank_function (hC.1 x hx))
  exact hB.2.2.2 x (hC.1 x hx) y hy
    (hC.comparable_of_rank_subset hT hord hinj hx (hBC y hy) hxy)

theorem IsInternalCofinalBranch.exists_difference
    {D S κ rank B C : V} (hT : InternalRankedTree D S κ rank)
    (hord : IsForcingPoset D S) [IsOrdinal κ]
    (hinj : ∀ x ∈ D, ∀ y ∈ D, ⟨x, y⟩ₖ ∈ S → rank ‘ x = rank ‘ y → x = y)
    (hB : IsInternalCofinalBranch D S κ rank B)
    (hC : IsInternalCofinalBranch D S κ rank C) (hne : B ≠ C) :
    ∃ x ∈ B, x ∉ C := by
  classical
  by_contra! h
  exact hne (hB.eq_of_subset hT hord hinj hC h)

noncomputable def internalEarlierBranches (J e ξ : V) : V := {B ∈ J ; e ‘ B ∈ ξ}

instance internalEarlierBranches_definable (J e : V) :
    ℒₛₑₜ-function₁[V] (internalEarlierBranches J e) := by
  have h : ℒₛₑₜ-relation[V] (fun I ξ ↦ ∀ B, B ∈ I ↔ B ∈ J ∧ e ‘ B ∈ ξ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [internalEarlierBranches, mem_sep_iff]
  rfl

theorem internalEarlierBranches_cardLE {J e κ ξ : V}
    (he : e ∈ κ ^ J) (hinj : Injective e) : internalEarlierBranches J e ξ ≤# ξ := by
  let I := internalEarlierBranches J e ξ
  let f := definableGraph I (fun B ↦ e ‘ B) (by definability)
  refine ⟨f, definableGraph_mem_function_of_mapsTo I _ _ _ (by
    intro B hB
    exact (mem_sep_iff.mp hB).2), ?_⟩
  intro B C z hB hC
  obtain ⟨hBI, hzB⟩ := (pair_mem_definableGraph_iff I _ _ B z).mp hB
  obtain ⟨hCI, hzC⟩ := (pair_mem_definableGraph_iff I _ _ C z).mp hC
  exact injective_value_eq he hinj (mem_sep_iff.mp hBI).1 (mem_sep_iff.mp hCI).1
    (hzB.symm.trans hzC)

noncomputable def internalMarkerCandidates (B I rank e f : V) : V :=
  {x ∈ B ; ∀ C ∈ I, rank ‘ (f ‘ (e ‘ C)) ∈ rank ‘ x ∧ x ∉ C}

instance internalMarkerCandidates_definable (rank e : V) :
    ℒₛₑₜ-function₃[V] (fun B I f ↦ internalMarkerCandidates B I rank e f) := by
  have h : ℒₛₑₜ-relation₄[V] (fun A B I f ↦ ∀ x,
      x ∈ A ↔ x ∈ B ∧ ∀ C ∈ I, rank ‘ (f ‘ (e ‘ C)) ∈ rank ‘ x ∧ x ∉ C) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = internalMarkerCandidates (v 1) (v 2) rank e (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [internalMarkerCandidates, mem_sep_iff]

set_option maxHeartbeats 800000 in
theorem internalMarkerCandidates_nonempty (hAC : InternalChoice V)
    {D S κ rank B I e f : V} (hT : InternalRankedTree D S κ rank)
    (hord : IsForcingPoset D S) (hreg : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hinj : ∀ x ∈ D, ∀ y ∈ D, ⟨x, y⟩ₖ ∈ S → rank ‘ x = rank ‘ y → x = y)
    (hB : IsInternalCofinalBranch D S κ rank B) (hI : IsInternallyCountable I)
    (hbranches : ∀ C ∈ I, IsInternalCofinalBranch D S κ rank C)
    (hdiff : ∀ C ∈ I, B ≠ C) (hprev : ∀ C ∈ I, f ‘ (e ‘ C) ∈ D) :
    IsNonempty (internalMarkerCandidates B I rank e f) := by
  have : IsOrdinal κ := hreg.1.1
  have hdiffne (C : V) (hC : C ∈ I) : IsNonempty (relativeComplement B C) := by
    obtain ⟨x, hx, hn⟩ := hB.exists_difference hT hord hinj (hbranches C hC) (hdiff C hC)
    exact ⟨⟨x, (mem_relativeComplement_iff _ _ _).mpr ⟨hx, hn⟩⟩⟩
  obtain ⟨g, _, _, hg⟩ := choice_for_definable_family hAC I
    (fun C ↦ relativeComplement B C) (by definability) hdiffne
  have hsplit (C : V) (hC : C ∈ I) : g ‘ C ∈ B ∧ g ‘ C ∉ C :=
    (mem_relativeComplement_iff _ _ _).mp (hg C hC)
  let U : V := repl (fun C ↦ rank ‘ (g ‘ C)) (by definability) I ∪
    repl (fun C ↦ rank ‘ (f ‘ (e ‘ C))) (by definability) I
  have hUC : IsInternallyCountable U := internallyCountable_union
    (internallyCountable_repl _ _ hI) (internallyCountable_repl _ _ hI)
  have hUκ : U ⊆ κ := by
    intro a ha
    rcases mem_union_iff.mp ha with ha | ha
    · obtain ⟨C, hC, rfl⟩ := (repl_spec _).mp ha
      exact function_value_mem hT.rank_function (hB.1 _ (hsplit C hC).1)
    · obtain ⟨C, hC, rfl⟩ := (repl_spec _).mp ha
      exact function_value_mem hT.rank_function (hprev C hC)
  obtain ⟨β, hβ, hUβ⟩ := regular_small_subset_bounded hreg hUκ hω hUC
  obtain ⟨x, hx, hβx⟩ := hB.2.2.1 β hβ
  refine ⟨⟨x, mem_sep_iff.mpr ⟨hx, fun C hC ↦ ?_⟩⟩⟩
  have hsplitrank : rank ‘ (g ‘ C) ∈ rank ‘ x := hβx _ (hUβ _
    (mem_union_iff.mpr (Or.inl ((repl_spec _).mpr ⟨C, hC, rfl⟩))))
  refine ⟨hβx _ (hUβ _ (mem_union_iff.mpr (Or.inr ((repl_spec _).mpr ⟨C, hC, rfl⟩)))), ?_⟩
  intro hxC
  have hcomp := hB.2.1 _ (hsplit C hC).1 x hx
  have hsx : ⟨g ‘ C, x⟩ₖ ∈ S := hcomp.resolve_right (fun hxs ↦ mem_irrefl _
    (hT.rank_monotone x (hB.1 x hx) _ (hB.1 _ (hsplit C hC).1) hxs _ hsplitrank))
  exact (hsplit C hC).2 ((hbranches C hC).2.2.2 _ (hB.1 _ (hsplit C hC).1) x hxC hsx)

noncomputable def internalIndexedBranch (J e ξ : V) : V := ⋃ˢ {B ∈ J ; e ‘ B = ξ}

instance internalIndexedBranch_definable (J e : V) :
    ℒₛₑₜ-function₁[V] (internalIndexedBranch J e) := by
  have h : ℒₛₑₜ-relation[V] (fun A ξ ↦ ∀ x, x ∈ A ↔ ∃ B ∈ J, e ‘ B = ξ ∧ x ∈ B) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = internalIndexedBranch J e (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [internalIndexedBranch, mem_sUnion_iff, mem_sep_iff]
  aesop

theorem internalIndexedBranch_eq {J e κ B : V} (he : e ∈ κ ^ J) (hinj : Injective e)
    (hB : B ∈ J) : internalIndexedBranch J e (e ‘ B) = B := by
  ext x
  constructor
  · intro hx
    obtain ⟨C, hC, hxC⟩ := mem_sUnion_iff.mp hx
    obtain ⟨hCJ, heq⟩ := mem_sep_iff.mp hC
    exact injective_value_eq he hinj hCJ hB heq ▸ hxC
  · intro hx
    exact mem_sUnion_iff.mpr ⟨B, mem_sep_iff.mpr ⟨hB, rfl⟩, hx⟩

noncomputable def internalMarkerStep (rank J e c f : V) : V :=
  c ‘ (internalMarkerCandidates (internalIndexedBranch J e (domain f))
    (internalEarlierBranches J e (domain f)) rank e f)

instance internalMarkerStep_definable (rank J e c : V) :
    ℒₛₑₜ-function₁[V] (internalMarkerStep rank J e c) := by
  have h : ℒₛₑₜ-relation[V] (fun z f ↦ ∃ A,
      (∀ x, x ∈ A ↔ x ∈ internalIndexedBranch J e (domain f) ∧
        ∀ C ∈ internalEarlierBranches J e (domain f),
          rank ‘ (f ‘ (e ‘ C)) ∈ rank ‘ x ∧ x ∉ C) ∧ z = c ‘ A) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = internalMarkerStep rank J e c (v 1) ↔ _
  constructor
  · intro hz
    refine ⟨internalMarkerCandidates (internalIndexedBranch J e (domain (v 1)))
      (internalEarlierBranches J e (domain (v 1))) rank e (v 1), ?_, hz⟩
    intro x
    exact mem_sep_iff
  · rintro ⟨A, hA, hz⟩
    have heq : A = internalMarkerCandidates (internalIndexedBranch J e (domain (v 1)))
        (internalEarlierBranches J e (domain (v 1))) rank e (v 1) := by
      ext x
      simpa only [internalMarkerCandidates, mem_sep_iff] using hA x
    exact hz.trans (congrArg (fun X ↦ c ‘ X) heq)

noncomputable def internalMarkerStage (rank J e c ξ : V) : V :=
  Replacement.transfiniteRec (internalMarkerStep rank J e c)
    (internalMarkerStep_definable rank J e c) ξ

instance internalMarkerStage_definable (rank J e c : V) :
    ℒₛₑₜ-function₁[V] (internalMarkerStage rank J e c) :=
  Replacement.transfiniteRec_definable (internalMarkerStep_definable rank J e c)

theorem internalMarkerStage_eq (rank J e c ξ : V) [IsOrdinal ξ] :
    internalMarkerStage rank J e c ξ =
      c ‘ (internalMarkerCandidates (internalIndexedBranch J e ξ)
        (internalEarlierBranches J e ξ) rank e
        (definableGraph ξ (internalMarkerStage rank J e c) (by definability))) := by
  have h := Replacement.transfiniteRec_spec (internalMarkerStep rank J e c)
    (internalMarkerStep_definable rank J e c) (IsOrdinal.toOrdinal ξ)
  change internalMarkerStage rank J e c ξ = internalMarkerStep rank J e c
    (definableGraph ξ (internalMarkerStage rank J e c) (by definability)) at h
  rw [h]
  unfold internalMarkerStep
  rw [domain_definableGraph]

set_option maxHeartbeats 1200000 in
theorem internalMarkerStage_spec (hAC : InternalChoice V)
    {D S κ rank J e c : V} (hT : InternalRankedTree D S κ rank)
    (hord : IsForcingPoset D S) (hreg : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hsmall : ∀ ξ ∈ κ, IsInternallyCountable ξ)
    (hrankinj : ∀ x ∈ D, ∀ y ∈ D, ⟨x, y⟩ₖ ∈ S → rank ‘ x = rank ‘ y → x = y)
    (he : e ∈ κ ^ J) (heinj : Injective e)
    (hbranches : ∀ B ∈ J, IsInternalCofinalBranch D S κ rank B)
    (hc : ∀ X, X ⊆ D → IsNonempty X → c ‘ X ∈ X) :
    ∀ B ∈ J, internalMarkerStage rank J e c (e ‘ B) ∈ B ∧
      ∀ C ∈ J, e ‘ C ∈ e ‘ B →
        rank ‘ (internalMarkerStage rank J e c (e ‘ C)) ∈
          rank ‘ (internalMarkerStage rank J e c (e ‘ B)) ∧
        internalMarkerStage rank J e c (e ‘ B) ∉ C := by
  have : IsOrdinal κ := hreg.1.1
  have key : ∀ ξ : Ordinal V, ∀ B ∈ J, e ‘ B = (ξ : V) →
      internalMarkerStage rank J e c (ξ : V) ∈ B ∧
      ∀ C ∈ J, e ‘ C ∈ (ξ : V) →
        rank ‘ (internalMarkerStage rank J e c (e ‘ C)) ∈
          rank ‘ (internalMarkerStage rank J e c (ξ : V)) ∧
        internalMarkerStage rank J e c (ξ : V) ∉ C := by
    apply transfinite_induction (fun ξ ↦ ∀ B ∈ J, e ‘ B = ξ →
      internalMarkerStage rank J e c ξ ∈ B ∧
      ∀ C ∈ J, e ‘ C ∈ ξ →
        rank ‘ (internalMarkerStage rank J e c (e ‘ C)) ∈
          rank ‘ (internalMarkerStage rank J e c ξ) ∧
        internalMarkerStage rank J e c ξ ∉ C) (by definability)
    intro ξ ih B hBJ heB
    let I := internalEarlierBranches J e (ξ : V)
    let f := definableGraph (ξ : V) (internalMarkerStage rank J e c) (by definability)
    have hI : IsInternallyCountable I :=
      (internalEarlierBranches_cardLE he heinj).trans
        (hsmall (ξ : V) (heB ▸ function_value_mem he hBJ))
    have hIbranches (C : V) (hC : C ∈ I) := hbranches C (mem_sep_iff.mp hC).1
    have hIdiff (C : V) (hC : C ∈ I) : B ≠ C := by
      intro hBC
      subst C
      have hbad : (ξ : V) ∈ (ξ : V) := heB ▸ (mem_sep_iff.mp hC).2
      exact mem_irrefl _ hbad
    have hIprev (C : V) (hC : C ∈ I) : f ‘ (e ‘ C) ∈ D := by
      have hCJ := (mem_sep_iff.mp hC).1
      have heC := (mem_sep_iff.mp hC).2
      have : IsOrdinal (e ‘ C) := IsOrdinal.of_mem heC
      rw [show f ‘ (e ‘ C) = internalMarkerStage rank J e c (e ‘ C) from
        value_definableGraph _ _ _ heC]
      exact (hbranches C hCJ).1 _
        ((ih (IsOrdinal.toOrdinal (e ‘ C)) (Ordinal.lt_def.mpr heC) C hCJ rfl).1)
    let A := internalMarkerCandidates B I rank e f
    have hA : IsNonempty A := internalMarkerCandidates_nonempty hAC hT hord hreg hω
      hrankinj (hbranches B hBJ) hI hIbranches hIdiff hIprev
    have hAD : A ⊆ D := subset_trans sep_subset (hbranches B hBJ).1
    have hval : c ‘ A ∈ A := hc A hAD hA
    have hIndexed : internalIndexedBranch J e (ξ : V) = B := by
      rw [← heB]
      exact internalIndexedBranch_eq he heinj hBJ
    have hstage : internalMarkerStage rank J e c (ξ : V) = c ‘ A := by
      rw [internalMarkerStage_eq, hIndexed]
    rw [← hstage] at hval
    have hval' := mem_sep_iff.mp hval
    refine ⟨hval'.1, fun C hCJ heC ↦ ?_⟩
    have hC := hval'.2 C (mem_sep_iff.mpr ⟨hCJ, heC⟩)
    rw [show f ‘ (e ‘ C) = internalMarkerStage rank J e c (e ‘ C) from
      value_definableGraph _ _ _ heC] at hC
    exact hC
  intro B hB
  have : IsOrdinal (e ‘ B) := IsOrdinal.of_mem (function_value_mem he hB)
  exact key (IsOrdinal.toOrdinal (e ‘ B)) B hB rfl

/-- The actual marker function exists from the internal branch-cardinality
bound. Neither markers nor a countable family of external nodes is supplied. -/
theorem exists_internal_separated_branch_markers (hAC : InternalChoice V)
    {D S rank J : V}
    (hT : InternalRankedTree D S (hartogsNumber (ω : V)) rank)
    (hord : IsForcingPoset D S)
    (hrankinj : ∀ x ∈ D, ∀ y ∈ D, ⟨x, y⟩ₖ ∈ S → rank ‘ x = rank ‘ y → x = y)
    (hJ : J ≤# hartogsNumber (ω : V))
    (hbranches : ∀ B ∈ J, IsInternalCofinalBranch D S (hartogsNumber (ω : V)) rank B) :
    ∃ m ∈ D ^ J, (∀ B ∈ J, m ‘ B ∈ B) ∧
      ∀ B ∈ J, ∀ C ∈ J, B ≠ C → ⟨m ‘ B, m ‘ C⟩ₖ ∈ S → m ‘ C ∉ B := by
  obtain ⟨e, he, heinj⟩ := hJ
  let A : V := {X ∈ ℘ D ; IsNonempty X}
  obtain ⟨c, _, hc⟩ := hAC A (fun X hX ↦ (mem_sep_iff.mp hX).2)
  have hchoice (X : V) (hX : X ⊆ D) (hne : IsNonempty X) : c ‘ X ∈ X :=
    hc X (mem_sep_iff.mpr ⟨mem_power_iff.mpr hX, hne⟩)
  have hreg := hartogsNumber_omega_regular (dependentChoiceAt_of_internalChoice hAC (ω : V))
  have hspec := internalMarkerStage_spec hAC hT hord hreg omega_mem_hartogs_omega
    (fun _ hξ ↦ countable_of_mem_hartogs_omega hξ) hrankinj he heinj hbranches hchoice
  let F : V → V := fun B ↦ internalMarkerStage rank J e c (e ‘ B)
  have hF : ℒₛₑₜ-function₁ F := by dsimp only [F]; definability
  let m := definableGraph J F hF
  have hm : m ∈ D ^ J := definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun B hB ↦ (hbranches B hB).1 _ (hspec B hB).1)
  have hval (B : V) (hB : B ∈ J) : m ‘ B = F B := value_definableGraph _ _ _ hB
  refine ⟨m, hm, (fun B hB ↦ hval B hB ▸ (hspec B hB).1), ?_⟩
  intro B hB C hC hBC hrel
  rw [hval B hB, hval C hC] at hrel
  rw [hval C hC]
  have : IsOrdinal (e ‘ B) := IsOrdinal.of_mem (function_value_mem he hB)
  have : IsOrdinal (e ‘ C) := IsOrdinal.of_mem (function_value_mem he hC)
  rcases IsOrdinal.mem_trichotomy (e ‘ B) (e ‘ C) with hlt | heq | hgt
  · exact (hspec C hC).2 B hB hlt |>.2
  · exact False.elim (hBC (injective_value_eq he heinj hB hC heq))
  · exact False.elim (mem_irrefl _ (hT.rank_monotone _ ((hbranches B hB).1 _ (hspec B hB).1)
      _ ((hbranches C hC).1 _ (hspec C hC).1) hrel _ ((hspec B hB).2 C hC hgt).1))

end ZFVP.Schmerl
