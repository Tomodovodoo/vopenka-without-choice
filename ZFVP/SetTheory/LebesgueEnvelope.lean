import ZFVP.SetTheory.NullCodes

/-! The measurable envelope: a countable family of trees together with a null set is contained in
a `G_δ` set whose difference from the union of the bodies is null. The `G_δ` code is decreasing,
built from monotone levels of the trees and finite intersections of the covers of the null set. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The union of a finite set of naturals is a natural. -/
theorem sUnion_naturals_mem {S : V} (hS : S ⊆ (ω : V)) (hfin : IsInternallyFinite S) : ⋃ˢ S ∈ (ω : V) := by
  obtain ⟨L, hL, hbound⟩ := internallyFinite_naturals_bounded hfin hS
  have : IsOrdinal L := IsOrdinal.nat hL
  have hord : IsOrdinal (⋃ˢ S) := IsOrdinal.sUnion (fun α hα ↦ IsOrdinal.nat (hS α hα))
  have hsub : ⋃ˢ S ⊆ L := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    exact IsOrdinal.toIsTransitive.transitive y (hbound y hy) x hxy
  rcases (IsOrdinal.subset_iff (α := ⋃ˢ S) (β := L)).mp hsub with h | h
  · rw [h]; exact hL
  · exact IsTransitive.ω.transitive L hL _ h

instance levelSet_definable : ℒₛₑₜ-function₂[V] levelSet := by
  have h : ℒₛₑₜ-relation₃ (fun S T M : V ↦ ∀ s, s ∈ S ↔ s ∈ T ∧ s ∈ ((2 : ℕ) : V) ^ M) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = levelSet (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_levelSet_iff]

theorem openFrom_mono {S S' : V} (h : S ⊆ S') : openFrom S ⊆ openFrom S' := by
  intro x hx
  obtain ⟨hxc, s, hs, hxs⟩ := (mem_openFrom_iff _ _).mp hx
  exact (mem_openFrom_iff _ _).mpr ⟨hxc, s, h s hs, hxs⟩

theorem mem_openFrom_union_iff (S S' x : V) : x ∈ openFrom (S ∪ S') ↔ x ∈ openFrom S ∨ x ∈ openFrom S' := by
  rw [mem_openFrom_iff, mem_openFrom_iff, mem_openFrom_iff]
  constructor
  · rintro ⟨hxc, s, hs, hxs⟩
    rcases mem_union_iff.mp hs with hs | hs
    · exact Or.inl ⟨hxc, s, hs, hxs⟩
    · exact Or.inr ⟨hxc, s, hs, hxs⟩
  · rintro (⟨hxc, s, hs, hxs⟩ | ⟨hxc, s, hs, hxs⟩)
    · exact ⟨hxc, s, mem_union_iff.mpr (Or.inl hs), hxs⟩
    · exact ⟨hxc, s, mem_union_iff.mpr (Or.inr hs), hxs⟩

theorem openFrom_levelSet_antitone {T M M' : V} (hT : IsTree T) (hM : M ∈ (ω : V)) (hM' : M' ∈ (ω : V))
    (hMM' : M ⊆ M') : openFrom (levelSet T M') ⊆ openFrom (levelSet T M) := by
  intro x hx
  obtain ⟨hxc, s, hs, hxs⟩ := (mem_openFrom_iff _ _).mp hx
  obtain ⟨hsT, hsM'⟩ := (mem_levelSet_iff _ _ _).mp hs
  have : IsFunction x := IsFunction.of_mem hxc
  rw [domain_eq_of_mem_function hsM'] at hxs
  have hxM' : x ↾ M' ∈ T := by rw [hxs]; exact hsT
  have hxM'' : x ↾ M' ∈ ((2 : ℕ) : V) ^ M' := function_restrict_mem hxc (IsTransitive.ω.transitive M' hM')
  have hxM : x ↾ M ∈ T := by
    rw [← restrict_restrict_of_subset hMM']
    exact tree_restrict_mem hT hxM' hM (by rw [domain_eq_of_mem_function hxM'']; exact hMM')
  refine (mem_openFrom_iff _ _).mpr ⟨hxc, x ↾ M, (mem_levelSet_iff _ _ _).mpr
    ⟨hxM, function_restrict_mem hxc (IsTransitive.ω.transitive M hM)⟩, ?_⟩
  rw [domain_eq_of_mem_function (function_restrict_mem hxc (IsTransitive.ω.transitive M hM))]

/-- `t` extends a member of each of the first `m + 1` covers. -/
def MultiMeets (f m t : V) : Prop := ∀ j ∈ succ m, ∃ s ∈ range (f ‘ j), s ⊆ t

instance multiMeets_definable : ℒₛₑₜ-relation₃[V] MultiMeets := by
  unfold MultiMeets
  definability

instance multiMeetsPred_definable (f m : V) : ℒₛₑₜ-predicate[V] (MultiMeets f m) := by
  definability

noncomputable def multiInter (f m : V) : V := sep (binarySequences V) (MultiMeets f m) (multiMeetsPred_definable f m)

instance multiInter_definable : ℒₛₑₜ-function₂[V] multiInter := by
  have h : ℒₛₑₜ-relation₃ (fun S f m : V ↦ ∀ t, t ∈ S ↔ t ∈ binarySequences V ∧ MultiMeets f m t) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = multiInter (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [multiInter, mem_sep_iff]

theorem mem_multiInter_iff (f m t : V) : t ∈ multiInter f m ↔ t ∈ binarySequences V ∧ MultiMeets f m t :=
  mem_sep_iff

theorem multiInter_subset (f m : V) : multiInter f m ⊆ binarySequences V := sep_subset

theorem openFrom_multiInter_subset {f m j : V} (hf : f ∈ ((binarySequences V) ^ (ω : V)) ^ (ω : V))
    (hj : j ∈ (ω : V)) (hjm : j ∈ succ m) : openFrom (multiInter f m) ⊆ openFrom (range (f ‘ j)) := by
  intro x hx
  obtain ⟨hxc, t, ht, hxt⟩ := (mem_openFrom_iff _ _).mp hx
  obtain ⟨-, hmeets⟩ := (mem_multiInter_iff _ _ _).mp ht
  obtain ⟨s, hs, hst⟩ := hmeets j hjm
  have : IsFunction x := IsFunction.of_mem hxc
  have hsB : s ∈ binarySequences V := range_subset_of_mem_function (function_value_mem hf hj) s hs
  have hsf : IsFunction s := binarySequence_isFunction hsB
  refine (mem_openFrom_iff _ _).mpr ⟨hxc, s, hs, ?_⟩
  have hsx : s ⊆ x := by
    intro p hp
    have := hst p hp
    rw [← hxt] at this
    exact restrict_subset x (domain t) p this
  exact restrict_domain_eq_of_subset hsx

theorem succ_subset_succ_of_natural {m m' : V} (hm : m ∈ (ω : V)) (hm' : m' ∈ (ω : V)) (hmm' : m ⊆ m') :
    succ m ⊆ succ m' := by
  have : IsOrdinal m := IsOrdinal.nat hm
  have : IsOrdinal m' := IsOrdinal.nat hm'
  intro j hj
  rcases mem_succ_iff.mp hj with rfl | hj
  · rcases (IsOrdinal.subset_iff (α := j) (β := m')).mp hmm' with h | h
    · rw [h]; exact mem_succ_self m'
    · exact mem_succ_iff.mpr (Or.inr h)
  · exact mem_succ_iff.mpr (Or.inr (hmm' j hj))

theorem openFrom_multiInter_antitone {f m m' : V} (hm : m ∈ (ω : V)) (hm' : m' ∈ (ω : V)) (hmm' : m ⊆ m') :
    openFrom (multiInter f m') ⊆ openFrom (multiInter f m) := by
  refine openFrom_mono (fun t ht ↦ ?_)
  obtain ⟨htB, hmeets⟩ := (mem_multiInter_iff _ _ _).mp ht
  exact (mem_multiInter_iff _ _ _).mpr ⟨htB, fun j hj ↦ hmeets j (succ_subset_succ_of_natural hm hm' hmm' j hj)⟩

/-- `s` is an initial segment of `x`. -/
def MeetsPred (x s : V) : Prop := x ↾ (domain s) = s

instance meetsPred_definable : ℒₛₑₜ-relation[V] MeetsPred := by
  unfold MeetsPred
  definability

instance meetsPredFix_definable (x : V) : ℒₛₑₜ-predicate[V] (MeetsPred x) := by
  definability

noncomputable def witnessSet (f x j : V) : V := sep (range (f ‘ j)) (MeetsPred x) (meetsPredFix_definable x)

theorem mem_witnessSet_iff (f x j s : V) : s ∈ witnessSet f x j ↔ s ∈ range (f ‘ j) ∧ x ↾ (domain s) = s :=
  mem_sep_iff

instance witnessSet_definable (f x : V) : ℒₛₑₜ-function₁[V] (witnessSet f x) := by
  have h : ℒₛₑₜ-relation (fun W j : V ↦ ∀ s, s ∈ W ↔ s ∈ range (f ‘ j) ∧ MeetsPred x s) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = witnessSet f x (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [witnessSet, mem_sep_iff]

theorem witnessDomain_definable (c f x : V) : ℒₛₑₜ-function₁ (fun j : V ↦ domain (c ‘ (witnessSet f x j))) := by
  definability

/-- A real meeting the first `m + 1` covers lies in the open set of the finite intersection. -/
theorem mem_openFrom_multiInter (hAC : InternalChoice V) {f m x : V}
    (hf : f ∈ ((binarySequences V) ^ (ω : V)) ^ (ω : V)) (hm : m ∈ (ω : V)) (hx : x ∈ cantorSpace V)
    (h : ∀ j ∈ succ m, ∃ s ∈ range (f ‘ j), x ↾ (domain s) = s) : x ∈ openFrom (multiInter f m) := by
  have hxf : IsFunction x := IsFunction.of_mem hx
  have hjω : ∀ j ∈ succ m, j ∈ (ω : V) := fun j hj ↦ IsTransitive.ω.transitive _ (ω_succ_closed hm) j hj
  have hne : ∀ j ∈ succ m, IsNonempty (witnessSet f x j) := by
    intro j hj
    obtain ⟨s, hs, hxs⟩ := h j hj
    exact ⟨s, (mem_witnessSet_iff _ _ _ _).mpr ⟨hs, hxs⟩⟩
  obtain ⟨𝒲, h𝒲⟩ : ∃ W : V, W = repl (witnessSet f x) (witnessSet_definable f x) (succ m) := ⟨_, rfl⟩
  obtain ⟨c, -, hcval⟩ := hAC 𝒲 (fun X hX ↦ by
    rw [h𝒲] at hX
    obtain ⟨j, hj, rfl⟩ := (repl_spec (witnessSet_definable f x)).mp hX
    exact hne j hj)
  have hc : ∀ j ∈ succ m, c ‘ (witnessSet f x j) ∈ range (f ‘ j) ∧ x ↾ (domain (c ‘ (witnessSet f x j))) =
      c ‘ (witnessSet f x j) := fun j hj ↦
    (mem_witnessSet_iff _ _ _ _).mp (hcval _ (by rw [h𝒲]; exact (repl_spec (witnessSet_definable f x)).mpr ⟨j, hj, rfl⟩))
  have hcB : ∀ j ∈ succ m, c ‘ (witnessSet f x j) ∈ binarySequences V := fun j hj ↦
    range_subset_of_mem_function (function_value_mem hf (hjω j hj)) _ (hc j hj).1
  have hcdom : ∀ j ∈ succ m, domain (c ‘ (witnessSet f x j)) ∈ (ω : V) := fun j hj ↦
    ((mem_finiteSequences_iff_domain _ _).mp (hcB j hj)).1
  obtain ⟨D, hDdef⟩ : ∃ D : V, D = repl (fun j ↦ domain (c ‘ (witnessSet f x j))) (witnessDomain_definable c f x) (succ m) :=
    ⟨_, rfl⟩
  have hDω : D ⊆ (ω : V) := by
    intro d hd
    rw [hDdef] at hd
    obtain ⟨j, hj, rfl⟩ := (repl_spec (witnessDomain_definable c f x)).mp hd
    exact hcdom j hj
  have hDfin : IsInternallyFinite D := by
    rw [hDdef]
    exact internallyFinite_repl _ _ ⟨_, ω_succ_closed hm, CardEQ.refl _⟩
  obtain ⟨L, hLdef⟩ : ∃ L : V, L = ⋃ˢ D := ⟨_, rfl⟩
  have hL : L ∈ (ω : V) := by rw [hLdef]; exact sUnion_naturals_mem hDω hDfin
  have hdL : ∀ j ∈ succ m, domain (c ‘ (witnessSet f x j)) ⊆ L := by
    intro j hj
    rw [hLdef]
    refine subset_sUnion_of_mem ?_
    rw [hDdef]
    exact (repl_spec (witnessDomain_definable c f x)).mpr ⟨j, hj, rfl⟩
  have htB : x ↾ L ∈ binarySequences V := restrict_mem_binarySequences hx hL
  have htdom : domain (x ↾ L) = L := domain_eq_of_mem_function (function_restrict_mem hx (IsTransitive.ω.transitive L hL))
  refine (mem_openFrom_iff _ _).mpr ⟨hx, x ↾ L, (mem_multiInter_iff _ _ _).mpr ⟨htB, fun j hj ↦ ?_⟩, by rw [htdom]⟩
  refine ⟨c ‘ (witnessSet f x j), (hc j hj).1, ?_⟩
  rw [← (hc j hj).2, ← restrict_restrict_of_subset (hdL j hj)]
  exact restrict_subset _ _

/-- The covers of `N` at precision `m`. -/
def NullCoverPred (N m f' : V) : Prop := IsCoverAt f' N m

instance nullCoverPred_definable : ℒₛₑₜ-relation₃[V] NullCoverPred := by
  unfold NullCoverPred
  definability

instance nullCoverPredFix_definable (N m : V) : ℒₛₑₜ-predicate[V] (NullCoverPred N m) := by
  definability

noncomputable def nullCoverSet (N m : V) : V :=
  sep ((binarySequences V) ^ (ω : V)) (NullCoverPred N m) (nullCoverPredFix_definable N m)

instance nullCoverSet_definable (N : V) : ℒₛₑₜ-function₁[V] (nullCoverSet N) := by
  have h : ℒₛₑₜ-relation (fun C m : V ↦ ∀ f', f' ∈ C ↔ f' ∈ (binarySequences V) ^ (ω : V) ∧ NullCoverPred N m f') := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = nullCoverSet N (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [nullCoverSet, mem_sep_iff]

/-- The graph of the chosen covers of `N`. -/
def NullCoverGraphRel (c N p : V) : Prop := kpair.π₂ p = c ‘ (nullCoverSet N (kpair.π₁ p))

instance nullCoverGraphRel_definable (c N : V) : ℒₛₑₜ-predicate[V] (NullCoverGraphRel c N) := by
  unfold NullCoverGraphRel
  definability

/-- The level-cover pairs of `E n` at precision `m + n + 2`, indexed by the pair `(n, m)`. -/
def PieceCoverRel (E p q : V) : Prop :=
  ∃ p' : V, NatAddRel p' (succ (kpair.π₂ p)) (kpair.π₁ p) ∧ LevelCoverPair (E ‘ (kpair.π₁ p)) (succ p') q

instance pieceCoverRel_definable (E : V) : ℒₛₑₜ-relation[V] (PieceCoverRel E) := by
  unfold PieceCoverRel
  definability

instance pieceCoverRelFix_definable (E p : V) : ℒₛₑₜ-predicate[V] (PieceCoverRel E p) := by
  definability

noncomputable def pieceCoverSet (E p : V) : V :=
  sep ((ω : V) ×ˢ ((binarySequences V) ^ (ω : V))) (PieceCoverRel E p) (pieceCoverRelFix_definable E p)

instance pieceCoverSet_definable (E : V) : ℒₛₑₜ-function₁[V] (pieceCoverSet E) := by
  have h : ℒₛₑₜ-relation (fun C p : V ↦ ∀ q, q ∈ C ↔
      q ∈ (ω : V) ×ˢ ((binarySequences V) ^ (ω : V)) ∧ PieceCoverRel E p q) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = pieceCoverSet E (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [pieceCoverSet, mem_sep_iff]

theorem mem_pieceCoverSet_iff (E p q : V) : q ∈ pieceCoverSet E p ↔
    q ∈ (ω : V) ×ˢ ((binarySequences V) ^ (ω : V)) ∧ PieceCoverRel E p q :=
  mem_sep_iff

theorem pieceCoverSet_nonempty (hAC : InternalChoice V) {E n m : V} (hT : IsTree (E ‘ n)) (hn : n ∈ (ω : V))
    (hm : m ∈ (ω : V)) : IsNonempty (pieceCoverSet E ⟨n, m⟩ₖ) := by
  have hp : succ (ordinalAdd (succ m) n) ∈ (ω : V) := ω_succ_closed (ordinalAdd_natural (ω_succ_closed hm) hn)
  obtain ⟨M, hM, f, hf, hcov, hsurj⟩ := exists_level_cover hAC hT hp
  refine ⟨⟨M, f⟩ₖ, (mem_pieceCoverSet_iff _ _ _).mpr ⟨kpair_mem_iff.mpr ⟨hM, hf⟩, ?_⟩⟩
  refine ⟨ordinalAdd (succ m) n, ?_, ?_⟩
  · simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact natAddRel_add (ω_succ_closed hm) hn
  · simp only [kpair.π₁_kpair]
    unfold LevelCoverPair
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact ⟨hcov, hsurj⟩

noncomputable def levelAt (c E n m : V) : V := kpair.π₁ (c ‘ (pieceCoverSet E ⟨n, m⟩ₖ))

noncomputable def coverAt (c E n m : V) : V := kpair.π₂ (c ‘ (pieceCoverSet E ⟨n, m⟩ₖ))

theorem levelAt_definable (c E n : V) : ℒₛₑₜ-function₁ (fun j : V ↦ levelAt c E n j) := by
  unfold levelAt
  definability

/-- The properties of the chosen level-cover pair. -/
theorem levelAt_spec {c E n m : V} (hc : c ‘ (pieceCoverSet E ⟨n, m⟩ₖ) ∈ pieceCoverSet E ⟨n, m⟩ₖ)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) :
    levelAt c E n m ∈ (ω : V) ∧ coverAt c E n m ∈ (binarySequences V) ^ (ω : V) ∧
      IsCoverAt (coverAt c E n m) (openFrom (levelSet (E ‘ n) (levelAt c E n m)) \ treeBody (E ‘ n))
        (succ (ordinalAdd (succ m) n)) := by
  obtain ⟨hprod, p', ⟨-, -, hp'⟩, hpair⟩ := (mem_pieceCoverSet_iff _ _ _).mp hc
  obtain ⟨a, ha, b, hb, hab⟩ := mem_prod_iff.mp hprod
  simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hp' hpair
  unfold LevelCoverPair at hpair
  unfold levelAt coverAt
  rw [hab, kpair.π₁_kpair, kpair.π₂_kpair] at hpair ⊢
  rw [hp'] at hpair
  exact ⟨ha, hb, hpair.1⟩

/-- The monotone levels: the maximum of the chosen levels up to `m`. -/
def MonoLevelPred (c E n m M : V) : Prop := ∃ j ∈ succ m, M = levelAt c E n j

instance monoLevelPred_definable (c E : V) : ℒₛₑₜ-relation₃[V] (MonoLevelPred c E) := by
  unfold MonoLevelPred levelAt
  definability

instance monoLevelPredFix_definable (c E n m : V) : ℒₛₑₜ-predicate[V] (MonoLevelPred c E n m) := by
  definability

noncomputable def monoLevel (c E n m : V) : V := ⋃ˢ (sep (ω : V) (MonoLevelPred c E n m) (monoLevelPredFix_definable c E n m))

instance monoLevel_definable (c E : V) : ℒₛₑₜ-function₂[V] (monoLevel c E) := by
  have h : ℒₛₑₜ-relation₃ (fun L n m : V ↦ ∀ x, x ∈ L ↔ ∃ M, (M ∈ (ω : V) ∧ MonoLevelPred c E n m M) ∧ x ∈ M) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = monoLevel c E (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [monoLevel, mem_sUnion_iff, mem_sep_iff]

theorem levelAt_subset_monoLevel {c E n m j : V} (hj : j ∈ succ m) (hlev : levelAt c E n j ∈ (ω : V)) :
    levelAt c E n j ⊆ monoLevel c E n m :=
  subset_sUnion_of_mem (mem_sep_iff.mpr ⟨hlev, j, hj, rfl⟩)

theorem monoLevel_mem_omega {c E n m : V} (hm : m ∈ (ω : V)) (hlev : ∀ j ∈ succ m, levelAt c E n j ∈ (ω : V)) :
    monoLevel c E n m ∈ (ω : V) := by
  unfold monoLevel
  refine sUnion_naturals_mem sep_subset (internallyFinite_subset (internallyFinite_repl (fun j ↦ levelAt c E n j)
    (levelAt_definable c E n) ⟨_, ω_succ_closed hm, CardEQ.refl _⟩) (fun M hM ↦ ?_))
  obtain ⟨-, j, hj, rfl⟩ := mem_sep_iff.mp hM
  exact (repl_spec (levelAt_definable c E n)).mpr ⟨j, hj, rfl⟩

theorem monoLevel_mono {c E n m m' : V} (hm : m ∈ (ω : V)) (hm' : m' ∈ (ω : V)) (hmm' : m ⊆ m') :
    monoLevel c E n m ⊆ monoLevel c E n m' := by
  intro x hx
  obtain ⟨M, hM, hxM⟩ := mem_sUnion_iff.mp hx
  obtain ⟨hMω, j, hj, rfl⟩ := mem_sep_iff.mp hM
  exact mem_sUnion_iff.mpr ⟨_, mem_sep_iff.mpr ⟨hMω, j, succ_subset_succ_of_natural hm hm' hmm' j hj, rfl⟩, hxM⟩

theorem monoLevel_char (c E n m L : V) :
    L = monoLevel c E n m ↔ ∀ x : V, x ∈ L ↔ ∃ M : V, (M ∈ (ω : V) ∧ MonoLevelPred c E n m M) ∧ x ∈ M := by
  rw [mem_ext_iff]
  simp only [monoLevel, mem_sUnion_iff, mem_sep_iff]

/-- The nodes of the monotone levels of all the trees. -/
def LevelsPred (c E m s : V) : Prop :=
  ∃ n ∈ (ω : V), ∃ L : V, (∀ x : V, x ∈ L ↔ ∃ M : V, (M ∈ (ω : V) ∧ MonoLevelPred c E n m M) ∧ x ∈ M) ∧
    s ∈ E ‘ n ∧ s ∈ ((2 : ℕ) : V) ^ L

instance levelsPred_definable (c E : V) : ℒₛₑₜ-relation[V] (LevelsPred c E) := by
  unfold LevelsPred
  definability

instance levelsPredFix_definable (c E m : V) : ℒₛₑₜ-predicate[V] (LevelsPred c E m) := by
  definability

theorem levelsPred_iff (c E m s : V) : LevelsPred c E m s ↔ ∃ n ∈ (ω : V), s ∈ levelSet (E ‘ n) (monoLevel c E n m) := by
  unfold LevelsPred
  constructor
  · rintro ⟨n, hn, L, hL, hsE, hsL⟩
    rw [← monoLevel_char] at hL
    rw [hL] at hsL
    exact ⟨n, hn, (mem_levelSet_iff _ _ _).mpr ⟨hsE, hsL⟩⟩
  · rintro ⟨n, hn, hs⟩
    obtain ⟨hsE, hsL⟩ := (mem_levelSet_iff _ _ _).mp hs
    exact ⟨n, hn, monoLevel c E n m, (monoLevel_char _ _ _ _ _).mp rfl, hsE, hsL⟩

noncomputable def levelsSet (c E m : V) : V := sep (binarySequences V) (LevelsPred c E m) (levelsPredFix_definable c E m)

instance levelsSet_definable (c E : V) : ℒₛₑₜ-function₁[V] (levelsSet c E) := by
  have h : ℒₛₑₜ-relation (fun S m : V ↦ ∀ s, s ∈ S ↔ s ∈ binarySequences V ∧ LevelsPred c E m s) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = levelsSet c E (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [levelsSet, mem_sep_iff]

theorem mem_levelsSet_iff (c E m s : V) :
    s ∈ levelsSet c E m ↔ s ∈ binarySequences V ∧ ∃ n ∈ (ω : V), s ∈ levelSet (E ‘ n) (monoLevel c E n m) := by
  unfold levelsSet
  rw [mem_sep_iff, levelsPred_iff]

theorem mem_openFrom_levelsSet_iff {c E m x : V} (hlev : ∀ n ∈ (ω : V), monoLevel c E n m ∈ (ω : V)) :
    x ∈ openFrom (levelsSet c E m) ↔ x ∈ cantorSpace V ∧ ∃ n ∈ (ω : V), x ∈ openFrom (levelSet (E ‘ n) (monoLevel c E n m)) := by
  rw [mem_openFrom_iff]
  constructor
  · rintro ⟨hxc, s, hs, hxs⟩
    obtain ⟨-, n, hn, hsn⟩ := (mem_levelsSet_iff _ _ _ _).mp hs
    exact ⟨hxc, n, hn, (mem_openFrom_iff _ _).mpr ⟨hxc, s, hsn, hxs⟩⟩
  · rintro ⟨hxc, n, hn, hx⟩
    obtain ⟨-, s, hs, hxs⟩ := (mem_openFrom_iff _ _).mp hx
    exact ⟨hxc, s, (mem_levelsSet_iff _ _ _ _).mpr ⟨levelSet_subset_binarySequences (hlev n hn) s hs, n, hn, hs⟩, hxs⟩

/-- The envelope code at precision `m`. -/
noncomputable def envelopeSet (c E f m : V) : V := levelsSet c E m ∪ multiInter f m

instance envelopeSet_definable (c E f : V) : ℒₛₑₜ-function₁[V] (envelopeSet c E f) := by
  have h : ℒₛₑₜ-relation (fun S m : V ↦ ∀ s, s ∈ S ↔ s ∈ levelsSet c E m ∨ s ∈ multiInter f m) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = envelopeSet c E f (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [envelopeSet, mem_union_iff]

theorem envelopeSet_subset (c E f m : V) : envelopeSet c E f m ⊆ binarySequences V := by
  intro s hs
  rcases mem_union_iff.mp hs with hs | hs
  · exact (mem_sep_iff.mp hs).1
  · exact multiInter_subset f m s hs

def EnvelopeRel (c E f p : V) : Prop := kpair.π₂ p = envelopeSet c E f (kpair.π₁ p)

instance envelopeRel_definable (c E f : V) : ℒₛₑₜ-predicate[V] (EnvelopeRel c E f) := by
  unfold EnvelopeRel
  definability

/-- The union of the bodies of the trees `E n`. -/
def BodiesPred (E x : V) : Prop := ∃ n ∈ (ω : V), x ∈ treeBody (E ‘ n)

instance bodiesPred_definable : ℒₛₑₜ-relation[V] BodiesPred := by
  unfold BodiesPred
  definability

instance bodiesPredFix_definable (E : V) : ℒₛₑₜ-predicate[V] (BodiesPred E) := by
  definability

noncomputable def bodiesUnion (E : V) : V := sep (cantorSpace V) (BodiesPred E) (bodiesPredFix_definable E)

theorem mem_bodiesUnion_iff (E x : V) : x ∈ bodiesUnion E ↔ x ∈ cantorSpace V ∧ ∃ n ∈ (ω : V), x ∈ treeBody (E ‘ n) :=
  mem_sep_iff

/-- The shifted family of covers at precision `m`: the cover of `N` at precision `m + 1`, then the
piece covers. -/
def ShiftCoverRel (g' c E m p : V) : Prop :=
  (kpair.π₁ p = ∅ ∧ kpair.π₂ p = g') ∨ ∃ n ∈ (ω : V), kpair.π₁ p = succ n ∧ kpair.π₂ p = coverAt c E n m

instance shiftCoverRel_definable (g' c E m : V) : ℒₛₑₜ-predicate[V] (ShiftCoverRel g' c E m) := by
  unfold ShiftCoverRel coverAt
  definability

/-- The measurable envelope of a countable family of trees together with a null set. -/
theorem exists_measurable_envelope (hAC : InternalChoice V) {E N : V}
    (hE : E ∈ (℘ (binarySequences V)) ^ (ω : V)) (hEtree : ∀ n ∈ (ω : V), IsTree (E ‘ n))
    (hNc : N ⊆ cantorSpace V) (hN : IsNull N) :
    ∃ g ∈ (℘ (binarySequences V)) ^ (ω : V),
      bodiesUnion E ⊆ gDelta g ∧ N ⊆ gDelta g ∧ IsNull (gDelta g \ bodiesUnion E) := by
  have hEf : IsFunction E := IsFunction.of_mem hE
  -- the chosen covers of `N`
  obtain ⟨𝒩, h𝒩⟩ : ∃ S : V, S = repl (nullCoverSet N) (nullCoverSet_definable N) (ω : V) := ⟨_, rfl⟩
  obtain ⟨c₁, -, hc₁⟩ := hAC 𝒩 (fun X hX ↦ by
    rw [h𝒩] at hX
    obtain ⟨m, hm, rfl⟩ := (repl_spec (nullCoverSet_definable N)).mp hX
    obtain ⟨f', hf', hcov, hsmall⟩ := hN m hm
    exact ⟨f', mem_sep_iff.mpr ⟨hf', hcov, hsmall⟩⟩)
  have hc₁spec : ∀ m ∈ (ω : V), c₁ ‘ (nullCoverSet N m) ∈ (binarySequences V) ^ (ω : V) ∧
      IsCoverAt (c₁ ‘ (nullCoverSet N m)) N m := by
    intro m hm
    have := hc₁ _ (by rw [h𝒩]; exact (repl_spec (nullCoverSet_definable N)).mpr ⟨m, hm, rfl⟩)
    exact mem_sep_iff.mp this
  obtain ⟨f, hfdef⟩ : ∃ f : V, f = sep ((ω : V) ×ˢ ((binarySequences V) ^ (ω : V))) (NullCoverGraphRel c₁ N)
    (nullCoverGraphRel_definable c₁ N) := ⟨_, rfl⟩
  have hfmem : ∀ m y, ⟨m, y⟩ₖ ∈ f ↔ m ∈ (ω : V) ∧ y ∈ (binarySequences V) ^ (ω : V) ∧ y = c₁ ‘ (nullCoverSet N m) := by
    intro m y
    rw [hfdef, mem_sep_iff, kpair_mem_iff, and_assoc]
    unfold NullCoverGraphRel
    rw [kpair.π₁_kpair, kpair.π₂_kpair]
  have hf : f ∈ ((binarySequences V) ^ (ω : V)) ^ (ω : V) := by
    rw [mem_function_iff]
    refine ⟨fun p hp ↦ by rw [hfdef] at hp; exact (mem_sep_iff.mp hp).1, fun m hm ↦ ?_⟩
    exact ⟨_, (hfmem _ _).mpr ⟨hm, (hc₁spec m hm).1, rfl⟩, fun y hy ↦ ((hfmem _ _).mp hy).2.2⟩
  have hff : IsFunction f := IsFunction.of_mem hf
  have hfval : ∀ m ∈ (ω : V), f ‘ m = c₁ ‘ (nullCoverSet N m) := fun m hm ↦
    value_eq_of_kpair_mem ((hfmem _ _).mpr ⟨hm, (hc₁spec m hm).1, rfl⟩)
  have hfcov : ∀ m ∈ (ω : V), IsCoverAt (f ‘ m) N m := fun m hm ↦ by rw [hfval m hm]; exact (hc₁spec m hm).2
  -- the chosen level-cover pairs
  obtain ⟨Pfam, hPfam⟩ : ∃ S : V, S = repl (pieceCoverSet E) (pieceCoverSet_definable E) ((ω : V) ×ˢ (ω : V)) := ⟨_, rfl⟩
  obtain ⟨c₂, -, hc₂⟩ := hAC Pfam (fun X hX ↦ by
    rw [hPfam] at hX
    obtain ⟨p, hp, rfl⟩ := (repl_spec (pieceCoverSet_definable E)).mp hX
    obtain ⟨n, hn, m, hm, rfl⟩ := mem_prod_iff.mp hp
    exact pieceCoverSet_nonempty hAC (hEtree n hn) hn hm)
  have hc₂spec : ∀ n ∈ (ω : V), ∀ m ∈ (ω : V), c₂ ‘ (pieceCoverSet E ⟨n, m⟩ₖ) ∈ pieceCoverSet E ⟨n, m⟩ₖ :=
    fun n hn m hm ↦ hc₂ _ (by
      rw [hPfam]; exact (repl_spec (pieceCoverSet_definable E)).mpr ⟨_, kpair_mem_iff.mpr ⟨hn, hm⟩, rfl⟩)
  have hlev : ∀ n ∈ (ω : V), ∀ m ∈ (ω : V), levelAt c₂ E n m ∈ (ω : V) := fun n hn m hm ↦
    (levelAt_spec (hc₂spec n hn m hm) hn hm).1
  have hcovmem : ∀ n ∈ (ω : V), ∀ m ∈ (ω : V), coverAt c₂ E n m ∈ (binarySequences V) ^ (ω : V) := fun n hn m hm ↦
    (levelAt_spec (hc₂spec n hn m hm) hn hm).2.1
  have hcovat : ∀ n ∈ (ω : V), ∀ m ∈ (ω : V), IsCoverAt (coverAt c₂ E n m)
      (openFrom (levelSet (E ‘ n) (levelAt c₂ E n m)) \ treeBody (E ‘ n)) (succ (ordinalAdd (succ m) n)) :=
    fun n hn m hm ↦ (levelAt_spec (hc₂spec n hn m hm) hn hm).2.2
  have hmono : ∀ n ∈ (ω : V), ∀ m ∈ (ω : V), monoLevel c₂ E n m ∈ (ω : V) := fun n hn m hm ↦
    monoLevel_mem_omega hm (fun j hj ↦ hlev n hn j (IsTransitive.ω.transitive _ (ω_succ_closed hm) j hj))
  -- the code
  obtain ⟨g, hgdef⟩ : ∃ g : V, g = sep ((ω : V) ×ˢ ℘ (binarySequences V)) (EnvelopeRel c₂ E f)
    (envelopeRel_definable c₂ E f) := ⟨_, rfl⟩
  have hgmem : ∀ m y, ⟨m, y⟩ₖ ∈ g ↔ m ∈ (ω : V) ∧ y ⊆ binarySequences V ∧ y = envelopeSet c₂ E f m := by
    intro m y
    rw [hgdef, mem_sep_iff, kpair_mem_iff, mem_power_iff, and_assoc]
    unfold EnvelopeRel
    rw [kpair.π₁_kpair, kpair.π₂_kpair]
  have hg : g ∈ (℘ (binarySequences V)) ^ (ω : V) := by
    rw [mem_function_iff]
    refine ⟨fun p hp ↦ by rw [hgdef] at hp; exact (mem_sep_iff.mp hp).1, fun m hm ↦ ?_⟩
    exact ⟨_, (hgmem _ _).mpr ⟨hm, envelopeSet_subset c₂ E f m, rfl⟩, fun y hy ↦ ((hgmem _ _).mp hy).2.2⟩
  have hgf : IsFunction g := IsFunction.of_mem hg
  have hgval : ∀ m ∈ (ω : V), g ‘ m = envelopeSet c₂ E f m := fun m hm ↦
    value_eq_of_kpair_mem ((hgmem _ _).mpr ⟨hm, envelopeSet_subset c₂ E f m, rfl⟩)
  have hopen : ∀ m ∈ (ω : V), ∀ x, x ∈ openFrom (g ‘ m) ↔
      x ∈ openFrom (levelsSet c₂ E m) ∨ x ∈ openFrom (multiInter f m) := by
    intro m hm x
    rw [hgval m hm]
    exact mem_openFrom_union_iff _ _ _
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxc, n, hn, hxn⟩ := (mem_bodiesUnion_iff _ _).mp hx
    refine (mem_gDelta_iff _ _).mpr ⟨hxc, fun m hm ↦ (hopen m hm x).mpr (Or.inl ?_)⟩
    exact (mem_openFrom_levelsSet_iff (fun n' hn' ↦ hmono n' hn' m hm)).mpr
      ⟨hxc, n, hn, treeBody_subset_openFrom_levelSet (hmono n hn m hm) x hxn⟩
  · intro x hx
    refine (mem_gDelta_iff _ _).mpr ⟨hNc x hx, fun m hm ↦ (hopen m hm x).mpr (Or.inr ?_)⟩
    refine mem_openFrom_multiInter hAC hf hm (hNc x hx) (fun j hj ↦ ?_)
    have hjω : j ∈ (ω : V) := IsTransitive.ω.transitive _ (ω_succ_closed hm) j hj
    obtain ⟨i, hi, hxi⟩ := (hfcov j hjω).1 x hx
    have : IsFunction (f ‘ j) := IsFunction.of_mem (function_value_mem hf hjω)
    exact ⟨(f ‘ j) ‘ i, mem_range_iff.mpr ⟨i, kpair_value_mem (by
      rw [domain_eq_of_mem_function (function_value_mem hf hjω)]; exact hi)⟩, hxi⟩
  · intro m hm
    have : IsOrdinal m := IsOrdinal.nat hm
    have hsm : succ m ∈ (ω : V) := ω_succ_closed hm
    -- the shifted family: the cover of `N` at precision `m + 1`, then the piece covers
    obtain ⟨cov, hcovdef⟩ : ∃ cov : V, cov = sep ((ω : V) ×ˢ ((binarySequences V) ^ (ω : V)))
      (ShiftCoverRel (f ‘ (succ m)) c₂ E m) (shiftCoverRel_definable _ c₂ E m) := ⟨_, rfl⟩
    have hcovmem' : ∀ k y, ⟨k, y⟩ₖ ∈ cov ↔ k ∈ (ω : V) ∧ y ∈ (binarySequences V) ^ (ω : V) ∧
        ShiftCoverRel (f ‘ (succ m)) c₂ E m ⟨k, y⟩ₖ := by
      intro k y
      rw [hcovdef, mem_sep_iff, kpair_mem_iff, and_assoc]
    have hrel0 : ShiftCoverRel (f ‘ (succ m)) c₂ E m ⟨∅, f ‘ (succ m)⟩ₖ :=
      Or.inl ⟨by rw [kpair.π₁_kpair], by rw [kpair.π₂_kpair]⟩
    have hrelsucc : ∀ n ∈ (ω : V), ShiftCoverRel (f ‘ (succ m)) c₂ E m ⟨succ n, coverAt c₂ E n m⟩ₖ :=
      fun n hn ↦ Or.inr ⟨n, hn, by rw [kpair.π₁_kpair], by rw [kpair.π₂_kpair]⟩
    have huniq : ∀ k y y', ShiftCoverRel (f ‘ (succ m)) c₂ E m ⟨k, y⟩ₖ →
        ShiftCoverRel (f ‘ (succ m)) c₂ E m ⟨k, y'⟩ₖ → y = y' := by
      intro k y y' h1 h2
      rcases h1 with ⟨hk, hy⟩ | ⟨n, hn, hk, hy⟩ <;> rcases h2 with ⟨hk', hy'⟩ | ⟨n', hn', hk', hy'⟩
      · rw [kpair.π₂_kpair] at hy hy'
        rw [hy, hy']
      · rw [kpair.π₁_kpair] at hk hk'
        exact absurd (hk'.symm.trans hk) (fun h ↦ not_mem_empty (h ▸ mem_succ_self n'))
      · rw [kpair.π₁_kpair] at hk hk'
        exact absurd (hk.symm.trans hk') (fun h ↦ not_mem_empty (h ▸ mem_succ_self n))
      · rw [kpair.π₁_kpair] at hk hk'
        rw [kpair.π₂_kpair] at hy hy'
        have := natural_succ_injective hn hn' (hk.symm.trans hk')
        rw [hy, hy', this]
    have hfsm : f ‘ (succ m) ∈ (binarySequences V) ^ (ω : V) := function_value_mem hf hsm
    have hcov : cov ∈ ((binarySequences V) ^ (ω : V)) ^ (ω : V) := by
      rw [mem_function_iff]
      refine ⟨fun p hp ↦ by rw [hcovdef] at hp; exact (mem_sep_iff.mp hp).1, fun k hk ↦ ?_⟩
      rcases internalNatural_cases hk with rfl | ⟨n, hn, rfl⟩
      · exact ⟨_, (hcovmem' _ _).mpr ⟨hk, hfsm, hrel0⟩, fun y hy ↦ huniq _ _ _ ((hcovmem' _ _).mp hy).2.2 hrel0⟩
      · exact ⟨_, (hcovmem' _ _).mpr ⟨hk, hcovmem n hn m hm, hrelsucc n hn⟩,
          fun y hy ↦ huniq _ _ _ ((hcovmem' _ _).mp hy).2.2 (hrelsucc n hn)⟩
    have hcovf : IsFunction cov := IsFunction.of_mem hcov
    have hcov0 : cov ‘ (∅ : V) = f ‘ (succ m) := value_eq_of_kpair_mem ((hcovmem' _ _).mpr ⟨zero_mem_ω, hfsm, hrel0⟩)
    have hcovsucc : ∀ n ∈ (ω : V), cov ‘ (succ n) = coverAt c₂ E n m := fun n hn ↦
      value_eq_of_kpair_mem ((hcovmem' _ _).mpr ⟨ω_succ_closed hn, hcovmem n hn m hm, hrelsucc n hn⟩)
    obtain ⟨h, hh, hhsmall, hhval⟩ := exists_combined_cover hm hcov (by
      intro n hn k hk
      rcases internalNatural_cases hn with rfl | ⟨n', hn', rfl⟩
      · change SmallMeasure ((cov ‘ (∅ : V)) “ k) (succ (ordinalAdd m (∅ : V)))
        rw [hcov0, ordinalAdd_zero]
        exact (hfcov (succ m) hsm).2 k hk
      · have : IsOrdinal n' := IsOrdinal.nat hn'
        rw [hcovsucc n' hn', ordinalAdd_succ, ← ordinalAdd_succ_left_natural hm hn']
        exact (hcovat n' hn' m hm).2 k hk)
    refine ⟨h, hh, fun x hx ↦ ?_, hhsmall⟩
    obtain ⟨hxg, hxF⟩ := mem_sdiff_iff.mp hx
    obtain ⟨hxc, hxall⟩ := (mem_gDelta_iff _ _).mp hxg
    by_cases hU : x ∈ openFrom (levelsSet c₂ E m)
    · obtain ⟨-, n, hn, hxn⟩ := (mem_openFrom_levelsSet_iff (fun n' hn' ↦ hmono n' hn' m hm)).mp hU
      have hxn' : x ∈ openFrom (levelSet (E ‘ n) (levelAt c₂ E n m)) :=
        openFrom_levelSet_antitone (hEtree n hn) (hlev n hn m hm) (hmono n hn m hm)
          (levelAt_subset_monoLevel (mem_succ_self m) (hlev n hn m hm)) x hxn
      have hxnot : x ∉ treeBody (E ‘ n) := fun h' ↦ hxF ((mem_bodiesUnion_iff _ _).mpr ⟨hxc, n, hn, h'⟩)
      obtain ⟨i, hi, hxi⟩ := (hcovat n hn m hm).1 x (mem_sdiff_iff.mpr ⟨hxn', hxnot⟩)
      obtain ⟨k, hk, hhk⟩ := hhval (succ n) (ω_succ_closed hn) i hi
      refine ⟨k, hk, ?_⟩
      rw [hhk, hcovsucc n hn]
      exact hxi
    · have hW : x ∈ openFrom (multiInter f (succ m)) := by
        rcases (hopen (succ m) hsm x).mp (hxall (succ m) hsm) with hU' | hW'
        · exfalso
          apply hU
          obtain ⟨-, n, hn, hxn⟩ := (mem_openFrom_levelsSet_iff (fun n' hn' ↦ hmono n' hn' (succ m) hsm)).mp hU'
          exact (mem_openFrom_levelsSet_iff (fun n' hn' ↦ hmono n' hn' m hm)).mpr ⟨hxc, n, hn,
            openFrom_levelSet_antitone (hEtree n hn) (hmono n hn m hm) (hmono n hn (succ m) hsm)
              (monoLevel_mono hm hsm (fun z hz ↦ mem_succ_iff.mpr (Or.inr hz))) x hxn⟩
        · exact hW'
      have hW' : x ∈ openFrom (range (f ‘ (succ m))) :=
        openFrom_multiInter_subset hf hsm (mem_succ_self _) x hW
      obtain ⟨-, s, hs, hxs⟩ := (mem_openFrom_iff _ _).mp hW'
      obtain ⟨i, hi⟩ := mem_range_iff.mp hs
      have hfm : IsFunction (f ‘ (succ m)) := IsFunction.of_mem hfsm
      have hiω : i ∈ (ω : V) := by
        rw [← domain_eq_of_mem_function hfsm]
        exact mem_domain_of_kpair_mem hi
      obtain ⟨k, hk, hhk⟩ := hhval ∅ zero_mem_ω i hiω
      refine ⟨k, hk, ?_⟩
      rw [hhk, hcov0, value_eq_of_kpair_mem hi]
      exact hxs

end ZFVP
