import ZFVP.SetTheory.BaireRunInverse

/-! Both directions of the run bijection preserve the internal prefix topology. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem baire_subset_iff_restrict_eq {a s : V} (ha : a ∈ baireSpace V)
    (hs : s ∈ naturalSequences V) : s ⊆ a ↔ a ↾ (domain s) = s := by
  obtain ⟨_, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp hs
  constructor
  · intro h
    exact (sequence_eq_restrict_of_subset ha hsf h).symm
  · intro h
    rw [← h]
    exact restrict_subset _ _

theorem baireFiniteRunCode_restrict_real {a n : V} (ha : a ∈ baireSpace V) (hn : n ∈ (ω : V)) :
    baireFiniteRunCode (a ↾ n) = baireRunPrefix a n := by
  have : IsFunction a := IsFunction.of_mem ha
  unfold baireFiniteRunCode
  rw [domain_eq_of_mem_function (function_restrict_mem ha (IsTransitive.transitive _ hn))]
  exact baireRunPrefix_restrict hn (by rw [domain_eq_of_mem_function ha]; exact IsTransitive.transitive _ hn)

theorem baireFiniteRunCode_subset_code {s a : V} (hs : s ∈ naturalSequences V)
    (ha : a ∈ baireSpace V) (hsa : s ⊆ a) : baireFiniteRunCode s ⊆ baireRunCode a := by
  have hn := ((mem_finiteSequences_iff_domain _ s).mp hs).1
  have he := (baire_subset_iff_restrict_eq ha hs).mp hsa
  calc
    baireFiniteRunCode s = baireFiniteRunCode (a ↾ (domain s)) := congrArg baireFiniteRunCode he.symm
    _ = baireRunPrefix a (domain s) := baireFiniteRunCode_restrict_real ha hn
    _ ⊆ baireRunCode a := baireRunPrefix_subset_code a hn

theorem binarySequence_subset_runPrefix {a s n : V} (ha : a ∈ baireSpace V)
    (hs : s ∈ binarySequences V) (hsa : s ⊆ baireRunCode a)
    (hn : n ∈ (ω : V)) (hle : domain s ⊆ n) : s ⊆ baireRunPrefix a n := by
  obtain ⟨_, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp hs
  obtain ⟨_, hpf⟩ := (mem_finiteSequences_iff_domain _ _).mp (baireRunPrefix_real_mem ha hn)
  exact sequence_subset_of_subset_of_domain_subset (baireRunCode_mem ha) hsf hpf hsa
    (baireRunPrefix_subset_code a hn)
    (subset_trans hle (baireRunPrefix_length_bound ha hn (IsTransitive.transitive _ hn)))

theorem baireFiniteRunCode_reflects_subset {s a : V} (hs : s ∈ naturalSequences V)
    (ha : a ∈ baireSpace V) (hsa : baireFiniteRunCode s ⊆ baireRunCode a) : s ⊆ a := by
  obtain ⟨hm, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp hs
  have : IsOrdinal (domain s) := IsOrdinal.of_mem hm
  have : IsFunction s := IsFunction.of_mem hsf
  have : IsFunction a := IsFunction.of_mem ha
  have : IsFunction (baireRunCode a) := baireRunCode_isFunction ha
  have hagree : ∀ n ∈ (ω : V), n ⊆ domain s → ∀ i ∈ n, s ‘ i = a ‘ i := by
    apply naturalNumber_induction (fun n ↦ n ⊆ domain s → ∀ i ∈ n, s ‘ i = a ‘ i) (by definability)
    · intro _ i hi
      exact (not_mem_empty hi).elim
    · intro n hn ih hnm
      have hn' := ω_succ_closed hn
      have hnsub := subset_trans (mem_subset_refl n) hnm
      have hps := baireRunPrefix_mem hsf hn' hnm
      have hpa := baireRunPrefix_real_mem ha hn'
      have : IsFunction (baireRunPrefix s (succ n)) := binarySequence_isFunction hps
      have : IsFunction (baireRunPrefix a (succ n)) := binarySequence_isFunction hpa
      have hsubs : baireRunPrefix s (succ n) ⊆ baireRunCode a :=
        subset_trans (baireRunPrefix_mono hsf hn' hm hnm (subset_refl _)) hsa
      have hsuba := baireRunPrefix_subset_code a hn'
      have hnas := not_incompatible_of_subset_subset hsuba hsubs
      have hnsa := not_incompatible_of_subset_subset hsubs hsuba
      have heprefix := baireRunPrefix_agree hn (ih hnsub)
      rw [baireRunPrefix_succ s hn, baireRunPrefix_succ a hn, heprefix] at hnas hnsa
      have hsn := function_value_mem hsf (hnm n (mem_succ_self n))
      have han := function_value_mem ha hn
      have : IsOrdinal (s ‘ n) := IsOrdinal.of_mem hsn
      have : IsOrdinal (a ‘ n) := IsOrdinal.of_mem han
      have hv : s ‘ n = a ‘ n := by
        rcases IsOrdinal.mem_trichotomy (s ‘ n) (a ‘ n) with hlt | heq | hgt
        · exact (hnsa (binaryAppendRun_disagree (baireRunPrefix_real_mem ha hn) hsn han hlt)).elim
        · exact heq
        · exact (hnas (binaryAppendRun_disagree (baireRunPrefix_real_mem ha hn) han hsn hgt)).elim
      intro i hi
      rcases mem_succ_iff.mp hi with rfl | hi
      · exact hv
      · exact ih hnsub i hi
  apply (baire_subset_iff_restrict_eq ha hs).mpr
  have hr := function_restrict_mem ha (IsTransitive.transitive _ hm)
  have : IsFunction (a ↾ (domain s)) := IsFunction.of_mem hr
  apply functions_eq_of_domain_values (domain_eq_of_mem_function hr)
  intro i hi
  rw [domain_eq_of_mem_function hr] at hi
  rw [value_restrict (by rw [domain_eq_of_mem_function ha]; exact IsTransitive.ω.transitive _ hm _ hi) hi]
  exact (hagree (domain s) hm (subset_refl _) i hi).symm

theorem baireFiniteRunCode_subset_code_iff {s a : V} (hs : s ∈ naturalSequences V)
    (ha : a ∈ baireSpace V) : baireFiniteRunCode s ⊆ baireRunCode a ↔ s ⊆ a :=
  ⟨baireFiniteRunCode_reflects_subset hs ha, baireFiniteRunCode_subset_code hs ha⟩

noncomputable def baireRunPreimageBasis (S : V) : V :=
  {t ∈ naturalSequences V ; ∃ s ∈ S, s ⊆ baireFiniteRunCode t}

theorem mem_baireRunPreimageBasis_iff (S t : V) :
    t ∈ baireRunPreimageBasis S ↔ t ∈ naturalSequences V ∧ ∃ s ∈ S, s ⊆ baireFiniteRunCode t := by
  simp [baireRunPreimageBasis]

instance baireRunPreimageBasis_definable : ℒₛₑₜ-function₁[V] baireRunPreimageBasis := by
  have h : ℒₛₑₜ-relation (fun B S : V ↦
      ∀ t, t ∈ B ↔ t ∈ naturalSequences V ∧ ∃ s ∈ S, s ⊆ baireFiniteRunCode t) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [mem_baireRunPreimageBasis_iff]

theorem baireRunPreimageBasis_subset (S : V) : baireRunPreimageBasis S ⊆ naturalSequences V :=
  fun t ht ↦ ((mem_baireRunPreimageBasis_iff S t).mp ht).1

theorem baireRunCode_mem_open_iff {a S : V} (ha : a ∈ baireSpace V) (hS : S ⊆ binarySequences V) :
    baireRunCode a ∈ openFrom S ↔ a ∈ baireOpenFrom (baireRunPreimageBasis S) := by
  constructor
  · intro h
    obtain ⟨_, s, hs, he⟩ := (mem_openFrom_iff S _).mp h
    have hsb := hS s hs
    have hn := binarySequence_domain_mem hsb
    have hsa := (subset_iff_restrict_eq (baireRunCode_mem ha) hsb).mpr he
    let t := a ↾ (domain s)
    have ht := restrict_mem_naturalSequences ha hn
    have hst : s ⊆ baireFiniteRunCode t := by
      rw [baireFiniteRunCode_restrict_real ha hn]
      exact binarySequence_subset_runPrefix ha hsb hsa hn (subset_refl _)
    refine (mem_baireOpenFrom_iff _ _).mpr ⟨ha, t,
      (mem_baireRunPreimageBasis_iff S t).mpr ⟨ht, s, hs, hst⟩, ?_⟩
    exact (baire_subset_iff_restrict_eq ha ht).mp (restrict_subset _ _)
  · intro h
    obtain ⟨_, t, ht, he⟩ := (mem_baireOpenFrom_iff _ _).mp h
    obtain ⟨htn, s, hs, hst⟩ := (mem_baireRunPreimageBasis_iff S t).mp ht
    have hta := (baire_subset_iff_restrict_eq ha htn).mpr he
    have hsa := subset_trans hst (baireFiniteRunCode_subset_code htn ha hta)
    exact (mem_openFrom_iff _ _).mpr ⟨baireRunCode_mem ha, s, hs,
      (subset_iff_restrict_eq (baireRunCode_mem ha) (hS s hs)).mp hsa⟩

noncomputable def baireRunImageBasis (S : V) : V :=
  repl baireFiniteRunCode (by definability) S

theorem mem_baireRunImageBasis_iff (S t : V) :
    t ∈ baireRunImageBasis S ↔ ∃ s ∈ S, t = baireFiniteRunCode s := repl_spec (by definability)

instance baireRunImageBasis_definable : ℒₛₑₜ-function₁[V] baireRunImageBasis := by
  have h : ℒₛₑₜ-relation (fun B S : V ↦ ∀ t, t ∈ B ↔ ∃ s ∈ S, t = baireFiniteRunCode s) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [mem_baireRunImageBasis_iff]

theorem baireRunImageBasis_subset {S : V} (hS : S ⊆ naturalSequences V) :
    baireRunImageBasis S ⊆ binarySequences V := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := (mem_baireRunImageBasis_iff S t).mp ht
  exact baireFiniteRunCode_mem (hS s hs)

theorem baireRunCode_mem_imageOpen_iff {a S : V} (ha : a ∈ baireSpace V)
    (hS : S ⊆ naturalSequences V) :
    baireRunCode a ∈ openFrom (baireRunImageBasis S) ↔ a ∈ baireOpenFrom S := by
  constructor
  · intro h
    obtain ⟨_, t, ht, he⟩ := (mem_openFrom_iff _ _).mp h
    obtain ⟨s, hs, rfl⟩ := (mem_baireRunImageBasis_iff S t).mp ht
    have hsn := hS s hs
    have hsub := (subset_iff_restrict_eq (baireRunCode_mem ha) (baireFiniteRunCode_mem hsn)).mpr he
    exact (mem_baireOpenFrom_iff _ _).mpr ⟨ha, s, hs,
      (baire_subset_iff_restrict_eq ha hsn).mp (baireFiniteRunCode_reflects_subset hsn ha hsub)⟩
  · intro h
    obtain ⟨_, s, hs, he⟩ := (mem_baireOpenFrom_iff _ _).mp h
    have hsn := hS s hs
    have hsub := baireFiniteRunCode_subset_code hsn ha ((baire_subset_iff_restrict_eq ha hsn).mpr he)
    exact (mem_openFrom_iff _ _).mpr ⟨baireRunCode_mem ha, baireFiniteRunCode s,
      (mem_baireRunImageBasis_iff S _).mpr ⟨s, hs, rfl⟩,
      (subset_iff_restrict_eq (baireRunCode_mem ha) (baireFiniteRunCode_mem hsn)).mp hsub⟩

end ZFVP
