import ZFVP.SetTheory.SplittingScheme
import ZFVP.ModelTheory.GroundForcingGeneric
import ZFVP.SetTheory.Hessenberg

/-! The perfect-set core of Solovay's argument, inside one model: the tree of initial segments of
the `τ`-values along a binary splitting scheme is perfect, and every real in its body is the union
of the `τ`-values along a filter that contains the root and meets every dense set of the scheme.
Hence a set of reals containing all such unions contains the body of a perfect tree. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sequence_subset_of_subset_of_domain_subset {A s t u k n m : V} (hs : s ∈ A ^ k)
    (ht : t ∈ A ^ n) (hu : u ∈ A ^ m) (hts : t ⊆ s) (hus : u ⊆ s) (hnm : n ⊆ m) : t ⊆ u := by
  rw [sequence_eq_restrict_of_subset hs ht hts, sequence_eq_restrict_of_subset hs hu hus,
    ← restrict_restrict_of_subset hnm]
  exact restrict_subset _ _

theorem sequence_eq_of_subset_of_domain_eq {A t u n : V} (ht : t ∈ A ^ n) (hu : u ∈ A ^ n)
    (h : t ⊆ u) : t = u := by
  have : IsFunction u := IsFunction.of_mem hu
  rw [sequence_eq_restrict_of_subset hu ht h]
  exact IsFunction.restrict_eq_self u n (fun y hy ↦ by rwa [domain_eq_of_mem_function hu] at hy)

theorem sequence_eq_of_subset_subset_of_domain_eq {A s t u k n : V} (hs : s ∈ A ^ k) (ht : t ∈ A ^ n)
    (hu : u ∈ A ^ n) (hts : t ⊆ s) (hus : u ⊆ s) : t = u := by
  rw [sequence_eq_restrict_of_subset hs ht hts, sequence_eq_restrict_of_subset hs hu hus]

theorem subset_restrict_of_domain_subset {t x N : V} [IsFunction t] (h : t ⊆ x)
    (hd : domain t ⊆ N) : t ⊆ x ↾ N := by
  intro p hp
  obtain ⟨X, Y, ht⟩ := (inferInstance : IsFunction t).mem_func
  obtain ⟨i, _, v, _, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function ht p hp)
  exact kpair_mem_restrict_iff.mpr ⟨h _ hp, hd i (mem_domain_of_kpair_mem hp)⟩

theorem not_incompatible_of_subset_subset {t u x : V} [IsFunction t] [IsFunction u] [IsFunction x]
    (ht : t ⊆ x) (hu : u ⊆ x) : ¬Incompatible t u := by
  rintro ⟨i, hit, hiu, hne⟩
  exact hne ((value_eq_of_subset_function ht hit).symm.trans (value_eq_of_subset_function hu hiu))

theorem succ_subset_of_mem_nat {n k : V} (hk : k ∈ (ω : V)) (hnk : n ∈ k) : succ n ⊆ k := by
  intro y hy
  rcases mem_succ_iff.mp hy with rfl | hy
  · exact hnk
  · exact (IsTransitive.nat hk).transitive n hnk y hy

/-- A proper initial segment extends by one step inside the longer sequence. -/
theorem exists_append_subset_of_ssubset {A s ρ n k : V} (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V))
    (hs : s ∈ A ^ n) (hρ : ρ ∈ A ^ k) (hsub : s ⊆ ρ) (hne : s ≠ ρ) :
    ∃ a ∈ A, insert ⟨n, a⟩ₖ s ⊆ ρ := by
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have : IsOrdinal k := IsOrdinal.of_mem hk
  have : IsFunction ρ := IsFunction.of_mem hρ
  have hnk : n ⊆ k := sequence_domain_subset_of_subset hρ hs hsub
  have hnk' : n ∈ k := by
    rcases IsOrdinal.subset_iff.mp hnk with h | h
    · exfalso
      apply hne
      rw [sequence_eq_restrict_of_subset hρ hs hsub, h]
      exact IsFunction.restrict_eq_self ρ k (fun y hy ↦ by rwa [domain_eq_of_mem_function hρ] at hy)
    · exact h
  have hr : ρ ↾ (succ n) ∈ A ^ succ n := function_restrict_mem hρ (succ_subset_of_mem_nat hk hnk')
  obtain ⟨t, a, ht, ha, he⟩ := function_succ_decompose hr
  refine ⟨a, ha, ?_⟩
  have htρ : t ⊆ ρ := by
    intro p hp
    have : p ∈ ρ ↾ (succ n) := by
      rw [he]
      exact mem_insert.mpr (Or.inr hp)
    exact restrict_subset ρ (succ n) p this
  have hts : t = s := sequence_eq_of_subset_subset_of_domain_eq hρ ht hs htρ hsub
  rw [hts] at he
  rw [← he]
  exact restrict_subset ρ (succ n)

theorem restrict_mem_binarySequences_of_mem_domain {t n : V} (ht : t ∈ binarySequences V)
    (hn : n ∈ domain t) : t ↾ n ∈ binarySequences V := by
  obtain ⟨m, hm, htm⟩ := (mem_binarySequences_iff t).mp ht
  rw [domain_eq_of_mem_function htm] at hn
  exact (mem_binarySequences_iff _).mpr
    ⟨n, IsTransitive.ω.transitive m hm n hn, function_restrict_mem htm ((IsTransitive.nat hm).transitive n hn)⟩

theorem mem_image_iff' (τ F y : V) : y ∈ image τ F ↔ ∃ p ∈ F, ⟨p, y⟩ₖ ∈ τ := by
  unfold image
  rw [mem_range_iff]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨h1, h2⟩ := kpair_mem_restrict_iff.mp hp
    exact ⟨p, h2, h1⟩
  · rintro ⟨p, hp, hpy⟩
    exact ⟨p, kpair_mem_restrict_iff.mpr ⟨hpy, hp⟩⟩

theorem branchFilter_definable (R τ S x : V) :
    ℒₛₑₜ-predicate (fun p : V ↦ ∃ s ∈ binarySequences V, τ ‘ (S ‘ s) ⊆ x ∧ ⟨S ‘ s, p⟩ₖ ∈ R) := by
  definability

theorem levelPredicate_definable (τ S x : V) :
    ℒₛₑₜ-predicate (fun n : V ↦ ∃ s ∈ ((2 : ℕ) : V) ^ n, τ ‘ (S ‘ s) ⊆ x ∧ n ⊆ domain (τ ‘ (S ‘ s))) := by
  definability

section

variable {P R D τ p₀ Φ : V} (hR : IsForcingPreorder P R) (hτ : τ ∈ (binarySequences V) ^ P)
  (hmono : ∀ p ∈ P, ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → τ ‘ p ⊆ τ ‘ q)
  (hD : D ∈ (℘ P) ^ (ω : V)) (hp₀ : p₀ ∈ P)
  (hΦ : ∀ n ∈ (ω : V), ∀ p ∈ P, Φ ‘ ⟨n, p⟩ₖ ∈ splitFamily P R D τ ⟨n, p⟩ₖ)

/-- The tree of initial segments of the `τ`-values along the scheme. -/
noncomputable def schemeTree (τ p₀ Φ : V) : V :=
  {t ∈ binarySequences V ; ∃ s ∈ binarySequences V, t ⊆ τ ‘ ((scheme p₀ Φ) ‘ s)}

theorem mem_schemeTree_iff (τ p₀ Φ t : V) :
    t ∈ schemeTree τ p₀ Φ ↔ t ∈ binarySequences V ∧ ∃ s ∈ binarySequences V, t ⊆ τ ‘ ((scheme p₀ Φ) ‘ s) := by
  simp [schemeTree]

include hR hτ hmono hp₀ hΦ in
/-- A child's `τ`-value differs from its parent's. -/
theorem scheme_child_ne {s n a : V} (hn : n ∈ (ω : V)) (hs : s ∈ ((2 : ℕ) : V) ^ n)
    (ha : a ∈ ((2 : ℕ) : V)) :
    τ ‘ ((scheme p₀ Φ) ‘ (insert ⟨n, a⟩ₖ s)) ≠ τ ‘ ((scheme p₀ Φ) ‘ s) := by
  intro heq
  have hsB : s ∈ binarySequences V := (mem_binarySequences_iff _).mpr ⟨n, hn, hs⟩
  have hs0B := append_mem_binarySequences hn hs empty_mem_two
  have hs1B := append_mem_binarySequences hn hs succ_empty_mem_two
  have h0 := tau_isFunction hτ (scheme_mem hp₀ hΦ _ hs0B)
  have h1 := tau_isFunction hτ (scheme_mem hp₀ hΦ _ hs1B)
  have hinc := scheme_children_incompatible hp₀ hΦ hn hs
  rcases (mem_two_iff a).mp ha with rfl | rfl
  · apply not_incompatible_of_subset _ hinc
    rw [heq]
    exact scheme_tau_mono hR hτ hmono hp₀ hΦ hs1B hsB (subset_insert _ _)
  · apply not_incompatible_of_subset _ (incompatible_symm hinc)
    rw [heq]
    exact scheme_tau_mono hR hτ hmono hp₀ hΦ hs0B hsB (subset_insert _ _)

include hR hτ hmono hp₀ hΦ in
theorem schemeTree_perfect : IsPerfectTree (schemeTree τ p₀ Φ) := by
  refine ⟨⟨fun t ht ↦ ((mem_schemeTree_iff _ _ _ _).mp ht).1, ?_⟩, ?_, ?_⟩
  · intro t ht n hn
    obtain ⟨htB, s, hs, hts⟩ := (mem_schemeTree_iff _ _ _ _).mp ht
    exact (mem_schemeTree_iff _ _ _ _).mpr ⟨restrict_mem_binarySequences_of_mem_domain htB hn, s, hs,
      subset_trans (restrict_subset t n) hts⟩
  · exact (mem_schemeTree_iff _ _ _ _).mpr ⟨empty_mem_finiteSequences _, ∅, empty_mem_finiteSequences _,
      empty_subset _⟩
  · intro t ht
    obtain ⟨_, s, hsB, hts⟩ := (mem_schemeTree_iff _ _ _ _).mp ht
    obtain ⟨n, hn, hs⟩ := (mem_binarySequences_iff _).mp hsB
    have hs0B := append_mem_binarySequences hn hs empty_mem_two
    have hs1B := append_mem_binarySequences hn hs succ_empty_mem_two
    refine ⟨_, (mem_schemeTree_iff _ _ _ _).mpr ⟨function_value_mem hτ (scheme_mem hp₀ hΦ _ hs0B), _, hs0B,
      subset_refl _⟩, _, (mem_schemeTree_iff _ _ _ _).mpr ⟨function_value_mem hτ (scheme_mem hp₀ hΦ _ hs1B),
      _, hs1B, subset_refl _⟩, ?_, ?_, scheme_children_incompatible hp₀ hΦ hn hs⟩
    · exact subset_trans hts (scheme_tau_mono hR hτ hmono hp₀ hΦ hs0B hsB (subset_insert _ _))
    · exact subset_trans hts (scheme_tau_mono hR hτ hmono hp₀ hΦ hs1B hsB (subset_insert _ _))

include hR hτ hmono hD hp₀ hΦ in
/-- Every real in the body of the scheme tree is the union of the `τ`-values along a filter
containing the root and meeting every dense set of the scheme. -/
theorem treeBody_schemeTree_subset {A : V}
    (hA : ∀ F, IsForcingFilter P R F → p₀ ∈ F → (∀ n ∈ (ω : V), ∃ q ∈ F, q ∈ D ‘ n) →
      ⋃ˢ (image τ F) ∈ A) :
    treeBody (schemeTree τ p₀ Φ) ⊆ A := by
  intro x hx
  obtain ⟨hxc, hxT⟩ := (mem_treeBody_iff _ _).mp hx
  have hxf : IsFunction x := IsFunction.of_mem hxc
  have hτfun : IsFunction τ := IsFunction.of_mem hτ
  have hτf : ∀ s ∈ binarySequences V, IsFunction (τ ‘ ((scheme p₀ Φ) ‘ s)) :=
    fun s hs ↦ tau_isFunction hτ (scheme_mem hp₀ hΦ s hs)
  have hτB : ∀ s ∈ binarySequences V, τ ‘ ((scheme p₀ Φ) ‘ s) ∈ binarySequences V :=
    fun s hs ↦ function_value_mem hτ (scheme_mem hp₀ hΦ s hs)
  have hseg : ∀ N ∈ (ω : V), ∃ ρ ∈ binarySequences V, x ↾ N ⊆ τ ‘ ((scheme p₀ Φ) ‘ ρ) :=
    fun N hN ↦ ((mem_schemeTree_iff _ _ _ _).mp (hxT N hN)).2
  have hxN : ∀ N ∈ (ω : V), x ↾ N ∈ ((2 : ℕ) : V) ^ N :=
    fun N hN ↦ function_restrict_mem hxc (IsTransitive.ω.transitive N hN)
  -- the root value is an initial segment of `x`
  have hbase : τ ‘ ((scheme p₀ Φ) ‘ (∅ : V)) ⊆ x := by
    have h0B : (∅ : V) ∈ binarySequences V := empty_mem_finiteSequences _
    obtain ⟨N, hN, hτ0⟩ := (mem_binarySequences_iff _).mp (hτB ∅ h0B)
    obtain ⟨ρ, hρB, hxρ⟩ := hseg N hN
    obtain ⟨e, _, hτρ⟩ := (mem_binarySequences_iff _).mp (hτB ρ hρB)
    have h1 : τ ‘ ((scheme p₀ Φ) ‘ (∅ : V)) ⊆ τ ‘ ((scheme p₀ Φ) ‘ ρ) :=
      scheme_tau_mono hR hτ hmono hp₀ hΦ hρB h0B (empty_subset _)
    rw [sequence_eq_of_subset_subset_of_domain_eq hτρ hτ0 (hxN N hN) h1 hxρ]
    exact restrict_subset x N
  -- one child of every node whose value is an initial segment of `x` has the same property
  have hstep : ∀ n ∈ (ω : V), ∀ s ∈ ((2 : ℕ) : V) ^ n, τ ‘ ((scheme p₀ Φ) ‘ s) ⊆ x →
      ∃ a ∈ ((2 : ℕ) : V), τ ‘ ((scheme p₀ Φ) ‘ (insert ⟨n, a⟩ₖ s)) ⊆ x := by
    intro n hn s hs hsx
    have hsB : s ∈ binarySequences V := (mem_binarySequences_iff _).mpr ⟨n, hn, hs⟩
    have hs0B := append_mem_binarySequences hn hs empty_mem_two
    have hs1B := append_mem_binarySequences hn hs succ_empty_mem_two
    have hd0 := binarySequence_domain_mem (hτB _ hs0B)
    have hd1 := binarySequence_domain_mem (hτB _ hs1B)
    have : IsOrdinal (domain (τ ‘ ((scheme p₀ Φ) ‘ (insert ⟨n, ∅⟩ₖ s)))) := IsOrdinal.of_mem hd0
    have : IsOrdinal (domain (τ ‘ ((scheme p₀ Φ) ‘ (insert ⟨n, succ ∅⟩ₖ s)))) := IsOrdinal.of_mem hd1
    obtain ⟨N, hNdef⟩ : ∃ N : V, N = domain (τ ‘ ((scheme p₀ Φ) ‘ (insert ⟨n, ∅⟩ₖ s))) ∪
      domain (τ ‘ ((scheme p₀ Φ) ‘ (insert ⟨n, succ ∅⟩ₖ s))) := ⟨_, rfl⟩
    have hNω : N ∈ (ω : V) := by
      rw [hNdef]
      exact union_mem_of_ordinals hd0 hd1
    have hdN : ∀ a ∈ ((2 : ℕ) : V), domain (τ ‘ ((scheme p₀ Φ) ‘ (insert ⟨n, a⟩ₖ s))) ⊆ N := by
      intro a ha
      rw [hNdef]
      rcases (mem_two_iff a).mp ha with rfl | rfl
      · exact subset_union_left _ _
      · exact subset_union_right _ _
    obtain ⟨ρ, hρB, hxρ⟩ := hseg N hNω
    obtain ⟨k, hk, hρ⟩ := (mem_binarySequences_iff _).mp hρB
    obtain ⟨e, _, hτρ⟩ := (mem_binarySequences_iff _).mp (hτB ρ hρB)
    have hsfun := hτf s hsB
    have hs0fun := hτf _ hs0B
    have hs0 := scheme_tau_mono hR hτ hmono hp₀ hΦ hs0B hsB (subset_insert _ _)
    have hsxN : τ ‘ ((scheme p₀ Φ) ‘ s) ⊆ x ↾ N :=
      subset_restrict_of_domain_subset hsx
        (subset_trans (domain_subset_of_subset_function hs0) (hdN ∅ empty_mem_two))
    have hsρ : τ ‘ ((scheme p₀ Φ) ‘ s) ⊆ τ ‘ ((scheme p₀ Φ) ‘ ρ) := subset_trans hsxN hxρ
    by_cases hρs : ρ ⊆ s
    · exfalso
      have hρs' := scheme_tau_mono hR hτ hmono hp₀ hΦ hsB hρB hρs
      have heq : τ ‘ ((scheme p₀ Φ) ‘ s) = x ↾ N := subset_antisymm hsxN (subset_trans hxρ hρs')
      obtain ⟨d, _, hτs⟩ := (mem_binarySequences_iff _).mp (hτB s hsB)
      have hNd : N ⊆ d := sequence_domain_subset_of_subset hτs (hxN N hNω) (by rw [heq])
      obtain ⟨d0, _, hτ0⟩ := (mem_binarySequences_iff _).mp (hτB _ hs0B)
      have hd0d : d0 ⊆ d := by
        rw [← domain_eq_of_mem_function hτ0]
        exact subset_trans (hdN ∅ empty_mem_two) hNd
      have hdd0 : d ⊆ d0 := sequence_domain_subset_of_subset hτ0 hτs hs0
      have hd0d' : d0 = d := subset_antisymm hd0d hdd0
      rw [hd0d'] at hτ0
      exact scheme_child_ne hR hτ hmono hp₀ hΦ hn hs empty_mem_two
        (sequence_eq_of_subset_of_domain_eq hτs hτ0 hs0).symm
    · by_cases hsρ' : s ⊆ ρ
      · obtain ⟨a, ha, hsa⟩ := exists_append_subset_of_ssubset hn hk hs hρ hsρ'
          (fun h ↦ hρs (h ▸ subset_refl _))
        refine ⟨a, ha, ?_⟩
        have hsaB := append_mem_binarySequences hn hs ha
        obtain ⟨da, _, hτa⟩ := (mem_binarySequences_iff _).mp (hτB _ hsaB)
        have h1 := scheme_tau_mono hR hτ hmono hp₀ hΦ hρB hsaB hsa
        have hdaN : da ⊆ N := by
          rw [← domain_eq_of_mem_function hτa]
          exact hdN a ha
        exact subset_trans (sequence_subset_of_subset_of_domain_subset hτρ hτa (hxN N hNω) h1 hxρ hdaN)
          (restrict_subset x N)
      · exfalso
        have hinc := scheme_incompatible_of_incomparable hR hτ hmono hp₀ hΦ hn hk hs hρ hsρ' hρs
        have := hτf ρ hρB
        exact not_incompatible_of_subset hsρ hinc
  -- at every level there is a node whose value is an initial segment of `x` of length at least
  -- the level
  have hlevel : ∀ n ∈ (ω : V), ∃ s ∈ ((2 : ℕ) : V) ^ n, τ ‘ ((scheme p₀ Φ) ‘ s) ⊆ x ∧
      n ⊆ domain (τ ‘ ((scheme p₀ Φ) ‘ s)) := by
    apply naturalNumber_induction (fun n ↦ ∃ s ∈ ((2 : ℕ) : V) ^ n, τ ‘ ((scheme p₀ Φ) ‘ s) ⊆ x ∧
      n ⊆ domain (τ ‘ ((scheme p₀ Φ) ‘ s))) (levelPredicate_definable τ (scheme p₀ Φ) x)
    · exact ⟨∅, empty_mem_function_empty _, hbase, empty_subset _⟩
    · intro n hn ih
      obtain ⟨s, hs, hsx, hnd⟩ := ih
      obtain ⟨a, ha, hax⟩ := hstep n hn s hs hsx
      refine ⟨insert ⟨n, a⟩ₖ s, function_append_mem hs ha, hax, ?_⟩
      have hsB : s ∈ binarySequences V := (mem_binarySequences_iff _).mpr ⟨n, hn, hs⟩
      have hsaB := append_mem_binarySequences hn hs ha
      have hsfun := hτf s hsB
      have hd := binarySequence_domain_mem (hτB s hsB)
      have hd' := binarySequence_domain_mem (hτB _ hsaB)
      have : IsOrdinal (domain (τ ‘ ((scheme p₀ Φ) ‘ s))) := IsOrdinal.of_mem hd
      have : IsOrdinal (domain (τ ‘ ((scheme p₀ Φ) ‘ (insert ⟨n, a⟩ₖ s)))) := IsOrdinal.of_mem hd'
      have : IsOrdinal n := IsOrdinal.of_mem hn
      have hsub := scheme_tau_mono hR hτ hmono hp₀ hΦ hsaB hsB (subset_insert _ _)
      have hdd : domain (τ ‘ ((scheme p₀ Φ) ‘ s)) ⊆ domain (τ ‘ ((scheme p₀ Φ) ‘ (insert ⟨n, a⟩ₖ s))) :=
        domain_subset_of_subset_function hsub
      have hmem : domain (τ ‘ ((scheme p₀ Φ) ‘ s)) ∈ domain (τ ‘ ((scheme p₀ Φ) ‘ (insert ⟨n, a⟩ₖ s))) := by
        rcases IsOrdinal.subset_iff.mp hdd with h | h
        · exfalso
          obtain ⟨d, _, hτs⟩ := (mem_binarySequences_iff _).mp (hτB s hsB)
          obtain ⟨da, _, hτa⟩ := (mem_binarySequences_iff _).mp (hτB _ hsaB)
          have hda : da = d := by
            rw [← domain_eq_of_mem_function hτa, ← domain_eq_of_mem_function hτs, h]
          rw [hda] at hτa
          exact scheme_child_ne hR hτ hmono hp₀ hΦ hn hs ha
            (sequence_eq_of_subset_of_domain_eq hτs hτa hsub).symm
        · exact h
      have hn' : n ∈ domain (τ ‘ ((scheme p₀ Φ) ‘ (insert ⟨n, a⟩ₖ s))) := by
        rcases IsOrdinal.subset_iff.mp hnd with h | h
        · have := hmem
          rw [← h] at this
          exact this
        · exact (IsTransitive.nat hd').transitive _ hmem n h
      exact succ_subset_of_mem_nat hd' hn'
  -- the filter generated by the branch
  obtain ⟨F, hF⟩ : ∃ F : V, ∀ p, p ∈ F ↔ p ∈ P ∧ ∃ s ∈ binarySequences V,
      τ ‘ ((scheme p₀ Φ) ‘ s) ⊆ x ∧ ⟨(scheme p₀ Φ) ‘ s, p⟩ₖ ∈ R :=
    ⟨sep P (fun p ↦ ∃ s ∈ binarySequences V, τ ‘ ((scheme p₀ Φ) ‘ s) ⊆ x ∧ ⟨(scheme p₀ Φ) ‘ s, p⟩ₖ ∈ R)
      (branchFilter_definable R τ (scheme p₀ Φ) x), fun p ↦ by simp only [mem_sep_iff]⟩
  have hnode : ∀ s ∈ binarySequences V, τ ‘ ((scheme p₀ Φ) ‘ s) ⊆ x → (scheme p₀ Φ) ‘ s ∈ F :=
    fun s hs hsx ↦ (hF _).mpr ⟨scheme_mem hp₀ hΦ s hs, s, hs, hsx, hR.2.1 _ (scheme_mem hp₀ hΦ s hs)⟩
  have hfilter : IsForcingFilter P R F := by
    refine ⟨fun p hp ↦ ((hF p).mp hp).1, ⟨p₀, ?_⟩, ?_, ?_⟩
    · have := hnode ∅ (empty_mem_finiteSequences _) hbase
      rwa [scheme_empty] at this
    · intro p hp q hq hpq
      obtain ⟨hpP, s, hs, hsx, hsp⟩ := (hF p).mp hp
      exact (hF q).mpr ⟨hq, s, hs, hsx, hR.2.2 _ (scheme_mem hp₀ hΦ s hs) p hpP q hq hsp hpq⟩
    · intro p hp q hq
      obtain ⟨hpP, s, hsB, hsx, hsp⟩ := (hF p).mp hp
      obtain ⟨hqP, t, htB, htx, htq⟩ := (hF q).mp hq
      obtain ⟨n, hn, hs⟩ := (mem_binarySequences_iff _).mp hsB
      obtain ⟨m, hm, ht⟩ := (mem_binarySequences_iff _).mp htB
      have hsfun := hτf s hsB
      have htfun := hτf t htB
      have hcomp : s ⊆ t ∨ t ⊆ s := by
        by_contra hno
        push_neg at hno
        exact not_incompatible_of_subset_subset hsx htx
          (scheme_incompatible_of_incomparable hR hτ hmono hp₀ hΦ hn hm hs ht hno.1 hno.2)
      rcases hcomp with hst | hts
      · refine ⟨(scheme p₀ Φ) ‘ t, hnode t htB htx, ?_, htq⟩
        exact hR.2.2 _ (scheme_mem hp₀ hΦ t htB) _ (scheme_mem hp₀ hΦ s hsB) p hpP
          (scheme_mono hR hp₀ hΦ t htB s hsB hst) hsp
      · refine ⟨(scheme p₀ Φ) ‘ s, hnode s hsB hsx, hsp, ?_⟩
        exact hR.2.2 _ (scheme_mem hp₀ hΦ s hsB) _ (scheme_mem hp₀ hΦ t htB) q hqP
          (scheme_mono hR hp₀ hΦ s hsB t htB hts) htq
  have hp₀F : p₀ ∈ F := by
    have := hnode ∅ (empty_mem_finiteSequences _) hbase
    rwa [scheme_empty] at this
  have hmeets : ∀ n ∈ (ω : V), ∃ q ∈ F, q ∈ D ‘ n := by
    intro n hn
    obtain ⟨s, hs, hsx, _⟩ := hlevel n hn
    obtain ⟨a, ha, hax⟩ := hstep n hn s hs hsx
    exact ⟨_, hnode _ (append_mem_binarySequences hn hs ha) hax, (scheme_child hp₀ hΦ hn hs ha).2⟩
  have hxeq : x = ⋃ˢ (image τ F) := by
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨i, hi, v, _, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hxc z hz)
      obtain ⟨s, hs, hsx, hnd⟩ := hlevel (succ i) (ω_succ_closed hi)
      have hsB : s ∈ binarySequences V := (mem_binarySequences_iff _).mpr ⟨succ i, ω_succ_closed hi, hs⟩
      have hsfun := hτf s hsB
      have hid : i ∈ domain (τ ‘ ((scheme p₀ Φ) ‘ s)) := hnd i (mem_succ_iff.mpr (Or.inl rfl))
      have hv : (τ ‘ ((scheme p₀ Φ) ‘ s)) ‘ i = v := by
        rw [← value_eq_of_subset_function hsx hid]
        exact value_eq_of_kpair_mem hz
      refine mem_sUnion_iff.mpr ⟨τ ‘ ((scheme p₀ Φ) ‘ s), (mem_image_iff' _ _ _).mpr
        ⟨_, hnode s hsB hsx, kpair_value_mem ?_⟩, ?_⟩
      · rw [domain_eq_of_mem_function hτ]
        exact scheme_mem hp₀ hΦ s hsB
      · rw [← hv]
        exact kpair_value_mem hid
    · intro hz
      obtain ⟨y, hy, hzy⟩ := mem_sUnion_iff.mp hz
      obtain ⟨p, hp, hpy⟩ := (mem_image_iff' _ _ _).mp hy
      obtain ⟨hpP, s, hs, hsx, hsp⟩ := (hF p).mp hp
      rw [← value_eq_of_kpair_mem hpy] at hzy
      exact hsx _ (hmono p hpP _ (scheme_mem hp₀ hΦ s hs) hsp _ hzy)
  rw [hxeq]
  exact hA F hfilter hp₀F hmeets

end

/-- The perfect-set core: a set of reals containing the union of the `τ`-values along every
filter through `p₀` meeting the dense sets `D ‘ n` contains the body of a perfect tree, provided
`τ` is monotone and splits below every condition. -/
theorem exists_perfectTree_of_splitting (hAC : InternalChoice V) {P R τ D A p₀ : V}
    (hR : IsForcingPreorder P R) (hp₀ : p₀ ∈ P) (hτ : τ ∈ (binarySequences V) ^ P)
    (hmono : ∀ p ∈ P, ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → τ ‘ p ⊆ τ ‘ q)
    (hsplit : ∀ p ∈ P, ∃ q ∈ P, ∃ q' ∈ P, ⟨q, p⟩ₖ ∈ R ∧ ⟨q', p⟩ₖ ∈ R ∧
      Incompatible (τ ‘ q) (τ ‘ q'))
    (hD : D ∈ (℘ P) ^ (ω : V))
    (hdense : ∀ n ∈ (ω : V), ∀ p ∈ P, ∃ q ∈ D ‘ n, ⟨q, p⟩ₖ ∈ R)
    (hA : ∀ F, IsForcingFilter P R F → p₀ ∈ F → (∀ n ∈ (ω : V), ∃ q ∈ F, q ∈ D ‘ n) →
      ⋃ˢ (image τ F) ∈ A) :
    ∃ T, IsPerfectTree T ∧ treeBody T ⊆ A := by
  obtain ⟨Φ, _, _, hΦ⟩ := exists_splitChoice hR hτ hmono hD hAC hsplit hdense
  exact ⟨schemeTree τ p₀ Φ, schemeTree_perfect hR hτ hmono hp₀ hΦ,
    treeBody_schemeTree_subset hR hτ hmono hD hp₀ hΦ hA⟩

end ZFVP
