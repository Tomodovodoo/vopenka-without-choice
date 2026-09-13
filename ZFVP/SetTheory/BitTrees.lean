import ZFVP.SetTheory.PrunedTrees

/-! The trees of sequences with a prescribed bit at a prescribed position. Their bodies are the
reals with that bit, and they are positive (density one half). -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- No finite set injects into itself with a doubled copy. -/
theorem not_prod_two_cardLE_self {M : V} (hM : M ∈ (ω : V)) :
    ¬ (((2 : ℕ) : V) ^ M) ×ˢ ((2 : ℕ) : V) ≤# ((2 : ℕ) : V) ^ M := by
  intro h1
  have hsing : IsInternallyFinite ({∅} : V) := internallyFinite_subset internallyFinite_two (fun x hx ↦ by
    rw [mem_singleton_iff] at hx
    rw [hx]
    exact (mem_two_iff _).mpr (Or.inl rfl))
  have hfin : IsInternallyFinite ((((2 : ℕ) : V) ^ M) ×ˢ ({∅} : V)) :=
    internallyFinite_prod (internallyFinite_two_pow hM) hsing
  have h2 : ((2 : ℕ) : V) ^ M ≤# (((2 : ℕ) : V) ^ M) ×ˢ ({∅} : V) := by
    refine cardLE_of_injective_map (fun u ↦ ⟨u, ∅⟩ₖ) (by definability) ?_ ?_
    · intro u hu
      exact kpair_mem_iff.mpr ⟨hu, mem_singleton_iff.mpr rfl⟩
    · intro u _ u' _ h
      exact (kpair_inj h).1
  have hfresh : ⟨zeroSequence M, succ ∅⟩ₖ ∉ (((2 : ℕ) : V) ^ M) ×ˢ ({∅} : V) := by
    intro h
    exact succ_empty_ne_empty (mem_singleton_iff.mp (kpair_mem_iff.mp h).2)
  have hsub : insert ⟨zeroSequence M, succ ∅⟩ₖ ((((2 : ℕ) : V) ^ M) ×ˢ ({∅} : V)) ⊆
      (((2 : ℕ) : V) ^ M) ×ˢ ((2 : ℕ) : V) := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact kpair_mem_iff.mpr ⟨zeroSequence_mem_power M, (mem_two_iff _).mpr (Or.inr rfl)⟩
    · obtain ⟨u, hu, t, ht, rfl⟩ := mem_prod_iff.mp hz
      rw [mem_singleton_iff] at ht
      rw [ht]
      exact kpair_mem_iff.mpr ⟨hu, (mem_two_iff _).mpr (Or.inl rfl)⟩
  exact not_insert_fresh_cardLE hfin hfresh (((cardLE_of_subset hsub).trans h1).trans h2)

theorem two_cardLE_function_power_two : ((2 : ℕ) : V) ≤# ((2 : ℕ) : V) ^ succ (succ (∅ : V)) :=
  two_cardLE_function_power_one.trans (function_power_cardLE_succ _)

theorem prod_two_two_cardLE_function_power_two :
    ((2 : ℕ) : V) ×ˢ ((2 : ℕ) : V) ≤# ((2 : ℕ) : V) ^ succ (succ (∅ : V)) :=
  (prod_cardLE_prod two_cardLE_function_power_one (CardLE.refl _)).trans (prod_two_cardLE_function_power_succ _)

/-- Overwriting the bit at `n` with `i`. -/
noncomputable def setBit (t n i : V) : V := {p ∈ t ; kpair.π₁ p ≠ n} ∪ ({⟨n, i⟩ₖ} : V)

theorem mem_setBit_iff (t n i p : V) : p ∈ setBit t n i ↔ (p ∈ t ∧ kpair.π₁ p ≠ n) ∨ p = ⟨n, i⟩ₖ := by
  unfold setBit
  rw [mem_union_iff, mem_sep_iff, mem_singleton_iff]

theorem setBit_definable (n i : V) : ℒₛₑₜ-function₁ (fun t : V ↦ setBit t n i) := by
  have h : ℒₛₑₜ-relation (fun S t : V ↦ ∀ p, p ∈ S ↔ (p ∈ t ∧ kpair.π₁ p ≠ n) ∨ p = ⟨n, i⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = setBit (v 1) n i ↔ _
  rw [mem_ext_iff]
  simp only [mem_setBit_iff]

theorem setBit_mem_power {t M n i : V} (ht : t ∈ ((2 : ℕ) : V) ^ M) (hn : n ∈ M) (hi : i ∈ ((2 : ℕ) : V)) :
    setBit t n i ∈ ((2 : ℕ) : V) ^ M := by
  have : IsFunction t := IsFunction.of_mem ht
  have htsub := (mem_function_iff.mp ht).1
  rw [mem_function_iff]
  refine ⟨fun p hp ↦ ?_, fun k hk ↦ ?_⟩
  · rcases (mem_setBit_iff _ _ _ _).mp hp with ⟨hpt, -⟩ | rfl
    · exact htsub p hpt
    · exact kpair_mem_iff.mpr ⟨hn, hi⟩
  · by_cases hkn : k = n
    · subst hkn
      refine ⟨i, (mem_setBit_iff _ _ _ _).mpr (Or.inr rfl), fun y hy ↦ ?_⟩
      rcases (mem_setBit_iff _ _ _ _).mp hy with ⟨-, hne⟩ | he
      · exact (hne (kpair.π₁_kpair _ _)).elim
      · exact (kpair_inj he).2
    · refine ⟨t ‘ k, (mem_setBit_iff _ _ _ _).mpr (Or.inl ⟨kpair_value_mem (by
        rw [domain_eq_of_mem_function ht]; exact hk), by rw [kpair.π₁_kpair]; exact hkn⟩), fun y hy ↦ ?_⟩
      rcases (mem_setBit_iff _ _ _ _).mp hy with ⟨hyt, -⟩ | he
      · exact (value_eq_of_kpair_mem hyt).symm
      · exact (hkn (kpair_inj he).1).elim

theorem setBit_value_self {t M n i : V} (ht : t ∈ ((2 : ℕ) : V) ^ M) (hn : n ∈ M) (hi : i ∈ ((2 : ℕ) : V)) :
    (setBit t n i) ‘ n = i := by
  have : IsFunction (setBit t n i) := IsFunction.of_mem (setBit_mem_power ht hn hi)
  exact value_eq_of_kpair_mem ((mem_setBit_iff _ _ _ _).mpr (Or.inr rfl))

theorem setBit_value_other {t M n i k : V} (ht : t ∈ ((2 : ℕ) : V) ^ M) (hn : n ∈ M) (hi : i ∈ ((2 : ℕ) : V))
    (hk : k ∈ M) (hkn : k ≠ n) : (setBit t n i) ‘ k = t ‘ k := by
  have : IsFunction (setBit t n i) := IsFunction.of_mem (setBit_mem_power ht hn hi)
  have : IsFunction t := IsFunction.of_mem ht
  exact value_eq_of_kpair_mem ((mem_setBit_iff _ _ _ _).mpr (Or.inl ⟨kpair_value_mem (by
    rw [domain_eq_of_mem_function ht]; exact hk), by rw [kpair.π₁_kpair]; exact hkn⟩))

/-- The tree of sequences with bit `i` at `n`. -/
noncomputable def bitTree (n i : V) : V := {s ∈ binarySequences V ; n ∈ domain s → s ‘ n = i}

theorem mem_bitTree_iff (n i s : V) : s ∈ bitTree n i ↔ s ∈ binarySequences V ∧ (n ∈ domain s → s ‘ n = i) :=
  mem_sep_iff

theorem bitTree_isTree (n i : V) : IsTree (bitTree n i) := by
  refine ⟨fun s hs ↦ ((mem_bitTree_iff _ _ _).mp hs).1, fun s hs k hk ↦ ?_⟩
  obtain ⟨hsB, hbit⟩ := (mem_bitTree_iff _ _ _).mp hs
  obtain ⟨m, hm, hsm⟩ := (mem_binarySequences_iff _).mp hsB
  have hd : domain s = m := domain_eq_of_mem_function hsm
  rw [hd] at hk
  have : IsOrdinal m := IsOrdinal.nat hm
  have hkm : k ⊆ m := IsOrdinal.toIsTransitive.transitive k hk
  have : IsFunction s := IsFunction.of_mem hsm
  have hsk : s ↾ k ∈ ((2 : ℕ) : V) ^ k := function_restrict_mem hsm hkm
  refine (mem_bitTree_iff _ _ _).mpr ⟨(mem_binarySequences_iff _).mpr ⟨k, IsTransitive.ω.transitive m hm k hk, hsk⟩, ?_⟩
  intro hn
  rw [domain_eq_of_mem_function hsk] at hn
  rw [value_restrict (by rw [hd]; exact hkm n hn) hn]
  exact hbit (by rw [hd]; exact hkm n hn)

theorem mem_treeBody_bitTree_iff {n i x : V} (hn : n ∈ (ω : V)) :
    x ∈ treeBody (bitTree n i) ↔ x ∈ cantorSpace V ∧ x ‘ n = i := by
  rw [mem_treeBody_iff]
  constructor
  · rintro ⟨hxc, h⟩
    have : IsFunction x := IsFunction.of_mem hxc
    obtain ⟨-, hbit⟩ := (mem_bitTree_iff _ _ _).mp (h (succ n) (ω_succ_closed hn))
    have hd : domain (x ↾ (succ n)) = succ n :=
      domain_eq_of_mem_function (function_restrict_mem hxc (IsTransitive.ω.transitive _ (ω_succ_closed hn)))
    have := hbit (by rw [hd]; exact mem_succ_self n)
    rw [value_restrict (by rw [domain_eq_of_mem_function hxc]; exact hn) (mem_succ_self n)] at this
    exact ⟨hxc, this⟩
  · rintro ⟨hxc, hxn⟩
    have : IsFunction x := IsFunction.of_mem hxc
    refine ⟨hxc, fun k hk ↦ (mem_bitTree_iff _ _ _).mpr ⟨restrict_mem_binarySequences hxc hk, fun hnk ↦ ?_⟩⟩
    have hd : domain (x ↾ k) = k := domain_eq_of_mem_function (function_restrict_mem hxc (IsTransitive.ω.transitive _ hk))
    rw [hd] at hnk
    rw [value_restrict (by rw [domain_eq_of_mem_function hxc]; exact hn) hnk]
    exact hxn

theorem mem_levelSet_bitTree_iff {n i M t : V} (hn : n ∈ M) (hM : M ∈ (ω : V)) :
    t ∈ levelSet (bitTree n i) M ↔ t ∈ ((2 : ℕ) : V) ^ M ∧ t ‘ n = i := by
  rw [mem_levelSet_iff, mem_bitTree_iff]
  constructor
  · rintro ⟨⟨-, hbit⟩, htM⟩
    exact ⟨htM, hbit (by rw [domain_eq_of_mem_function htM]; exact hn)⟩
  · rintro ⟨htM, hbit⟩
    exact ⟨⟨(mem_binarySequences_iff _).mpr ⟨M, hM, htM⟩, fun _ ↦ hbit⟩, htM⟩

/-- Bit trees are positive: density one half. -/
theorem bitTree_positive {n i : V} (hn : n ∈ (ω : V)) (hi : i ∈ ((2 : ℕ) : V)) : IsPositiveTree (bitTree n i) := by
  refine ⟨bitTree_isTree n i, succ (succ ∅), ω_succ_closed (ω_succ_closed zero_mem_ω), fun M hM hle ↦ ?_⟩
  have : IsOrdinal M := IsOrdinal.nat hM
  have : IsOrdinal n := IsOrdinal.nat hn
  by_cases hnM : n ∈ M
  · -- injection `2^M → levelSet × 2`
    have hinj : ((2 : ℕ) : V) ^ M ≤# levelSet (bitTree n i) M ×ˢ ((2 : ℕ) : V) := by
      refine cardLE_of_injective_map (fun t ↦ ⟨setBit t n i, t ‘ n⟩ₖ) (by
        have := setBit_definable n i
        definability) ?_ ?_
      · intro t ht
        exact kpair_mem_iff.mpr ⟨(mem_levelSet_bitTree_iff hnM hM).mpr
          ⟨setBit_mem_power ht hnM hi, setBit_value_self ht hnM hi⟩, function_value_mem ht hnM⟩
      · intro t ht t' ht' h
        obtain ⟨h1, h2⟩ := kpair_inj h
        have : IsFunction t := IsFunction.of_mem ht
        have : IsFunction t' := IsFunction.of_mem ht'
        apply functions_eq_of_domain_values ((domain_eq_of_mem_function ht).trans (domain_eq_of_mem_function ht').symm)
        intro k hk
        rw [domain_eq_of_mem_function ht] at hk
        by_cases hkn : k = n
        · rw [hkn]; exact h2
        · have := congrArg (fun f ↦ f ‘ k) h1
          rw [setBit_value_other ht hnM hi hk hkn, setBit_value_other ht' hnM hi hk hkn] at this
          exact this
    apply not_prod_two_cardLE_self hM
    have h3 : (((2 : ℕ) : V) ^ M) ×ˢ ((2 : ℕ) : V) ≤# (levelSet (bitTree n i) M ×ˢ ((2 : ℕ) : V)) ×ˢ ((2 : ℕ) : V) :=
      prod_cardLE_prod hinj (CardLE.refl _)
    have h4 : (levelSet (bitTree n i) M ×ˢ ((2 : ℕ) : V)) ×ˢ ((2 : ℕ) : V) ≤#
        levelSet (bitTree n i) M ×ˢ (((2 : ℕ) : V) ×ˢ ((2 : ℕ) : V)) := prod_assoc_cardLE _ _ _
    have h5 : levelSet (bitTree n i) M ×ˢ (((2 : ℕ) : V) ×ˢ ((2 : ℕ) : V)) ≤#
        levelSet (bitTree n i) M ×ˢ (((2 : ℕ) : V) ^ succ (succ (∅ : V))) :=
      prod_cardLE_prod (CardLE.refl _) prod_two_two_cardLE_function_power_two
    exact h3.trans (h4.trans (h5.trans hle))
  · -- the level is the full level
    have hlev : levelSet (bitTree n i) M = ((2 : ℕ) : V) ^ M := by
      apply mem_ext
      intro t
      rw [mem_levelSet_iff, mem_bitTree_iff]
      constructor
      · exact fun h ↦ h.2
      · intro ht
        refine ⟨⟨(mem_binarySequences_iff _).mpr ⟨M, hM, ht⟩, fun hnd ↦ ?_⟩, ht⟩
        rw [domain_eq_of_mem_function ht] at hnd
        exact (hnM hnd).elim
    rw [hlev] at hle
    exact not_prod_two_cardLE_self hM ((prod_cardLE_prod (CardLE.refl _) two_cardLE_function_power_two).trans hle)

end ZFVP
