import ZFVP.SetTheory.BaireCore
import ZFVP.SetTheory.TreeEmbedding

/-! Binary splitting schemes below a condition: for a monotone assignment `τ` of finite binary
sequences to conditions that splits below every condition, choose for each node two extensions
lying in a prescribed dense set with incompatible `τ`-values, and run the tree recursion of
`treeMap` on binary sequences. Nodes map to conditions monotonically, and incomparable nodes have
incompatible `τ`-values. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem value_eq_of_subset_function {t u i : V} [IsFunction t] [IsFunction u] (h : t ⊆ u)
    (hi : i ∈ domain t) : u ‘ i = t ‘ i :=
  value_eq_of_kpair_mem (h _ (kpair_value_mem hi))

theorem domain_subset_of_subset_function {t u : V} [IsFunction t] (h : t ⊆ u) :
    domain t ⊆ domain u := fun i hi ↦ mem_domain_of_kpair_mem (h _ (kpair_value_mem hi))

theorem incompatible_symm {t u : V} (h : Incompatible t u) : Incompatible u t := by
  obtain ⟨i, hit, hiu, hne⟩ := h
  exact ⟨i, hiu, hit, fun e ↦ hne e.symm⟩

theorem incompatible_mono {t u t' u' : V} [IsFunction t] [IsFunction u] [IsFunction t']
    [IsFunction u'] (h : Incompatible t u) (ht : t ⊆ t') (hu : u ⊆ u') : Incompatible t' u' := by
  obtain ⟨i, hit, hiu, hne⟩ := h
  refine ⟨i, domain_subset_of_subset_function ht i hit, domain_subset_of_subset_function hu i hiu, ?_⟩
  rw [value_eq_of_subset_function ht hit, value_eq_of_subset_function hu hiu]
  exact hne

theorem not_incompatible_of_subset {t u : V} [IsFunction t] [IsFunction u] (h : t ⊆ u) :
    ¬Incompatible t u := by
  rintro ⟨i, hit, _, hne⟩
  exact hne (value_eq_of_subset_function h hit).symm

theorem two_eq_succ_succ : ((2 : ℕ) : V) = succ (succ ∅) := by
  rw [num_succ_def 1, num_succ_def 0]
  rfl

theorem mem_two_iff (α : V) : α ∈ ((2 : ℕ) : V) ↔ α = ∅ ∨ α = succ ∅ := by
  rw [two_eq_succ_succ, mem_succ_iff, mem_succ_iff]
  constructor
  · rintro (h | h | h)
    · exact Or.inr h
    · exact Or.inl h
    · exact (not_mem_empty h).elim
  · rintro (h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h

theorem empty_mem_two : (∅ : V) ∈ ((2 : ℕ) : V) := (mem_two_iff _).mpr (Or.inl rfl)

theorem succ_empty_mem_two : succ (∅ : V) ∈ ((2 : ℕ) : V) := (mem_two_iff _).mpr (Or.inr rfl)

/-- The two-element sequence `⟨a, b⟩`. -/
noncomputable def pairSeq (a b : V) : V := insert ⟨succ ∅, b⟩ₖ (insert ⟨∅, a⟩ₖ (∅ : V))

theorem pairSeq_mem {P a b : V} (ha : a ∈ P) (hb : b ∈ P) : pairSeq a b ∈ P ^ ((2 : ℕ) : V) := by
  rw [two_eq_succ_succ]
  exact function_append_mem (function_append_mem (empty_mem_function_empty P) ha) hb

theorem pairSeq_value_zero {P a b : V} (ha : a ∈ P) (hb : b ∈ P) : (pairSeq a b) ‘ (∅ : V) = a := by
  have : IsFunction (pairSeq a b) := IsFunction.of_mem (pairSeq_mem ha hb)
  exact value_eq_of_kpair_mem (mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inl rfl))))

theorem pairSeq_value_one {P a b : V} (ha : a ∈ P) (hb : b ∈ P) : (pairSeq a b) ‘ (succ (∅ : V)) = b :=
  value_insert_kpair (function_append_mem (empty_mem_function_empty P) ha) hb

/-- The pairs of extensions of `π₂ z` in the `π₁ z`-th dense set with incompatible `τ`-values. -/
noncomputable def splitFamily (P R D τ : V) (z : V) : V :=
  {f ∈ P ^ ((2 : ℕ) : V) ; ⟨f ‘ (∅ : V), kpair.π₂ z⟩ₖ ∈ R ∧ ⟨f ‘ (succ (∅ : V)), kpair.π₂ z⟩ₖ ∈ R ∧
    f ‘ (∅ : V) ∈ D ‘ (kpair.π₁ z) ∧ f ‘ (succ (∅ : V)) ∈ D ‘ (kpair.π₁ z) ∧
    Incompatible (τ ‘ (f ‘ (∅ : V))) (τ ‘ (f ‘ (succ (∅ : V))))}

theorem mem_splitFamily_iff (P R D τ z f : V) :
    f ∈ splitFamily P R D τ z ↔ f ∈ P ^ ((2 : ℕ) : V) ∧
      ⟨f ‘ (∅ : V), kpair.π₂ z⟩ₖ ∈ R ∧ ⟨f ‘ (succ (∅ : V)), kpair.π₂ z⟩ₖ ∈ R ∧
      f ‘ (∅ : V) ∈ D ‘ (kpair.π₁ z) ∧ f ‘ (succ (∅ : V)) ∈ D ‘ (kpair.π₁ z) ∧
      Incompatible (τ ‘ (f ‘ (∅ : V))) (τ ‘ (f ‘ (succ (∅ : V)))) := by
  simp only [splitFamily, mem_sep_iff]

theorem splitFamily_definable (P R D τ : V) : ℒₛₑₜ-function₁[V] (splitFamily P R D τ) := by
  have h : ℒₛₑₜ-relation (fun S z : V ↦ ∀ f, f ∈ S ↔ f ∈ P ^ ((2 : ℕ) : V) ∧
      ⟨f ‘ (∅ : V), kpair.π₂ z⟩ₖ ∈ R ∧ ⟨f ‘ (succ (∅ : V)), kpair.π₂ z⟩ₖ ∈ R ∧
      f ‘ (∅ : V) ∈ D ‘ (kpair.π₁ z) ∧ f ‘ (succ (∅ : V)) ∈ D ‘ (kpair.π₁ z) ∧
      Incompatible (τ ‘ (f ‘ (∅ : V))) (τ ‘ (f ‘ (succ (∅ : V))))) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = splitFamily P R D τ (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_splitFamily_iff]

section

variable {P R D τ : V} (hR : IsForcingPreorder P R) (hτ : τ ∈ (binarySequences V) ^ P)
  (hmono : ∀ p ∈ P, ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → τ ‘ p ⊆ τ ‘ q)
  (hD : D ∈ (℘ P) ^ (ω : V))

include hτ in
theorem tau_isFunction {p : V} (hp : p ∈ P) : IsFunction (τ ‘ p) :=
  binarySequence_isFunction (function_value_mem hτ hp)

include hR hτ hmono hD in
/-- A choice of splitting pairs for every node and level. -/
theorem exists_splitChoice (hAC : InternalChoice V)
    (hsplit : ∀ p ∈ P, ∃ q ∈ P, ∃ q' ∈ P, ⟨q, p⟩ₖ ∈ R ∧ ⟨q', p⟩ₖ ∈ R ∧
      Incompatible (τ ‘ q) (τ ‘ q'))
    (hdense : ∀ n ∈ (ω : V), ∀ p ∈ P, ∃ q ∈ D ‘ n, ⟨q, p⟩ₖ ∈ R) :
    ∃ Φ : V, IsFunction Φ ∧ domain Φ = (ω : V) ×ˢ P ∧
      ∀ n ∈ (ω : V), ∀ p ∈ P, Φ ‘ ⟨n, p⟩ₖ ∈ splitFamily P R D τ ⟨n, p⟩ₖ := by
  obtain ⟨Φ, hΦ, hdom, hval⟩ := choice_for_definable_family hAC ((ω : V) ×ˢ P)
    (splitFamily P R D τ) (splitFamily_definable P R D τ) (by
      intro z hz
      obtain ⟨n, hn, p, hp, rfl⟩ := mem_prod_iff.mp hz
      obtain ⟨q, hq, q', hq', hqp, hq'p, hinc⟩ := hsplit p hp
      obtain ⟨q₀, hq₀, hq₀q⟩ := hdense n hn q hq
      obtain ⟨q₁, hq₁, hq₁q'⟩ := hdense n hn q' hq'
      have hDn : D ‘ n ⊆ P := mem_power_iff.mp (function_value_mem hD hn)
      have hq₀P := hDn q₀ hq₀
      have hq₁P := hDn q₁ hq₁
      refine ⟨pairSeq q₀ q₁, (mem_splitFamily_iff _ _ _ _ _ _).mpr ⟨pairSeq_mem hq₀P hq₁P, ?_⟩⟩
      rw [pairSeq_value_zero hq₀P hq₁P, pairSeq_value_one hq₀P hq₁P, kpair.π₁_kpair, kpair.π₂_kpair]
      refine ⟨hR.2.2 q₀ hq₀P q hq p hp hq₀q hqp, hR.2.2 q₁ hq₁P q' hq' p hp hq₁q' hq'p, hq₀, hq₁, ?_⟩
      have := tau_isFunction hτ hq
      have := tau_isFunction hτ hq'
      have := tau_isFunction hτ hq₀P
      have := tau_isFunction hτ hq₁P
      exact incompatible_mono hinc (hmono q hq q₀ hq₀P hq₀q) (hmono q' hq' q₁ hq₁P hq₁q'))
  exact ⟨Φ, hΦ, hdom, fun n hn p hp ↦ hval _ (kpair_mem_iff.mpr ⟨hn, hp⟩)⟩

/-- The binary scheme below `p₀` determined by the splitting choice `Φ`. -/
noncomputable def scheme (p₀ Φ : V) : V := treeMap p₀ Φ ((2 : ℕ) : V)

variable {p₀ Φ : V} (hp₀ : p₀ ∈ P)
  (hΦ : ∀ n ∈ (ω : V), ∀ p ∈ P, Φ ‘ ⟨n, p⟩ₖ ∈ splitFamily P R D τ ⟨n, p⟩ₖ)

theorem scheme_empty : (scheme p₀ Φ) ‘ (∅ : V) = p₀ := treeMap_empty _ _ _

theorem binarySequences_eq : binarySequences V = finiteSequences ((2 : ℕ) : V) := rfl

theorem scheme_append {t n α : V} (hn : n ∈ (ω : V)) (ht : t ∈ ((2 : ℕ) : V) ^ n)
    (hα : α ∈ ((2 : ℕ) : V)) :
    (scheme p₀ Φ) ‘ (insert ⟨n, α⟩ₖ t) = (Φ ‘ ⟨n, (scheme p₀ Φ) ‘ t⟩ₖ) ‘ α :=
  treeMap_append hn ht hα

theorem append_mem_binarySequences {t n α : V} (hn : n ∈ (ω : V)) (ht : t ∈ ((2 : ℕ) : V) ^ n)
    (hα : α ∈ ((2 : ℕ) : V)) : insert ⟨n, α⟩ₖ t ∈ binarySequences V :=
  (mem_binarySequences_iff _).mpr ⟨succ n, ω_succ_closed hn, function_append_mem ht hα⟩

include hp₀ hΦ in
theorem scheme_mem : ∀ s ∈ binarySequences V, (scheme p₀ Φ) ‘ s ∈ P := by
  apply finiteSequence_induction ((2 : ℕ) : V) (fun s ↦ (scheme p₀ Φ) ‘ s ∈ P) (by definability)
  · rw [scheme_empty]
    exact hp₀
  · intro n hn t ht α hα ih
    rw [scheme_append hn ht hα]
    have hf := (mem_splitFamily_iff _ _ _ _ _ _).mp (hΦ n hn _ ih)
    exact function_value_mem hf.1 hα

include hp₀ hΦ in
/-- Children lie below their parent and in the dense set of their level. -/
theorem scheme_child {t n α : V} (hn : n ∈ (ω : V)) (ht : t ∈ ((2 : ℕ) : V) ^ n)
    (hα : α ∈ ((2 : ℕ) : V)) :
    ⟨(scheme p₀ Φ) ‘ (insert ⟨n, α⟩ₖ t), (scheme p₀ Φ) ‘ t⟩ₖ ∈ R ∧
      (scheme p₀ Φ) ‘ (insert ⟨n, α⟩ₖ t) ∈ D ‘ n := by
  rw [scheme_append hn ht hα]
  have htP := scheme_mem hp₀ hΦ t ((mem_binarySequences_iff _).mpr ⟨n, hn, ht⟩)
  have hf := (mem_splitFamily_iff _ _ _ _ _ _).mp (hΦ n hn _ htP)
  rw [kpair.π₁_kpair, kpair.π₂_kpair] at hf
  rcases (mem_two_iff α).mp hα with rfl | rfl
  · exact ⟨hf.2.1, hf.2.2.2.1⟩
  · exact ⟨hf.2.2.1, hf.2.2.2.2.1⟩

include hp₀ hΦ in
theorem scheme_children_incompatible {t n : V} (hn : n ∈ (ω : V)) (ht : t ∈ ((2 : ℕ) : V) ^ n) :
    Incompatible (τ ‘ ((scheme p₀ Φ) ‘ (insert ⟨n, ∅⟩ₖ t)))
      (τ ‘ ((scheme p₀ Φ) ‘ (insert ⟨n, succ ∅⟩ₖ t))) := by
  rw [scheme_append hn ht empty_mem_two, scheme_append hn ht succ_empty_mem_two]
  have htP := scheme_mem hp₀ hΦ t ((mem_binarySequences_iff _).mpr ⟨n, hn, ht⟩)
  exact ((mem_splitFamily_iff _ _ _ _ _ _).mp (hΦ n hn _ htP)).2.2.2.2.2

include hR hp₀ hΦ in
/-- The scheme is order preserving. -/
theorem scheme_mono : ∀ s ∈ binarySequences V, ∀ t ∈ binarySequences V, t ⊆ s →
    ⟨(scheme p₀ Φ) ‘ s, (scheme p₀ Φ) ‘ t⟩ₖ ∈ R := by
  apply finiteSequence_induction ((2 : ℕ) : V) (fun s ↦ ∀ t ∈ binarySequences V, t ⊆ s →
    ⟨(scheme p₀ Φ) ‘ s, (scheme p₀ Φ) ‘ t⟩ₖ ∈ R) (by definability)
  · intro t _ hts
    have ht0 : t = ∅ := by
      apply mem_ext
      intro z
      exact ⟨fun hz ↦ hts z hz, fun hz ↦ (not_mem_empty hz).elim⟩
    rw [ht0, scheme_empty]
    exact hR.2.1 p₀ hp₀
  · intro n hn u hu α hα ih t ht hts
    have hs : insert ⟨n, α⟩ₖ u ∈ ((2 : ℕ) : V) ^ succ n := function_append_mem hu hα
    have hsB := append_mem_binarySequences hn hu hα
    by_cases heq : t = insert ⟨n, α⟩ₖ u
    · rw [heq]
      exact hR.2.1 _ (scheme_mem hp₀ hΦ _ hsB)
    · have htu : t ⊆ u := by
        have := subset_restrict_of_properSegment hn hs ht hts heq
        rwa [function_append_restrict hu] at this
      have h1 := (scheme_child hp₀ hΦ hn hu hα).1
      have h2 := ih t ht htu
      exact hR.2.2 _ (scheme_mem hp₀ hΦ _ hsB) _ (scheme_mem hp₀ hΦ u ((mem_binarySequences_iff _).mpr
        ⟨n, hn, hu⟩)) _ (scheme_mem hp₀ hΦ t ht) h1 h2

include hR hτ hmono hp₀ hΦ in
theorem scheme_tau_mono {s t : V} (hs : s ∈ binarySequences V) (ht : t ∈ binarySequences V)
    (hts : t ⊆ s) : τ ‘ ((scheme p₀ Φ) ‘ t) ⊆ τ ‘ ((scheme p₀ Φ) ‘ s) :=
  hmono _ (scheme_mem hp₀ hΦ t ht) _ (scheme_mem hp₀ hΦ s hs) (scheme_mono hR hp₀ hΦ s hs t ht hts)

include hR hτ hmono hp₀ hΦ in
/-- Incomparable nodes have incompatible `τ`-values. -/
theorem scheme_incompatible_of_incomparable {s t n m : V} (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hs : s ∈ ((2 : ℕ) : V) ^ n) (ht : t ∈ ((2 : ℕ) : V) ^ m) (h1 : ¬s ⊆ t) (h2 : ¬t ⊆ s) :
    Incompatible (τ ‘ ((scheme p₀ Φ) ‘ s)) (τ ‘ ((scheme p₀ Φ) ‘ t)) := by
  obtain ⟨k, hk, u, hu, a, ha, b, hb, hab, hus, hut⟩ := exists_branching_of_incomparable hn hm hs ht h1 h2
  have hsB : s ∈ binarySequences V := (mem_binarySequences_iff _).mpr ⟨n, hn, hs⟩
  have htB : t ∈ binarySequences V := (mem_binarySequences_iff _).mpr ⟨m, hm, ht⟩
  have hua := append_mem_binarySequences hk hu ha
  have hub := append_mem_binarySequences hk hu hb
  have hsa := scheme_tau_mono hR hτ hmono hp₀ hΦ hsB hua hus
  have htb := scheme_tau_mono hR hτ hmono hp₀ hΦ htB hub hut
  have := tau_isFunction hτ (scheme_mem hp₀ hΦ s hsB)
  have := tau_isFunction hτ (scheme_mem hp₀ hΦ t htB)
  have := tau_isFunction hτ (scheme_mem hp₀ hΦ _ hua)
  have := tau_isFunction hτ (scheme_mem hp₀ hΦ _ hub)
  have hinc : Incompatible (τ ‘ ((scheme p₀ Φ) ‘ (insert ⟨k, a⟩ₖ u)))
      (τ ‘ ((scheme p₀ Φ) ‘ (insert ⟨k, b⟩ₖ u))) := by
    rcases (mem_two_iff a).mp ha with rfl | rfl <;> rcases (mem_two_iff b).mp hb with rfl | rfl
    · exact (hab rfl).elim
    · exact scheme_children_incompatible hp₀ hΦ hk hu
    · exact incompatible_symm (scheme_children_incompatible hp₀ hΦ hk hu)
    · exact (hab rfl).elim
  exact incompatible_mono hinc hsa htb

end

end ZFVP
