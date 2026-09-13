import ZFVP.SetTheory.LevelCounting
import ZFVP.SetTheory.NaturalAdditionDefinable
import ZFVP.SetTheory.NaturalPredecessor
import ZFVP.SetTheory.NaturalPairing
import ZFVP.SetTheory.FiniteNaturalSets
import ZFVP.SetTheory.InternalChoice
import ZFVP.SetTheory.SequenceCollapseAbsorption
import ZFVP.SetTheory.PerfectSetCore

/-! Null sets in the coded sense: geometric subadditivity `Σ 2^{-(m+j+1)} ≤ 2^{-m}`, null sets from
finite small covers, and countable unions of null sets under internal choice. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem natural_mem_of_succ_mem_succ {n i : V} (hn : n ∈ (ω : V)) (h : succ i ∈ succ n) : i ∈ n := by
  have : IsOrdinal n := IsOrdinal.nat hn
  rcases mem_succ_iff.mp h with h | h
  · rw [← h]
    exact mem_succ_self i
  · exact IsOrdinal.toIsTransitive.mem_trans (mem_succ_self i) h

/-- Membership in the union of the values of a function on `N`. -/
theorem mem_sUnion_image_iff {g N : V} [IsFunction g] (hdom : N ⊆ domain g) (z : V) :
    z ∈ ⋃ˢ (g “ N) ↔ ∃ j ∈ N, z ∈ g ‘ j := by
  rw [mem_sUnion_iff]
  constructor
  · rintro ⟨y, hy, hz⟩
    obtain ⟨j, hj, hjy⟩ := (mem_image_iff' _ _ _).mp hy
    refine ⟨j, hj, ?_⟩
    rw [value_eq_of_kpair_mem hjy]
    exact hz
  · rintro ⟨j, hj, hz⟩
    exact ⟨g ‘ j, (mem_image_iff' _ _ _).mpr ⟨j, hj, kpair_value_mem (hdom j hj)⟩, hz⟩

theorem image_empty_eq (g : V) : g “ (∅ : V) = ∅ := by
  apply mem_ext
  intro y
  simp only [not_mem_empty, iff_false]
  intro hy
  obtain ⟨j, hj, -⟩ := (mem_image_iff' _ _ _).mp hy
  exact not_mem_empty hj

/-- The geometric union statement, as a predicate of the index bound. -/
def GeomSmall (N : V) : Prop :=
  ∀ m ∈ (ω : V), ∀ g ∈ (℘ (binarySequences V)) ^ (ω : V),
    (∀ j ∈ N, ∃ p, NatAddRel p m j ∧ SmallMeasure (g ‘ j) (succ p)) → SmallMeasure (⋃ˢ (g “ N)) m

instance geomSmall_definable : ℒₛₑₜ-predicate[V] GeomSmall := by
  unfold GeomSmall
  definability

theorem geomSmall_all : ∀ N ∈ (ω : V), GeomSmall N := by
  apply naturalNumber_induction GeomSmall (by definability)
  · intro m hm g _ _
    rw [zero_def, image_empty_eq, sUnion_empty_eq_empty]
    exact smallMeasure_empty m
  · intro N hN ih m hm g hg hpieces
    have : IsOrdinal N := IsOrdinal.nat hN
    have : IsOrdinal m := IsOrdinal.nat hm
    have hgf : IsFunction g := IsFunction.of_mem hg
    have hgdom : domain g = (ω : V) := domain_eq_of_mem_function hg
    obtain ⟨h, hhdef⟩ : ∃ h : V, h = definableGraph (ω : V) (fun j ↦ g ‘ (succ j)) (by definability) :=
      ⟨_, rfl⟩
    have hh : h ∈ (℘ (binarySequences V)) ^ (ω : V) := by
      rw [hhdef]
      exact definableGraph_mem_function_of_mapsTo _ _ _ _ (fun j hj ↦ function_value_mem hg (ω_succ_closed hj))
    have hhf : IsFunction h := IsFunction.of_mem hh
    have hhdom : domain h = (ω : V) := domain_eq_of_mem_function hh
    have hval : ∀ j ∈ (ω : V), h ‘ j = g ‘ (succ j) := by
      intro j hj
      rw [hhdef]
      exact value_definableGraph _ _ _ hj
    have hsplit : ⋃ˢ (g “ (succ N)) ⊆ g ‘ (∅ : V) ∪ ⋃ˢ (h “ N) := by
      intro z hz
      obtain ⟨j, hj, hzj⟩ := (mem_sUnion_image_iff (by rw [hgdom]; exact IsTransitive.ω.transitive _ (ω_succ_closed hN)) z).mp hz
      have hjω : j ∈ (ω : V) := IsTransitive.ω.transitive (succ N) (ω_succ_closed hN) j hj
      rcases internalNatural_cases hjω with rfl | ⟨i, hi, rfl⟩
      · exact mem_union_iff.mpr (Or.inl hzj)
      · refine mem_union_iff.mpr (Or.inr ((mem_sUnion_image_iff
          (by rw [hhdom]; exact IsTransitive.ω.transitive N hN) z).mpr
          ⟨i, natural_mem_of_succ_mem_succ hN hj, ?_⟩))
        rw [hval i hi]
        exact hzj
    have h0 : SmallMeasure (g ‘ (∅ : V)) (succ m) := by
      obtain ⟨p, ⟨-, -, hp⟩, hsmall⟩ := hpieces ∅ (zero_mem_succ_natural hN)
      rw [hp, ordinalAdd_zero] at hsmall
      exact hsmall
    have hrest : SmallMeasure (⋃ˢ (h “ N)) (succ m) := by
      refine ih (succ m) (ω_succ_closed hm) h hh ?_
      intro i hi
      have hiω : i ∈ (ω : V) := IsTransitive.ω.transitive N hN i hi
      have : IsOrdinal i := IsOrdinal.nat hiω
      obtain ⟨p, ⟨-, -, hp⟩, hsmall⟩ := hpieces (succ i) (succ_mem_succ_of_natural_mem hN hi)
      refine ⟨ordinalAdd (succ m) i, natAddRel_add (ω_succ_closed hm) hiω, ?_⟩
      rw [hval i hiω, ordinalAdd_succ_left_natural hm hiω, ← ordinalAdd_succ, ← hp]
      exact hsmall
    exact smallMeasure_mono_family (smallMeasure_union hm h0 hrest) hsplit

/-- Geometric subadditivity: pieces of measure `2^{-(m+j+1)}`, `j < N`, have union of measure at
most `2^{-m}`. -/
theorem smallMeasure_geometric_union {N m g : V} (hN : N ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hg : g ∈ (℘ (binarySequences V)) ^ (ω : V))
    (hpieces : ∀ j ∈ N, SmallMeasure (g ‘ j) (succ (ordinalAdd m j))) :
    SmallMeasure (⋃ˢ (g “ N)) m :=
  geomSmall_all N hN m hm g hg (fun j hj ↦
    ⟨ordinalAdd m j, natAddRel_add hm (IsTransitive.ω.transitive N hN j hj), hpieces j hj⟩)

/-- The zero sequence of length `m`. -/
noncomputable def zeroSequence (m : V) : V := m ×ˢ ({∅} : V)

theorem zeroSequence_mem_power (m : V) : zeroSequence m ∈ ((2 : ℕ) : V) ^ m := by
  rw [mem_function_iff]
  refine ⟨prod_subset_prod_of_subset (fun x hx ↦ hx) (fun x hx ↦ ?_), fun x hx ↦ ?_⟩
  · rw [mem_singleton_iff] at hx
    rw [hx]
    exact (mem_two_iff _).mpr (Or.inl rfl)
  · refine ⟨∅, kpair_mem_iff.mpr ⟨hx, mem_singleton_iff.mpr rfl⟩, fun y hy ↦ ?_⟩
    exact mem_singleton_iff.mp (kpair_mem_iff.mp hy).2

theorem zeroSequence_mem_binarySequences {m : V} (hm : m ∈ (ω : V)) : zeroSequence m ∈ binarySequences V :=
  (mem_binarySequences_iff _).mpr ⟨m, hm, zeroSequence_mem_power m⟩

theorem domain_zeroSequence (m : V) : domain (zeroSequence m) = m :=
  domain_eq_of_mem_function (zeroSequence_mem_power m)

theorem smallMeasure_singleton_zeroSequence {m : V} (hm : m ∈ (ω : V)) :
    SmallMeasure ({zeroSequence m} : V) m := by
  refine ⟨m, hm, fun s hs ↦ ?_, ?_⟩
  · rw [mem_singleton_iff] at hs
    rw [hs, domain_zeroSequence]
  · have hsh : shadow ({zeroSequence m} : V) m = {zeroSequence m} := by
      apply mem_ext
      intro t
      rw [mem_shadow_iff, mem_singleton_iff]
      constructor
      · rintro ⟨ht, s, hs, hst⟩
        rw [mem_singleton_iff] at hs
        rw [hs] at hst
        exact (sequence_eq_of_subset_of_domain_eq (zeroSequence_mem_power m) ht hst).symm
      · rintro rfl
        exact ⟨zeroSequence_mem_power m, _, mem_singleton_iff.mpr rfl, fun x hx ↦ hx⟩
    rw [hsh]
    refine cardLE_of_injective_map kpair.π₂ (by definability) ?_ ?_
    · intro z hz
      obtain ⟨a, -, b, hb, rfl⟩ := mem_prod_iff.mp hz
      rw [kpair.π₂_kpair]
      exact hb
    · intro z hz z' hz' h
      obtain ⟨a, ha, b, -, rfl⟩ := mem_prod_iff.mp hz
      obtain ⟨a', ha', b', -, rfl⟩ := mem_prod_iff.mp hz'
      rw [mem_singleton_iff] at ha ha'
      simp only [kpair.π₂_kpair] at h
      rw [ha, ha', h]

/-- A set covered, for each precision, by a finite family of small measure is null. -/
theorem isNull_of_small_covers {A : V}
    (hA : ∀ m ∈ (ω : V), ∃ F : V, F ⊆ binarySequences V ∧ IsInternallyFinite F ∧ SmallMeasure F m ∧
      ∀ x ∈ A, Meets F x) : IsNull A := by
  intro m hm
  obtain ⟨F, hFsub, hFfin, hFsmall, hFcov⟩ := hA m hm
  by_cases hne : ∃ s, s ∈ F
  · obtain ⟨s₀, hs₀⟩ := hne
    obtain ⟨n, hn, hFn⟩ := hFfin
    have hFω : F ≤# (ω : V) := hFn.le.trans (cardLE_of_subset (IsTransitive.ω.transitive n hn))
    obtain ⟨E, hE, hrange⟩ := exists_surjection_of_cardLE hFω hs₀
    have hEf : IsFunction E := IsFunction.of_mem hE
    refine ⟨E, mem_function_of_mem_function_of_subset hE hFsub, fun x hx ↦ ?_, fun k _ ↦ ?_⟩
    · obtain ⟨s, hs, hxs⟩ := hFcov x hx
      have hsr : s ∈ range E := by rw [hrange]; exact hs
      obtain ⟨i, hi⟩ := mem_range_iff.mp hsr
      refine ⟨i, by rw [← domain_eq_of_mem_function hE]; exact mem_domain_of_kpair_mem hi, ?_⟩
      rw [value_eq_of_kpair_mem hi]
      exact hxs
    · refine smallMeasure_mono_family hFsmall (fun s hs ↦ ?_)
      obtain ⟨i, -, hi⟩ := (mem_image_iff' _ _ _).mp hs
      have : s ∈ range E := mem_range_iff.mpr ⟨i, hi⟩
      rw [hrange] at this
      exact this
  · have hAempty : ∀ x, x ∉ A := fun x hx ↦ by
      obtain ⟨s, hs, -⟩ := hFcov x hx
      exact hne ⟨s, hs⟩
    obtain ⟨E, hEdef⟩ : ∃ E : V, E = definableGraph (ω : V) (fun _ ↦ zeroSequence m) (by definability) :=
      ⟨_, rfl⟩
    have hE : E ∈ (binarySequences V) ^ (ω : V) := by
      rw [hEdef]
      exact definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ _ ↦ zeroSequence_mem_binarySequences hm)
    refine ⟨E, hE, fun x hx ↦ (hAempty x hx).elim, fun k _ ↦ ?_⟩
    refine smallMeasure_mono_family (smallMeasure_singleton_zeroSequence hm) (fun s hs ↦ ?_)
    obtain ⟨i, hi, his⟩ := (mem_image_iff' _ _ _).mp hs
    have hiω : i ∈ (ω : V) := by
      have := mem_domain_of_kpair_mem his
      rw [domain_eq_of_mem_function hE] at this
      exact this
    have : IsFunction E := IsFunction.of_mem hE
    rw [mem_singleton_iff, ← value_eq_of_kpair_mem his, hEdef, value_definableGraph _ _ _ hiω]

theorem isNull_mono {A B : V} (hB : IsNull B) (hAB : A ⊆ B) : IsNull A := by
  intro m hm
  obtain ⟨f, hf, hcov, hsmall⟩ := hB m hm
  exact ⟨f, hf, fun x hx ↦ hcov x (hAB x hx), hsmall⟩

theorem isNull_empty : IsNull (∅ : V) :=
  isNull_of_small_covers (fun m _ ↦ ⟨∅, fun _ hs ↦ (not_mem_empty hs).elim, internallyFinite_empty,
    smallMeasure_empty m, fun _ hx ↦ (not_mem_empty hx).elim⟩)

/-- `f` is a cover of `B` at precision `p`. -/
def IsCoverAt (f B p : V) : Prop :=
  (∀ x ∈ B, ∃ i ∈ (ω : V), x ↾ (domain (f ‘ i)) = f ‘ i) ∧ ∀ k ∈ (ω : V), SmallMeasure (f “ k) p

instance isCoverAt_definable : ℒₛₑₜ-relation₃[V] IsCoverAt := by
  unfold IsCoverAt
  definability

/-- The covers of `A n` at precision `m + n + 1`. -/
noncomputable def coverSet (A m n : V) : V :=
  {f ∈ (binarySequences V) ^ (ω : V) ; IsCoverAt f (A ‘ n) (succ (ordinalAdd m n))}

instance coverSet_definable (A m : V) : ℒₛₑₜ-function₁[V] (coverSet A m) := by
  have h : ℒₛₑₜ-relation (fun C n : V ↦ ∀ f, f ∈ C ↔
      f ∈ (binarySequences V) ^ (ω : V) ∧ IsCoverAt f (A ‘ n) (succ (ordinalAdd m n))) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = coverSet A m (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [coverSet, mem_sep_iff]

theorem mem_coverSet_iff (A m n f : V) :
    f ∈ coverSet A m n ↔ f ∈ (binarySequences V) ^ (ω : V) ∧ IsCoverAt f (A ‘ n) (succ (ordinalAdd m n)) :=
  mem_sep_iff

theorem coverSet_nonempty {A m n : V} (hm : m ∈ (ω : V)) (hn : n ∈ (ω : V)) (hnull : IsNull (A ‘ n)) :
    IsNonempty (coverSet A m n) := by
  obtain ⟨f, hf, hcov, hsmall⟩ := hnull _ (ω_succ_closed (ordinalAdd_natural hm hn))
  exact ⟨f, (mem_coverSet_iff _ _ _ _).mpr ⟨hf, hcov, hsmall⟩⟩

/-- The graph relation of the combined cover: `k ↦ cov n i` when `k` codes `(n, i)`, and the first
element of the first cover otherwise. -/
def CombinedCoverRel (e cov p : V) : Prop :=
  (∃ n ∈ (ω : V), ∃ i ∈ (ω : V), ⟨⟨n, i⟩ₖ, kpair.π₁ p⟩ₖ ∈ e ∧ kpair.π₂ p = (cov ‘ n) ‘ i) ∨
    (kpair.π₁ p ∉ range e ∧ kpair.π₂ p = (cov ‘ ∅) ‘ ∅)

instance combinedCoverRel_definable (e cov : V) : ℒₛₑₜ-predicate[V] (CombinedCoverRel e cov) := by
  unfold CombinedCoverRel
  definability

/-- The graph relation of the pieces `n ↦ cov n “ K₀`. -/
def PieceRel (cov K₀ p : V) : Prop := kpair.π₂ p = image (cov ‘ (kpair.π₁ p)) K₀

instance pieceRel_definable (cov K₀ : V) : ℒₛₑₜ-predicate[V] (PieceRel cov K₀) := by
  unfold PieceRel
  definability

theorem valueMemPredicate_definable (e k : V) : ℒₛₑₜ-predicate (fun z : V ↦ e ‘ z ∈ k) := by
  definability

theorem valueMap_definable (e : V) : ℒₛₑₜ-function₁ (fun z : V ↦ e ‘ z) := by
  definability

theorem pi1_definable : ℒₛₑₜ-function₁ (kpair.π₁ : V → V) := by
  definability

theorem pi2_definable : ℒₛₑₜ-function₁ (kpair.π₂ : V → V) := by
  definability

/-- Combining a sequence of covers of precisions `m + n + 1` into one cover of precision `m`
whose values include all values of the pieces. -/
theorem exists_combined_cover {m cov : V} (hm : m ∈ (ω : V))
    (hcov : cov ∈ ((binarySequences V) ^ (ω : V)) ^ (ω : V))
    (hsmall : ∀ n ∈ (ω : V), ∀ k ∈ (ω : V), SmallMeasure ((cov ‘ n) “ k) (succ (ordinalAdd m n))) :
    ∃ f ∈ (binarySequences V) ^ (ω : V), (∀ k ∈ (ω : V), SmallMeasure (f “ k) m) ∧
      ∀ n ∈ (ω : V), ∀ i ∈ (ω : V), ∃ k ∈ (ω : V), f ‘ k = (cov ‘ n) ‘ i := by
  have : IsOrdinal m := IsOrdinal.nat hm
  have hcovf : ∀ n ∈ (ω : V), cov ‘ n ∈ (binarySequences V) ^ (ω : V) := fun n hn ↦ function_value_mem hcov hn
  have hvalmem : ∀ n ∈ (ω : V), ∀ i ∈ (ω : V), (cov ‘ n) ‘ i ∈ binarySequences V :=
    fun n hn i hi ↦ function_value_mem (hcovf n hn) hi
  -- pairing
  obtain ⟨e, he, heinj⟩ := omega_prod_cardLE_omega (V := V)
  have hef : IsFunction e := IsFunction.of_mem he
  have hedom : domain e = (ω : V) ×ˢ (ω : V) := domain_eq_of_mem_function he
  have hepair : ∀ n ∈ (ω : V), ∀ i ∈ (ω : V), ⟨⟨n, i⟩ₖ, e ‘ ⟨n, i⟩ₖ⟩ₖ ∈ e := fun n hn i hi ↦
    kpair_value_mem (by rw [hedom]; exact kpair_mem_iff.mpr ⟨hn, hi⟩)
  -- the combined cover as a set of pairs
  obtain ⟨f, hfdef⟩ : ∃ f : V, f = sep ((ω : V) ×ˢ binarySequences V) (CombinedCoverRel e cov)
    (combinedCoverRel_definable e cov) := ⟨_, rfl⟩
  have hfmem : ∀ k y, ⟨k, y⟩ₖ ∈ f ↔ k ∈ (ω : V) ∧ y ∈ binarySequences V ∧ CombinedCoverRel e cov ⟨k, y⟩ₖ := by
    intro k y
    rw [hfdef, mem_sep_iff, kpair_mem_iff, and_assoc]
  have hrel1 : ∀ n ∈ (ω : V), ∀ i ∈ (ω : V), CombinedCoverRel e cov ⟨e ‘ ⟨n, i⟩ₖ, (cov ‘ n) ‘ i⟩ₖ := by
    intro n hn i hi
    left
    refine ⟨n, hn, i, hi, ?_, ?_⟩
    · rw [kpair.π₁_kpair]; exact hepair n hn i hi
    · rw [kpair.π₂_kpair]
  have hrel2 : ∀ k, k ∉ range e → CombinedCoverRel e cov ⟨k, (cov ‘ ∅) ‘ ∅⟩ₖ := by
    intro k hk
    right
    refine ⟨?_, ?_⟩
    · rw [kpair.π₁_kpair]; exact hk
    · rw [kpair.π₂_kpair]
  have huniq : ∀ k y y', CombinedCoverRel e cov ⟨k, y⟩ₖ → CombinedCoverRel e cov ⟨k, y'⟩ₖ → y = y' := by
    intro k y y' h1 h2
    rcases h1 with ⟨n, hn, i, hi, hp, hy⟩ | ⟨hk, hy⟩ <;> rcases h2 with ⟨n', hn', i', hi', hp', hy'⟩ | ⟨hk', hy'⟩
    · rw [kpair.π₁_kpair] at hp hp'
      rw [kpair.π₂_kpair] at hy hy'
      have := heinj _ _ _ hp hp'
      obtain ⟨rfl, rfl⟩ := kpair_inj this
      rw [hy, hy']
    · rw [kpair.π₁_kpair] at hp hk'
      exact (hk' (mem_range_iff.mpr ⟨_, hp⟩)).elim
    · rw [kpair.π₁_kpair] at hp' hk
      exact (hk (mem_range_iff.mpr ⟨_, hp'⟩)).elim
    · rw [kpair.π₂_kpair] at hy hy'
      rw [hy, hy']
  have hf : f ∈ (binarySequences V) ^ (ω : V) := by
    rw [mem_function_iff]
    refine ⟨fun p hp ↦ by rw [hfdef] at hp; exact (mem_sep_iff.mp hp).1, fun k hk ↦ ?_⟩
    by_cases hkr : k ∈ range e
    · obtain ⟨z, hz⟩ := mem_range_iff.mp hkr
      have hzd : z ∈ domain e := mem_domain_of_kpair_mem hz
      rw [hedom] at hzd
      obtain ⟨n, hn, i, hi, rfl⟩ := mem_prod_iff.mp hzd
      have hke : k = e ‘ ⟨n, i⟩ₖ := (value_eq_of_kpair_mem hz).symm
      refine ⟨(cov ‘ n) ‘ i, (hfmem _ _).mpr ⟨hk, hvalmem n hn i hi, by rw [hke]; exact hrel1 n hn i hi⟩,
        fun y hy ↦ ?_⟩
      exact huniq k _ _ ((hfmem _ _).mp hy).2.2 (by rw [hke]; exact hrel1 n hn i hi)
    · refine ⟨(cov ‘ ∅) ‘ ∅, (hfmem _ _).mpr ⟨hk, hvalmem ∅ zero_mem_ω ∅ zero_mem_ω, hrel2 k hkr⟩,
        fun y hy ↦ ?_⟩
      exact huniq k _ _ ((hfmem _ _).mp hy).2.2 (hrel2 k hkr)
  have hff : IsFunction f := IsFunction.of_mem hf
  have hF1 : ∀ n ∈ (ω : V), ∀ i ∈ (ω : V), f ‘ (e ‘ ⟨n, i⟩ₖ) = (cov ‘ n) ‘ i := by
    intro n hn i hi
    apply value_eq_of_kpair_mem
    exact (hfmem _ _).mpr ⟨function_value_mem he (kpair_mem_iff.mpr ⟨hn, hi⟩), hvalmem n hn i hi, hrel1 n hn i hi⟩
  have hF2 : ∀ k ∈ (ω : V), k ∉ range e → f ‘ k = (cov ‘ ∅) ‘ ∅ := by
    intro k hk hkr
    apply value_eq_of_kpair_mem
    exact (hfmem _ _).mpr ⟨hk, hvalmem ∅ zero_mem_ω ∅ zero_mem_ω, hrel2 k hkr⟩
  refine ⟨f, hf, fun k hk ↦ ?_, fun n hn i hi ↦ ⟨e ‘ ⟨n, i⟩ₖ,
    function_value_mem he (kpair_mem_iff.mpr ⟨hn, hi⟩), hF1 n hn i hi⟩⟩
  -- the finitely many pairs coded below `k`
  obtain ⟨P, hPdef⟩ : ∃ P : V, P = sep ((ω : V) ×ˢ (ω : V)) (fun z ↦ e ‘ z ∈ k) (valueMemPredicate_definable e k) := ⟨_, rfl⟩
  have hPmem : ∀ z, z ∈ P ↔ z ∈ (ω : V) ×ˢ (ω : V) ∧ e ‘ z ∈ k := by
    intro z
    rw [hPdef]
    exact mem_sep_iff
  have hPfin : IsInternallyFinite P := by
    refine internallyFinite_of_cardLE_natural hk (cardLE_of_injective_map (fun z ↦ e ‘ z) (valueMap_definable e)
      (fun z hz ↦ ((hPmem z).mp hz).2) ?_)
    intro z hz z' hz' h
    have hzd : z ∈ domain e := by rw [hedom]; exact ((hPmem z).mp hz).1
    have hz'd : z' ∈ domain e := by rw [hedom]; exact ((hPmem z').mp hz').1
    exact heinj z z' _ (kpair_value_mem hzd) (h ▸ kpair_value_mem hz'd)
  have hN₁ : IsInternallyFinite (repl kpair.π₁ pi1_definable P) := internallyFinite_repl _ _ hPfin
  have hK₁ : IsInternallyFinite (repl kpair.π₂ pi2_definable P) := internallyFinite_repl _ _ hPfin
  obtain ⟨N₀', hN₀', hN₁sub⟩ := internallyFinite_naturals_bounded hN₁ (fun x hx ↦ by
    obtain ⟨z, hz, rfl⟩ := (repl_spec pi1_definable).mp hx
    obtain ⟨n, hn, i, -, rfl⟩ := mem_prod_iff.mp ((hPmem z).mp hz).1
    rw [kpair.π₁_kpair]
    exact hn)
  obtain ⟨K₀', hK₀', hK₁sub⟩ := internallyFinite_naturals_bounded hK₁ (fun x hx ↦ by
    obtain ⟨z, hz, rfl⟩ := (repl_spec pi2_definable).mp hx
    obtain ⟨n, -, i, hi, rfl⟩ := mem_prod_iff.mp ((hPmem z).mp hz).1
    rw [kpair.π₂_kpair]
    exact hi)
  obtain ⟨N₀, hN₀def⟩ : ∃ N₀ : V, N₀ = succ N₀' := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀def⟩ : ∃ K₀ : V, K₀ = succ K₀' := ⟨_, rfl⟩
  have hN₀ : N₀ ∈ (ω : V) := by rw [hN₀def]; exact ω_succ_closed hN₀'
  have hK₀ : K₀ ∈ (ω : V) := by rw [hK₀def]; exact ω_succ_closed hK₀'
  have h0N₀ : (∅ : V) ∈ N₀ := by rw [hN₀def]; exact zero_mem_succ_natural hN₀'
  have h0K₀ : (∅ : V) ∈ K₀ := by rw [hK₀def]; exact zero_mem_succ_natural hK₀'
  -- the pieces
  obtain ⟨g, hgdef⟩ : ∃ g : V, g = sep ((ω : V) ×ˢ ℘ (binarySequences V)) (PieceRel cov K₀) (pieceRel_definable cov K₀) := ⟨_, rfl⟩
  have hgmem : ∀ n y, ⟨n, y⟩ₖ ∈ g ↔ n ∈ (ω : V) ∧ y ⊆ binarySequences V ∧ y = image (cov ‘ n) K₀ := by
    intro n y
    rw [hgdef, mem_sep_iff, kpair_mem_iff, mem_power_iff, and_assoc]
    unfold PieceRel
    rw [kpair.π₁_kpair, kpair.π₂_kpair]
  have himgsub : ∀ n ∈ (ω : V), image (cov ‘ n) K₀ ⊆ binarySequences V := by
    intro n hn s hs
    obtain ⟨i, -, hi⟩ := (mem_image_iff' _ _ _).mp hs
    exact range_subset_of_mem_function (hcovf n hn) s (mem_range_iff.mpr ⟨i, hi⟩)
  have hg : g ∈ (℘ (binarySequences V)) ^ (ω : V) := by
    rw [mem_function_iff]
    refine ⟨fun p hp ↦ by rw [hgdef] at hp; exact (mem_sep_iff.mp hp).1, fun n hn ↦ ?_⟩
    refine ⟨image (cov ‘ n) K₀, (hgmem _ _).mpr ⟨hn, himgsub n hn, rfl⟩, fun y hy ↦ ?_⟩
    exact ((hgmem _ _).mp hy).2.2
  have hgf : IsFunction g := IsFunction.of_mem hg
  have hgdom : domain g = (ω : V) := domain_eq_of_mem_function hg
  have hgval : ∀ n ∈ (ω : V), g ‘ n = image (cov ‘ n) K₀ := by
    intro n hn
    apply value_eq_of_kpair_mem
    exact (hgmem _ _).mpr ⟨hn, himgsub n hn, rfl⟩
  have hgsmall : SmallMeasure (⋃ˢ (g “ N₀)) m := by
    refine smallMeasure_geometric_union hN₀ hm hg (fun j hj ↦ ?_)
    have hjω : j ∈ (ω : V) := IsTransitive.ω.transitive N₀ hN₀ j hj
    rw [hgval j hjω]
    exact hsmall j hjω K₀ hK₀
  refine smallMeasure_mono_family hgsmall (fun s hs ↦ ?_)
  obtain ⟨k', hk'k, hk's⟩ := (mem_image_iff' _ _ _).mp hs
  have hk'ω : k' ∈ (ω : V) := IsTransitive.ω.transitive k hk k' hk'k
  have hs' : s = f ‘ k' := (value_eq_of_kpair_mem hk's).symm
  rw [mem_sUnion_image_iff (by rw [hgdom]; exact IsTransitive.ω.transitive N₀ hN₀)]
  by_cases hkr : k' ∈ range e
  · obtain ⟨z, hz⟩ := mem_range_iff.mp hkr
    have hzd : z ∈ domain e := mem_domain_of_kpair_mem hz
    rw [hedom] at hzd
    obtain ⟨n, hn, i, hi, rfl⟩ := mem_prod_iff.mp hzd
    have hzP : ⟨n, i⟩ₖ ∈ P := (hPmem _).mpr ⟨kpair_mem_iff.mpr ⟨hn, hi⟩, by
      rw [value_eq_of_kpair_mem hz]; exact hk'k⟩
    have hnN : n ∈ N₀ := by
      rw [hN₀def]
      exact mem_succ_iff.mpr (Or.inr (hN₁sub _ ((repl_spec pi1_definable).mpr
        ⟨_, hzP, (kpair.π₁_kpair n i).symm⟩)))
    have hiK : i ∈ K₀ := by
      rw [hK₀def]
      exact mem_succ_iff.mpr (Or.inr (hK₁sub _ ((repl_spec pi2_definable).mpr
        ⟨_, hzP, (kpair.π₂_kpair n i).symm⟩)))
    refine ⟨n, hnN, ?_⟩
    rw [hgval n hn, hs', ← value_eq_of_kpair_mem hz, hF1 n hn i hi]
    have : IsFunction (cov ‘ n) := IsFunction.of_mem (hcovf n hn)
    exact (mem_image_iff' _ _ _).mpr ⟨i, hiK, kpair_value_mem (by
      rw [domain_eq_of_mem_function (hcovf n hn)]; exact hi)⟩
  · refine ⟨∅, h0N₀, ?_⟩
    rw [hgval ∅ zero_mem_ω, hs', hF2 k' hk'ω hkr]
    have : IsFunction (cov ‘ ∅) := IsFunction.of_mem (hcovf ∅ zero_mem_ω)
    exact (mem_image_iff' _ _ _).mpr ⟨∅, h0K₀, kpair_value_mem (by
      rw [domain_eq_of_mem_function (hcovf ∅ zero_mem_ω)]; exact zero_mem_ω)⟩

theorem coverGraph_definable (c A m : V) : ℒₛₑₜ-function₁ (fun n : V ↦ c ‘ (coverSet A m n)) := by
  definability

/-- Countable unions of null sets are null, given internal choice. -/
theorem isNull_sUnion_range (hAC : InternalChoice V) {A : V} [IsFunction A] (hdom : domain A = (ω : V))
    (hnull : ∀ n ∈ (ω : V), IsNull (A ‘ n)) : IsNull (⋃ˢ range A) := by
  intro m hm
  -- choose covers
  obtain ⟨𝒮, h𝒮⟩ : ∃ S : V, S = repl (coverSet A m) (coverSet_definable A m) (ω : V) := ⟨_, rfl⟩
  have hmem𝒮 : ∀ X, X ∈ 𝒮 ↔ ∃ n ∈ (ω : V), X = coverSet A m n := by
    intro X
    rw [h𝒮]
    exact repl_spec (coverSet_definable A m)
  obtain ⟨c, -, hcval⟩ := hAC 𝒮 (fun X hX ↦ by
    obtain ⟨n, hn, rfl⟩ := (hmem𝒮 X).mp hX
    exact coverSet_nonempty hm hn (hnull n hn))
  have hcov : ∀ n ∈ (ω : V), c ‘ (coverSet A m n) ∈ coverSet A m n := fun n hn ↦
    hcval _ ((hmem𝒮 _).mpr ⟨n, hn, rfl⟩)
  obtain ⟨cov, hcovdef⟩ : ∃ cov : V, cov = definableGraph (ω : V) (fun n ↦ c ‘ (coverSet A m n))
    (coverGraph_definable c A m) := ⟨_, rfl⟩
  have hcovval : ∀ n ∈ (ω : V), cov ‘ n = c ‘ (coverSet A m n) := by
    intro n hn
    rw [hcovdef]
    exact value_definableGraph _ _ _ hn
  have hcovmem : cov ∈ ((binarySequences V) ^ (ω : V)) ^ (ω : V) := by
    rw [hcovdef]
    exact definableGraph_mem_function_of_mapsTo _ _ _ _ (fun n hn ↦ ((mem_coverSet_iff _ _ _ _).mp (hcov n hn)).1)
  have hcovat : ∀ n ∈ (ω : V), IsCoverAt (cov ‘ n) (A ‘ n) (succ (ordinalAdd m n)) := by
    intro n hn
    rw [hcovval n hn]
    exact ((mem_coverSet_iff _ _ _ _).mp (hcov n hn)).2
  obtain ⟨f, hf, hfsmall, hfval⟩ := exists_combined_cover hm hcovmem (fun n hn k hk ↦ (hcovat n hn).2 k hk)
  refine ⟨f, hf, fun x hx ↦ ?_, hfsmall⟩
  obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
  obtain ⟨n, hn⟩ := mem_range_iff.mp hy
  have hnω : n ∈ (ω : V) := by rw [← hdom]; exact mem_domain_of_kpair_mem hn
  rw [← value_eq_of_kpair_mem hn] at hxy
  obtain ⟨i, hi, hxi⟩ := (hcovat n hnω).1 x hxy
  obtain ⟨k, hk, hfk⟩ := hfval n hnω i hi
  refine ⟨k, hk, ?_⟩
  rw [hfk]
  exact hxi

end ZFVP
