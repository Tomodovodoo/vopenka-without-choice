import ZFVP.SetTheory.UltrapowerClosure
import ZFVP.SetTheory.UltrapowerEmbeddingMap

/-! # Rank stages of size at most `lam` sit inside the ultrapower target

The target `ultraTarget P U A` of the internal ultrapower by a normal fine measure on
`P_κ(lam)` contains every subset of itself of size at most `lam`
(`mem_ultraTarget_of_subset_cardLE`). Two consequences are recorded here.

The first is that a rank stage `hierarchy γ` of size at most `lam` is a subset of the target. The
proof is one membership induction on the stage: a member `x` of `hierarchy γ` is a subset of it, so
the induction hypothesis puts `x` inside the target, and `x` inherits the size bound, so `x` itself
is a member of the target.

The second is that the restriction of the canonical map to such a stage is a member of the target.
The restriction is a set of Kuratowski pairs `⟨x, j ‘ x⟩ₖ`. Both components lie in the target, and
the target is closed under pairing because a doubleton of members is a nonempty subset of size two,
which is at most `lam` once `ω ⊆ lam`. The restriction is then a subset of the target injecting
into `hierarchy γ` by first projection, so the size bound applies to it too.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Two-element sets -/

private theorem singleton_cardLE_singleton (a b : V) : ({a} : V) ≤# ({b} : V) := by
  have h := cardLE_insert_fresh (A := (∅ : V)) (B := (∅ : V)) (a := a) (b := b)
    (CardLE.refl _) (by simp) (by simp)
  simpa using h

private theorem doubleton_self_eq (a : V) : ({a, a} : V) = ({a} : V) := by
  apply mem_ext
  intro z
  simp

/-- A doubleton has at most the size of any doubleton with two distinct entries. -/
private theorem doubleton_cardLE_doubleton {a b p q : V} (hpq : p ≠ q) :
    ({a, b} : V) ≤# ({p, q} : V) := by
  by_cases hab : a = b
  · subst hab
    rw [doubleton_self_eq]
    refine CardLE.trans (singleton_cardLE_singleton a p) (cardLE_of_subset ?_)
    intro z hz
    rw [mem_singleton_iff] at hz
    simp [hz]
  · exact cardLE_insert_fresh (singleton_cardLE_singleton b q)
      (by simpa using hab) (by simpa using hpq)

/-! ### The target is closed under pairing -/

/-- Two members of the target form a Kuratowski pair inside the target. This needs `ω ⊆ lam`,
which is where the hypothesis `κ ⊆ lam` is used. -/
theorem kpair_mem_ultraTarget (hAC : InternalChoice V) {P U A κ lam a b : V} [IsOrdinal κ]
    [IsTransitive A] (hU : IsNormalFineMeasure κ lam U)
    (hP : P = smallSubsetsBelow κ lam) (hcomp : IsOrdinalCompleteOn P κ U) (hω : (ω : V) ∈ κ)
    (hA : IsNonempty A) (hsmall : ∀ w, w ⊆ A → USmall κ w → w ∈ A) (h0 : (∅ : V) ∈ lam)
    (hκlam : κ ⊆ lam) (ha : a ∈ ultraTarget P U A) (hb : b ∈ ultraTarget P U A) :
    ⟨a, b⟩ₖ ∈ ultraTarget P U A := by
  have hωlam : (ω : V) ∈ lam := hκlam _ hω
  have hne0 : (∅ : V) ≠ (ω : V) := by
    intro h
    exact mem_irrefl (∅ : V) (by simpa [← h] using (empty_mem_ω : (∅ : V) ∈ (ω : V)))
  have hsub2 : ({(∅ : V), (ω : V)} : V) ⊆ lam := by
    intro z hz
    rcases show z = (∅ : V) ∨ z = (ω : V) by simpa using hz with rfl | rfl
    · exact h0
    · exact hωlam
  have hcard2 : ∀ u v : V, ({u, v} : V) ≤# lam := fun u v ↦
    CardLE.trans (doubleton_cardLE_doubleton hne0) (cardLE_of_subset hsub2)
  have hstep : ∀ u v : V, u ∈ ultraTarget P U A → v ∈ ultraTarget P U A →
      ({u, v} : V) ∈ ultraTarget P U A := by
    intro u v hu hv
    refine mem_ultraTarget_of_subset_cardLE hAC hU hP hcomp hω hA hsmall h0 ?_
      ⟨⟨u, by simp⟩⟩ (hcard2 u v)
    intro z hz
    rcases show z = u ∨ z = v by simpa using hz with rfl | rfl
    · exact hu
    · exact hv
  have hsa : ({a} : V) ∈ ultraTarget P U A := by
    have := hstep a a ha ha
    rwa [doubleton_self_eq] at this
  have hsab : ({a, b} : V) ∈ ultraTarget P U A := hstep a b ha hb
  have : ({{a}, {a, b}} : V) ∈ ultraTarget P U A := hstep _ _ hsa hsab
  simpa [kpair] using this

/-! ### Rank stages inside the target -/

/-- A rank stage no larger than `lam` is contained in the ultrapower target. -/
theorem hierarchy_subset_ultraTarget (hAC : InternalChoice V) {P U A κ lam γ : V} [IsOrdinal κ]
    [IsOrdinal γ] [IsTransitive A] (hU : IsNormalFineMeasure κ lam U)
    (hP : P = smallSubsetsBelow κ lam) (hcomp : IsOrdinalCompleteOn P κ U) (hω : (ω : V) ∈ κ)
    (hA : IsNonempty A) (hsmall : ∀ w, w ⊆ A → USmall κ w → w ∈ A) (h0 : (∅ : V) ∈ lam)
    (hcard : hierarchy γ ≤# lam) (hempty : (∅ : V) ∈ ultraTarget P U A) :
    hierarchy γ ⊆ ultraTarget P U A := by
  have hΦ : ℒₛₑₜ-predicate[V] (fun x ↦ x ∈ ultraTarget P U A) := by
    have hd : ℒₛₑₜ-predicate[V] (fun x ↦ ∃ M, M = ultraTarget P U A ∧ x ∈ M) := by definability
    apply Language.Definable.of_iff hd
    intro v
    change (v 0) ∈ ultraTarget P U A ↔ _
    exact ⟨fun h ↦ ⟨_, rfl, h⟩, fun ⟨M, hM, h⟩ ↦ hM ▸ h⟩
  intro x hx
  refine internalWellFounded_induction (membershipRelation_wellFounded (hierarchy γ)) _ hΦ ?_ x hx
  clear hx x
  intro x hxγ ih
  have hxsub : x ⊆ hierarchy γ := (hierarchy_transitive γ).transitive x hxγ
  have hxM : x ⊆ ultraTarget P U A := by
    intro y hy
    exact ih y (hxsub y hy)
      ((pair_mem_membershipRelation _ y x).mpr ⟨hxsub y hy, hxγ, hy⟩)
  by_cases hne : IsNonempty x
  · exact mem_ultraTarget_of_subset_cardLE hAC hU hP hcomp hω hA hsmall h0 hxM hne
      (CardLE.trans (cardLE_of_subset hxsub) hcard)
  · have hxe : x = (∅ : V) := by
      apply mem_ext
      intro z
      rw [not_isNonempty_iff_isEmpty] at hne
      simp only [not_mem_empty, iff_false]
      exact hne z
    rw [hxe]
    exact hempty

/-! ### The restricted canonical map -/

/-- The restriction of the canonical map to a rank stage of size at most `lam` is a member of the
ultrapower target. -/
theorem restrict_mem_ultraTarget (hAC : InternalChoice V) {P U A κ lam γ : V} [IsOrdinal κ]
    [IsOrdinal γ] [IsTransitive A] (hU : IsNormalFineMeasure κ lam U)
    (hP : P = smallSubsetsBelow κ lam) (hcomp : IsOrdinalCompleteOn P κ U) (hω : (ω : V) ∈ κ)
    (hA : IsNonempty A) (hsmall : ∀ w, w ⊆ A → USmall κ w → w ∈ A) (h0 : (∅ : V) ∈ lam)
    (hκlam : κ ⊆ lam) (hγA : hierarchy γ ⊆ A) (hcard : hierarchy γ ≤# lam)
    (hempty : (∅ : V) ∈ ultraTarget P U A) :
    (ultraEmbedding P U A) ↾ (hierarchy γ) ∈ ultraTarget P U A := by
  have hstage : hierarchy γ ⊆ ultraTarget P U A :=
    hierarchy_subset_ultraTarget hAC hU hP hcomp hω hA hsmall h0 hcard hempty
  have hUf : IsSetUltrafilter P U := hP ▸ hU.1
  have hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P) := by
    subst hP
    exact ultraMemRelation_wellFounded hAC hUf hcomp hω
  have hjmem : ultraEmbedding P U A ∈ (ultraTarget P U A) ^ A := ultraEmbedding_mem_function hwf
  set j : V := ultraEmbedding P U A with hjdef
  -- every member of the restriction is a pair of members of the target
  have hsub : (j ↾ (hierarchy γ)) ⊆ ultraTarget P U A := by
    intro p hp
    obtain ⟨hpj, x, hxγ, y, rfl⟩ := mem_restrict_iff.mp hp
    have hyv : j ‘ x = y := value_eq_of_kpair_mem hpj
    have hyM : y ∈ ultraTarget P U A := by
      rw [← hyv]
      exact function_value_mem hjmem (hγA x hxγ)
    exact kpair_mem_ultraTarget hAC hU hP hcomp hω hA hsmall h0 hκlam (hstage x hxγ) hyM
  -- the first projection injects the restriction into the stage
  have hcardr : (j ↾ (hierarchy γ)) ≤# lam := by
    refine CardLE.trans (cardLE_of_injective_map kpair.π₁ (by definability) ?_ ?_) hcard
    · intro p hp
      obtain ⟨-, x, hxγ, y, rfl⟩ := mem_restrict_iff.mp hp
      simpa using hxγ
    · intro p hp q hq hpq
      obtain ⟨hpj, x, -, y, rfl⟩ := mem_restrict_iff.mp hp
      obtain ⟨hqj, x', -, y', rfl⟩ := mem_restrict_iff.mp hq
      simp only [kpair.π₁_kpair] at hpq
      subst hpq
      rw [← value_eq_of_kpair_mem hpj, ← value_eq_of_kpair_mem hqj]
  by_cases hne : IsNonempty (j ↾ (hierarchy γ))
  · exact mem_ultraTarget_of_subset_cardLE hAC hU hP hcomp hω hA hsmall h0 hsub hne hcardr
  · have he : (j ↾ (hierarchy γ)) = (∅ : V) := by
      apply mem_ext
      intro z
      rw [not_isNonempty_iff_isEmpty] at hne
      simp only [not_mem_empty, iff_false]
      exact hne z
    rw [he]
    exact hempty

end ZFVP
