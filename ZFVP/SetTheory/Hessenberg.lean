import ZFVP.SetTheory.PulledWellOrder
import ZFVP.SetTheory.WellOrderedProducts
import ZFVP.SetTheory.WellOrderedCardinal
import ZFVP.SetTheory.UltrafilterOrdinals
import ZFVP.SetTheory.NaturalPairing
import ZFVP.SetTheory.NaturalPigeonhole
import ZFVP.SetTheory.TransitiveClosure

/-! Hessenberg's theorem: `α × α ≤# α ∪ ω` for every ordinal `α`, hence `λ × λ ≋ λ` for every
infinite initial ordinal `λ`. The proof is by internal `∈`-induction using the Gödel pairing order,
pulled back from the lexicographic order on `⟨max(a, b), a, b⟩`: an initial segment of the Gödel
order sits inside `(μ + 1) × (μ + 1)` for some `μ < λ`, so the order type of `λ × λ` cannot exceed
`λ`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinal_union_eq (a b : V) [IsOrdinal a] [IsOrdinal b] : a ∪ b = a ∨ a ∪ b = b := by
  rcases IsOrdinal.subset_or_supset (α := a) (β := b) with h | h
  · exact Or.inr (union_eq_iff_left.mpr h)
  · exact Or.inl (union_eq_iff_right.mpr h)

theorem ordinal_union_isOrdinal (a b : V) [IsOrdinal a] [IsOrdinal b] : IsOrdinal (a ∪ b) := by
  rcases ordinal_union_eq a b with h | h <;> rw [h] <;> infer_instance

theorem union_mem_of_ordinals {a b lam : V} [IsOrdinal a] [IsOrdinal b] (ha : a ∈ lam) (hb : b ∈ lam) :
    a ∪ b ∈ lam := by
  rcases ordinal_union_eq a b with h | h <;> rw [h] <;> assumption

theorem omega_not_cardLE_natural {n : V} (hn : n ∈ (ω : V)) : ¬(ω : V) ≤# n := by
  intro h
  have hs : succ n ⊆ (ω : V) := IsOrdinal.toIsTransitive.transitive _ (ω_succ_closed hn)
  exact not_succ_cardLE_self hn ((cardLE_of_subset hs).trans h)

/-- The Gödel coding map `⟨a, b⟩ ↦ ⟨⟨a ∪ b, a⟩, b⟩`. -/
noncomputable def godelCode (p : V) : V :=
  ⟨⟨kpair.π₁ p ∪ kpair.π₂ p, kpair.π₁ p⟩ₖ, kpair.π₂ p⟩ₖ

theorem godelCode_definable : ℒₛₑₜ-function₁[V] godelCode := by
  unfold godelCode
  definability

theorem godelCode_kpair (a b : V) : godelCode ⟨a, b⟩ₖ = ⟨⟨a ∪ b, a⟩ₖ, b⟩ₖ := by
  simp [godelCode]

/-- The lexicographic order on `⟨max, a, b⟩` over the ordinal `α`. -/
noncomputable def godelTarget (α : V) : V :=
  lexicographicRelation (α ×ˢ α) α
    (lexicographicRelation α α (membershipRelation α) (membershipRelation α)) (membershipRelation α)

/-- The Gödel well-order on `α ×ˢ α`. -/
noncomputable def godelOrder (α : V) : V :=
  pulledRelation (α ×ˢ α) godelCode godelCode_definable (godelTarget α)

theorem godelOrder_wellOrder (α : V) [IsOrdinal α] : IsInternalWellOrder (godelOrder α) (α ×ˢ α) := by
  apply pulledRelation_wellOrder godelCode godelCode_definable
  · exact lexicographicRelation_wellOrder
      (lexicographicRelation_wellOrder (ordinal_membership_wellOrder α) (ordinal_membership_wellOrder α))
      (ordinal_membership_wellOrder α)
  · intro p hp
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hp
    have : IsOrdinal a := IsOrdinal.of_mem ha
    have : IsOrdinal b := IsOrdinal.of_mem hb
    rw [godelCode_kpair]
    exact kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨union_mem_of_ordinals ha hb, ha⟩, hb⟩
  · intro p hp q hq h
    obtain ⟨a, _, b, _, rfl⟩ := mem_prod_iff.mp hp
    obtain ⟨c, _, d, _, rfl⟩ := mem_prod_iff.mp hq
    rw [godelCode_kpair, godelCode_kpair] at h
    obtain ⟨h1, rfl⟩ := kpair_iff.mp h
    obtain ⟨_, rfl⟩ := kpair_iff.mp h1
    rfl

/-- A predecessor of `⟨a, b⟩` in the Gödel order has both coordinates in `succ (a ∪ b)`. -/
theorem godelOrder_pred_mem {α a b c d : V} [IsOrdinal α] (ha : a ∈ α) (hb : b ∈ α)
    (hc : c ∈ α) (hd : d ∈ α) (h : ⟨⟨c, d⟩ₖ, ⟨a, b⟩ₖ⟩ₖ ∈ godelOrder α) :
    c ∈ succ (a ∪ b) ∧ d ∈ succ (a ∪ b) := by
  have : IsOrdinal a := IsOrdinal.of_mem ha
  have : IsOrdinal b := IsOrdinal.of_mem hb
  have : IsOrdinal c := IsOrdinal.of_mem hc
  have : IsOrdinal d := IsOrdinal.of_mem hd
  have hab : IsOrdinal (a ∪ b) := ordinal_union_isOrdinal a b
  have hcd : IsOrdinal (c ∪ d) := ordinal_union_isOrdinal c d
  obtain ⟨_, _, hlex⟩ := (pair_mem_pulledRelation_iff _ _ _ _ _ _).mp h
  rw [godelCode_kpair, godelCode_kpair] at hlex
  obtain ⟨_, _, hlex⟩ := (pair_mem_lexicographicRelation _ _ _ _ _ _).mp hlex
  simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hlex
  -- in every case `c ∪ d ⊆ a ∪ b`
  have hsub : c ∪ d ⊆ a ∪ b := by
    rcases hlex with hlex | ⟨heq, _⟩
    · obtain ⟨_, _, hlex⟩ := (pair_mem_lexicographicRelation _ _ _ _ _ _).mp hlex
      simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hlex
      rcases hlex with hmem | ⟨heq, _⟩
      · obtain ⟨_, _, hmem⟩ := (pair_mem_membershipRelation _ _ _).mp hmem
        exact IsOrdinal.toIsTransitive.transitive _ hmem
      · rw [heq]
    · rw [(kpair_iff.mp heq).1]
  have hcsub : c ⊆ a ∪ b := fun z hz ↦ hsub z (subset_union_left c d z hz)
  have hdsub : d ⊆ a ∪ b := fun z hz ↦ hsub z (subset_union_right c d z hz)
  constructor
  · rcases IsOrdinal.subset_iff.mp hcsub with h | h
    · exact mem_succ_iff.mpr (Or.inl h)
    · exact mem_succ_iff.mpr (Or.inr h)
  · rcases IsOrdinal.subset_iff.mp hdsub with h | h
    · exact mem_succ_iff.mpr (Or.inl h)
    · exact mem_succ_iff.mpr (Or.inr h)

/-- The range of an injective function restricted to a subset of its domain injects into that subset. -/
theorem range_restrict_cardLE {f D I : V} (hf : IsFunction f) (hinj : Injective f)
    (hD : domain f = D) (hI : I ⊆ D) : range (f ↾ I) ≤# I := by
  have hdom : domain (f ↾ I) = I := by
    rw [domain_restrict_eq, hD]
    apply mem_ext
    intro z
    simp only [mem_inter_iff]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hI z h, h⟩⟩
  have hfun : f ↾ I ∈ range (f ↾ I) ^ I := by
    have := IsFunction.mem_function (f ↾ I)
    rwa [hdom] at this
  have hinj' : Injective (f ↾ I) := by
    intro x y z hx hy
    exact hinj x y z (restrict_subset f I _ hx) (restrict_subset f I _ hy)
  exact ⟨converseGraph (f ↾ I), converseGraph_mem_function hfun hinj', converseGraph_injective _⟩

/-- Hessenberg's theorem in the form `λ × λ ≤# λ` for initial `λ` with `ω ∈ λ`, given the
inductive hypothesis for products of smaller ordinals. -/
theorem initial_prod_cardLE_of_ih {lam : V} (hlam : IsInitialOrdinal lam) (hω : (ω : V) ∈ lam)
    (ih : ∀ μ ∈ lam, μ ×ˢ μ ≤# μ ∪ (ω : V)) : lam ×ˢ lam ≤# lam := by
  have : IsOrdinal lam := hlam.1
  have hωsub : (ω : V) ⊆ lam := IsOrdinal.toIsTransitive.transitive _ hω
  have hR := godelOrder_wellOrder lam
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = internalOrderType (godelOrder lam) (lam ×ˢ lam) := ⟨_, rfl⟩
  have hθord : IsOrdinal θ := by
    rw [hθ]
    exact internalOrderType_ordinal hR
  have hθD : CardEQ θ (lam ×ˢ lam) := by
    rw [hθ]
    exact internalOrderType_cardEQ hR
  by_cases hθlam : θ ⊆ lam
  · exact hθD.2.trans (cardLE_of_subset hθlam)
  exfalso
  have hlamθ : lam ∈ θ := by
    rcases IsOrdinal.subset_or_supset (α := θ) (β := lam) with h | h
    · exact (hθlam h).elim
    · rcases IsOrdinal.subset_iff.mp h with h | h
      · exact (hθlam (h ▸ fun z hz ↦ hz)).elim
      · exact h
  -- the collapse of the Gödel order
  obtain ⟨f, hf⟩ : ∃ f, f = mostowskiMap (godelOrder lam) (lam ×ˢ lam) := ⟨_, rfl⟩
  have hc : IsTransitiveCollapse (godelOrder lam) (lam ×ˢ lam) (range f) f := by
    rw [hf]
    exact mostowskiMap_isTransitiveCollapse hR.2.1 (internalWellOrder_extensional hR)
  have hfun : IsFunction f := IsFunction.of_mem hc.2.1
  have hfdom : domain f = lam ×ˢ lam := domain_eq_of_mem_function hc.2.1
  have hfinj : Injective f := by
    intro x y z hx hy
    have hxD : x ∈ lam ×ˢ lam := hfdom ▸ mem_domain_of_kpair_mem hx
    have hyD : y ∈ lam ×ˢ lam := hfdom ▸ mem_domain_of_kpair_mem hy
    exact hc.2.2.2.1 x hxD y hyD ((value_eq_of_kpair_mem hx).trans (value_eq_of_kpair_mem hy).symm)
  have hrec := (transitiveCollapse_recursion hc).1.2.2
  have hθf : θ = range f := by
    rw [hθ, hf]
    rfl
  have hlamrange : lam ∈ range f := by
    rw [← hθf]
    exact hlamθ
  obtain ⟨q, hq⟩ := mem_range_iff.mp hlamrange
  have hqD : q ∈ lam ×ˢ lam := hfdom ▸ mem_domain_of_kpair_mem hq
  have hqdom : q ∈ domain f := hfdom ▸ hqD
  have hval : f ‘ q = lam := value_eq_of_kpair_mem hq
  have hseg : lam = range (f ↾ (predecessors (godelOrder lam) (lam ×ˢ lam) q)) := by
    have h := hrec q hqdom
    dsimp only at h
    rw [hval] at h
    exact h
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hqD
  have : IsOrdinal a := IsOrdinal.of_mem ha
  have : IsOrdinal b := IsOrdinal.of_mem hb
  have hμ : a ∪ b ∈ lam := union_mem_of_ordinals ha hb
  have hμord : IsOrdinal (a ∪ b) := ordinal_union_isOrdinal a b
  have hsucc : succ (a ∪ b) ∈ lam := initial_succ_mem hlam hωsub hμ
  have hpred : predecessors (godelOrder lam) (lam ×ˢ lam) ⟨a, b⟩ₖ ⊆ succ (a ∪ b) ×ˢ succ (a ∪ b) := by
    intro p hp
    obtain ⟨hpD, hpq⟩ := (mem_predecessors_iff _ _ _ _).mp hp
    obtain ⟨c, hc', d, hd', rfl⟩ := mem_prod_iff.mp hpD
    obtain ⟨h1, h2⟩ := godelOrder_pred_mem ha hb hc' hd' hpq
    exact kpair_mem_iff.mpr ⟨h1, h2⟩
  have h1 : lam ≤# predecessors (godelOrder lam) (lam ×ˢ lam) ⟨a, b⟩ₖ := by
    have h := range_restrict_cardLE hfun hfinj hfdom
      (fun p hp ↦ ((mem_predecessors_iff (godelOrder lam) (lam ×ˢ lam) ⟨a, b⟩ₖ p).mp hp).1)
    rwa [← hseg] at h
  have h2 : lam ≤# succ (a ∪ b) ∪ (ω : V) :=
    (h1.trans (cardLE_of_subset hpred)).trans (ih _ hsucc)
  have hsuccord : IsOrdinal (succ (a ∪ b)) := inferInstance
  rcases ordinal_union_eq (succ (a ∪ b)) (ω : V) with h | h
  · rw [h] at h2
    exact hlam.2 _ hsucc h2
  · rw [h] at h2
    exact hlam.2 _ hω h2

/-- Hessenberg's theorem: `α × α ≤# α ∪ ω` for every ordinal `α`. -/
theorem ordinal_prod_cardLE_union_omega (α : V) [IsOrdinal α] : α ×ˢ α ≤# α ∪ (ω : V) := by
  have hmain : ∀ α : V, IsOrdinal α → α ×ˢ α ≤# α ∪ (ω : V) := by
    apply set_induction (fun α : V ↦ IsOrdinal α → α ×ˢ α ≤# α ∪ (ω : V)) (by definability)
    intro α ih hα
    by_cases hαω : α ⊆ (ω : V)
    · have hsub : α ×ˢ α ⊆ (ω : V) ×ˢ (ω : V) := by
        intro p hp
        obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hp
        exact kpair_mem_iff.mpr ⟨hαω a ha, hαω b hb⟩
      exact ((cardLE_of_subset hsub).trans omega_prod_cardLE_omega).trans
        (cardLE_of_subset (subset_union_right α (ω : V)))
    · have hωα : (ω : V) ∈ α := by
        rcases IsOrdinal.subset_or_supset (α := α) (β := (ω : V)) with h | h
        · exact (hαω h).elim
        · rcases IsOrdinal.subset_iff.mp h with h | h
          · exact (hαω (h ▸ fun z hz ↦ hz)).elim
          · exact h
      have hwo : IsWellOrderable α := ordinal_wellOrderable α
      set lam := wellOrderedCardinal α with hlamdef
      have hlam : IsInitialOrdinal lam := wellOrderedCardinal_initial hwo
      have hlamα : lam ≋ α := wellOrderedCardinal_cardEQ hwo
      have hlamsub : lam ⊆ α := (wellOrderedCardinal_spec hwo).2.2 α inferInstance (CardEQ.refl α)
      have : IsOrdinal lam := hlam.1
      have hωlam : (ω : V) ⊆ lam := by
        rcases IsOrdinal.subset_or_supset (α := (ω : V)) (β := lam) with h | h
        · exact h
        · rcases IsOrdinal.subset_iff.mp h with h | h
          · exact h ▸ fun z hz ↦ hz
          · exfalso
            exact omega_not_cardLE_natural h
              ((cardLE_of_subset (IsOrdinal.toIsTransitive.transitive _ hωα)).trans hlamα.2)
      have hlamlam : lam ×ˢ lam ≤# lam := by
        rcases IsOrdinal.subset_iff.mp hωlam with h | h
        · rw [← h]
          exact omega_prod_cardLE_omega
        · exact initial_prod_cardLE_of_ih hlam h (fun μ hμ ↦ ih μ (hlamsub μ hμ) (IsOrdinal.of_mem hμ))
      exact ((prod_cardLE_prod hlamα.2 hlamα.2).trans hlamlam).trans
        (hlamα.1.trans (cardLE_of_subset (subset_union_left α (ω : V))))
  exact hmain α inferInstance

/-- `λ × λ ≋ λ` for every infinite initial ordinal `λ`. -/
theorem initial_prod_cardEQ {lam : V} (hlam : IsInitialOrdinal lam) (hω : (ω : V) ⊆ lam) :
    CardEQ (lam ×ˢ lam) lam := by
  have : IsOrdinal lam := hlam.1
  refine ⟨?_, ?_⟩
  · have h := ordinal_prod_cardLE_union_omega lam
    rwa [union_eq_iff_right.mpr hω] at h
  · obtain ⟨z, hz⟩ : ∃ z, z ∈ lam := ⟨∅, hω ∅ empty_mem_ω⟩
    let F : V → V := fun x ↦ ⟨x, z⟩ₖ
    have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
    refine ⟨definableGraph lam F hF, definableGraph_mem_function_of_mapsTo lam (lam ×ˢ lam) F hF
      (fun x hx ↦ kpair_mem_iff.mpr ⟨hx, hz⟩), ?_⟩
    intro x y w hx hy
    obtain ⟨_, rfl⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hx
    obtain ⟨_, h⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hy
    exact (kpair_iff.mp h).1

/-- Products of sets of size at most an infinite initial `λ` have size at most `λ`. -/
theorem prod_cardLE_of_cardLE_initial {lam A B : V} (hlam : IsInitialOrdinal lam) (hω : (ω : V) ⊆ lam)
    (hA : A ≤# lam) (hB : B ≤# lam) : A ×ˢ B ≤# lam :=
  (prod_cardLE_prod hA hB).trans (initial_prod_cardEQ hlam hω).1

end ZFVP
