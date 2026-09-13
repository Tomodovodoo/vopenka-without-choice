import ZFVP.SetTheory.DenseEmbeddingComposition
import ZFVP.SetTheory.FunctionComposition
import ZFVP.SetTheory.FunctionUnion

/-! Absorption for arbitrary infinite ordinals `λ` (not only initial ones): `λ^{<ω}` embeds
densely into `P × Coll(ω, λ)` whenever `|P| ≤ λ`. This is the form needed inside extensions,
where ground cardinals need not remain cardinals. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Finite sequences respect injections: `A ≤# B` gives `A^{<ω} ≤# B^{<ω}`. -/
theorem finiteSequences_cardLE_of_cardLE {A B : V} (h : A ≤# B) : finiteSequences A ≤# finiteSequences B := by
  obtain ⟨i, hi, hinj⟩ := h
  have : IsFunction i := IsFunction.of_mem hi
  let F : V → V := fun s ↦ compose s i
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  refine ⟨definableGraph (finiteSequences A) F hF, definableGraph_mem_function_of_mapsTo _ _ F hF ?_, ?_⟩
  · intro s hs
    obtain ⟨n, hn, hsn⟩ := (mem_finiteSequences_iff A s).mp hs
    exact (mem_finiteSequences_iff B _).mpr ⟨n, hn, compose_function hsn hi⟩
  · intro s t z hs ht
    obtain ⟨hsA, rfl⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hs
    obtain ⟨htA, hz⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp ht
    obtain ⟨n, hn, hsn⟩ := (mem_finiteSequences_iff A s).mp hsA
    obtain ⟨m, hm, htm⟩ := (mem_finiteSequences_iff A t).mp htA
    have : IsFunction s := IsFunction.of_mem hsn
    have : IsFunction t := IsFunction.of_mem htm
    have hds := domain_eq_of_mem_function hsn
    have hdt := domain_eq_of_mem_function htm
    have hcs : IsFunction (compose s i) := IsFunction.of_mem (compose_function hsn hi)
    have hct : IsFunction (compose t i) := IsFunction.of_mem (compose_function htm hi)
    have hdom : domain (compose s i) = domain (compose t i) := congrArg domain hz
    rw [domain_eq_of_mem_function (compose_function hsn hi), domain_eq_of_mem_function (compose_function htm hi)] at hdom
    subst hdom
    apply functions_eq_of_domain_values
    · rw [hds, hdt]
    · intro x hx
      rw [hds] at hx
      have h1 := value_compose_of_mem_function hsn hi hx
      have h2 := value_compose_of_mem_function htm hi hx
      have heq : (compose s i) ‘ x = (compose t i) ‘ x := congrArg (fun f : V ↦ f ‘ x) hz
      rw [h1, h2] at heq
      exact injective_value_eq hi hinj (function_value_mem hsn hx) (function_value_mem htm hx) heq

/-- An infinite ordinal is equinumerous with an infinite initial ordinal. -/
theorem exists_initial_cardEQ {lam : V} [IsOrdinal lam] (hω : (ω : V) ⊆ lam) :
    ∃ μ : V, IsInitialOrdinal μ ∧ (ω : V) ⊆ μ ∧ lam ≋ μ := by
  have hwo : IsWellOrderable lam := ordinal_wellOrderable lam
  have hinit := wellOrderedCardinal_initial hwo
  have hceq := wellOrderedCardinal_cardEQ hwo
  have : IsOrdinal (wellOrderedCardinal lam) := hinit.1
  refine ⟨wellOrderedCardinal lam, hinit, ?_, hceq.symm⟩
  rcases IsOrdinal.subset_or_supset (α := (ω : V)) (β := wellOrderedCardinal lam) with h | h
  · exact h
  · rcases IsOrdinal.subset_iff.mp h with h | h
    · exact h ▸ fun z hz ↦ hz
    · exfalso
      exact omega_not_cardLE_natural h ((cardLE_of_subset hω).trans hceq.2)

/-- Absorption into the sequence tree for an infinite ordinal `λ`. -/
theorem exists_sequenceProduct_denseEmbedding_ordinal (hAC : InternalChoice V) {P R one lam : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) [IsOrdinal lam]
    (hω : (ω : V) ⊆ lam) (hP : P ≤# lam) :
    ∃ e, IsDenseEmbedding (finiteSequences lam) (sequenceOrder lam) (sequenceProduct P lam)
      (sequenceProductOrder P R lam) e := by
  have h0 : (∅ : V) ∈ lam := hω ∅ empty_mem_ω
  obtain ⟨μ, hμ, hωμ, hlamμ⟩ := exists_initial_cardEQ hω
  have : IsOrdinal μ := hμ.1
  have hRP : IsForcingPreorder (sequenceProduct P lam) (sequenceProductOrder P R lam) :=
    productOrder_preorder hR (sequenceOrder_poset lam).1
  have htopP : IsForcingTop (sequenceProduct P lam) (sequenceProductOrder P R lam) ⟨one, ∅⟩ₖ :=
    product_top htop (sequence_top lam)
  have hsize : sequenceProduct P lam ≤# lam := by
    have h1 : P ≤# μ := hP.trans hlamμ.1
    have h2 : finiteSequences lam ≤# μ :=
      (finiteSequences_cardLE_of_cardLE hlamμ.1).trans (finiteSequences_cardLE_initial hAC hμ hωμ)
    exact (prod_cardLE_of_cardLE_initial hμ hωμ h1 h2).trans hlamμ.2
  have hsplit := sequenceProduct_splitting (lam := lam) hR
  have hsys := sequenceProduct_collapsingSystem hR htop h0
  obtain ⟨E, hE, hEsurj⟩ := exists_surjection_of_cardLE hsize htopP.1
  obtain ⟨Φ, _, _, hΦ⟩ := exists_childChoice hAC hRP hsize hsplit hsys hE
  exact ⟨_, treeMap_denseEmbedding hRP htopP.1 htopP.2 hsys hE hΦ hEsurj⟩

/-- Absorption for an infinite ordinal: `λ^{<ω}` embeds densely into `P × Coll(ω, λ)` when `|P| ≤ λ`. -/
theorem exists_collapseProduct_denseEmbedding_ordinal (hAC : InternalChoice V) {P R one lam : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) [IsOrdinal lam]
    (hω : (ω : V) ⊆ lam) (hP : P ≤# lam) :
    ∃ e, IsDenseEmbedding (finiteSequences lam) (sequenceOrder lam) (P ×ˢ collapseConditions lam)
      (productOrder P R (collapseConditions lam) (collapseOrder lam)) e := by
  obtain ⟨e₁, he₁⟩ := exists_sequenceProduct_denseEmbedding_ordinal hAC hR htop hω hP
  have he₂ := (sequence_collapse_denseEmbedding (hω ∅ empty_mem_ω)).productLeft (P := P) (R := R) hR
  exact ⟨_, he₁.comp (productOrder_preorder hR (collapse_poset lam).1) he₂⟩

end ZFVP
