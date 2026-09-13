import ZFVP.ModelTheory.WoodinSparseAutomorphismLimit

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance isCoherentForcingAutomorphismFamily_definable :
    ℒₛₑₜ-relation₃[V] IsCoherentForcingAutomorphismFamily := by
  have h : ℒₛₑₜ-relation₃[V] (fun θ c m ↦
    (∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP c) ‘ i) ((forcingCodeR c) ‘ i)
      ((forcingCodeP c) ‘ i) ((forcingCodeR c) ‘ i) (m ‘ i)) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ j) ‘ p) =
        (m ‘ i) ‘ (((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p)) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ i,
      (m ‘ j) ‘ (((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ p) =
        ((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ i) ‘ p))) := by definability
  apply Language.Definable.of_iff h
  intro v
  exact ⟨fun h ↦ ⟨h.iso, h.proj, h.sec⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

/-- Local obligations for one new map, relative to its earlier history. -/
structure IsCoherentAutomorphismRow (θ c H f : V) : Prop where
  iso : IsForcingIsomorphism ((forcingCodeP c) ‘ θ) ((forcingCodeR c) ‘ θ)
    ((forcingCodeP c) ‘ θ) ((forcingCodeR c) ‘ θ) f
  fixesTop : (f ‘ ((forcingCodet c) ‘ θ) = (forcingCodet c) ‘ θ)
  proj : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ θ,
    ((forcingCodeπ c) ‘ ⟨i, θ⟩ₖ) ‘ (f ‘ p) = (H ‘ i) ‘ (((forcingCodeπ c) ‘ ⟨i, θ⟩ₖ) ‘ p)
  sec : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i,
    f ‘ (((forcingCodeE c) ‘ ⟨i, θ⟩ₖ) ‘ p) = ((forcingCodeE c) ‘ ⟨i, θ⟩ₖ) ‘ ((H ‘ i) ‘ p)

instance isCoherentAutomorphismRow_definable : ℒₛₑₜ-relation₄[V] IsCoherentAutomorphismRow := by
  have h : ℒₛₑₜ-relation₄[V] (fun θ c H f ↦
    IsForcingIsomorphism ((forcingCodeP c) ‘ θ) ((forcingCodeR c) ‘ θ)
      ((forcingCodeP c) ‘ θ) ((forcingCodeR c) ‘ θ) f ∧
    f ‘ ((forcingCodet c) ‘ θ) = (forcingCodet c) ‘ θ ∧
    (∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ θ,
      ((forcingCodeπ c) ‘ ⟨i, θ⟩ₖ) ‘ (f ‘ p) = (H ‘ i) ‘ (((forcingCodeπ c) ‘ ⟨i, θ⟩ₖ) ‘ p)) ∧
    (∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i,
      f ‘ (((forcingCodeE c) ‘ ⟨i, θ⟩ₖ) ‘ p) = ((forcingCodeE c) ‘ ⟨i, θ⟩ₖ) ‘ ((H ‘ i) ‘ p))) := by definability
  apply Language.Definable.of_iff h
  intro v
  exact ⟨fun h ↦ ⟨h.iso, h.fixesTop, h.proj, h.sec⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

theorem IsCoherentForcingAutomorphismFamily.of_values {θ c m n : V}
    (hm : IsCoherentForcingAutomorphismFamily θ c m) (he : ∀ i ∈ θ, n ‘ i = m ‘ i) :
    IsCoherentForcingAutomorphismFamily θ c n := by
  constructor
  · intro i hi
    rw [he i hi]
    exact hm.iso i hi
  · intro i hi j hj hij p hp
    rw [he i hi, he j hj]
    exact hm.proj i hi j hj hij p hp
  · intro i hi j hj hij p hp
    rw [he i hi, he j hj]
    exact hm.sec i hi j hj hij p hp

theorem IsCoherentForcingAutomorphismFamily.restrict {θ η c m : V}
    (hm : IsCoherentForcingAutomorphismFamily θ c m) (ht : IsIterationTable θ m) (hη : η ⊆ θ) :
    IsCoherentForcingAutomorphismFamily η c (m ↾ η) := by
  let := ht.function
  have he (i : V) (hi : i ∈ η) : (m ↾ η) ‘ i = m ‘ i :=
    value_restrict (ht.domain_eq.symm ▸ hη i hi) hi
  exact (IsCoherentForcingAutomorphismFamily.mk
    (fun i hi ↦ hm.iso i (hη i hi))
    (fun i hi j hj hij p hp ↦ hm.proj i (hη i hi) j (hη j hj) hij p hp)
    (fun i hi j hj hij p hp ↦ hm.sec i (hη i hi) j (hη j hj) hij p hp)).of_values he

theorem IsCoherentForcingAutomorphismFamily.extend {θ Δ c m f : V} [IsOrdinal θ] [IsOrdinal Δ]
    (hc : IsForcingIterationCode Δ c) (hθ : θ ∈ Δ)
    (hm : IsCoherentForcingAutomorphismFamily θ c m) (hf : IsCoherentAutomorphismRow θ c m f) :
    IsCoherentForcingAutomorphismFamily (succ θ) c (forcingFamilyNext θ m f) := by
  constructor
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · rw [forcingFamilyNext_new]
      exact hf.iso
    · rw [forcingFamilyNext_old hi]
      exact hm.iso i hi
  · intro i hi j hj hij p hp
    rcases mem_succ_iff.mp hj with hjθ | hj
    · subst j
      rcases mem_succ_iff.mp hi with hiθ | hi
      · subst i
        rw [forcingFamilyNext_new, hc.system.split.projId hθ hp,
          hc.system.split.projId hθ (function_value_mem hf.iso.1 hp)]
      · rw [forcingFamilyNext_old hi, forcingFamilyNext_new]
        exact hf.proj i hi p hp
    · have hiθ : i ∈ θ := by
        rcases mem_succ_iff.mp hi with hiθ | hi
        · subst i
          exact False.elim (mem_irrefl j (hij j hj))
        · exact hi
      rw [forcingFamilyNext_old hiθ, forcingFamilyNext_old hj]
      exact hm.proj i hiθ j hj hij p hp
  · intro i hi j hj hij p hp
    rcases mem_succ_iff.mp hj with hjθ | hj
    · subst j
      rcases mem_succ_iff.mp hi with hiθ | hi
      · subst i
        rw [forcingFamilyNext_new, hc.system.split.secId θ hθ p hp,
          hc.system.split.secId θ hθ _ (function_value_mem hf.iso.1 hp)]
      · rw [forcingFamilyNext_old hi, forcingFamilyNext_new]
        exact hf.sec i hi p hp
    · have hiθ : i ∈ θ := by
        rcases mem_succ_iff.mp hi with hiθ | hi
        · subst i
          exact False.elim (mem_irrefl j (hij j hj))
        · exact hi
      rw [forcingFamilyNext_old hiθ, forcingFamilyNext_old hj]
      exact hm.sec i hiθ j hj hij p hp

noncomputable def coherentAutomorphismRec (F : V → V) (hF : ℒₛₑₜ-function₁ F) (θ : V) : V :=
  Replacement.transfiniteRec F hF θ

instance coherentAutomorphismRec_definable (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    ℒₛₑₜ-function₁[V] (coherentAutomorphismRec F hF) := Replacement.transfiniteRec_definable hF

noncomputable def coherentAutomorphismHistory (F : V → V) (hF : ℒₛₑₜ-function₁ F) (θ : V) : V :=
  definableGraph θ (coherentAutomorphismRec F hF) (coherentAutomorphismRec_definable F hF)

instance coherentAutomorphismHistory_definable (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    ℒₛₑₜ-function₁[V] (coherentAutomorphismHistory F hF) := by
  have h : ℒₛₑₜ-relation[V] (fun H θ ↦ ∀ z, z ∈ H ↔ ∃ i ∈ θ, z = ⟨i, coherentAutomorphismRec F hF i⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = coherentAutomorphismHistory F hF (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [coherentAutomorphismHistory, mem_definableGraph_iff]

theorem coherentAutomorphismHistory_value (F : V → V) (hF : ℒₛₑₜ-function₁ F) {θ i : V} (hi : i ∈ θ) :
    (coherentAutomorphismHistory F hF θ) ‘ i = coherentAutomorphismRec F hF i := value_definableGraph _ _ _ hi

theorem coherentAutomorphismHistory_table (F : V → V) (hF : ℒₛₑₜ-function₁ F) (θ : V) :
    IsIterationTable θ (coherentAutomorphismHistory F hF θ) :=
  ⟨inferInstanceAs (IsFunction (definableGraph θ _ _)), domain_definableGraph _ _ _⟩

theorem coherentAutomorphismRec_rule (F : V → V) (hF : ℒₛₑₜ-function₁ F) (θ : V) [IsOrdinal θ] :
    coherentAutomorphismRec F hF θ = F (coherentAutomorphismHistory F hF θ) :=
  Replacement.transfiniteRec_spec F hF (IsOrdinal.toOrdinal θ)

theorem coherentAutomorphismHistory_restrict (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    {η θ : V} (hη : η ⊆ θ) :
    (coherentAutomorphismHistory F hF θ) ↾ η = coherentAutomorphismHistory F hF η := by
  have ht := coherentAutomorphismHistory_table F hF θ
  have he := coherentAutomorphismHistory_table F hF η
  let := ht.function
  let := he.function
  have hh := restrict_eq_of_values
    (show η ⊆ domain (coherentAutomorphismHistory F hF θ) by rw [ht.domain_eq]; exact hη)
    (show η ⊆ domain (coherentAutomorphismHistory F hF η) by rw [he.domain_eq])
    (fun i hi ↦ (coherentAutomorphismHistory_value F hF (hη i hi)).trans
      (coherentAutomorphismHistory_value F hF hi).symm)
  exact hh.trans (IsFunction.restrict_eq_self _ _ (by rw [he.domain_eq]))

theorem coherentAutomorphismHistory_next (F : V → V) (hF : ℒₛₑₜ-function₁ F) (θ : V) :
    coherentAutomorphismHistory F hF (succ θ) =
      forcingFamilyNext θ (coherentAutomorphismHistory F hF θ) (coherentAutomorphismRec F hF θ) := by
  have ht := coherentAutomorphismHistory_table F hF (succ θ)
  have hn := forcingFamilyNext_table θ (coherentAutomorphismHistory F hF θ) (coherentAutomorphismRec F hF θ)
  let := ht.function
  let := hn.function
  apply functions_eq_of_domain_values (ht.domain_eq.trans hn.domain_eq.symm)
  intro i hi
  rw [ht.domain_eq] at hi
  rw [coherentAutomorphismHistory_value F hF hi]
  rcases mem_succ_iff.mp hi with rfl | hi
  · rw [forcingFamilyNext_new]
  · rw [forcingFamilyNext_old hi, coherentAutomorphismHistory_value F hF hi]

theorem coherentAutomorphismHistory_of_rows (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    {Δ θ c : V} [IsOrdinal Δ] [IsOrdinal θ]
    (hc : IsForcingIterationCode Δ c) (hθ : θ ⊆ Δ)
    (hr : ∀ i ∈ θ, IsCoherentAutomorphismRow i c (coherentAutomorphismHistory F hF i)
      (coherentAutomorphismRec F hF i)) :
    IsCoherentForcingAutomorphismFamily θ c (coherentAutomorphismHistory F hF θ) ∧
      ∀ i ∈ θ, ((coherentAutomorphismHistory F hF θ) ‘ i) ‘ ((forcingCodet c) ‘ i) = (forcingCodet c) ‘ i := by
  constructor
  · constructor
    · intro i hi
      rw [coherentAutomorphismHistory_value F hF hi]
      exact (hr i hi).iso
    · intro i hi j hj hij p hp
      rw [coherentAutomorphismHistory_value F hF hi, coherentAutomorphismHistory_value F hF hj]
      let := IsOrdinal.of_mem hi
      let := IsOrdinal.of_mem hj
      rcases IsOrdinal.subset_iff.mp hij with hij | hij
      · subst j
        rw [hc.system.split.projId (hθ i hi) hp,
          hc.system.split.projId (hθ i hi) (function_value_mem (hr i hi).iso.1 hp)]
      · simpa only [coherentAutomorphismHistory_value F hF hij] using (hr j hj).proj i hij p hp
    · intro i hi j hj hij p hp
      rw [coherentAutomorphismHistory_value F hF hi, coherentAutomorphismHistory_value F hF hj]
      let := IsOrdinal.of_mem hi
      let := IsOrdinal.of_mem hj
      rcases IsOrdinal.subset_iff.mp hij with hij | hij
      · subst j
        rw [hc.system.split.secId i (hθ i hi) p hp,
          hc.system.split.secId i (hθ i hi) _ (function_value_mem (hr i hi).iso.1 hp)]
      · simpa only [coherentAutomorphismHistory_value F hF hij] using (hr j hj).sec i hij p hp
  · intro i hi
    rw [coherentAutomorphismHistory_value F hF hi]
    exact (hr i hi).fixesTop

/-- A definable local builder receives a coherent, top-fixing history. Its contract
only asks for the next row and the new projection/section column. -/
theorem coherentAutomorphismRec_rows (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    {Δ c : V} [IsOrdinal Δ] (hc : IsForcingIterationCode Δ c)
    (hstep : ∀ θ ∈ Δ, ∀ H, IsIterationTable θ H →
      IsCoherentForcingAutomorphismFamily θ c H →
      (∀ i ∈ θ, (H ‘ i) ‘ ((forcingCodet c) ‘ i) = (forcingCodet c) ‘ i) →
      IsCoherentAutomorphismRow θ c H (F H)) :
    ∀ θ ∈ Δ, IsCoherentAutomorphismRow θ c (coherentAutomorphismHistory F hF θ)
      (coherentAutomorphismRec F hF θ) := by
  have hall := transfinite_induction (fun θ : V ↦ θ ∈ Δ →
    IsCoherentAutomorphismRow θ c (coherentAutomorphismHistory F hF θ)
      (coherentAutomorphismRec F hF θ)) (by definability) ?_
  · intro θ hθ
    let := IsOrdinal.of_mem hθ
    exact hall (IsOrdinal.toOrdinal θ) hθ
  intro θ ih hθ
  have hsub : (θ : V) ⊆ Δ := IsOrdinal.toIsTransitive.transitive _ hθ
  have hr : ∀ i ∈ (θ : V), IsCoherentAutomorphismRow i c (coherentAutomorphismHistory F hF i)
      (coherentAutomorphismRec F hF i) := by
    intro i hi
    let := IsOrdinal.of_mem hi
    exact ih (IsOrdinal.toOrdinal i) hi (hsub i hi)
  have hh := coherentAutomorphismHistory_of_rows F hF hc hsub hr
  rw [coherentAutomorphismRec_rule F hF]
  exact hstep θ hθ _ (coherentAutomorphismHistory_table F hF θ) hh.1 hh.2

theorem coherentAutomorphismRec_family (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    {Δ θ c : V} [IsOrdinal Δ] [IsOrdinal θ] (hc : IsForcingIterationCode Δ c)
    (hstep : ∀ η ∈ Δ, ∀ H, IsIterationTable η H →
      IsCoherentForcingAutomorphismFamily η c H →
      (∀ i ∈ η, (H ‘ i) ‘ ((forcingCodet c) ‘ i) = (forcingCodet c) ‘ i) →
      IsCoherentAutomorphismRow η c H (F H)) (hθ : θ ⊆ Δ) :
    IsIterationTable θ (coherentAutomorphismHistory F hF θ) ∧
      IsCoherentForcingAutomorphismFamily θ c (coherentAutomorphismHistory F hF θ) ∧
      ∀ i ∈ θ, ((coherentAutomorphismHistory F hF θ) ‘ i) ‘ ((forcingCodet c) ‘ i) = (forcingCodet c) ‘ i :=
  ⟨coherentAutomorphismHistory_table F hF θ,
    coherentAutomorphismHistory_of_rows F hF hc hθ
      (fun i hi ↦ coherentAutomorphismRec_rows F hF hc hstep i (hθ i hi))⟩

end ZFVP
