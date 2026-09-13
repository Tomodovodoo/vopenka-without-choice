import ZFVP.ModelTheory.CoherentAutomorphismRecursion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def automorphismWitnessMaps (T : V) : V :=
  definableGraph (domain T) (fun i ↦ kpair.π₁ (T ‘ i)) (by definability)

noncomputable def automorphismWitnessBounds (T : V) : V :=
  definableGraph (domain T) (fun i ↦ kpair.π₂ (T ‘ i)) (by definability)

instance automorphismWitnessMaps_definable : ℒₛₑₜ-function₁[V] automorphismWitnessMaps := by
  have h : ℒₛₑₜ-relation[V] (fun M T ↦ ∀ z, z ∈ M ↔ ∃ i ∈ domain T, z = ⟨i, kpair.π₁ (T ‘ i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = automorphismWitnessMaps (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [automorphismWitnessMaps, mem_definableGraph_iff]

instance automorphismWitnessBounds_definable : ℒₛₑₜ-function₁[V] automorphismWitnessBounds := by
  have h : ℒₛₑₜ-relation[V] (fun M T ↦ ∀ z, z ∈ M ↔ ∃ i ∈ domain T, z = ⟨i, kpair.π₂ (T ‘ i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = automorphismWitnessBounds (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [automorphismWitnessBounds, mem_definableGraph_iff]

theorem automorphismWitnessMaps_value {T i : V} (hi : i ∈ domain T) :
    (automorphismWitnessMaps T) ‘ i = kpair.π₁ (T ‘ i) := value_definableGraph _ _ _ hi

theorem automorphismWitnessBounds_value {T i : V} (hi : i ∈ domain T) :
    (automorphismWitnessBounds T) ‘ i = kpair.π₂ (T ‘ i) := value_definableGraph _ _ _ hi

theorem automorphismWitnessMaps_table {θ T : V} (hT : IsIterationTable θ T) :
    IsIterationTable θ (automorphismWitnessMaps T) :=
  ⟨inferInstanceAs (IsFunction (definableGraph _ _ _)), (domain_definableGraph _ _ _).trans hT.domain_eq⟩

theorem automorphismWitnessBounds_table {θ T : V} (hT : IsIterationTable θ T) :
    IsIterationTable θ (automorphismWitnessBounds T) :=
  ⟨inferInstanceAs (IsFunction (definableGraph _ _ _)), (domain_definableGraph _ _ _).trans hT.domain_eq⟩

/-- One automorphism and one common extension, with exact earlier projections.
The endpoint conditions are supplied as tables `a` and `b`. -/
structure IsCoherentAutomorphismWitnessRow (θ c a b δ H W z : V) : Prop where
  automorphism : IsCoherentAutomorphismRow θ c H (kpair.π₁ z)
  preservesDomain : ∀ p ∈ (forcingCodeP c) ‘ θ, domain ((kpair.π₁ z) ‘ p) = domain p
  fixesInitial : θ ⊆ δ → ∀ p ∈ (forcingCodeP c) ‘ θ, (kpair.π₁ z) ‘ p = p
  mem : kpair.π₂ z ∈ ((forcingCodeP c) ‘ θ)
  left : ⟨kpair.π₂ z, (kpair.π₁ z) ‘ (a ‘ θ)⟩ₖ ∈ ((forcingCodeR c) ‘ θ)
  right : ⟨kpair.π₂ z, b ‘ θ⟩ₖ ∈ ((forcingCodeR c) ‘ θ)
  proj : ∀ i ∈ θ, ((forcingCodeπ c) ‘ ⟨i, θ⟩ₖ) ‘ (kpair.π₂ z) = (W ‘ i)
  support : domain (kpair.π₂ z) ⊆ domain (a ‘ θ) ∪ domain (b ‘ θ)
  initialWitness : θ ⊆ δ → kpair.π₂ z = (a ‘ θ)

instance isCoherentAutomorphismWitnessRow_definable (c a b δ : V) :
    ℒₛₑₜ-relation₄[V] (fun θ H W z ↦ IsCoherentAutomorphismWitnessRow θ c a b δ H W z) := by
  have h : ℒₛₑₜ-relation₄[V] (fun θ H W z ↦
    IsCoherentAutomorphismRow θ c H (kpair.π₁ z) ∧
    (∀ p ∈ (forcingCodeP c) ‘ θ, domain ((kpair.π₁ z) ‘ p) = domain p) ∧
    (θ ⊆ δ → ∀ p ∈ (forcingCodeP c) ‘ θ, (kpair.π₁ z) ‘ p = p) ∧
    kpair.π₂ z ∈ (forcingCodeP c) ‘ θ ∧
    ⟨kpair.π₂ z, (kpair.π₁ z) ‘ (a ‘ θ)⟩ₖ ∈ (forcingCodeR c) ‘ θ ∧
    ⟨kpair.π₂ z, b ‘ θ⟩ₖ ∈ (forcingCodeR c) ‘ θ ∧
    (∀ i ∈ θ, ((forcingCodeπ c) ‘ ⟨i, θ⟩ₖ) ‘ (kpair.π₂ z) = W ‘ i) ∧
    domain (kpair.π₂ z) ⊆ domain (a ‘ θ) ∪ domain (b ‘ θ) ∧
    (θ ⊆ δ → kpair.π₂ z = (a ‘ θ))) := by definability
  apply Language.Definable.of_iff h
  intro v
  exact ⟨fun h ↦ ⟨h.automorphism, h.preservesDomain, h.fixesInitial, h.mem,
    h.left, h.right, h.proj, h.support, h.initialWitness⟩,
    fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩⟩

structure IsCoherentAutomorphismWitnessHistory (θ c a b δ H W : V) : Prop where
  mapsTable : IsIterationTable θ H
  boundsTable : IsIterationTable θ W
  automorphism : IsCoherentForcingAutomorphismFamily θ c H
  fixesTop : ∀ i ∈ θ, (H ‘ i) ‘ ((forcingCodet c) ‘ i) = ((forcingCodet c) ‘ i)
  preservesDomain : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, domain ((H ‘ i) ‘ p) = domain p
  fixesInitial : ∀ i ∈ θ, i ⊆ δ → ∀ p ∈ (forcingCodeP c) ‘ i, (H ‘ i) ‘ p = p
  mem : ∀ i ∈ θ, W ‘ i ∈ ((forcingCodeP c) ‘ i)
  left : ∀ i ∈ θ, ⟨W ‘ i, (H ‘ i) ‘ (a ‘ i)⟩ₖ ∈ ((forcingCodeR c) ‘ i)
  right : ∀ i ∈ θ, ⟨W ‘ i, b ‘ i⟩ₖ ∈ ((forcingCodeR c) ‘ i)
  proj : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ (W ‘ j) = (W ‘ i)
  support : ∀ i ∈ θ, domain (W ‘ i) ⊆ domain (a ‘ i) ∪ domain (b ‘ i)
  initialWitness : ∀ i ∈ θ, i ⊆ δ → W ‘ i = (a ‘ i)

theorem IsCoherentAutomorphismWitnessHistory.compatible {θ c a b δ H W i : V}
    (h : IsCoherentAutomorphismWitnessHistory θ c a b δ H W) (hi : i ∈ θ) :
    ForcingCompatible ((forcingCodeP c) ‘ i) ((forcingCodeR c) ‘ i) ((H ‘ i) ‘ (a ‘ i)) (b ‘ i) :=
  ⟨W ‘ i, h.mem i hi, h.left i hi, h.right i hi⟩

theorem IsCoherentAutomorphismWitnessHistory.relative_projection {θ c a b δ H W i : V}
    (h : IsCoherentAutomorphismWitnessHistory θ c a b δ H W)
    (hc : IsForcingIterationCode θ c) (hi : i ∈ θ) (hδ : δ ∈ θ) (hδi : δ ⊆ i)
    {p : V} (hp : p ∈ (forcingCodeP c) ‘ i) :
    ((forcingCodeπ c) ‘ ⟨δ, i⟩ₖ) ‘ ((H ‘ i) ‘ p) = ((forcingCodeπ c) ‘ ⟨δ, i⟩ₖ) ‘ p := by
  rw [h.automorphism.proj δ hδ i hi hδi p hp]
  exact h.fixesInitial δ hδ (subset_refl _) _ (hc.system.split.projMaps δ hδ i hi hδi p hp)

noncomputable abbrev coherentAutomorphismWitnessRec := @coherentAutomorphismRec
noncomputable abbrev coherentAutomorphismWitnessHistory := @coherentAutomorphismHistory

theorem coherentAutomorphismWitnessHistory_maps_value (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    {θ i : V} (hi : i ∈ θ) :
    (automorphismWitnessMaps (coherentAutomorphismHistory F hF θ)) ‘ i =
      kpair.π₁ (coherentAutomorphismRec F hF i) := by
  rw [automorphismWitnessMaps_value (by rw [(coherentAutomorphismHistory_table F hF θ).domain_eq]; exact hi),
    coherentAutomorphismHistory_value F hF hi]

theorem coherentAutomorphismWitnessHistory_bounds_value (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    {θ i : V} (hi : i ∈ θ) :
    (automorphismWitnessBounds (coherentAutomorphismHistory F hF θ)) ‘ i =
      kpair.π₂ (coherentAutomorphismRec F hF i) := by
  rw [automorphismWitnessBounds_value (by rw [(coherentAutomorphismHistory_table F hF θ).domain_eq]; exact hi),
    coherentAutomorphismHistory_value F hF hi]

theorem coherentAutomorphismWitnessHistory_of_rows (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    {Δ θ c a b δ : V} [IsOrdinal Δ] [IsOrdinal θ]
    (hc : IsForcingIterationCode Δ c) (hθ : θ ⊆ Δ)
    (hr : ∀ i ∈ θ, IsCoherentAutomorphismWitnessRow i c a b δ
      (automorphismWitnessMaps (coherentAutomorphismHistory F hF i))
      (automorphismWitnessBounds (coherentAutomorphismHistory F hF i))
      (coherentAutomorphismRec F hF i)) :
    IsCoherentAutomorphismWitnessHistory θ c a b δ
      (automorphismWitnessMaps (coherentAutomorphismHistory F hF θ))
      (automorphismWitnessBounds (coherentAutomorphismHistory F hF θ)) := by
  constructor
  · exact automorphismWitnessMaps_table (coherentAutomorphismHistory_table F hF θ)
  · exact automorphismWitnessBounds_table (coherentAutomorphismHistory_table F hF θ)
  · constructor
    · intro i hi
      rw [coherentAutomorphismWitnessHistory_maps_value F hF hi]
      exact (hr i hi).automorphism.iso
    · intro i hi j hj hij p hp
      rw [coherentAutomorphismWitnessHistory_maps_value F hF hi,
        coherentAutomorphismWitnessHistory_maps_value F hF hj]
      let := IsOrdinal.of_mem hi
      let := IsOrdinal.of_mem hj
      rcases IsOrdinal.subset_iff.mp hij with hij | hij
      · subst j
        rw [hc.system.split.projId (hθ i hi) hp,
          hc.system.split.projId (hθ i hi) (function_value_mem (hr i hi).automorphism.iso.1 hp)]
      · simpa only [coherentAutomorphismWitnessHistory_maps_value F hF hij] using
          (hr j hj).automorphism.proj i hij p hp
    · intro i hi j hj hij p hp
      rw [coherentAutomorphismWitnessHistory_maps_value F hF hi,
        coherentAutomorphismWitnessHistory_maps_value F hF hj]
      let := IsOrdinal.of_mem hi
      let := IsOrdinal.of_mem hj
      rcases IsOrdinal.subset_iff.mp hij with hij | hij
      · subst j
        rw [hc.system.split.secId i (hθ i hi) p hp,
          hc.system.split.secId i (hθ i hi) _ (function_value_mem (hr i hi).automorphism.iso.1 hp)]
      · simpa only [coherentAutomorphismWitnessHistory_maps_value F hF hij] using
          (hr j hj).automorphism.sec i hij p hp
  · intro i hi
    rw [coherentAutomorphismWitnessHistory_maps_value F hF hi]
    exact (hr i hi).automorphism.fixesTop
  · intro i hi
    rw [coherentAutomorphismWitnessHistory_maps_value F hF hi]
    exact (hr i hi).preservesDomain
  · intro i hi
    rw [coherentAutomorphismWitnessHistory_maps_value F hF hi]
    exact (hr i hi).fixesInitial
  · intro i hi
    rw [coherentAutomorphismWitnessHistory_bounds_value F hF hi]
    exact (hr i hi).mem
  · intro i hi
    rw [coherentAutomorphismWitnessHistory_bounds_value F hF hi,
      coherentAutomorphismWitnessHistory_maps_value F hF hi]
    exact (hr i hi).left
  · intro i hi
    rw [coherentAutomorphismWitnessHistory_bounds_value F hF hi]
    exact (hr i hi).right
  · intro i hi j hj hij
    rw [coherentAutomorphismWitnessHistory_bounds_value F hF hi,
      coherentAutomorphismWitnessHistory_bounds_value F hF hj]
    let := IsOrdinal.of_mem hi
    let := IsOrdinal.of_mem hj
    rcases IsOrdinal.subset_iff.mp hij with hij | hij
    · subst j
      exact hc.system.split.projId (hθ i hi) (hr i hi).mem
    · simpa only [coherentAutomorphismWitnessHistory_bounds_value F hF hij] using (hr j hj).proj i hij
  · intro i hi
    rw [coherentAutomorphismWitnessHistory_bounds_value F hF hi]
    exact (hr i hi).support
  · intro i hi
    rw [coherentAutomorphismWitnessHistory_bounds_value F hF hi]
    exact (hr i hi).initialWitness

/-- The recursion propagates common witnesses together with the automorphisms.
In particular, limit builders receive an exactly coherent witness history. -/
theorem coherentAutomorphismWitnessRec_rows (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    {Δ c a b δ : V} [IsOrdinal Δ] (hc : IsForcingIterationCode Δ c)
    (hstep : ∀ θ ∈ Δ, ∀ T, IsIterationTable θ T →
      IsCoherentAutomorphismWitnessHistory θ c a b δ (automorphismWitnessMaps T) (automorphismWitnessBounds T) →
      IsCoherentAutomorphismWitnessRow θ c a b δ (automorphismWitnessMaps T) (automorphismWitnessBounds T) (F T)) :
    ∀ θ ∈ Δ, IsCoherentAutomorphismWitnessRow θ c a b δ
      (automorphismWitnessMaps (coherentAutomorphismHistory F hF θ))
      (automorphismWitnessBounds (coherentAutomorphismHistory F hF θ))
      (coherentAutomorphismRec F hF θ) := by
  have hall := transfinite_induction (fun θ : V ↦ θ ∈ Δ →
    IsCoherentAutomorphismWitnessRow θ c a b δ
      (automorphismWitnessMaps (coherentAutomorphismHistory F hF θ))
      (automorphismWitnessBounds (coherentAutomorphismHistory F hF θ))
      (coherentAutomorphismRec F hF θ)) (by
        apply Language.Definable.imp (by definability)
        apply Language.DefinableRel₄.comp
          (P := fun θ H W z ↦ IsCoherentAutomorphismWitnessRow θ c a b δ H W z) <;>
          definability) ?_
  · intro θ hθ
    let := IsOrdinal.of_mem hθ
    exact hall (IsOrdinal.toOrdinal θ) hθ
  intro θ ih hθ
  have hsub : (θ : V) ⊆ Δ := IsOrdinal.toIsTransitive.transitive _ hθ
  have hr : ∀ i ∈ (θ : V), IsCoherentAutomorphismWitnessRow i c a b δ
      (automorphismWitnessMaps (coherentAutomorphismHistory F hF i))
      (automorphismWitnessBounds (coherentAutomorphismHistory F hF i))
      (coherentAutomorphismRec F hF i) := by
    intro i hi
    let := IsOrdinal.of_mem hi
    exact ih (IsOrdinal.toOrdinal i) hi (hsub i hi)
  have hh := coherentAutomorphismWitnessHistory_of_rows F hF hc hsub hr
  rw [coherentAutomorphismRec_rule F hF]
  exact hstep θ hθ _ (coherentAutomorphismHistory_table F hF θ) hh

theorem coherentAutomorphismWitnessRec_family (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    {Δ θ c a b δ : V} [IsOrdinal Δ] [IsOrdinal θ] (hc : IsForcingIterationCode Δ c)
    (hstep : ∀ η ∈ Δ, ∀ T, IsIterationTable η T →
      IsCoherentAutomorphismWitnessHistory η c a b δ (automorphismWitnessMaps T) (automorphismWitnessBounds T) →
      IsCoherentAutomorphismWitnessRow η c a b δ (automorphismWitnessMaps T) (automorphismWitnessBounds T) (F T))
    (hθ : θ ⊆ Δ) :
    IsCoherentAutomorphismWitnessHistory θ c a b δ
      (automorphismWitnessMaps (coherentAutomorphismHistory F hF θ))
      (automorphismWitnessBounds (coherentAutomorphismHistory F hF θ)) :=
  coherentAutomorphismWitnessHistory_of_rows F hF hc hθ
    (fun i hi ↦ coherentAutomorphismWitnessRec_rows F hF hc hstep i (hθ i hi))

noncomputable def coherentAutomorphismWitnessBuilder (G : V → V → V → V) (T : V) : V :=
  G (domain T) (automorphismWitnessMaps T) (automorphismWitnessBounds T)

theorem coherentAutomorphismWitnessBuilder_definable (G : V → V → V → V)
    (hG : ℒₛₑₜ-function₃ G) : ℒₛₑₜ-function₁[V] (coherentAutomorphismWitnessBuilder G) := by
  unfold coherentAutomorphismWitnessBuilder
  apply Language.DefinableFunction₃.comp (F := G) (hF := hG) <;> definability

/-- An interface for builders expressed directly in terms of the stage and the
two histories, without exposing the paired recursion table. -/
theorem coherentAutomorphismWitnessRec_family_of_builder (G : V → V → V → V)
    (hG : ℒₛₑₜ-function₃ G) {Δ θ c a b δ : V} [IsOrdinal Δ] [IsOrdinal θ]
    (hc : IsForcingIterationCode Δ c)
    (hstep : ∀ η ∈ Δ, ∀ H W, IsCoherentAutomorphismWitnessHistory η c a b δ H W →
      IsCoherentAutomorphismWitnessRow η c a b δ H W (G η H W))
    (hθ : θ ⊆ Δ) :
    IsCoherentAutomorphismWitnessHistory θ c a b δ
      (automorphismWitnessMaps (coherentAutomorphismHistory (coherentAutomorphismWitnessBuilder G)
        (coherentAutomorphismWitnessBuilder_definable G hG) θ))
      (automorphismWitnessBounds (coherentAutomorphismHistory (coherentAutomorphismWitnessBuilder G)
        (coherentAutomorphismWitnessBuilder_definable G hG) θ)) := by
  apply coherentAutomorphismWitnessRec_family _ _ hc ?_ hθ
  intro η hη T hT hH
  simpa only [coherentAutomorphismWitnessBuilder, hT.domain_eq] using
    hstep η hη _ _ hH

end ZFVP
