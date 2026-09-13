import ZFVP.ModelTheory.WoodinSparseDirectBase
import ZFVP.ModelTheory.WoodinSparseCodeLaws
import ZFVP.ModelTheory.ForcingThreadIsomorphism

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A family on earlier stages, with both projection and section coherence. -/
structure IsCoherentForcingAutomorphismFamily (θ c m : V) : Prop where
  iso : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP c) ‘ i) ((forcingCodeR c) ‘ i)
    ((forcingCodeP c) ‘ i) ((forcingCodeR c) ‘ i) (m ‘ i)
  proj : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ j,
    ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ j) ‘ p) =
      (m ‘ i) ‘ (((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p)
  sec : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ i,
    (m ‘ j) ‘ (((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ p) =
      ((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ i) ‘ p)

variable {θ c m : V} [IsOrdinal θ]

omit [IsOrdinal θ] in
theorem IsCoherentForcingAutomorphismFamily.inverse
    (hc : IsForcingIterationCode θ c) (hm : IsCoherentForcingAutomorphismFamily θ c m) :
    IsCoherentForcingAutomorphismFamily θ c (forcingInverseMapFamily θ m) := by
  constructor
  · intro i hi
    rw [forcingInverseMapFamily_value hi]
    exact (hm.iso i hi).inverse
  · intro i hi j hj hij q hq
    obtain ⟨p, hp, rfl⟩ := (hm.iso j hj).surjective q hq
    rw [forcingInverseMapFamily_value hi, forcingInverseMapFamily_value hj,
      (hm.iso j hj).inverse_value hp, hm.proj i hi j hj hij p hp,
      (hm.iso i hi).inverse_value (hc.system.split.projMaps i hi j hj hij p hp)]
  · intro i hi j hj hij q hq
    obtain ⟨p, hp, rfl⟩ := (hm.iso i hi).surjective q hq
    rw [forcingInverseMapFamily_value hi, forcingInverseMapFamily_value hj,
      (hm.iso i hi).inverse_value hp, ← hm.sec i hi j hj hij p hp,
      (hm.iso j hj).inverse_value (hc.system.split.secMaps i hi j hj hij p hp)]

theorem IsCoherentForcingAutomorphismFamily.maps_inverse
    (hc : IsForcingIterationCode θ c) (hm : IsCoherentForcingAutomorphismFamily θ c m)
    {f : V} (hf : f ∈ forcingInverseCodePoset θ c) :
    forcingThreadAction θ m f ∈ forcingInverseCodePoset θ c := by
  apply forcingThreadAction_mem_inverse (fun i hi ↦ (hm.iso i hi).1) hc.subset_universe ?_ hf
  intro j hj i hij hi p hp
  let := IsOrdinal.of_mem hj
  exact hm.proj i hi j hj (IsOrdinal.toIsTransitive.transitive _ hij) p hp

theorem IsCoherentForcingAutomorphismFamily.maps_direct
    (hc : IsForcingIterationCode θ c) (hm : IsCoherentForcingAutomorphismFamily θ c m)
    {f : V} (hf : f ∈ forcingDirectLimit θ (forcingCodeP c) (forcingCodeπ c)
      (forcingCodeE c) (forcingCodeUniverse c)) :
    forcingThreadAction θ m f ∈ forcingDirectLimit θ (forcingCodeP c) (forcingCodeπ c)
      (forcingCodeE c) (forcingCodeUniverse c) := by
  apply forcingThreadAction_mem_direct (fun i hi ↦ (hm.iso i hi).1) hc.subset_universe ?_ hm.sec hf
  intro j hj i hij hi p hp
  let := IsOrdinal.of_mem hj
  exact hm.proj i hi j hj (IsOrdinal.toIsTransitive.transitive _ hij) p hp

theorem coherentForcingInverseAutomorphism
    (hc : IsForcingIterationCode θ c) (hm : IsCoherentForcingAutomorphismFamily θ c m) :
    IsForcingIsomorphism (forcingInverseCodePoset θ c) (forcingInverseCodeOrder θ c)
      (forcingInverseCodePoset θ c) (forcingInverseCodeOrder θ c)
      (forcingThreadActionMap θ m (forcingInverseCodePoset θ c)) := by
  apply forcingThreadActionMap_isomorphism hm.iso
    (fun f hf ↦ ⟨((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).1,
      ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1⟩)
    (fun f hf ↦ ⟨((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).1,
      ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1⟩)
  · exact fun _ hf ↦ hm.maps_inverse hc hf
  · exact fun _ hf ↦ (hm.inverse hc).maps_inverse hc hf

local notation "D" => forcingDirectLimit θ (forcingCodeP c) (forcingCodeπ c) (forcingCodeE c) (forcingCodeUniverse c)

theorem coherentForcingDirectAutomorphism
    (hc : IsForcingIterationCode θ c) (hm : IsCoherentForcingAutomorphismFamily θ c m) :
    IsForcingIsomorphism D (forcingThreadOrder θ (forcingCodeR c) D)
      D (forcingThreadOrder θ (forcingCodeR c) D) (forcingThreadActionMap θ m D) := by
  have hv : ∀ f ∈ D, f ∈ (forcingCodeUniverse c) ^ θ ∧
      ∀ i ∈ θ, f ‘ i ∈ (forcingCodeP c) ‘ i := by
    intro f hf
    have hh := (mem_forcingInverseLimit_iff _ _ _ _ _).mp (forcingDirectLimit_subset _ _ _ _ _ _ hf)
    exact ⟨hh.1, hh.2.1⟩
  exact forcingThreadActionMap_isomorphism hm.iso hv hv
    (fun _ hf ↦ hm.maps_direct hc hf) (fun _ hf ↦ (hm.inverse hc).maps_direct hc hf)

theorem IsCoherentForcingAutomorphismFamily.sectionThread
    (hm : IsCoherentForcingAutomorphismFamily θ c m) {k p : V}
    (hk : k ∈ θ) (hp : p ∈ (forcingCodeP c) ‘ k) :
    forcingThreadAction θ m (forcingSectionThread θ (forcingCodeπ c) (forcingCodeE c) k p) =
      forcingSectionThread θ (forcingCodeπ c) (forcingCodeE c) k ((m ‘ k) ‘ p) := by
  classical
  unfold forcingThreadAction forcingSectionThread
  apply functions_eq_of_domain_values
  · rw [domain_definableGraph, domain_definableGraph]
  · intro i hi
    rw [domain_definableGraph] at hi
    simp only [value_definableGraph _ _ _ hi]
    let := IsOrdinal.of_mem hi
    let := IsOrdinal.of_mem hk
    by_cases hik : i ∈ k
    · simp only [forcingSectionValue, ite_eq_left hik]
      exact (hm.proj i hi k hk (IsOrdinal.toIsTransitive.transitive _ hik) p hp).symm
    · have hki : k ⊆ i := by
        rcases IsOrdinal.mem_trichotomy i k with hh | rfl | hh
        · exact (hik hh).elim
        · exact subset_refl _
        · exact IsOrdinal.toIsTransitive.transitive _ hh
      simp only [forcingSectionValue, ite_eq_right hik]
      exact hm.sec k hk i hi hki p hp

noncomputable def woodinSparseInverseAutomorphism (θ c m : V) : V :=
  compose (compose (converseGraph (woodinSparseInverseFlatten θ c))
    (forcingThreadActionMap θ m (forcingInverseCodePoset θ c))) (woodinSparseInverseFlatten θ c)

noncomputable def woodinSparseDirectAutomorphism (θ c m : V) : V :=
  compose (compose (converseGraph (woodinSparseDirectFlatten θ c))
    (forcingThreadActionMap θ m (forcingDirectLimit θ (forcingCodeP c) (forcingCodeπ c)
      (forcingCodeE c) (forcingCodeUniverse c)))) (woodinSparseDirectFlatten θ c)

instance woodinSparseInverseAutomorphism_definable : ℒₛₑₜ-function₃[V] woodinSparseInverseAutomorphism := by
  unfold woodinSparseInverseAutomorphism
  apply Language.DefinableFunction₂.comp
  · apply Language.DefinableFunction₂.comp
    · apply Language.DefinableFunction₁.comp
      apply Language.DefinableFunction₂.comp <;> definability
    · apply Language.DefinableFunction₃.comp
      · definability
      · definability
      · unfold forcingInverseCodePoset
        apply Language.DefinableFunction₄.comp <;> definability
  · apply Language.DefinableFunction₂.comp <;> definability

instance woodinSparseDirectAutomorphism_definable : ℒₛₑₜ-function₃[V] woodinSparseDirectAutomorphism := by
  unfold woodinSparseDirectAutomorphism
  apply Language.DefinableFunction₂.comp
  · apply Language.DefinableFunction₂.comp
    · apply Language.DefinableFunction₁.comp
      apply Language.DefinableFunction₂.comp <;> definability
    · apply Language.DefinableFunction₃.comp
      · definability
      · definability
      · apply Language.DefinableFunction₅.comp <;> definability
  · apply Language.DefinableFunction₂.comp <;> definability

variable (hc : IsForcingIterationCode θ c) (hm : IsCoherentForcingAutomorphismFamily θ c m)
variable (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
variable (hsp : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
variable (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
  ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)))
variable (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ i,
  ((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ p = p)

include hc hm h0 hlim hsp hπ in
theorem woodinSparseInverseAutomorphism_isomorphism :
    IsForcingIsomorphism (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c)
      (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) (woodinSparseInverseAutomorphism θ c m) := by
  have hf := woodinSparseInverseFlatten_isomorphism hc h0 hlim hsp hπ
  exact (hf.inverse.comp (coherentForcingInverseAutomorphism hc hm)).comp hf

include hc hm h0 hlim hsp hπ hE in
theorem woodinSparseDirectAutomorphism_isomorphism :
    IsForcingIsomorphism (woodinSparseDirectBase θ c) (woodinSparseDirectOrder θ c)
      (woodinSparseDirectBase θ c) (woodinSparseDirectOrder θ c) (woodinSparseDirectAutomorphism θ c m) := by
  have hf := woodinSparseDirectFlatten_isomorphism hc h0 hlim hsp hπ hE
  exact (hf.inverse.comp (coherentForcingDirectAutomorphism hc hm)).comp hf

include hc hm h0 hlim hsp hπ in
theorem woodinSparseInverseAutomorphism_flatten {t : V} (ht : t ∈ forcingInverseCodePoset θ c) :
    (woodinSparseInverseAutomorphism θ c m) ‘ ((woodinSparseInverseFlatten θ c) ‘ t) =
      (woodinSparseInverseFlatten θ c) ‘ (forcingThreadAction θ m t) := by
  have hf := woodinSparseInverseFlatten_isomorphism hc h0 hlim hsp hπ
  have ha := coherentForcingInverseAutomorphism hc hm
  have hq := function_value_mem hf.1 ht
  rw [woodinSparseInverseAutomorphism,
    value_compose_of_mem_function (hf.inverse.comp ha).1 hf.1 hq,
    value_compose_of_mem_function hf.inverse.1 ha.1 hq,
    hf.inverse_value ht, forcingThreadActionMap_value ht]

include hc hm h0 hlim hsp hπ hE in
theorem woodinSparseDirectAutomorphism_flatten {t : V} (ht : t ∈ D) :
    (woodinSparseDirectAutomorphism θ c m) ‘ ((woodinSparseDirectFlatten θ c) ‘ t) =
      (woodinSparseDirectFlatten θ c) ‘ (forcingThreadAction θ m t) := by
  have hf := woodinSparseDirectFlatten_isomorphism hc h0 hlim hsp hπ hE
  have ha := coherentForcingDirectAutomorphism hc hm
  have hq := function_value_mem hf.1 ht
  rw [woodinSparseDirectAutomorphism,
    value_compose_of_mem_function (hf.inverse.comp ha).1 hf.1 hq,
    value_compose_of_mem_function hf.inverse.1 ha.1 hq,
    hf.inverse_value ht, forcingThreadActionMap_value ht]

include hc hm h0 hlim hsp hπ in
theorem woodinSparseInverseAutomorphism_restrict {q i : V}
    (hq : q ∈ woodinSparseInverseBase θ c) (hi : i ∈ θ) :
    ((woodinSparseInverseAutomorphism θ c m) ‘ q) ↾ (succ (woodinSourceIndex i)) =
      (m ‘ i) ‘ (q ↾ (succ (woodinSourceIndex i))) := by
  obtain ⟨t, ht, rfl⟩ := (woodinSparseInverseFlatten_isomorphism hc h0 hlim hsp hπ).surjective q hq
  rw [woodinSparseInverseAutomorphism_flatten hc hm h0 hlim hsp hπ ht,
    woodinSparseInverseFlatten_restrict hsp hπ (hm.maps_inverse hc ht) hi,
    forcingThreadAction_value hi, woodinSparseInverseFlatten_restrict hsp hπ ht hi]

include hc hm h0 hlim hsp hπ hE in
theorem woodinSparseDirectAutomorphism_restrict {q i : V}
    (hq : q ∈ woodinSparseDirectBase θ c) (hi : i ∈ θ) :
    ((woodinSparseDirectAutomorphism θ c m) ‘ q) ↾ (succ (woodinSourceIndex i)) =
      (m ‘ i) ‘ (q ↾ (succ (woodinSourceIndex i))) := by
  obtain ⟨t, ht, rfl⟩ := (woodinSparseDirectFlatten_isomorphism hc h0 hlim hsp hπ hE).surjective q hq
  rw [woodinSparseDirectAutomorphism_flatten hc hm h0 hlim hsp hπ hE ht,
    woodinSparseDirectFlatten_value (hm.maps_direct hc ht), woodinSparseDirectFlatten_value ht]
  have ht' := forcingDirectLimit_subset _ _ _ _ _ _ ht
  change t ∈ forcingInverseCodePoset θ c at ht'
  have hm' := hm.maps_inverse hc ht'
  rw [woodinSparseInverse_threads hsp hπ] at ht' hm'
  have he := sparseRestrictionThread_union_restrict ht' hi
  have he' := sparseRestrictionThread_union_restrict hm' hi
  simp only [woodinSparseBounds_value hi, forcingThreadAction_value hi] at he he'
  rw [he, he']

include hc hm h0 hlim hsp hπ in
theorem woodinSparseInverseAutomorphism_value {q : V}
    (hq : q ∈ woodinSparseInverseBase θ c) :
    (woodinSparseInverseAutomorphism θ c m) ‘ q =
      ⋃ˢ range (forcingThreadAction θ m (sparseThreadDecodeValue θ (woodinSparseBounds θ) q)) := by
  obtain ⟨t, ht, rfl⟩ := (woodinSparseInverseFlatten_isomorphism hc h0 hlim hsp hπ).surjective q hq
  rw [woodinSparseInverseAutomorphism_flatten hc hm h0 hlim hsp hπ ht,
    woodinSparseInverseFlatten_value hsp hπ (hm.maps_inverse hc ht),
    woodinSparseInverseFlatten_value hsp hπ ht]
  have ht' := ht
  rw [woodinSparseInverse_threads hsp hπ] at ht'
  rw [sparseThreadDecodeValue_union ht']

include hc hm h0 hlim hsp hπ hE in
theorem woodinSparseDirectAutomorphism_value {q : V}
    (hq : q ∈ woodinSparseDirectBase θ c) :
    (woodinSparseDirectAutomorphism θ c m) ‘ q =
      ⋃ˢ range (forcingThreadAction θ m (sparseThreadDecodeValue θ (woodinSparseBounds θ) q)) := by
  obtain ⟨t, ht, rfl⟩ := (woodinSparseDirectFlatten_isomorphism hc h0 hlim hsp hπ hE).surjective q hq
  rw [woodinSparseDirectAutomorphism_flatten hc hm h0 hlim hsp hπ hE ht,
    woodinSparseDirectFlatten_value (hm.maps_direct hc ht), woodinSparseDirectFlatten_value ht]
  have ht' := forcingDirectLimit_subset _ _ _ _ _ _ ht
  change t ∈ forcingInverseCodePoset θ c at ht'
  rw [woodinSparseInverse_threads hsp hπ] at ht'
  rw [sparseThreadDecodeValue_union ht']

include hc hπ hE in
theorem woodinSparse_sectionThread_union {k p : V}
    (hk : k ∈ θ) (hp : p ∈ (forcingCodeP c) ‘ k) :
    ⋃ˢ range (forcingSectionThread θ (forcingCodeπ c) (forcingCodeE c) k p) = p := by
  have ht := forcingSectionThread_mem hc.system.split hk hp hc.subset_universe
  rw [woodinSparseDirect_union_of_support hπ hE (forcingDirectLimit_subset _ _ _ _ _ _ ht)
    (forcingSectionThread_support hc.system.split hk hp), forcingSectionThread_value hk,
    forcingSectionValue_self hc.system.split hk hp]

include hc hm h0 hlim hsp hπ hE in
theorem woodinSparseDirectAutomorphism_section {k p : V}
    (hk : k ∈ θ) (hp : p ∈ (forcingCodeP c) ‘ k) :
    p ∈ woodinSparseDirectBase θ c ∧ (woodinSparseDirectAutomorphism θ c m) ‘ p = (m ‘ k) ‘ p := by
  have ht := forcingSectionThread_mem hc.system.split hk hp hc.subset_universe
  have hflat : (woodinSparseDirectFlatten θ c) ‘
      (forcingSectionThread θ (forcingCodeπ c) (forcingCodeE c) k p) = p := by
    rw [woodinSparseDirectFlatten_value ht, woodinSparse_sectionThread_union hc hπ hE hk hp]
  refine ⟨hflat ▸ function_value_mem (woodinSparseDirectFlatten_isomorphism hc h0 hlim hsp hπ hE).1 ht, ?_⟩
  conv_lhs => rw [← hflat]
  rw [woodinSparseDirectAutomorphism_flatten hc hm h0 hlim hsp hπ hE ht,
    hm.sectionThread hk hp, woodinSparseDirectFlatten_value
      (forcingSectionThread_mem hc.system.split hk (function_value_mem (hm.iso k hk).1 hp) hc.subset_universe),
    woodinSparse_sectionThread_union hc hπ hE hk (function_value_mem (hm.iso k hk).1 hp)]

include hc hm h0 hlim hsp hπ hE in
theorem woodinSparseInverseAutomorphism_section {k p : V}
    (hk : k ∈ θ) (hp : p ∈ (forcingCodeP c) ‘ k) :
    p ∈ woodinSparseInverseBase θ c ∧ (woodinSparseInverseAutomorphism θ c m) ‘ p = (m ‘ k) ‘ p := by
  have ht := forcingDirectLimit_subset _ _ _ _ _ _
    (forcingSectionThread_mem hc.system.split hk hp hc.subset_universe)
  have hflat : (woodinSparseInverseFlatten θ c) ‘
      (forcingSectionThread θ (forcingCodeπ c) (forcingCodeE c) k p) = p := by
    rw [woodinSparseInverseFlatten_value hsp hπ ht, woodinSparse_sectionThread_union hc hπ hE hk hp]
  refine ⟨hflat ▸ function_value_mem (woodinSparseInverseFlatten_isomorphism hc h0 hlim hsp hπ).1 ht, ?_⟩
  conv_lhs => rw [← hflat]
  rw [woodinSparseInverseAutomorphism_flatten hc hm h0 hlim hsp hπ ht,
    woodinSparseInverseFlatten_value hsp hπ (hm.maps_inverse hc ht), hm.sectionThread hk hp,
    woodinSparse_sectionThread_union hc hπ hE hk (function_value_mem (hm.iso k hk).1 hp)]

end ZFVP
