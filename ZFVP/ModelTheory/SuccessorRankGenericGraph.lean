import ZFVP.ModelTheory.SuccessorRankLiftGraph
import ZFVP.ModelTheory.ForcingGenericInclusion
import ZFVP.ModelTheory.SuccessorRankLiftChecks
import ZFVP.ModelTheory.ForcingLowRankNames
import ZFVP.SetTheory.BoundedGraphDependentChoice

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SuccessorRankLiftData

variable {A B : ForcingContext V} {δ ε e : V} (L : SuccessorRankLiftData A B δ ε e)
  (hP : A.P ⊆ B.P)
  (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P)

include hP

theorem genericGraphName_isName : IsForcingName B.P (nameMapGraph B.one L.nameDomain e) :=
  nameMapGraph_isName B.top.1 (fun _ hτ ↦ (L.nameDomain_name hτ).mono hP)
    (fun _ hτ ↦ L.image_name (L.nameDomain_rank hτ) (L.nameDomain_name hτ))

noncomputable def genericGraph : B.Model := B.mapGraph L.nameDomain e (L.genericGraphName_isName hP)

include hG in
theorem genericGraph_isFunction : IsFunction (L.genericGraph hP) := by
  apply B.mapGraph_isFunction L.nameDomain e (L.genericGraphName_isName hP)
    (fun _ hτ ↦ (L.nameDomain_name hτ).mono hP)
    (fun _ hτ ↦ L.image_name (L.nameDomain_rank hτ) (L.nameDomain_name hτ))
  intro σ hσ τ hτ heq
  let σA : ForcingName A.P := ⟨σ, L.nameDomain_name hσ⟩
  let τA : ForcingName A.P := ⟨τ, L.nameDomain_name hτ⟩
  have hsmall : A.ofName σA = A.ofName τA :=
    (A.genericInclusion B hG).injective (by
      simpa only [A.genericInclusion_ofName B hP hG] using heq)
  exact (L.image_eq_iff σA τA (L.nameDomain_rank hσ) (L.nameDomain_rank hτ)).mpr hsmall

theorem genericGraph_domain (x : B.Model) : x ∈ domain (L.genericGraph hP) ↔
    ∃ τ : ForcingName A.P, τ.val ∈ hierarchy δ ∧ x = B.ofName ⟨τ.val, τ.property.mono hP⟩ := by
  rw [genericGraph, B.mem_domain_mapGraph_iff L.nameDomain e (L.genericGraphName_isName hP)
    (fun _ hτ ↦ (L.nameDomain_name hτ).mono hP)
    (fun _ hτ ↦ L.image_name (L.nameDomain_rank hτ) (L.nameDomain_name hτ))]
  constructor
  · rintro ⟨τ, hτ, he⟩
    exact ⟨⟨τ, L.nameDomain_name hτ⟩, L.nameDomain_rank hτ, he⟩
  · rintro ⟨τ, hτ, he⟩
    exact ⟨τ.val, mem_sep_iff.mpr ⟨hτ, τ.property⟩, he⟩

include hG in
theorem genericGraph_value (τ : ForcingName A.P) (hτ : τ.val ∈ hierarchy δ) :
    (L.genericGraph hP) ‘ (B.ofName ⟨τ.val, τ.property.mono hP⟩) =
      B.ofName (L.imageName τ hτ) := by
  let : IsFunction (B.mapGraph L.nameDomain e (L.genericGraphName_isName hP)) := L.genericGraph_isFunction hP hG
  exact B.mapGraph_value L.nameDomain e (L.genericGraphName_isName hP)
    (fun _ hσ ↦ (L.nameDomain_name hσ).mono hP)
    (fun _ hσ ↦ L.image_name (L.nameDomain_rank hσ) (L.nameDomain_name hσ))
    (mem_sep_iff.mpr ⟨hτ, τ.property⟩)

theorem genericGraph_domain_transitive : IsTransitive (domain (L.genericGraph hP)) := by
  let := L.source_correct.ordinal
  let := hierarchy_transitive δ
  constructor
  intro x hx y hy
  obtain ⟨τ, hτ, rfl⟩ := (L.genericGraph_domain hP x).mp hx
  obtain ⟨ν, p, _, hp, he⟩ := (B.mem_ofName_iff _ y).mp hy
  have hν : ν.val ∈ hierarchy δ :=
    (kpair_components_mem_transitive ((hierarchy_transitive δ).mem_trans hp hτ)).1
  exact (L.genericGraph_domain hP y).mpr ⟨⟨ν.val, forcingName_subname τ.property hp⟩, hν, he⟩

include hG in
theorem genericGraph_bounded_iff {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsBoundedSetFormula φ) (v : Fin n → B.Model) (hv : ∀ i, v i ∈ domain (L.genericGraph hP)) :
    φ.Evalb v ↔ φ.Evalb (fun i ↦ (L.genericGraph hP) ‘ (v i)) := by
  classical
  have hn (i : Fin n) := (L.genericGraph_domain hP (v i)).mp (hv i)
  let names : Fin n → ForcingName A.P := fun i ↦ (hn i).choose
  have hr (i : Fin n) : (names i).val ∈ hierarchy δ := (hn i).choose_spec.1
  have he (i : Fin n) : v i = B.ofName ⟨(names i).val, (names i).property.mono hP⟩ :=
    (hn i).choose_spec.2
  let j := A.genericInclusion B hG
  have hsrc : φ.Evalb (A.ofName ∘ names) ↔ φ.Evalb v := by
    have ht := j.bounded_elementary hφ (A.ofName ∘ names)
    have hh : (fun i ↦ j ((A.ofName ∘ names) i)) = v := by
      funext i
      exact (A.genericInclusion_ofName B hP hG (names i)).trans (he i).symm
    rwa [hh] at ht
  have ht := L.bounded_formula_iff hφ names hr
  have him : (fun i ↦ B.ofName (L.imageName (names i) (hr i))) =
      (fun i ↦ (L.genericGraph hP) ‘ (v i)) := by
    funext i
    rw [he i, L.genericGraph_value hP hG]
  rw [him] at ht
  exact hsrc.symm.trans ht

include hG in
theorem genericGraph_injective : Injective (L.genericGraph hP) := by
  let := L.genericGraph_isFunction hP hG
  intro x y z hx hy
  have hxd := mem_domain_of_kpair_mem hx
  have hyd := mem_domain_of_kpair_mem hy
  have h := L.genericGraph_bounded_iff hP hG
    (IsBoundedSetFormula.rel Language.Set.Rel.eq ![.bvar 0, .bvar 1]) ![x, y]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hxd, hyd])
  have he : (L.genericGraph hP) ‘ x = (L.genericGraph hP) ‘ y :=
    (value_eq_of_kpair_mem hx).trans (value_eq_of_kpair_mem hy).symm
  exact (show x = y ↔ (L.genericGraph hP) ‘ x = (L.genericGraph hP) ‘ y from by
    simpa [Semiformula.Evalb, Structure.rel] using h).mpr he

include hG in
theorem genericGraph_boundedElementary : IsBoundedElementaryGraph (L.genericGraph hP) :=
  ⟨L.genericGraph_isFunction hP hG, L.genericGraph_domain_transitive hP,
    fun hφ v hv ↦ L.genericGraph_bounded_iff hP hG hφ v hv⟩

include hG in
theorem genericGraph_domain_eq_rank_image :
    domain (L.genericGraph hP) = A.genericInclusion B hG (hierarchy (A.check δ)) := by
  let := L.source_correct.ordinal
  apply mem_ext
  intro x
  constructor
  · intro hx
    obtain ⟨τ, hτ, rfl⟩ := (L.genericGraph_domain hP x).mp hx
    rw [← A.genericInclusion_ofName B hP hG]
    exact ((A.genericInclusion B hG).mem_iff _ _).mpr (A.ofName_mem_checked_hierarchy τ hτ)
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (A.genericInclusion B hG).endExtension _ x hx
    obtain ⟨τ, hτ, rfl⟩ := (A.mem_checked_hierarchy_iff_low_name L.source_correct L.poset_mem y).mp hy
    exact (L.genericGraph_domain hP _).mpr ⟨τ, hτ, A.genericInclusion_ofName B hP hG τ⟩

include hG in
theorem check_mem_genericGraph_domain {x : V} (hx : x ∈ hierarchy δ) :
    B.check x ∈ domain (L.genericGraph hP) := by
  let := L.source_correct.ordinal
  rw [L.genericGraph_domain_eq_rank_image hP hG, ← A.genericInclusion_check B hG]
  apply ((A.genericInclusion B hG).mem_iff _ _).mpr
  exact A.ofName_mem_checked_hierarchy
    ⟨checkName A.one x, checkName_isName A.top.1 x⟩ (L.checkName_mem_source hx)

include hG in
theorem genericGraph_check (heone : e ‘ A.one = B.one) {x : V} (hx : x ∈ hierarchy δ) :
    (L.genericGraph hP) ‘ (B.check x) = B.check (e ‘ x) := by
  let τ : ForcingName A.P := ⟨checkName A.one x, checkName_isName A.top.1 x⟩
  have ht : B.ofName ⟨τ.val, τ.property.mono hP⟩ = B.check x :=
    (A.genericInclusion_ofName B hP hG τ).symm.trans (A.genericInclusion_check B hG x)
  rw [← ht, L.genericGraph_value hP hG τ (L.checkName_mem_source hx)]
  change B.ofName ⟨e ‘ (checkName A.one x), _⟩ = B.ofName ⟨checkName B.one (e ‘ x), _⟩
  congr 1
  apply Subtype.ext
  change e ‘ (checkName A.one x) = checkName B.one (e ‘ x)
  rw [successorRankEmbedding_value_checkName L.source_correct L.target_correct L.embedding
    L.one_mem_source hx, heone]

end SuccessorRankLiftData
end ZFVP
