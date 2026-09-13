import ZFVP.SetTheory.EventualRankCertificates
import ZFVP.ModelTheory.TransitiveZFInaccessible
import ZFVP.SetTheory.WoodinClosedFiniteModels

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankCertificateHolds_absolute {δ : V} [IsOrdinal δ]
    [Nonempty (SetDomain (hierarchy δ))] [(SetDomain (hierarchy δ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (φ : SetTheorySemisentence 2) (z x ξ : SetDomain (hierarchy δ)) (hξ : IsOrdinal ξ) :
    RankCertificateHolds φ z x ξ ↔ RankCertificateHolds φ z.val x.val ξ.val := by
  let := hierarchy_transitive δ
  let := (TransitiveZF.ordinal_iff (hierarchy δ) ξ).mp hξ
  have hH : (hierarchy ξ).val = hierarchy ξ.val := by
    apply TransitiveZF.hierarchy_val (hierarchy δ) ξ hξ
    exact hierarchy_mono (IsOrdinal.toIsTransitive.transitive _
      (ordinal_mem_hierarchy_iff.mp ξ.property))
  have hb := bounded_formula_absolute (hierarchy δ)
    (boundedDomainParametersFormula_bounded φ) ![hierarchy ξ, z, x]
  have hv : (fun i : Fin 3 ↦ ((![hierarchy ξ, z, x] : Fin 3 → SetDomain (hierarchy δ)) i).val) =
      ![hierarchy ξ.val, z.val, x.val] := by
    funext i
    exact Fin.cases hH (Fin.cases rfl (Fin.cases rfl (fun j ↦ Fin.elim0 j))) i
  simp only [hv] at hb
  unfold RankCertificateHolds
  change z.val ∈ (hierarchy ξ).val ∧ x.val ∈ (hierarchy ξ).val ∧ _ ↔ _
  rw [hH]
  exact and_congr Iff.rfl (and_congr Iff.rfl hb)

/-- Internal eventual evaluation ranges over precisely the ambient inaccessible
heights below the endpoint. -/
theorem eval_eventualRankCertificate_in_rank {δ : V} (hδ : IsChoicelessInaccessible δ) :
    letI := hδ.1
    letI := rankDomain_nonempty hδ.2.1
    letI := hδ.rankCriterion.models_zf
    ∀ (φ : SetTheorySemisentence 2) (z x : SetDomain (hierarchy δ)),
      (eventualRankCertificate φ).Evalb ![z, x] ↔
        ∃ η ∈ δ, ∀ ξ ∈ δ, η ∈ ξ → IsChoicelessInaccessible ξ →
          RankCertificateHolds φ z.val x.val ξ := by
  let := hδ.1
  let := rankDomain_nonempty hδ.2.1
  let := hδ.rankCriterion.models_zf
  let := hierarchy_transitive δ
  intro φ z x
  rw [eval_eventualRankCertificate_raw]
  have hs := hδ.rankCriterion.2.2.1
  constructor
  · rintro ⟨η, ho, h⟩
    let := (TransitiveZF.ordinal_iff (hierarchy δ) η).mp ho
    refine ⟨η.val, ordinal_mem_hierarchy_iff.mp η.property, ?_⟩
    intro ξ hξδ hηξ hξ
    let := hξ.1
    let t : SetDomain (hierarchy δ) := ⟨ξ, ordinal_mem_hierarchy_iff.mpr hξδ⟩
    have ht : IsChoicelessInaccessible t := (rank_choicelessInaccessible_iff hs t).mpr hξ
    exact (rankCertificateHolds_absolute φ z x t ht.1).mp (h t hηξ ht)
  · rintro ⟨η, hηδ, h⟩
    let := IsOrdinal.of_mem hηδ
    let a : SetDomain (hierarchy δ) := ⟨η, ordinal_mem_hierarchy_iff.mpr hηδ⟩
    refine ⟨a, (TransitiveZF.ordinal_iff (hierarchy δ) a).mpr inferInstance, ?_⟩
    intro t hat ht
    have ht' := (rank_choicelessInaccessible_iff hs t).mp ht
    let := ht'.1
    exact (rankCertificateHolds_absolute φ z x t ht.1).mpr
      (h t.val (ordinal_mem_hierarchy_iff.mp t.property) hat ht')

/-- A rank computation that stabilizes below a Woodin-supercompact gives an
internal Sigma-three graph at that endpoint. -/
theorem eval_eventualRankCertificate_of_stable {δ a : V}
    (hδ : IsWoodinSupercompact δ) :
    letI := hδ.inaccessible.1
    letI := rankDomain_nonempty hδ.inaccessible.2.1
    letI := hδ.inaccessible.rankCriterion.models_zf
    ∀ (φ : SetTheorySemisentence 2) (z x : SetDomain (hierarchy δ)),
      (∃ η ∈ δ, ∀ ξ ∈ δ, η ∈ ξ → IsChoicelessInaccessible ξ →
        (RankCertificateHolds φ z.val x.val ξ ↔ z.val = a)) →
      ((eventualRankCertificate φ).Evalb ![z, x] ↔ z.val = a) := by
  let := hδ.inaccessible.1
  let := rankDomain_nonempty hδ.inaccessible.2.1
  let := hδ.inaccessible.rankCriterion.models_zf
  intro φ z x hstable
  obtain ⟨η, hηδ, he⟩ := hstable
  rw [eval_eventualRankCertificate_in_rank hδ.inaccessible]
  constructor
  · rintro ⟨b, hbδ, hb⟩
    let := IsOrdinal.of_mem hηδ
    let := IsOrdinal.of_mem hbδ
    let := IsOrdinal.of_mem (ordinal_union_mem hηδ hbδ)
    obtain ⟨ξ, hξδ, hUξ, hξ⟩ := hδ.inaccessible_above (ordinal_union_mem hηδ hbδ)
    let := hξ.1
    have hηξ : η ∈ ξ := ordinal_mem_of_subset_mem
      (fun y hy ↦ mem_union_iff.mpr (Or.inl hy)) hUξ
    have hbξ : b ∈ ξ := ordinal_mem_of_subset_mem
      (fun y hy ↦ mem_union_iff.mpr (Or.inr hy)) hUξ
    exact (he ξ hξδ hηξ hξ).mp (hb ξ hξδ hbξ hξ)
  · intro hz
    exact ⟨η, hηδ, fun ξ hξδ hηξ hξ ↦ (he ξ hξδ hηξ hξ).mpr hz⟩

theorem eval_eventualRankCertificate_of_rank_graph {δ a : V}
    (hδ : IsWoodinSupercompact δ) :
    letI := hδ.inaccessible.1
    letI := rankDomain_nonempty hδ.inaccessible.2.1
    letI := hδ.inaccessible.rankCriterion.models_zf
    ∀ (φ : SetTheorySemisentence 2) (z x : SetDomain (hierarchy δ)),
      (∃ η ∈ δ, x.val ∈ η ∧ ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
        letI := hξ.1
        letI := rankDomain_nonempty hξ.2.1
        letI := hξ.rankCriterion.models_zf
        ∀ t : SetDomain (hierarchy ξ), t.val = x.val →
          ∃ y : SetDomain (hierarchy ξ), y.val = a ∧
            ∀ w : SetDomain (hierarchy ξ), φ.Evalb ![w, t] ↔ w = y) →
      ((eventualRankCertificate φ).Evalb ![z, x] ↔ z.val = a) := by
  let := hδ.inaccessible.1
  let := rankDomain_nonempty hδ.inaccessible.2.1
  let := hδ.inaccessible.rankCriterion.models_zf
  intro φ z x hgraph
  obtain ⟨η, hηδ, hxη, hg⟩ := hgraph
  apply eval_eventualRankCertificate_of_stable hδ φ z x
  refine ⟨η, hηδ, ?_⟩
  intro ξ _ hηξ hξ
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := IsOrdinal.of_mem hηδ
  let := IsOrdinal.of_mem hxη
  have hxξ : x.val ∈ ξ := IsOrdinal.toIsTransitive.mem_trans hxη hηξ
  let t : SetDomain (hierarchy ξ) := ⟨x.val, ordinal_mem_hierarchy_iff.mpr hxξ⟩
  obtain ⟨y, hy, he⟩ := hg ξ hηξ hξ t rfl
  simpa only [hy] using rankCertificateHolds_iff_of_graph φ ξ z.val t y he

end ZFVP
