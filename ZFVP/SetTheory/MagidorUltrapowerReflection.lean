import ZFVP.SetTheory.SmallSubsetClosedModel
import ZFVP.ModelTheory.EndExtensionCodedEmbedding
import ZFVP.ModelTheory.EndExtensionCriticalPoint
import ZFVP.ModelTheory.TransitiveZFInaccessible
import ZFVP.ModelTheory.CriticalPointRestriction
import ZFVP.ModelTheory.TransitiveZFInaccessibleDownward

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def inaccessibleMagidorFormula : SetTheorySemisentence 3 :=
  “κ γ η. ∃ β ∈ κ, ∃ α ∈ β, ∃ A B e,
    η ∈ α ∧ !choicelessInaccessibleFormula β ∧
    !piOneHierarchyFormula A β ∧ !piOneHierarchyFormula B γ ∧
    !piOneMembershipEmbeddingFormula A B e ∧
    !boundedCriticalPointFormula A e α ∧ !boundedPairMemberFormula e α κ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_inaccessibleMagidorFormula (κ γ η : V) :
    inaccessibleMagidorFormula.Evalb ![κ, γ, η] ↔
    ∃ β ∈ κ, ∃ α ∈ β, ∃ A B e : V,
      η ∈ α ∧ IsChoicelessInaccessible β ∧
      (IsOrdinal β ∧ A = hierarchy β) ∧ (IsOrdinal γ ∧ B = hierarchy γ) ∧
      IsCodedMembershipEmbedding A B e ∧ CriticalPointGraphSpec A e α ∧ ⟨α, κ⟩ₖ ∈ e := by
  simp [inaccessibleMagidorFormula, IsHierarchySegment]

theorem inaccessibleMagidor_of_closed_embedding {θ M j κ γ η lam : V}
    [IsOrdinal θ] [IsTransitive M]
    [Nonempty (SetDomain (hierarchy θ))] [Nonempty (SetDomain M)]
    [(SetDomain (hierarchy θ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain M)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hθ : ∀ β ∈ θ, succ β ∈ θ)
    (hj : IsCodedMembershipEmbedding (hierarchy θ) M j)
    (hc : IsCriticalPoint (hierarchy θ) j κ)
    (hγ : IsChoicelessInaccessible γ) (hκγ : κ ∈ γ) (hγθ : γ ∈ θ)
    (hγκ : γ ∈ j ‘ κ) (hη : η ∈ κ)
    (hclosed : ∀ y, y ⊆ M → IsNonempty y → y ≤# lam → y ∈ M)
    (hcard : hierarchy γ ≤# lam) :
    ∃ β ∈ κ, IsChoicelessInaccessible β ∧ ∃ α ∈ β, η ∈ α ∧ ∃ e : V,
      IsCodedMembershipEmbedding (hierarchy β) (hierarchy γ) e ∧
      IsCriticalPoint (hierarchy β) e α ∧ e ‘ α = κ := by
  let := hγ.1
  let := hc.ordinal
  let := hierarchy_transitive θ
  let := hierarchy_transitive γ
  let := IsFunction.of_mem hj.function
  have hempty : (∅ : V) ∈ M := by
    simpa only [TransitiveZF.empty_val M] using (∅ : SetDomain M).property
  have hAM := small_transitive_subset_of_subset_closure hempty hclosed hcard
  have hA_mem := small_transitive_mem_of_subset_closure hempty hclosed hcard
  have hγcard : γ ≤# lam := (cardLE_of_subset (ordinal_subset_hierarchy γ)).trans hcard
  have hγM : γ ∈ M := small_transitive_mem_of_subset_closure hempty hclosed hγcard
  have hκM : κ ∈ M := (inferInstance : IsTransitive M).mem_trans hκγ hγM
  have hγH : γ ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr hγθ
  have hAH : hierarchy γ ∈ hierarchy θ := hierarchy_mem hγθ
  have hηH : η ∈ hierarchy θ := (hierarchy_transitive θ).mem_trans hη hc.mem_domain
  have he : IsCodedMembershipEmbedding (hierarchy γ) (j ‘ (hierarchy γ)) (j ↾ (hierarchy γ)) :=
    modelEmbedding_restrict hj hAH ⟨κ, ordinal_mem_hierarchy_iff.mpr hκγ⟩
  have heM : j ↾ (hierarchy γ) ∈ M := function_mem_of_small_subset_closure hclosed he.function hAM
    ((inferInstance : IsTransitive M).transitive _ (function_value_mem hj.function hAH)) hcard
  let sk : SetDomain (hierarchy θ) := ⟨κ, hc.mem_domain⟩
  let sg : SetDomain (hierarchy θ) := ⟨γ, hγH⟩
  let se : SetDomain (hierarchy θ) := ⟨η, hηH⟩
  let sA : SetDomain (hierarchy θ) := ⟨hierarchy γ, hAH⟩
  let g : SetDomain M := ⟨γ, hγM⟩
  let k : SetDomain M := ⟨κ, hκM⟩
  let e : SetDomain M := ⟨j ↾ (hierarchy γ), heM⟩
  have hgo : IsOrdinal g := (TransitiveZF.ordinal_iff M g).mpr hγ.1
  let := hgo
  let := hierarchy_transitive g
  have hAval : (hierarchy g).val = hierarchy γ := TransitiveZF.hierarchy_val M g hgo hAM
  have hmap : (hj.toFunction sA) = hierarchy (hj.toFunction sg) := by
    have hs := (TransitiveZF.rankHierarchy_formula θ sA sg).mpr ⟨hγ.1, rfl⟩
    have ht := (hj.eval_semisentence piOneHierarchyFormula ![sA, sg]).mp hs
    have hv : hj.toFunction ∘ ![sA, sg] = ![hj.toFunction sA, hj.toFunction sg] := by
      funext i
      exact Fin.cases rfl (fun t ↦ Fin.cases rfl (fun z ↦ Fin.elim0 z) t) i
    rw [hv] at ht
    exact ((eval_piOneHierarchyFormula _ _).mp ht).2
  have hei : IsCodedMembershipEmbedding (hierarchy g) (hj.toFunction sA) e := by
    apply (TransitiveZF.codedMembershipEmbedding_iff M _ _ _).mp
    change IsCodedMembershipEmbedding (hierarchy g).val (j ‘ (hierarchy γ)) (j ↾ (hierarchy γ))
    rw [hAval]
    exact he
  have hcri : IsCriticalPoint (hierarchy g) e k := by
    apply (MembershipEndExtension.transitiveSubtype M).criticalPoint_iff.mp
    have hr := hc.restrict hj.function ((hierarchy_transitive θ).transitive _ hAH)
      (ordinal_mem_hierarchy_iff.mpr hκγ)
    change IsCriticalPoint (hierarchy g).val (j ↾ (hierarchy γ)) κ
    rw [hAval]
    exact hr
  have hp : (⟨k, hj.toFunction sk⟩ₖ : SetDomain M) ∈ e := by
    change (⟨k, hj.toFunction sk⟩ₖ : SetDomain M).val ∈ j ↾ (hierarchy γ)
    rw [TransitiveZF.kpair_val]
    change ⟨κ, j ‘ κ⟩ₖ ∈ j ↾ (hierarchy γ)
    have hfun := he.function
    let := IsFunction.of_mem hfun
    have hv : (j ↾ (hierarchy γ)) ‘ κ = j ‘ κ := value_restrict
      (by rw [domain_eq_of_mem_function hj.function]; exact hc.mem_domain)
      (ordinal_mem_hierarchy_iff.mpr hκγ)
    rw [← hv]
    exact kpair_value_mem (by rw [domain_eq_of_mem_function hfun]; exact ordinal_mem_hierarchy_iff.mpr hκγ)
  have ht : inaccessibleMagidorFormula.Evalb
      ![hj.toFunction sk, hj.toFunction sg, hj.toFunction se] := by
    apply (eval_inaccessibleMagidorFormula _ _ _).mpr
    refine ⟨g, hγκ, k, hκγ, hierarchy g, hj.toFunction sA, e, ?_,
      TransitiveZF.choicelessInaccessible_downward M g hγ hAM,
      ⟨hgo, rfl⟩, ⟨(TransitiveZF.ordinal_iff M (hj.toFunction sg)).mpr (hj.value_ordinal hγ.1 hγH), hmap⟩,
      hei, (criticalPoint_iff_graphSpec hei.function).mp hcri, hp⟩
    change j ‘ η ∈ κ
    rw [hc.fixed_below hη]
    exact hη
  have hv : hj.toFunction ∘ ![sk, sg, se] = ![hj.toFunction sk, hj.toFunction sg, hj.toFunction se] := by
    funext i
    exact Fin.cases rfl (fun t ↦ Fin.cases rfl (fun u ↦ Fin.cases rfl (fun z ↦ Fin.elim0 z) u) t) i
  have hs := (hj.eval_semisentence inaccessibleMagidorFormula ![sk, sg, se]).mpr (hv ▸ ht)
  obtain ⟨β, hβ, α, hα, A, B, f, hηα, hβin, hA, hB, hf, hcrit, hpair⟩ :=
    (eval_inaccessibleMagidorFormula sk sg se).mp hs
  have hβext := (rank_choicelessInaccessible_iff hθ β).mp hβin
  have hAext : A.val = hierarchy β.val := by
    rw [hA.2]
    exact TransitiveZF.rankHierarchy_val θ β hA.1
  have hBext : B.val = hierarchy γ := by
    rw [hB.2]
    exact TransitiveZF.rankHierarchy_val θ sg hB.1
  have hfe : IsCodedMembershipEmbedding (hierarchy β.val) (hierarchy γ) f.val := by
    rw [← hAext, ← hBext]
    exact (TransitiveZF.codedMembershipEmbedding_iff (hierarchy θ) A B f).mpr hf
  have hce : IsCriticalPoint (hierarchy β.val) f.val α.val := by
    let := hA.1
    let : IsTransitive A := hA.2 ▸ hierarchy_transitive β
    have hi := (criticalPoint_iff_graphSpec hf.function).mpr hcrit
    have hh := (MembershipEndExtension.transitiveSubtype (hierarchy θ)).criticalPoint_map hi
    change IsCriticalPoint A.val f.val α.val at hh
    rwa [hAext] at hh
  refine ⟨β.val, hβ, hβext, α.val, hα, hηα, f.val, hfe, hce, ?_⟩
  have hpV : ⟨α.val, κ⟩ₖ ∈ f.val := by
    change (⟨α, sk⟩ₖ : SetDomain (hierarchy θ)).val ∈ f.val at hpair
    simpa only [TransitiveZF.kpair_val] using hpair
  let := IsFunction.of_mem hfe.function
  exact value_eq_of_kpair_mem hpV

end ZFVP
