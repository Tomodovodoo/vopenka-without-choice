import ZFVP.ModelTheory.SuccessorRankCriticalPoint

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def largestOrdinalFormula : SetTheorySemisentence 1 :=
  “a. !IsOrdinal.dfn a ∧ ∀ x, !IsOrdinal.dfn x → !isSubsetOf x a”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_largestOrdinal_successorRank (δ : V) [IsOrdinal δ]
    (a : SetDomain (hierarchy (succ δ))) :
    largestOrdinalFormula.Evalb ![a] ↔ a.val = δ := by
  let := hierarchy_transitive (succ δ)
  have ho (x : SetDomain (hierarchy (succ δ))) :
      IsOrdinal x ↔ IsOrdinal x.val := by
    simpa using bounded_formula_absolute _ isOrdinalFormula_bounded ![x]
  have hs (x : SetDomain (hierarchy (succ δ))) :
      x ⊆ a ↔ x.val ⊆ a.val := by
    simpa using bounded_formula_absolute _ isSubsetOf_bounded ![x, a]
  have hev : largestOrdinalFormula.Evalb ![a] ↔
      IsOrdinal a.val ∧ ∀ x : SetDomain (hierarchy (succ δ)), IsOrdinal x.val → x.val ⊆ a.val := by
    simp [largestOrdinalFormula]
    constructor
    · rintro ⟨ha, h⟩
      exact ⟨(ho a).mp ha, fun x hx ↦ (hs x).mp (h x ((ho x).mpr hx))⟩
    · rintro ⟨ha, h⟩
      exact ⟨(ho a).mpr ha, fun x hx ↦ (hs x).mpr (h x ((ho x).mp hx))⟩
  rw [hev]
  constructor
  · rintro ⟨ha, h⟩
    let := ha
    have haδ : a.val ⊆ δ := by
      have hm := ordinal_mem_hierarchy_iff.mp a.property
      rcases mem_succ_iff.mp hm with he | hm
      · rw [he]
      · exact IsOrdinal.toIsTransitive.transitive _ hm
    exact SetTheory.subset_antisymm haδ
      (h ⟨δ, ordinal_mem_hierarchy_iff.mpr (mem_succ_self δ)⟩ inferInstance)
  · intro he
    refine ⟨by rw [he]; infer_instance, fun x hx ↦ ?_⟩
    let := hx
    rw [he]
    have hm := ordinal_mem_hierarchy_iff.mp x.property
    rcases mem_succ_iff.mp hm with he | hm
    · rw [he]
    · exact IsOrdinal.toIsTransitive.transitive _ hm

theorem successorRankEmbedding_value_height {δ ε f : V} [IsOrdinal δ] [IsOrdinal ε]
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) f) :
    f ‘ δ = ε := by
  let a : SetDomain (hierarchy (succ δ)) :=
    ⟨δ, ordinal_mem_hierarchy_iff.mpr (mem_succ_self δ)⟩
  have ht := (h.eval_semisentence largestOrdinalFormula ![a]).mp
    ((eval_largestOrdinal_successorRank δ a).mpr rfl)
  have hv : h.toFunction ∘ ![a] = ![h.toFunction a] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [hv] at ht
  exact (eval_largestOrdinal_successorRank ε (h.toFunction a)).mp ht

theorem successorRankEmbedding_criticalPoint_lt_height {δ ε f κ : V}
    [IsOrdinal δ] [IsOrdinal ε]
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) f)
    (hc : IsCriticalPoint (hierarchy (succ δ)) f κ) (he : f ‘ κ ∈ ε) : κ ∈ δ := by
  let := hc.ordinal
  have hm := ordinal_mem_hierarchy_iff.mp hc.mem_domain
  rcases mem_succ_iff.mp hm with heq | hlt
  · rw [heq, successorRankEmbedding_value_height h] at he
    exact False.elim (mem_irrefl ε he)
  · exact hlt

end ZFVP



