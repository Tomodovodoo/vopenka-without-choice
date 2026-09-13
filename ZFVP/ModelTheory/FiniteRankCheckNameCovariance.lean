import ZFVP.ModelTheory.NormalizedPoolRank
import ZFVP.ModelTheory.LimitRankEmbeddingAction
import ZFVP.SetTheory.BoundedCheckNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem inaccessible_checkNameTable_finite_rank {η one : V}
    (hη : IsChoicelessInaccessible η) (ho : one ∈ hierarchy η) :
    ∃ g ∈ hierarchy (ordinalAdd η (ω : V)),
      IsCheckNameTable one (hierarchy η) (hierarchy η) g := by
  let := hη.1
  let := hierarchy_transitive η
  let hf : ℒₛₑₜ-function₁[V] (checkName one) := by definability
  let g := definableGraph (hierarchy η) (checkName one) hf
  have hg : g ∈ hierarchy η ^ hierarchy η :=
    definableGraph_mem_function_of_mapsTo _ _ _ hf (fun _ hx ↦ hη.checkName_mem_hierarchy ho hx)
  have hU : hierarchy η ∈ hierarchy (ordinalAdd η (ω : V)) := hierarchy_mem (ordinalAdd_omega_gt η)
  have hs : ∀ β ∈ ordinalAdd η (ω : V), succ β ∈ ordinalAdd η (ω : V) :=
    fun _ ↦ ordinalAdd_omega_succ_closed η
  refine ⟨g, (hierarchy_transitive _).mem_trans hg (function_mem_hierarchy_limit hs hU hU), hg, ?_⟩
  intro u hu z
  rw [value_definableGraph _ _ _ hu, mem_checkName_iff]
  apply exists_congr
  intro s
  apply and_congr_right
  intro hsu
  rw [value_definableGraph _ _ _ ((hierarchy_transitive η).mem_trans hsu hu)]

/-- Check-name preservation uses a bounded recursion table in the finite
allowance above an inaccessible. Neither finite-allowance domain needs ZF. -/
theorem finiteRankEmbedding_value_checkName {η B f one x : V}
    (hη : IsChoicelessInaccessible η) [IsTransitive B]
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd η (ω : V))) B f)
    (ho : one ∈ hierarchy η) (hx : x ∈ hierarchy η) :
    f ‘ (checkName one x) = checkName (f ‘ one) (f ‘ x) := by
  let := hη.1
  let := hierarchy_transitive η
  let := hierarchy_transitive (ordinalAdd η (ω : V))
  have hU : hierarchy η ∈ hierarchy (ordinalAdd η (ω : V)) := hierarchy_mem (ordinalAdd_omega_gt η)
  have hlow : hierarchy η ⊆ hierarchy (ordinalAdd η (ω : V)) :=
    (hierarchy_transitive _).transitive _ hU
  obtain ⟨g, hgA, hg⟩ := inaccessible_checkNameTable_finite_rank hη ho
  let := IsFunction.of_mem hg.1
  let : IsTransitive (f ‘ (hierarchy η)) := he.value_transitive hU inferInstance
  have ht := (he.bounded_formula_iff boundedCheckNameTableFormula_bounded
    ![one, hierarchy η, hierarchy η, g]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hlow _ ho, hU, hgA])).mp
      ((eval_boundedCheckNameTableFormula _ _ _ _).mpr hg)
  have hv : (fun i ↦ f ‘ (![one, hierarchy η, hierarchy η, g] i)) =
      ![f ‘ one, f ‘ (hierarchy η), f ‘ (hierarchy η), f ‘ g] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.elim0 m) l) k) j) i
  rw [hv] at ht
  have hgt := (eval_boundedCheckNameTableFormula _ _ _ _).mp ht
  have hval := he.value_apply hgA hU inferInstance (domain_eq_of_mem_function hg.1) hx
  rw [hg.correct x hx] at hval
  exact hval.symm.trans (hgt.correct _ ((he.value_mem_iff (hlow _ hx) hU).mpr hx))

end ZFVP
