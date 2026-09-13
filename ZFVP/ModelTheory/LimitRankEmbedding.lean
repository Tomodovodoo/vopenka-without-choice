import ZFVP.ModelTheory.CriticalPointZF
import ZFVP.SetTheory.BoundedRankTables

/-! Rank preservation needs only a limit source rank and a transitive target.
The bounded rank table used in the proof belongs to the source rank. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCodedMembershipEmbedding.bounded_formula_iff {A B f : V}
    [IsTransitive A] [IsTransitive B] (h : IsCodedMembershipEmbedding A B f)
    {n : ℕ} {φ : SetTheorySemisentence n} (hφ : IsBoundedSetFormula φ)
    (v : Fin n → V) (hv : ∀ i, v i ∈ A) :
    φ.Evalb v ↔ φ.Evalb (fun i ↦ f ‘ (v i)) := by
  let b : Fin n → SetDomain A := fun i ↦ ⟨v i, hv i⟩
  exact (bounded_formula_absolute A hφ b).symm.trans
    ((h.eval_semisentence φ b).trans (bounded_formula_absolute B hφ (h.toFunction ∘ b)))

theorem IsCodedMembershipEmbedding.value_transitive {A B f T : V}
    [IsTransitive A] [IsTransitive B] (h : IsCodedMembershipEmbedding A B f)
    (hT : T ∈ A) (ht : IsTransitive T) : IsTransitive (f ‘ T) :=
  (h.bounded_defined_iff isTransitiveFormula_bounded (fun v ↦ IsTransitive (v 0))
    ![T] (by simp [hT])).mp ht

theorem rankTable_exists_in_limit {δ T : V} [IsOrdinal δ] [IsTransitive T]
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hT : T ∈ hierarchy δ) :
    ∃ g ∈ hierarchy δ, IsRankTable T (rank T) g := by
  obtain ⟨R, g, hg⟩ := rankTable_exists T
  have hgr : g ∈ rank T ^ T := by
    apply mem_function_of_mem_function_of_subset (mem_function_range_of_mem_function hg.1)
    intro y hy
    obtain ⟨x, hp⟩ := mem_range_iff.mp hy
    have hx := (mem_of_mem_functions hg.1 hp).1
    let := IsFunction.of_mem hg.1
    rw [← value_eq_of_kpair_mem hp, rankTable_correct hg x hx]
    exact rank_mem hx
  have hr : rank T ∈ hierarchy δ := by
    rw [mem_hierarchy_iff_rank_mem, rank_of_ordinal]
    exact (mem_hierarchy_iff_rank_mem _ _).mp hT
  exact ⟨g, (hierarchy_transitive δ).mem_trans hgr
    (function_mem_hierarchy_limit hδ hT hr), hgr, hg.2⟩

theorem limitRankEmbedding_value_rank {δ B f x : V} [IsOrdinal δ] [IsTransitive B]
    (hδ : ∀ β ∈ δ, succ β ∈ δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) B f) (hx : x ∈ hierarchy δ) :
    f ‘ (rank x) = rank (f ‘ x) := by
  let := hierarchy_transitive δ
  let T := hierarchy (succ (rank x))
  let : IsTransitive T := hierarchy_transitive _
  have hrδ := (mem_hierarchy_iff_rank_mem _ _).mp hx
  have hT : T ∈ hierarchy δ := by
    change hierarchy (succ (rank x)) ∈ hierarchy δ
    rw [mem_hierarchy_iff_rank_mem, rank_hierarchy]
    exact hδ _ hrδ
  have hxT : x ∈ T := by
    change x ∈ hierarchy (succ (rank x))
    rw [mem_hierarchy_iff_rank_mem]
    simp
  have hRT : rank T ∈ hierarchy δ := by
    rw [mem_hierarchy_iff_rank_mem, rank_of_ordinal]
    exact (mem_hierarchy_iff_rank_mem _ _).mp hT
  obtain ⟨g, hgδ, hg⟩ := rankTable_exists_in_limit hδ hT
  let : IsTransitive (f ‘ T) := h.value_transitive hT inferInstance
  have hs := (eval_boundedRankTableFormula (rank T) g).mpr hg
  have he := (h.bounded_formula_iff boundedRankTableFormula_bounded ![T, rank T, g]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hT, hRT, hgδ])).mp hs
  have hv : (fun i ↦ f ‘ (![T, rank T, g] i)) = ![f ‘ T, f ‘ (rank T), f ‘ g] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl
      (fun k ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) k) j) i
  rw [hv] at he
  have ht := (eval_boundedRankTableFormula (f ‘ (rank T)) (f ‘ g)).mp he
  have hval := h.value_apply hgδ hT (IsFunction.of_mem hg.1)
    (domain_eq_of_mem_function hg.1) hxT
  rw [rankTable_correct hg x hxT] at hval
  exact hval.symm.trans (rankTable_correct ht _ ((h.value_mem_iff hx hT).mpr hxT))

end ZFVP
