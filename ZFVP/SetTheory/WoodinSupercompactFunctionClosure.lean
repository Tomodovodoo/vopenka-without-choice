import ZFVP.SetTheory.InaccessibleFunctionClosure
import ZFVP.SetTheory.WoodinSupercompactInaccessible
import ZFVP.ModelTheory.SuccessorRankFunctionClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def transitiveContainerFormula : SetTheorySemisentence 2 :=
  “a b. a ∈ b ∧ !IsTransitive.dfn b”

theorem transitiveContainerFormula_bounded : IsBoundedSetFormula transitiveContainerFormula :=
  .and (.rel _ _) (isTransitiveFormula_bounded.subst _)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A bounded property valid of every parameter in the inaccessible rank
can be realized, with an arbitrary target parameter, in a set closed under
functions from a prescribed rank. Star reflection supplies the small witness. -/
theorem IsWoodinSupercompact.exists_functionClosed_spec {δ : V}
    (hδ : IsWoodinSupercompact δ) {φ : SetTheorySemisentence 2}
    (hφ : IsBoundedSetFormula φ)
    (hvalid : ∀ u ∈ hierarchy δ, φ.Evalb ![u, hierarchy δ])
    (α a : V) [IsOrdinal α] :
    ∃ b : V, IsRankFunctionClosed α b ∧ φ.Evalb ![a, b] := by
  let := hδ.1.1
  let η := δ ∪ rank ⟨a, α⟩ₖ
  let : IsOrdinal η := ordinal_union_ordinal δ (rank ⟨a, α⟩ₖ)
  obtain ⟨γ, hηγ, hγ⟩ := sigmaOneStarCorrect_unbounded η
  let := hγ.1.ordinal
  have hδγ : δ ∈ γ := ordinal_mem_of_subset_mem
    (show δ ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inl hz)) hηγ
  have hpγ : ⟨a, α⟩ₖ ∈ hierarchy γ := (mem_hierarchy_iff_rank_mem _ _).mpr
    (ordinal_mem_of_subset_mem
      (show rank ⟨a, α⟩ₖ ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inr hz)) hηγ)
  obtain ⟨_, ρ, hρδ, hρ, x, hx, e, he, c, hc, hec, hxe⟩ := hδ.2 γ hδγ hγ ⟨a, α⟩ₖ hpγ
  let := hρ.1.ordinal
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ γ)
  obtain ⟨u, v, hu, hv, _, heu, hev⟩ := successorRankEmbedding_pair_preimages hρ.1 hγ.1 he hx hxe
  have hinc : hierarchy ρ ⊆ hierarchy (succ ρ) := hierarchy_mono
    (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz))
  have hvord : IsOrdinal v := by
    apply (he.bounded_defined_iff isOrdinalFormula_bounded (fun w ↦ IsOrdinal (w 0))
      ![v] (by simpa using hinc v hv)).mpr
    simpa [hev] using (inferInstance : IsOrdinal α)
  let := hvord
  have hvρ : v ∈ ρ := ordinal_mem_hierarchy_iff.mp hv
  have hvδ : v ∈ δ := IsOrdinal.toIsTransitive.mem_trans hvρ hρδ
  have huδ : u ∈ hierarchy δ := hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hρδ) u hu
  obtain ⟨b, hb, hclosed, hcontainer⟩ := hρ.reflect hvρ hu hφ
    (show ∃ b, IsRankFunctionClosed v b ∧ φ.Evalb ![u, b] from
      ⟨hierarchy δ, hδ.inaccessible.rankFunctionClosed hvδ, hvalid u huδ⟩)
  have hclosed' := (successorRankEmbedding_rankFunctionClosed hρ.1 hγ.1 he hvord hv hb).mp hclosed
  rw [hev] at hclosed'
  have hcontainer' := (successorRankEmbedding_pi_iff hρ.1 hγ.1 he
    (.bounded hφ) ![u, b]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hu, hb])).mp hcontainer
  have hv' : (fun i ↦ e ‘ (![u, b] i)) = ![a, e ‘ b] := by
    funext i
    exact Fin.cases heu (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [hv'] at hcontainer'
  exact ⟨e ‘ b, hclosed', hcontainer'⟩

/-- The closure is in the whole ground universe. -/
theorem IsWoodinSupercompact.exists_functionClosed_container {δ : V}
    (hδ : IsWoodinSupercompact δ) (α a : V) [IsOrdinal α] :
    ∃ b : V, IsRankFunctionClosed α b ∧ a ∈ b ∧ IsTransitive b := by
  let := hδ.1.1
  obtain ⟨b, hc, hb⟩ := hδ.exists_functionClosed_spec transitiveContainerFormula_bounded
    (fun u hu ↦ by simpa [transitiveContainerFormula] using
      (show u ∈ hierarchy δ ∧ IsTransitive (hierarchy δ) from ⟨hu, hierarchy_transitive δ⟩)) α a
  exact ⟨b, hc, by simpa [transitiveContainerFormula] using hb⟩

end ZFVP
