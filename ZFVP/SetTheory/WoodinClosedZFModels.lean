import ZFVP.SetTheory.SigmaOneStarCertificates
import ZFVP.SetTheory.WoodinClosedFiniteModels
import ZFVP.SetTheory.CnOpenModelCertificates
import ZFVP.ModelTheory.EndExtensionOpenModels
import ZFVP.ModelTheory.LimitRankEmbedding

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def closedModelCertificateFormula : SetTheorySemisentence 3 :=
  “aZ C U. !IsTransitive.dfn C ∧ ∃ a ∈ C, ∃ Z ∈ U,
    !boundedKpairFormula aZ a Z ∧ !boundedOpenModelCertificate U C Z”

theorem closedModelCertificateFormula_bounded : IsBoundedSetFormula closedModelCertificateFormula :=
  .and (isTransitiveFormula_bounded.subst _) (.exs (.bvar 1) (.exs (.bvar 3)
    (.and (boundedKpairFormula_bounded.subst _) (boundedOpenModelCertificate_bounded.subst _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_closedModelCertificateFormula (a Z C U : V) :
    closedModelCertificateFormula.Evalb ![⟨a, Z⟩ₖ, C, U] ↔
      IsTransitive C ∧ a ∈ C ∧ Z ∈ U ∧ boundedOpenModelCertificate.Evalb ![U, C, Z] := by
  simp [closedModelCertificateFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]

theorem IsChoicelessInaccessible.zfOpenAxiomCodes_mem {δ : V} (hδ : IsChoicelessInaccessible δ) :
    (zfOpenAxiomCodes : V) ∈ hierarchy δ := by
  let := hδ.1
  let := hierarchy_transitive δ
  have hω : (ω : V) ∈ hierarchy δ := ordinal_mem_hierarchy_iff.mpr hδ.2.1
  let : Nonempty (SetDomain (hierarchy δ)) := ⟨⟨ω, hω⟩⟩
  let := hδ.internalZFModel.models_zf
  exact subset_mem_hierarchy_limit hδ.rankCriterion.2.2.1
    (transitiveZF_membershipFormulaFamily_mem (hierarchy δ))
    (show (zfOpenAxiomCodes : V) ⊆ formulaFamily membershipLanguageCode ∅ from sep_subset)

theorem IsWoodinSupercompact.exists_rankClosed_internalZFModel {δ : V}
    (hδ : IsWoodinSupercompact δ) (α a : V) [IsOrdinal α] :
    ∃ C : V, IsRankFunctionClosed α C ∧ a ∈ C ∧ IsTransitive C ∧ IsInternalZFModel C := by
  let := hδ.1.1
  let Z := (zfOpenAxiomCodes : V)
  have hZδ : Z ∈ hierarchy δ := hδ.inaccessible.zfOpenAxiomCodes_mem
  let η := δ ∪ rank ⟨a, α⟩ₖ
  let : IsOrdinal η := ordinal_union_ordinal δ (rank ⟨a, α⟩ₖ)
  obtain ⟨γ, hηγ, hγ⟩ := sigmaOneStarCorrect_unbounded η
  let := hγ.1.ordinal
  have hδγ : δ ∈ γ := ordinal_mem_of_subset_mem
    (show δ ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inl hz)) hηγ
  have hpγ : ⟨a, α⟩ₖ ∈ hierarchy γ := (mem_hierarchy_iff_rank_mem _ _).mpr
    (ordinal_mem_of_subset_mem
      (show rank ⟨a, α⟩ₖ ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inr hz)) hηγ)
  obtain ⟨_, ρ, hρδ, hρ, x, hx, e, he, κ, hc, heκ, hxe, hrZκ⟩ :=
    hδ.highCritical.2.2 γ hδγ hγ ⟨a, α⟩ₖ hpγ (rank Z) ((mem_hierarchy_iff_rank_mem _ _).mp hZδ)
  let := hρ.1.ordinal
  let := hc.ordinal
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ γ)
  have hκρ := successorRankEmbedding_criticalPoint_lt_height he hc (heκ.symm ▸ hδγ)
  have hZκ : Z ∈ hierarchy κ := (mem_hierarchy_iff_rank_mem _ _).mpr hrZκ
  have hZρ : Z ∈ hierarchy ρ := hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hκρ) _ hZκ
  have heZ := successorRankEmbedding_fixed_below_criticalPoint hρ.1 hγ.1 he hc hκρ Z hZκ
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
  have huδ : u ∈ hierarchy δ := hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hρδ) _ hu
  have huZ := kpair_mem_hierarchy_limit hρ.1.successor_closed hu hZρ
  have hex : ∃ C U : V, IsRankFunctionClosed v C ∧
      closedModelCertificateFormula.Evalb ![⟨u, Z⟩ₖ, C, U] := by
    obtain ⟨U, hU⟩ := (boundedOpenModelCertificate_exists (hierarchy δ) Z).mpr
      hδ.inaccessible.internalZFModel.satisfies_open_codes
    have hZU := (eval_boundedOpenModelCertificate U (hierarchy δ) Z).mp hU |>.2.2.1
    exact ⟨hierarchy δ, U, hδ.inaccessible.rankFunctionClosed hvδ,
      (eval_closedModelCertificateFormula u Z (hierarchy δ) U).mpr
        ⟨hierarchy_transitive δ, huδ, hZU, hU⟩⟩
  obtain ⟨C, hC, U, hU, hclosed, hcert⟩ := hρ.reflect_rankClosed_certificate hδ hvρ huZ
    closedModelCertificateFormula_bounded hex
  have hc' := (successorRankEmbedding_rankFunctionClosed hρ.1 hγ.1 he hvord hv hC).mp hclosed
  rw [hev] at hc'
  have ht := (he.bounded_formula_iff closedModelCertificateFormula_bounded ![⟨u, Z⟩ₖ, C, U]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hinc _ huZ, hinc _ hC, hinc _ hU])).mp hcert
  have hep : e ‘ ⟨u, Z⟩ₖ = ⟨a, Z⟩ₖ := by
    rw [he.value_pair (hinc _ hu) (hinc _ hZρ) (hinc _ huZ), heu, heZ]
  have hvec : (fun i ↦ e ‘ (![⟨u, Z⟩ₖ, C, U] i)) = ![⟨a, Z⟩ₖ, e ‘ C, e ‘ U] := by
    funext i
    exact Fin.cases hep (fun k ↦ Fin.cases rfl (fun l ↦ Fin.cases rfl (fun m ↦ Fin.elim0 m) l) k) i
  rw [hvec] at ht
  obtain ⟨htrans, ha, _, hcert⟩ := (eval_closedModelCertificateFormula a Z (e ‘ C) (e ‘ U)).mp ht
  have hm := (boundedOpenModelCertificate_exists (e ‘ C) Z).mp ⟨e ‘ U, hcert⟩
  exact ⟨e ‘ C, hc', ha, htrans, (satisfiesOpenCodes_zf_iff _).mp hm⟩

theorem IsSigmaOneStarCorrect.rankClosed_internalZFModel {δ γ α a : V}
    (hδ : IsWoodinSupercompact δ) (hγ : IsSigmaOneStarCorrect γ)
    (hα : α ∈ γ) (ha : a ∈ hierarchy γ) :
    ∃ C ∈ hierarchy γ, IsRankFunctionClosed α C ∧ a ∈ C ∧
      IsTransitive C ∧ IsInternalZFModel C := by
  let := hγ.1.ordinal
  let := IsOrdinal.of_mem hα
  have hp := kpair_mem_hierarchy_limit hγ.1.successor_closed ha hγ.1.zfOpenAxiomCodes_mem
  have hex : ∃ C U : V, IsRankFunctionClosed α C ∧
      closedModelCertificateFormula.Evalb ![⟨a, zfOpenAxiomCodes⟩ₖ, C, U] := by
    obtain ⟨C, hc, haC, ht, hm⟩ := hδ.exists_rankClosed_internalZFModel α a
    obtain ⟨U, hU⟩ := (boundedOpenModelCertificate_exists C zfOpenAxiomCodes).mpr hm.satisfies_open_codes
    have hZU := (eval_boundedOpenModelCertificate U C zfOpenAxiomCodes).mp hU |>.2.2.1
    exact ⟨C, U, hc, (eval_closedModelCertificateFormula a zfOpenAxiomCodes C U).mpr ⟨ht, haC, hZU, hU⟩⟩
  obtain ⟨C, hC, U, _, hc, hcert⟩ := hγ.reflect_rankClosed_certificate hδ hα hp
    closedModelCertificateFormula_bounded hex
  obtain ⟨ht, haC, _, hcert⟩ := (eval_closedModelCertificateFormula a zfOpenAxiomCodes C U).mp hcert
  exact ⟨C, hC, hc, haC, ht, (satisfiesOpenCodes_zf_iff C).mp
    ((boundedOpenModelCertificate_exists C zfOpenAxiomCodes).mp ⟨U, hcert⟩)⟩

end ZFVP
