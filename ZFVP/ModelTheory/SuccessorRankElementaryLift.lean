import ZFVP.ModelTheory.SuccessorRankForcingElementarity
import ZFVP.ModelTheory.SuccessorRankLiftDomain
import ZFVP.ModelTheory.FiniteParameterElementarity

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SuccessorRankLiftData
variable {A B : ForcingContext V} {δ ε e : V} (L : SuccessorRankLiftData A B δ ε e)

noncomputable def sourceRankValue (τ : ForcingName A.P) (hτ : τ.val ∈ hierarchy δ) :
    SetDomain (hierarchy (A.check δ)) :=
  ⟨A.ofName τ, (A.mem_checked_hierarchy_iff_low_name L.source_correct L.poset_mem _).mpr ⟨τ, hτ, rfl⟩⟩

noncomputable def targetRankValue (τ : ForcingName A.P) (hτ : τ.val ∈ hierarchy δ) :
    SetDomain (hierarchy (B.check ε)) := ⟨B.ofName (L.imageName τ hτ), L.imageName_mem_rank τ hτ⟩

theorem rank_formula_forward {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → ForcingName A.P) (hv : ∀ i, (v i).val ∈ hierarchy δ)
    (ht : φ.Evalb (fun i ↦ L.sourceRankValue (v i) (hv i))) :
    φ.Evalb (fun i ↦ L.targetRankValue (v i) (hv i)) := by
  let := L.source_correct.ordinal
  let := L.target_correct.ordinal
  obtain ⟨p, hpG, hpF⟩ := (A.rankName_formula_truth L.source_correct L.poset_mem φ v hv).mp ht
  have hpδ := (hierarchy_transitive δ).mem_trans (A.generic.1.1 p hpG) L.poset_mem
  have hord : IsForcingPreorder (e ‘ A.P) (e ‘ A.R) := by
    rw [L.poset_image, L.relation_image]
    exact B.order
  have hm := (successorRankEmbedding_rankForcing_iff L.source_correct L.target_correct L.embedding
    L.poset_mem L.relation_mem hpδ A.order hord φ (fun i ↦ (v i).val) hv (fun i ↦ (v i).property)).mp hpF
  have hB : B.P ∈ hierarchy ε := L.poset_image ▸
    (successorRankElementaryMap L.embedding ⟨A.P, L.poset_mem⟩).property
  have hn (i : Fin n) : (L.imageName (v i) (hv i)).val ∈ hierarchy ε :=
    (successorRankElementaryMap L.embedding ⟨(v i).val, hv i⟩).property
  apply (B.rankName_formula_truth L.target_correct hB φ (fun i ↦ L.imageName (v i) (hv i)) hn).mpr
  refine ⟨e ‘ p, L.generic p hpG, ?_⟩
  simpa only [L.poset_image, L.relation_image, imageName] using hm

theorem rank_formula_iff {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → ForcingName A.P) (hv : ∀ i, (v i).val ∈ hierarchy δ) :
    φ.Evalb (fun i ↦ L.sourceRankValue (v i) (hv i)) ↔
      φ.Evalb (fun i ↦ L.targetRankValue (v i) (hv i)) := by
  classical
  constructor
  · exact L.rank_formula_forward φ v hv
  · intro ht
    by_contra hn
    have hf := L.rank_formula_forward (∼φ) v hv (by simpa using hn)
    exact (show ¬φ.Evalb (fun i ↦ L.targetRankValue (v i) (hv i)) from by simpa using hf) ht

noncomputable def sourceRankName (x : SetDomain (hierarchy (A.check δ))) : ForcingName A.P :=
  ((A.mem_checked_hierarchy_iff_low_name L.source_correct L.poset_mem x.val).mp x.property).choose

theorem sourceRankName_rank (x : SetDomain (hierarchy (A.check δ))) :
    (L.sourceRankName x).val ∈ hierarchy δ :=
  ((A.mem_checked_hierarchy_iff_low_name L.source_correct L.poset_mem x.val).mp x.property).choose_spec.1

theorem sourceRankName_value (x : SetDomain (hierarchy (A.check δ))) :
    A.ofName (L.sourceRankName x) = x.val :=
  ((A.mem_checked_hierarchy_iff_low_name L.source_correct L.poset_mem x.val).mp x.property).choose_spec.2.symm

noncomputable def rankLiftFun (x : SetDomain (hierarchy (A.check δ))) :
    SetDomain (hierarchy (B.check ε)) := L.targetRankValue (L.sourceRankName x) (L.sourceRankName_rank x)

theorem rankLiftFun_sourceRankValue (τ : ForcingName A.P) (hτ : τ.val ∈ hierarchy δ) :
    L.rankLiftFun (L.sourceRankValue τ hτ) = L.targetRankValue τ hτ := by
  apply Subtype.ext
  exact (L.image_eq_iff _ τ (L.sourceRankName_rank _) hτ).mpr (L.sourceRankName_value _)

theorem rankLiftFun_formula_iff {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → SetDomain (hierarchy (A.check δ))) : φ.Evalb v ↔ φ.Evalb (L.rankLiftFun ∘ v) := by
  have hf := L.rank_formula_iff φ (fun i ↦ L.sourceRankName (v i)) (fun i ↦ L.sourceRankName_rank (v i))
  have hs : (fun i ↦ L.sourceRankValue (L.sourceRankName (v i)) (L.sourceRankName_rank (v i))) = v := by
    funext i
    exact Subtype.ext (L.sourceRankName_value (v i))
  rw [hs] at hf
  exact hf

noncomputable def rankElementaryLift :
    ElementaryMap (SetDomain (hierarchy (A.check δ))) (SetDomain (hierarchy (B.check ε))) where
  toFun := L.rankLiftFun
  elementary φ v a := by
    let := L.source_correct.ordinal
    have hem : (∅ : V) ∈ hierarchy δ := (hierarchy_transitive δ).mem_trans empty_mem_ω
      (ordinal_mem_hierarchy_iff.mpr L.source_correct.omega_lt)
    let : Nonempty (SetDomain (hierarchy (A.check δ))) :=
      ⟨L.sourceRankValue ⟨∅, empty_forcingName A.P⟩ hem⟩
    exact elementary_of_semisentences L.rankLiftFun L.rankLiftFun_formula_iff φ v a

end SuccessorRankLiftData
end ZFVP
