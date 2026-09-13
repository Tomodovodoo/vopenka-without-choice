import ZFVP.ModelTheory.SuccessorRankForcing
import ZFVP.ModelTheory.ForcingModel

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure SuccessorRankLiftData (A B : ForcingContext V) (δ ε e : V) : Prop where
  source_correct : Cn 1 δ
  target_correct : Cn 1 ε
  embedding : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e
  poset_mem : A.P ∈ hierarchy δ
  relation_mem : A.R ∈ hierarchy δ
  poset_image : e ‘ A.P = B.P
  relation_image : e ‘ A.R = B.R
  generic : ∀ p ∈ A.G, e ‘ p ∈ B.G

namespace SuccessorRankLiftData

variable {A B : ForcingContext V} {δ ε e : V} (L : SuccessorRankLiftData A B δ ε e)

include L

theorem image_name {τ : V} (hτ : τ ∈ hierarchy δ) (hn : IsForcingName A.P τ) :
    IsForcingName B.P (e ‘ τ) := by
  have h := (successorRankEmbedding_forcingName_iff L.source_correct L.target_correct L.embedding
    L.poset_mem hτ).mp hn
  rwa [L.poset_image] at h

noncomputable def imageName (τ : ForcingName A.P) (hτ : τ.val ∈ hierarchy δ) : ForcingName B.P :=
  ⟨e ‘ τ.val, L.image_name hτ τ.property⟩

set_option maxHeartbeats 800000 in
theorem bounded_formula_forward {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsBoundedSetFormula φ) (v : Fin n → ForcingName A.P)
    (hv : ∀ i, (v i).val ∈ hierarchy δ) (ht : φ.Evalb (A.ofName ∘ v)) :
    φ.Evalb (fun i ↦ B.ofName (L.imageName (v i) (hv i))) := by
  let := L.source_correct.ordinal
  let := hierarchy_transitive δ
  obtain ⟨p, hp, hf⟩ := (forcingFormula_quotient_truth A.P A.R A.G A.order A.generic φ v).mp ht
  have hpδ := (hierarchy_transitive δ).mem_trans (A.generic.1.1 p hp) L.poset_mem
  have hord : IsForcingPreorder (e ‘ A.P) (e ‘ A.R) := by
    rw [L.poset_image, L.relation_image]
    exact B.order
  have he := (successorRankEmbedding_boundedForcing_iff L.source_correct L.target_correct L.embedding
    L.poset_mem L.relation_mem hpδ A.order hord hφ (fun i ↦ (v i).val) hv
    (fun i ↦ (v i).property)).mp hf
  rw [L.poset_image, L.relation_image] at he
  exact (forcingFormula_quotient_truth B.P B.R B.G B.order B.generic φ
    (fun i ↦ L.imageName (v i) (hv i))).mpr ⟨e ‘ p, L.generic p hp, he⟩

theorem bounded_formula_iff {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsBoundedSetFormula φ) (v : Fin n → ForcingName A.P)
    (hv : ∀ i, (v i).val ∈ hierarchy δ) :
    φ.Evalb (A.ofName ∘ v) ↔ φ.Evalb (fun i ↦ B.ofName (L.imageName (v i) (hv i))) := by
  classical
  constructor
  · exact L.bounded_formula_forward hφ v hv
  · intro ht
    by_contra hn
    have hnot := L.bounded_formula_forward hφ.neg v hv (by simpa using hn)
    exact (show ¬φ.Evalb (fun i ↦ B.ofName (L.imageName (v i) (hv i))) from by simpa using hnot) ht

theorem image_eq_iff (σ τ : ForcingName A.P) (hσ : σ.val ∈ hierarchy δ) (hτ : τ.val ∈ hierarchy δ) :
    B.ofName (L.imageName σ hσ) = B.ofName (L.imageName τ hτ) ↔ A.ofName σ = A.ofName τ := by
  have h := L.bounded_formula_iff (IsBoundedSetFormula.rel Language.Set.Rel.eq ![.bvar 0, .bvar 1])
    ![σ, τ] (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hσ, hτ])
  simpa [Semiformula.Evalb, Structure.rel, Function.comp_def] using h.symm

theorem image_mem_iff (σ τ : ForcingName A.P) (hσ : σ.val ∈ hierarchy δ) (hτ : τ.val ∈ hierarchy δ) :
    B.ofName (L.imageName σ hσ) ∈ B.ofName (L.imageName τ hτ) ↔ A.ofName σ ∈ A.ofName τ := by
  have h := L.bounded_formula_iff (IsBoundedSetFormula.rel Language.Set.Rel.mem ![.bvar 0, .bvar 1])
    ![σ, τ] (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hσ, hτ])
  simpa [Semiformula.Evalb, Structure.rel, Function.comp_def] using h.symm

end SuccessorRankLiftData
end ZFVP
