import ZFVP.ModelTheory.CodedEmbeddingRestriction
import ZFVP.SetTheory.CnAbsoluteness

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def largestSetFormula : SetTheorySemisentence 1 := “a. ∀ x, !isSubsetOf x a”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_largestSet_successorRank (δ : V) [IsOrdinal δ]
    (a : SetDomain (hierarchy (succ δ))) :
    largestSetFormula.Evalb ![a] ↔ a.val = hierarchy δ := by
  let := hierarchy_transitive (succ δ)
  have hev : largestSetFormula.Evalb ![a] ↔ ∀ x : SetDomain (hierarchy (succ δ)), x.val ⊆ a.val := by
    simp only [largestSetFormula]
    constructor
    · intro h x
      simpa using (bounded_formula_absolute _ isSubsetOf_bounded ![x, a]).mp (h x)
    · intro h x
      apply (bounded_formula_absolute _ isSubsetOf_bounded ![x, a]).mpr
      simpa using h x
  rw [hev]
  have ha : a.val ⊆ hierarchy δ := by simpa only [hierarchy_succ, mem_power_iff] using a.property
  constructor
  · intro h
    apply SetTheory.subset_antisymm ha
    exact h ⟨hierarchy δ, by rw [hierarchy_succ, mem_power_iff]⟩
  · rintro he x
    rw [he]
    simpa only [hierarchy_succ, mem_power_iff] using x.property

theorem successorRankEmbedding_value_hierarchy {δ ε f : V} [IsOrdinal δ] [IsOrdinal ε]
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) f) :
    f ‘ (hierarchy δ) = hierarchy ε := by
  let a : SetDomain (hierarchy (succ δ)) := ⟨hierarchy δ, by rw [hierarchy_succ, mem_power_iff]⟩
  have hs := (eval_largestSet_successorRank δ a).mpr rfl
  have ht := (h.eval_semisentence largestSetFormula ![a]).mp hs
  have hv : h.toFunction ∘ ![a] = ![h.toFunction a] := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [hv] at ht
  exact (eval_largestSet_successorRank ε (h.toFunction a)).mp ht

noncomputable def successorRankElementaryMap {δ ε f : V} [IsOrdinal δ] [IsOrdinal ε]
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) f) :
    ElementaryMap (SetDomain (hierarchy δ)) (SetDomain (hierarchy ε)) := by
  let := hierarchy_transitive (succ δ)
  let := hierarchy_transitive (succ ε)
  have hm : hierarchy δ ∈ hierarchy (succ δ) := by rw [hierarchy_succ, mem_power_iff]
  have hh := successorRankEmbedding_value_hierarchy h
  let e : SetDomain (f ‘ (hierarchy δ)) ≃ SetDomain (hierarchy ε) := {
    toFun := fun x ↦ ⟨x.val, hh ▸ x.property⟩
    invFun := fun x ↦ ⟨x.val, hh.symm ▸ x.property⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }
  exact (ElementaryMap.ofMembershipIso e (fun _ _ ↦ Iff.rfl)).comp (h.restrictElementaryMap hm)

theorem successorRankElementaryMap_value {δ ε f : V} [IsOrdinal δ] [IsOrdinal ε]
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) f)
    (x : SetDomain (hierarchy δ)) : (successorRankElementaryMap h x).val = f ‘ x.val := rfl

theorem successorRankEmbedding_pi_iff {δ ε f : V} (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) f)
    {n : ℕ} {φ : SetTheorySemisentence n} (hφ : IsPiFormula 1 φ)
    (v : Fin n → V) (hv : ∀ i, v i ∈ hierarchy δ) :
    φ.Evalb v ↔ φ.Evalb (fun i ↦ f ‘ (v i)) := by
  let := hδ.ordinal
  let := hε.ordinal
  let j := successorRankElementaryMap h
  let b : Fin n → SetDomain (hierarchy δ) := fun i ↦ ⟨v i, hv i⟩
  have hj : φ.Evalb b ↔ φ.Evalb (j ∘ b) := by
    have he := j.elementary φ b Empty.elim
    have hz : j ∘ (Empty.elim : Empty → SetDomain (hierarchy δ)) = Empty.elim := by
      funext i
      exact Empty.elim i
    rwa [hz] at he
  have he := (hδ.pi_correct hφ b).symm.trans (hj.trans (hε.pi_correct hφ (j ∘ b)))
  have hvj : (fun i ↦ ((j ∘ b) i).val) = (fun i ↦ f ‘ (v i)) := by
    funext i
    exact successorRankElementaryMap_value h (b i)
  rw [hvj] at he
  exact he

end ZFVP
