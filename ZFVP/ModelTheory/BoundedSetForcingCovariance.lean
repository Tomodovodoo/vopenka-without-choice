import ZFVP.Syntax.BoundedSetForcingMeaning
import ZFVP.ModelTheory.InternalForcingTableTransport
import ZFVP.SetTheory.CanonicalAtomicTruthTable

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCodedMembershipEmbedding.setForcing_iff {A B f T P R D H p : V}
    [IsTransitive A] [IsTransitive B] [IsTransitive T]
    (he : IsCodedMembershipEmbedding A B f)
    (hT : T ∈ A) (hP : P ∈ A) (hR : R ∈ A) (hD : D ∈ A) (hH : H ∈ A)
    (hDT : D ⊆ T) (ht : IsAtomicTruthTable P R T H) (hp : p ∈ A)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V) (hv : ∀ i, v i ∈ D) :
    p ∈ classForcingFormula P R (fun x ↦ x ∈ D) (by definability) φ (standardTuple v) ↔
      f ‘ p ∈ classForcingFormula (f ‘ P) (f ‘ R) (fun x ↦ x ∈ f ‘ D) (by definability)
        φ (standardTuple (fun i ↦ f ‘ (v i))) := by
  let := he.value_transitive hT inferInstance
  have hDT' : f ‘ D ⊆ f ‘ T := (he.bounded_defined_iff isSubsetOf_bounded
    (fun w ↦ w 0 ⊆ w 1) ![D, T] (by simp [hD, hT])).mp hDT
  have ht' := he.value_atomicTruthTable hT hP hR hH ht
  have hvA : ∀ i, v i ∈ A := fun i ↦ (inferInstance : IsTransitive A).mem_trans (hv i) hD
  have hv' : ∀ i, f ‘ (v i) ∈ f ‘ D := fun i ↦ (he.value_mem_iff (hvA i) hD).mpr (hv i)
  have hc := he.bounded_formula_iff (boundedSetForcingTranslation_bounded φ)
    (T :> P :> R :> D :> H :> p :> v)
    (fun i ↦ Fin.cases hT (fun j ↦ Fin.cases hP (fun k ↦ Fin.cases hR
      (fun l ↦ Fin.cases hD (fun m ↦ Fin.cases hH (fun a ↦ Fin.cases hp hvA a) m) l) k) j) i)
  have hh : (fun i ↦ f ‘ ((T :> P :> R :> D :> H :> p :> v) i)) =
      (f ‘ T :> f ‘ P :> f ‘ R :> f ‘ D :> f ‘ H :> f ‘ p :> fun i ↦ f ‘ (v i)) := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun a ↦ Fin.cases rfl (fun _ ↦ rfl) a) m) l) k) j) i
  rw [hh] at hc
  exact (boundedSetForcingTranslation_meaning hDT ht φ v hv p).symm.trans
    (hc.trans (boundedSetForcingTranslation_meaning hDT' ht' φ _ hv' _))

theorem canonicalAtomicTruthTable_mem_limit {δ P R T : V} [IsOrdinal δ]
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hT : T ∈ hierarchy δ) :
    canonicalAtomicTruthTable P R T ∈ hierarchy δ :=
  subset_mem_hierarchy_limit hδ
    (prod_mem_hierarchy_limit hδ (prod_mem_hierarchy_limit hδ hT hT) hP) sep_subset

theorem limitRankEmbedding_setForcing_iff {δ B f T P R D p : V}
    [IsOrdinal δ] [IsTransitive B] [IsTransitive T]
    (hδ : ∀ β ∈ δ, succ β ∈ δ)
    (he : IsCodedMembershipEmbedding (hierarchy δ) B f)
    (hT : T ∈ hierarchy δ) (hP : P ∈ hierarchy δ) (hR : R ∈ hierarchy δ)
    (hD : D ∈ hierarchy δ) (hDT : D ⊆ T) (hp : p ∈ hierarchy δ)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V) (hv : ∀ i, v i ∈ D) :
    p ∈ classForcingFormula P R (fun x ↦ x ∈ D) (by definability) φ (standardTuple v) ↔
      f ‘ p ∈ classForcingFormula (f ‘ P) (f ‘ R) (fun x ↦ x ∈ f ‘ D) (by definability)
        φ (standardTuple (fun i ↦ f ‘ (v i))) := by
  let := hierarchy_transitive δ
  exact he.setForcing_iff hT hP hR hD (canonicalAtomicTruthTable_mem_limit hδ hP hT)
    hDT (canonicalAtomicTruthTable_spec P R T (transitive_subnameClosed inferInstance)) hp φ v hv

end ZFVP
