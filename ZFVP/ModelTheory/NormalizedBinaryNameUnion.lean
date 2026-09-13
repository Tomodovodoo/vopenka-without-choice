import ZFVP.ModelTheory.ForcingLeastRankNameBounds
import ZFVP.ModelTheory.ForcingSemanticConsequence
import ZFVP.ModelTheory.CountableZFTransfer
import ZFVP.ModelTheory.ForcingCheckedTruth
import ZFVP.SetTheory.ClassForcingCongruence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def binaryNameUnionFormula : SetTheorySemisentence 3 := f“u x y. u = !union.dfn x y”

def binaryNameUnionLawFormula : SetTheorySemisentence 5 :=
  f“P R o σ τ. !forcingPreorderFormula P R → !forcingTopFormula P R o →
    !forcingNameFormula P σ → !forcingNameFormula P τ →
    !(tripleForcingTruthFormula binaryNameUnionFormula) o P R (!union.dfn σ τ) σ τ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem binaryUnion_isForcingName {P σ τ : V}
    (hσ : IsForcingName P σ) (hτ : IsForcingName P τ) : IsForcingName P (σ ∪ τ) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  rcases mem_union_iff.mp hz with h | h
  · exact (forcingName_iff _ _).mp hσ z h
  · exact (forcingName_iff _ _).mp hτ z h

theorem ForcingContext.binaryNameUnion_value (A : ForcingContext V) (σ τ : ForcingName A.P) :
    A.ofName ⟨σ.val ∪ τ.val, binaryUnion_isForcingName σ.property τ.property⟩ = A.ofName σ ∪ A.ofName τ := by
  apply mem_ext
  intro x
  rw [mem_union_iff, A.mem_ofName_iff, A.mem_ofName_iff, A.mem_ofName_iff]
  constructor
  · rintro ⟨ν, p, hp, hz, rfl⟩
    rcases mem_union_iff.mp hz with h | h
    · exact Or.inl ⟨ν, p, hp, h, rfl⟩
    · exact Or.inr ⟨ν, p, hp, h, rfl⟩
  · rintro (⟨ν, p, hp, hz, rfl⟩ | ⟨ν, p, hp, hz, rfl⟩)
    · exact ⟨ν, p, hp, mem_union_iff.mpr (Or.inl hz), rfl⟩
    · exact ⟨ν, p, hp, mem_union_iff.mpr (Or.inr hz), rfl⟩

theorem binaryNameUnion_forces_countable [Countable V] {P R top : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (σ τ : ForcingName P) :
    top ∈ forcingFormula P R binaryNameUnionFormula (standardTuple ![σ.val ∪ τ.val, σ.val, τ.val]) := by
  apply forcingFormula_of_all_generics hR ht ht.1 binaryNameUnionFormula
    ![⟨σ.val ∪ τ.val, binaryUnion_isForcingName σ.property τ.property⟩, σ, τ]
  intro G hG _
  let A : ForcingContext V := ⟨P, R, top, G, hR, ht, hG⟩
  simpa [binaryNameUnionFormula] using A.binaryNameUnion_value σ τ

private theorem union_forall_three_eq {β : Type*} (a b c : β) (F : β → β → β → Prop) :
    (∀ u v w, u = a → v = b → w = c → F u v w) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, fun h u v w hu hv hw ↦ by subst u v w; exact h⟩
private theorem union_forall_six_eq {β : Type*} (a b c d e f : β) (F : β → β → β → β → β → β → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

@[simp] theorem eval_binaryNameUnionLawFormula (v : Fin 5 → V) : binaryNameUnionLawFormula.Evalb v ↔
    (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
      IsForcingName (v 0) (v 3) → IsForcingName (v 0) (v 4) →
      v 2 ∈ forcingFormula (v 0) (v 1) binaryNameUnionFormula (standardTuple ![v 3 ∪ v 4, v 3, v 4])) := by
  simp [binaryNameUnionLawFormula, Semiformula.eval_nestFormulae, Matrix.vecForall_iff,
    Fin.forall_fin_succ, union_forall_three_eq, union_forall_six_eq]

theorem binaryNameUnion_forces {P R top : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (σ τ : ForcingName P) :
    top ∈ forcingFormula P R binaryNameUnionFormula (standardTuple ![σ.val ∪ τ.val, σ.val, τ.val]) := by
  have h := eval_of_countable_zf binaryNameUnionLawFormula (by
    intro W _ _ _ _ v
    apply (eval_binaryNameUnionLawFormula v).mpr
    intro hR ht hσ hτ
    exact binaryNameUnion_forces_countable hR ht ⟨v 3, hσ⟩ ⟨v 4, hτ⟩)
      ![P, R, top, σ.val, τ.val]
  exact (eval_binaryNameUnionLawFormula _).mp h hR ht σ.property τ.property

noncomputable def normalizedBinaryNameUnion (P R top σ τ : V) : V :=
  forcingLeastRankName P R top (σ ∪ τ)

theorem normalizedBinaryNameUnion_isName {P R top σ τ : V}
    (hR : IsForcingPreorder P R) (ht : top ∈ P)
    (hσ : IsForcingName P σ) (hτ : IsForcingName P τ) :
    IsForcingName P (normalizedBinaryNameUnion P R top σ τ) :=
  forcingLeastRankName_isName hR ht (binaryUnion_isForcingName hσ hτ)

theorem normalizedBinaryNameUnion_mem_hierarchy {P R top σ τ δ : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (ht : top ∈ P)
    (hσ : IsForcingName P σ) (hτ : IsForcingName P τ)
    (hδ : ∀ β ∈ δ, succ β ∈ δ)
    (hσδ : σ ∈ hierarchy δ) (hτδ : τ ∈ hierarchy δ) :
    normalizedBinaryNameUnion P R top σ τ ∈ hierarchy δ := by
  have hn := binaryUnion_isForcingName hσ hτ
  apply forcingLeastRankName_mem_hierarchy_of_equiv hR ht hn hn
    (by rwa [atomicEquality_refl hR])
  simpa only [pair_eq_doubleton, ← union_def] using sUnion_mem_hierarchy_limit hδ (pair_mem_hierarchy_limit hδ hσδ hτδ)

theorem normalizedBinaryNameUnion_normalized {P R top σ τ : V}
    (hR : IsForcingPreorder P R) (ht : top ∈ P)
    (hσ : IsForcingName P σ) (hτ : IsForcingName P τ) :
    forcingLeastRankName P R top (normalizedBinaryNameUnion P R top σ τ) =
      normalizedBinaryNameUnion P R top σ τ :=
  forcingLeastRankName_idempotent hR ht (binaryUnion_isForcingName hσ hτ)

theorem normalizedBinaryNameUnion_forces {P R top : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (σ τ : ForcingName P) :
    top ∈ forcingFormula P R binaryNameUnionFormula
      (standardTuple ![normalizedBinaryNameUnion P R top σ.val τ.val, σ.val, τ.val]) := by
  have he := forcingLeastRankName_forced_equal hR ht.1 (binaryUnion_isForcingName σ.property τ.property)
  have hc := classForcingFormula_congr hR (IsForcingName P) (by definability) binaryNameUnionFormula
    ![σ.val ∪ τ.val, σ.val, τ.val]
    ![normalizedBinaryNameUnion P R top σ.val τ.val, σ.val, τ.val] ht.1
    (by
      intro i
      exact Fin.cases he (fun j ↦ Fin.cases
        ((atomicEquality_refl hR σ.val).symm ▸ ht.1)
        (fun k ↦ Fin.cases ((atomicEquality_refl hR τ.val).symm ▸ ht.1)
          (fun l ↦ Fin.elim0 l) k) j) i)
  exact hc.mp (binaryNameUnion_forces hR ht σ τ)
end ZFVP





