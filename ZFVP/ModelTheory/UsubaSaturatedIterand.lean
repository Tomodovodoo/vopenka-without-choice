import ZFVP.ModelTheory.ForcingCarrierNormalization
import ZFVP.ModelTheory.UsubaRestorationIterand
import ZFVP.ModelTheory.SaturatedEmptyIterand

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def usubaSaturatedPosetName (P R : V) : V :=
  forcingSaturatedName P R (forcingCarrierPool P R (usubaRestorationPosetName P R))
    (usubaRestorationPosetName P R)

instance usubaSaturatedPosetName_definable : ℒₛₑₜ-function₂[V] usubaSaturatedPosetName := by
  unfold usubaSaturatedPosetName
  apply Language.DefinableFunction₄.comp (F := forcingSaturatedName)
  · definability
  · definability
  · apply Language.DefinableFunction₃.comp (F := forcingCarrierPool) <;> definability
  · definability

theorem usubaSaturatedPosetName_isName (P R : V) :
    IsForcingName P (usubaSaturatedPosetName P R) := forcingSaturatedName_isName _ _ _ _

theorem usubaRestorationPosetName_forces_empty_member {P R one p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hp : p ∈ P) :
    p ∈ atomicMembership P R ∅ (usubaRestorationPosetName P R) := by
  let Q : ForcingName P := ⟨usubaRestorationPosetName P R, usubaRestorationPosetName_isName _ _⟩
  let t : ForcingName P := ⟨∅, empty_forcingName P⟩
  let φ : SetTheorySemisentence 2 :=
    (isEmpty.subst (fun i ↦ .bvar ((![0] : Fin 1 → Fin 2) i))).and
      (usubaRestorationPosetFormula.subst (fun i ↦ .bvar ((![1] : Fin 1 → Fin 2) i)))
  have hφ : p ∈ forcingFormula P R φ (standardTuple ![t.val, Q.val]) := by
    dsimp only [φ]
    rw [forcingFormula_and, mem_inter_iff, forcingFormula_rename, forcingFormula_rename]
    exact ⟨emptyName_forces hR ht hp, usubaRestorationPosetName_forces hR ht hp⟩
  have hm := forcingFormula_entailment φ nameMemberFormula (by
    intro W _ _ _ v hv
    change (isEmpty.subst (fun i ↦ .bvar ((![0] : Fin 1 → Fin 2) i))).Evalb v ∧
      (usubaRestorationPosetFormula.subst (fun i ↦ .bvar ((![1] : Fin 1 → Fin 2) i))).Evalb v at hv
    have hh : v 0 = ∅ ∧ v 1 = usubaRestorationPoset := by
      simpa [Semiformula.eval_substs] using hv
    have hm : v 0 ∈ v 1 := by
      rw [hh.1, hh.2]
      exact usubaRestorationPoset_empty_mem
    simpa [nameMemberFormula] using hm) hR ht hp ![t, Q] hφ
  exact (forcingFormula_nameMember P R ∅ Q.val) ▸ hm

theorem usubaSaturated_iterand {P R one : V} (hR : IsForcingPreorder P R)
    (ht : IsForcingTop P R one) :
    IsForcingIterand P R (usubaSaturatedPosetName P R)
      (reverseInclusionOrderName P R (usubaSaturatedPosetName P R)) ∅ :=
  saturatedName_empty_iterand hR ht
    ⟨usubaRestorationPosetName P R, usubaRestorationPosetName_isName _ _⟩
    (forcingCarrierPool_empty _ _ _) (fun p hp ↦ usubaRestorationPosetName_forces_empty_member hR ht hp)

namespace ForcingContext

noncomputable def usubaSaturatedName (A : ForcingContext V) : ForcingName A.P :=
  ⟨usubaSaturatedPosetName A.P A.R, usubaSaturatedPosetName_isName _ _⟩

theorem usubaSaturatedName_value (A : ForcingContext V) :
    A.ofName A.usubaSaturatedName = (usubaRestorationPoset : A.Model) :=
  (A.carrierSaturatedName_value A.usubaRestorationName).trans A.usubaRestorationName_value

end ForcingContext
end ZFVP
