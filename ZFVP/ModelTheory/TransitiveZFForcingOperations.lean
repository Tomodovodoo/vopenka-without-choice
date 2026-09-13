import ZFVP.ModelTheory.TransitiveZFAtomicForcing
import ZFVP.ModelTheory.TransitiveZFConstructors
import ZFVP.SetTheory.FormulaForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem inter_val (A B : SetDomain U) : (A ∩ B).val = A.val ∩ B.val := by
  apply SetTheory.mem_ext_iff.mpr
  intro x
  constructor
  · intro hx
    let x' : SetDomain U := ⟨x, (inferInstance : IsTransitive U).mem_trans hx (A ∩ B).property⟩
    obtain ⟨ha, hb⟩ := mem_inter_iff.mp (show x' ∈ A ∩ B from hx)
    exact mem_inter_iff.mpr ⟨ha, hb⟩
  · intro hx
    obtain ⟨ha, hb⟩ := mem_inter_iff.mp hx
    let x' : SetDomain U := ⟨x, (inferInstance : IsTransitive U).mem_trans ha A.property⟩
    exact show x' ∈ A ∩ B from mem_inter_iff.mpr ⟨ha, hb⟩

theorem forcingNegation_val (P R A : SetDomain U) :
    (forcingNegation P R A).val = forcingNegation P.val R.val A.val := by
  unfold forcingNegation
  apply sep_val U
  intro p _
  apply forall_mem_val_iff U P
  intro q
  simp only [kpair_mem_val_iff U]
  rfl

theorem forcingClosure_val (P R A : SetDomain U) :
    (forcingClosure P R A).val = forcingClosure P.val R.val A.val := by
  unfold forcingClosure
  apply sep_val U
  intro p _
  apply forall_mem_val_iff U P
  intro q
  simp only [kpair_mem_val_iff U]
  apply imp_congr_right
  intro _
  apply exists_mem_val_iff U A
  intro r
  rfl

theorem forcingTermValue_val {n : ℕ} (t : Semiterm ℒₛₑₜ Empty n) (b : SetDomain U) :
    (forcingTermValue t b).val = forcingTermValue t b.val := by
  cases t with
  | bvar i => simp only [forcingTermValue, value_val_total U, numeral_val U]
  | fvar i => exact Empty.elim i
  | func f _ => exact Empty.elim f

theorem forcingAtomic_val {n k : ℕ} (P R b : SetDomain U) (r : Language.Set.Rel k)
    (ts : Fin k → Semiterm ℒₛₑₜ Empty n) :
    (forcingAtomic P R r ts b).val = forcingAtomic P.val R.val r ts b.val := by
  cases r <;> simp only [forcingAtomic, atomicEquality_val U, atomicMembership_val U, forcingTermValue_val U]

end TransitiveZF
end ZFVP
