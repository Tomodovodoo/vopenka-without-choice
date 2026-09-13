import ZFVP.SetTheory.ClassFormulaForcing
import ZFVP.SetTheory.AtomicForcingSubstitution
import ZFVP.SetTheory.ForcingFormulaWitnesses

/-! Replacing names by names forced equal preserves formula forcing. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingNegation_congr_below {P R A B p : V}
    (he : ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → (q ∈ A ↔ q ∈ B)) :
    p ∈ forcingNegation P R A ↔ p ∈ forcingNegation P R B := by
  rw [mem_forcingNegation_iff, mem_forcingNegation_iff]
  apply and_congr Iff.rfl
  exact forall_congr' fun q ↦ imp_congr_right fun hq ↦ imp_congr_right fun hqp ↦ not_congr (he q hq hqp)

theorem forcingClosure_congr_below {P R A B p : V} (hR : IsForcingPreorder P R)
    (hA : A ⊆ P) (hB : B ⊆ P)
    (he : ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → (q ∈ A ↔ q ∈ B)) :
    p ∈ forcingClosure P R A ↔ p ∈ forcingClosure P R B := by
  rw [mem_forcingClosure_iff, mem_forcingClosure_iff]
  apply and_congr_right
  intro hp
  constructor
  · intro h q hq hqp
    obtain ⟨r, hr, hrq⟩ := h q hq hqp
    exact ⟨r, (he r (hA r hr) (hR.2.2 r (hA r hr) q hq p hp hrq hqp)).mp hr, hrq⟩
  · intro h q hq hqp
    obtain ⟨r, hr, hrq⟩ := h q hq hqp
    exact ⟨r, (he r (hB r hr) (hR.2.2 r (hB r hr) q hq p hp hrq hqp)).mpr hr, hrq⟩

theorem forcingTermValue_congr {P R p : V} {n : ℕ} (v w : Fin n → V)
    (he : ∀ i, p ∈ atomicEquality P R (v i) (w i)) (t : SetTheorySemiterm Empty n) :
    p ∈ atomicEquality P R (forcingTermValue t (standardTuple v)) (forcingTermValue t (standardTuple w)) := by
  cases t with
  | bvar i => simpa only [forcingTermValue, value_standardTuple] using he i
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

theorem forcingAtomic_congr {P R p : V} (hR : IsForcingPreorder P R) {n k : ℕ}
    (r : Language.Set.Rel k) (ts : Fin k → SetTheorySemiterm Empty n) (v w : Fin n → V)
    (he : ∀ i, p ∈ atomicEquality P R (v i) (w i)) :
    p ∈ forcingAtomic P R r ts (standardTuple v) ↔ p ∈ forcingAtomic P R r ts (standardTuple w) := by
  have ht (t : SetTheorySemiterm Empty n) := forcingTermValue_congr v w he t
  cases r with
  | eq =>
    change p ∈ atomicEquality P R _ _ ↔ p ∈ atomicEquality P R _ _
    have hl := ht (ts 0)
    have hr := ht (ts 1)
    have hl' := atomicEquality_symm P R _ _ ▸ hl
    have hr' := atomicEquality_symm P R _ _ ▸ hr
    exact ⟨fun h ↦ atomicEquality_trans hR _ _ _ p (atomicEquality_trans hR _ _ _ p hl' h) hr,
      fun h ↦ atomicEquality_trans hR _ _ _ p (atomicEquality_trans hR _ _ _ p hl h) hr'⟩
  | mem =>
    change p ∈ atomicMembership P R _ _ ↔ p ∈ atomicMembership P R _ _
    have hl := ht (ts 0)
    have hr := ht (ts 1)
    exact ⟨fun h ↦ atomicMembership_subst_right hR hr (atomicMembership_subst_left hR hl h),
      fun h ↦ atomicMembership_subst_right hR (atomicEquality_symm P R _ _ ▸ hr)
        (atomicMembership_subst_left hR (atomicEquality_symm P R _ _ ▸ hl) h)⟩

theorem classForcingFormula_congr {P R : V} (hR : IsForcingPreorder P R)
    (N : V → Prop) (hN : ℒₛₑₜ-predicate N) {n : ℕ} (φ : SetTheorySemisentence n)
    (v w : Fin n → V) {p : V} (hp : p ∈ P) (he : ∀ i, p ∈ atomicEquality P R (v i) (w i)) :
    p ∈ classForcingFormula P R N hN φ (standardTuple v) ↔
      p ∈ classForcingFormula P R N hN φ (standardTuple w) := by
  induction φ generalizing p with
  | verum => rfl
  | falsum => rfl
  | rel r ts => exact forcingAtomic_congr hR r ts v w he
  | nrel r ts =>
    rw [classForcingFormula_nrel, classForcingFormula_nrel]
    apply forcingNegation_congr_below
    intro q hq hqp
    exact forcingAtomic_congr hR r ts v w (fun i ↦ atomicEquality_mono hR (he i) hq hqp)
  | and φ ψ ihφ ihψ =>
    rw [classForcingFormula_and, classForcingFormula_and, mem_inter_iff, mem_inter_iff]
    exact and_congr (ihφ v w hp he) (ihψ v w hp he)
  | or φ ψ ihφ ihψ =>
    rw [classForcingFormula_or, classForcingFormula_or]
    apply forcingClosure_congr_below hR
    · intro q hq
      rcases mem_union_iff.mp hq with h | h
      · exact (classForcingFormula_regular N hN hR φ _).1 q h
      · exact (classForcingFormula_regular N hN hR ψ _).1 q h
    · intro q hq
      rcases mem_union_iff.mp hq with h | h
      · exact (classForcingFormula_regular N hN hR φ _).1 q h
      · exact (classForcingFormula_regular N hN hR ψ _).1 q h
    · intro q hq hqp
      rw [mem_union_iff, mem_union_iff]
      exact or_congr (ihφ v w hq (fun i ↦ atomicEquality_mono hR (he i) hq hqp))
        (ihψ v w hq (fun i ↦ atomicEquality_mono hR (he i) hq hqp))
  | @all n φ ih =>
    rw [classForcingFormula_all, classForcingFormula_all, mem_forcingClassIntersection_iff, mem_forcingClassIntersection_iff]
    apply and_congr Iff.rfl
    apply forall_congr'
    intro x
    apply imp_congr_right
    intro _
    apply ih (x :> v) (x :> w) hp
    intro i
    exact Fin.cases (by change p ∈ atomicEquality P R x x; rw [atomicEquality_refl hR]; exact hp) (fun j ↦ he j) i
  | @exs n φ ih =>
    rw [classForcingFormula_exs_dense_iff, classForcingFormula_exs_dense_iff]
    apply and_congr Iff.rfl
    apply forall_congr'
    intro q
    apply imp_congr_right
    intro hq
    apply imp_congr_right
    intro hqp
    apply exists_congr
    intro r
    apply and_congr_right
    intro hr
    apply and_congr_right
    intro hrq
    apply exists_congr
    intro x
    apply and_congr_right
    intro _
    apply ih (x :> v) (x :> w) hr
    intro i
    exact Fin.cases (by change r ∈ atomicEquality P R x x; rw [atomicEquality_refl hR]; exact hr)
      (fun j ↦ atomicEquality_mono hR (he j) hr (hR.2.2 r hr q hq p hp hrq hqp)) i

end ZFVP
