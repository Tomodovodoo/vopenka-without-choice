import ZFVP.ModelTheory.InternalHenkinOmissionStep
import ZFVP.SetTheory.FiniteNaturalSets

/-! An actual countable schedule repeats every type/name request beyond every
finite stage. A dummy task handles the empty family. Repetition allows the
omission step to skip names absent from an early context. -/

set_option autoImplicit false

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_internal_recurrent_schedule {K : V} (hK : IsInternallyCountable K) (hne : IsNonempty K) :
    ∃ s ∈ K ^ (ω : V), ∀ x ∈ K, ∀ k ∈ (ω : V), ∃ m ∈ (ω : V), k ∈ m ∧ s ‘ m = x := by
  have hprod : IsInternallyCountable (K ×ˢ (ω : V)) :=
    (prod_cardLE_prod hK internallyCountable_omega).trans omega_prod_cardLE_omega
  obtain ⟨x₀, hx₀⟩ := hne.nonempty
  obtain ⟨e, he, hre⟩ := exists_surjection_of_cardLE hprod
    (kpair_mem_iff.mpr ⟨hx₀, empty_mem_ω⟩ : ⟨x₀, (∅ : V)⟩ₖ ∈ K ×ˢ (ω : V))
  let : IsFunction e := IsFunction.of_mem he
  let s := definableGraph (ω : V) (fun n ↦ kpair.π₁ (e ‘ n)) (by definability)
  have hs : s ∈ K ^ (ω : V) := by
    apply definableGraph_mem_function_of_mapsTo
    intro n hn
    obtain ⟨x, hx, y, _, hv⟩ := mem_prod_iff.mp (function_value_mem he hn)
    rw [hv, kpair.π₁_kpair]
    exact hx
  refine ⟨s, hs, ?_⟩
  intro x hx k hk
  let B := repl (fun n ↦ kpair.π₂ (e ‘ n)) (by definability) (succ k)
  have hB : IsInternallyFinite B := internallyFinite_repl _ _
    (internallyFinite_of_cardLE_natural (ω_succ_closed hk) (CardLE.refl _))
  obtain ⟨r, hr, hrB⟩ := internallyFinite_fresh_natural hB
  have hxR : ⟨x, r⟩ₖ ∈ range e := by rw [hre]; exact kpair_mem_iff.mpr ⟨hx, hr⟩
  obtain ⟨m, hm⟩ := mem_range_iff.mp hxR
  have hmω : m ∈ (ω : V) := by
    simpa only [domain_eq_of_mem_function he] using mem_domain_of_kpair_mem hm
  have hval : e ‘ m = ⟨x, r⟩ₖ := value_eq_of_kpair_mem hm
  have hnot : m ∉ succ k := by
    intro hmk
    apply hrB
    exact (repl_spec (by definability)).mpr ⟨m, hmk, by rw [hval, kpair.π₂_kpair]⟩
  have hkm : k ∈ m := by
    let : IsOrdinal k := IsOrdinal.of_mem hk
    let : IsOrdinal m := IsOrdinal.of_mem hmω
    rcases IsOrdinal.mem_trichotomy k m with h | h | h
    · exact h
    · exact False.elim (hnot (h ▸ (show k ∈ succ k by simp)))
    · exact False.elim (hnot (mem_succ_iff.mpr (Or.inr h)))
  refine ⟨m, hmω, hkm, ?_⟩
  rw [show s ‘ m = kpair.π₁ (e ‘ m) from value_definableGraph _ _ _ hmω, hval, kpair.π₁_kpair]

noncomputable def henkinOmissionTasks (F : V) : V := insert ∅ (F ×ˢ (ω : V))

theorem henkinOmissionTasks_countable {F : V} (hF : IsInternallyCountable F) :
    IsInternallyCountable (henkinOmissionTasks F) :=
  internallyCountable_insert ((prod_cardLE_prod hF internallyCountable_omega).trans omega_prod_cardLE_omega) ∅

def IsHenkinOmissionSchedule (F e : V) : Prop :=
  e ∈ (henkinOmissionTasks F) ^ (ω : V) ∧
    ∀ P ∈ F, ∀ i ∈ (ω : V), ∀ k ∈ (ω : V), ∃ m ∈ (ω : V), k ∈ m ∧ e ‘ m = ⟨P, i⟩ₖ

theorem exists_henkinOmissionSchedule {F : V} (hF : IsInternallyCountable F) :
    ∃ e : V, IsHenkinOmissionSchedule F e := by
  have hne : IsNonempty (henkinOmissionTasks F) := ⟨⟨∅, by simp [henkinOmissionTasks]⟩⟩
  obtain ⟨e, he, hcover⟩ := exists_internal_recurrent_schedule (henkinOmissionTasks_countable hF) hne
  refine ⟨e, he, ?_⟩
  intro P hP i hi k hk
  exact hcover ⟨P, i⟩ₖ (mem_insert.mpr (Or.inr (kpair_mem_iff.mpr ⟨hP, hi⟩))) k hk

noncomputable def scheduledHenkinOmissionStep (s T q p : V) : V :=
  henkinOmissionStep s T (kpair.π₁ q) (kpair.π₂ q) p

instance scheduledHenkinOmissionStep_definable : ℒₛₑₜ-function₄[V] scheduledHenkinOmissionStep := by
  unfold scheduledHenkinOmissionStep
  exact Language.DefinableFunction₅.comp (by definability) (by definability) (by definability)
    (by definability) (by definability)

theorem scheduledHenkinOmissionStep_context (s T q p : V) :
    kpair.π₁ (scheduledHenkinOmissionStep s T q p) = kpair.π₁ p := henkinOmissionStep_context _ _ _ _ _

theorem scheduledHenkinOmissionStep_consistent (hω : Schmerl.HasStandardOmega V) {s T q p : V}
    (hs : IsHenkinOmissionSelector s) (hp : p ∈ henkinConditions T) :
    scheduledHenkinOmissionStep s T q p ∈ henkinConditions T := henkinOmissionStep_consistent hω hs hp

theorem scheduledHenkinOmissionStep_implies (hω : Schmerl.HasStandardOmega V) {s T q p : V}
    (hs : IsHenkinOmissionSelector s) (hp : p ∈ henkinConditions T) :
    CodedFormulaImplies T (kpair.π₁ p) (kpair.π₂ (scheduledHenkinOmissionStep s T q p)) (kpair.π₂ p) :=
  henkinOmissionStep_implies hω hs hp

end ZFVP
