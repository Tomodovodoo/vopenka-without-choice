import ZFVP.ModelTheory.SchmerlCodedBranchSequence
import ZFVP.ModelTheory.SchmerlUniverseGraphs
import ZFVP.ModelTheory.SchmerlCodedRepresentedDefinitions

/-! A coded cofinal omega-one chain supplies the exact internal-Q rank
selection. The bound on every initial segment is witnessed by an actual
internally countable image of an ordinal. -/

set_option autoImplicit false

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W]
variable (R : BinaryRelationRepresentation (V := V) W)

theorem equiv_val_injective : Function.Injective (fun x : W ↦ (R.equiv x).val) := by
  intro x y he
  exact R.equiv.injective (Subtype.ext he)

def representedQ (S : Set W) : Prop :=
  ¬∃ A : V, IsInternallyCountable A ∧ ∀ x ∈ S, (R.equiv x).val ∈ A

theorem representedQ_iff {A : V} {S : Set W} (hA : A ⊆ R.carrier)
    (hS : ∀ x : W, x ∈ S ↔ (R.equiv x).val ∈ A) :
    R.representedQ S ↔ ¬IsInternallyCountable A := by
  apply not_congr
  constructor
  · rintro ⟨B, hB, hcover⟩
    apply internallyCountable_subset hB
    intro a ha
    obtain ⟨x, hx⟩ := R.equiv.surjective ⟨a, hA a ha⟩
    have he : (R.equiv x).val = a := congrArg Subtype.val hx
    rw [← he]
    exact hcover x ((hS x).mpr (he ▸ ha))
  · intro h
    exact ⟨A, h, fun x hx ↦ (hS x).mp hx⟩

theorem countable_of_not_representedQ (hω : HasStandardOmega V) {S : Set W}
    (h : ¬R.representedQ S) : S.Countable := by
  classical
  obtain ⟨A, hA, hcover⟩ : ∃ A : V, IsInternallyCountable A ∧ ∀ x ∈ S, (R.equiv x).val ∈ A :=
    not_not.mp h
  let := externalCountable_of_internal hω hA
  let f : S → {x : V // x ∈ A} := fun x ↦ ⟨(R.equiv x.val).val, hcover x.val x.property⟩
  have hf : Function.Injective f := by
    intro x y he
    have hv : (R.equiv x.val).val = (R.equiv y.val).val :=
      congrArg (fun z : {x : V // x ∈ A} ↦ z.val) he
    exact Subtype.ext (R.equiv_val_injective hv)
  let := hf.countable
  exact Set.to_countable S

variable [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {c : V}
variable (hc : IsInternalCofinalStrictChain (hartogsNumber (ω : V))
  (codedOrdinals R.code) (codedOrdinalOrder R.code) c)

include hc

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem cofinalChain_range_subset : range c ⊆ R.carrier := by
  intro x hx
  have hxO : x ∈ codedOrdinals R.code := range_subset_of_mem_function hc.1 x hx
  obtain ⟨α, rfl⟩ := (R.mem_ordinals_iff x).mp hxO
  exact (R.equiv α.val).property

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem cofinalChain_range_not_countable : ¬IsInternallyCountable (range c) := by
  let : IsFunction c := IsFunction.of_mem hc.1
  intro hcount
  apply hartogs_omega_not_countable (V := V)
  apply internallyCountable_of_cardLE hcount
  refine ⟨c, ?_, ?_⟩
  · simpa only [domain_eq_of_mem_function hc.1] using IsFunction.mem_function c
  · intro i j x hix hjx
    have hi : i ∈ hartogsNumber (ω : V) := by
      simpa only [domain_eq_of_mem_function hc.1] using mem_domain_of_kpair_mem hix
    have hj : j ∈ hartogsNumber (ω : V) := by
      simpa only [domain_eq_of_mem_function hc.1] using mem_domain_of_kpair_mem hjx
    exact hc.value_injective hi hj ((value_eq_of_kpair_mem hix).trans (value_eq_of_kpair_mem hjx).symm)

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem cofinalChain_selected_ordinal {x : W} (hx : (R.equiv x).val ∈ range c) : IsOrdinal x := by
  have hxO := range_subset_of_mem_function hc.1 _ hx
  obtain ⟨α, he⟩ := (R.mem_ordinals_iff _).mp hxO
  have he' : α.val = x := R.equiv_val_injective he
  exact he' ▸ α.ordinal

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem cofinalChain_selected_cofinal (α : SetTheory.Ordinal W) :
    ∃ x : W, (R.equiv x).val ∈ range c ∧ α.val ⊆ x := by
  let : IsFunction c := IsFunction.of_mem hc.1
  obtain ⟨i, hi, hαi⟩ := hc.2.2 _ (R.ordinal_mem α)
  obtain ⟨β, he⟩ := (R.mem_ordinals_iff _).mp (function_value_mem hc.1 hi)
  refine ⟨β.val, ?_, ?_⟩
  · rw [he]
    exact mem_range_of_kpair_mem (kpair_value_mem (by simpa only [domain_eq_of_mem_function hc.1] using hi))
  · exact (R.ordinalOrder_iff α β).mp (he ▸ hαi)

theorem cofinalChain_selected_initial (α : SetTheory.Ordinal W) :
    ¬R.representedQ {x : W | (R.equiv x).val ∈ range c ∧ x ⊆ α.val} := by
  let : IsFunction c := IsFunction.of_mem hc.1
  obtain ⟨i, hi, hαi⟩ := hc.2.2 _ (R.ordinal_mem α)
  let : IsOrdinal i := IsOrdinal.of_mem hi
  let B := repl (fun j : V ↦ c ‘ j) (by definability) (succ i)
  have hB : IsInternallyCountable B :=
    internallyCountable_repl (fun j : V ↦ c ‘ j) (by definability)
      (by simpa [succ] using internallyCountable_insert (countable_of_mem_hartogs_omega hi) i)
  intro hQ
  apply hQ
  refine ⟨B, hB, ?_⟩
  intro x hx
  obtain ⟨j, hjx⟩ := mem_range_iff.mp hx.1
  have hj : j ∈ hartogsNumber (ω : V) := by
    simpa only [domain_eq_of_mem_function hc.1] using mem_domain_of_kpair_mem hjx
  let : IsOrdinal j := IsOrdinal.of_mem hj
  have hjval : c ‘ j = (R.equiv x).val := value_eq_of_kpair_mem hjx
  let β : SetTheory.Ordinal W := ⟨x, R.cofinalChain_selected_ordinal hc hx.1⟩
  have hji : j ⊆ i := hc.index_mono R.ordinalOrder_poset hj hi
    (R.ordinalOrder_poset.1.2.2 _ (function_value_mem hc.1 hj) _ (R.ordinal_mem α)
      _ (function_value_mem hc.1 hi) (by
        rw [hjval]
        exact (R.ordinalOrder_iff β α).mpr hx.2) hαi)
  exact (repl_spec (by definability)).mpr ⟨j, mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hji), hjval.symm⟩

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem cofinalChain_selected_Q : R.representedQ {x : W | (R.equiv x).val ∈ range c} :=
  (R.representedQ_iff (R.cofinalChain_range_subset hc) (fun _ ↦ Iff.rfl)).mpr
    (R.cofinalChain_range_not_countable hc)

end ZFVP.BinaryRelationRepresentation
