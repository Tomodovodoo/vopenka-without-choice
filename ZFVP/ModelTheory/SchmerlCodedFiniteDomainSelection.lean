import ZFVP.ModelTheory.SchmerlCodedFiniteDomains
import ZFVP.ModelTheory.SchmerlCodedRankSelection
import ZFVP.ModelTheory.SchmerlInfinitaryFunctionWithQ

/-! Selected finite domains from an actual coded cofinal chain.
The Q clauses use actual internal countable covers, including all initial segments. -/

set_option autoImplicit false

namespace ZFVP.BinaryRelationRepresentation
open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W) {s : W} {c : V}
variable (hc : IsInternalCofinalStrictChain (hartogsNumber (ω : V))
  (codedFiniteDomains R.code (R.equiv s).val) (codedFiniteDomainOrder R.code (R.equiv s).val) c)

include hc

theorem finiteDomainChain_range_subset : range c ⊆ R.carrier := by
  intro x hx
  have hxf := range_subset_of_mem_function hc.1 x hx
  obtain ⟨a, rfl, _⟩ := (R.mem_finiteDomains_iff s x).mp hxf
  exact (R.equiv a).property

theorem finiteDomainChain_selected_finite {a : W} (ha : (R.equiv a).val ∈ range c) :
    IsInternallyFinite a ∧ a ⊆ s :=
  (R.finiteDomain_mem_iff s a).mp (range_subset_of_mem_function hc.1 _ ha)

theorem finiteDomainChain_selected_linear {a b : W}
    (ha : (R.equiv a).val ∈ range c) (hb : (R.equiv b).val ∈ range c) : a ⊆ b ∨ b ⊆ a := by
  let : IsFunction c := IsFunction.of_mem hc.1
  obtain ⟨i, hia⟩ := mem_range_iff.mp ha
  obtain ⟨j, hjb⟩ := mem_range_iff.mp hb
  have hi : i ∈ hartogsNumber (ω : V) := domain_eq_of_mem_function hc.1 ▸ mem_domain_of_kpair_mem hia
  have hj : j ∈ hartogsNumber (ω : V) := domain_eq_of_mem_function hc.1 ▸ mem_domain_of_kpair_mem hjb
  let : IsOrdinal i := IsOrdinal.of_mem hi
  let : IsOrdinal j := IsOrdinal.of_mem hj
  have hea : c ‘ i = (R.equiv a).val := value_eq_of_kpair_mem hia
  have heb : c ‘ j = (R.equiv b).val := value_eq_of_kpair_mem hjb
  rcases IsOrdinal.subset_or_supset (α := i) (β := j) with hij | hji
  · have h := hc.mono (R.finiteDomainOrder_poset s) hi hj hij
    rw [hea, heb] at h
    exact Or.inl ((R.finiteDomainOrder_iff s a b).mp h).2.2
  · have h := hc.mono (R.finiteDomainOrder_poset s) hj hi hji
    rw [heb, hea] at h
    exact Or.inr ((R.finiteDomainOrder_iff s b a).mp h).2.2

theorem finiteDomainChain_selected_cofinal {a : W} (ha : IsInternallyFinite a) (has : a ⊆ s) :
    ∃ d : W, (R.equiv d).val ∈ range c ∧ a ⊆ d := by
  obtain ⟨i, hi, hai⟩ := hc.2.2 _ ((R.finiteDomain_mem_iff s a).mpr ⟨ha, has⟩)
  obtain ⟨d, he, _⟩ := (R.mem_finiteDomains_iff s _).mp (function_value_mem hc.1 hi)
  refine ⟨d, he.symm ▸ value_mem_range hc.1 hi, ?_⟩
  exact ((R.finiteDomainOrder_iff s a d).mp (he.symm ▸ hai)).2.2

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem finiteDomainChain_range_not_countable : ¬IsInternallyCountable (range c) := by
  let : IsFunction c := IsFunction.of_mem hc.1
  intro hcount
  apply hartogs_omega_not_countable (V := V)
  apply internallyCountable_of_cardLE hcount
  refine ⟨c, ?_, ?_⟩
  · simpa only [domain_eq_of_mem_function hc.1] using IsFunction.mem_function c
  · intro i j x hix hjx
    have hi : i ∈ hartogsNumber (ω : V) := domain_eq_of_mem_function hc.1 ▸ mem_domain_of_kpair_mem hix
    have hj : j ∈ hartogsNumber (ω : V) := domain_eq_of_mem_function hc.1 ▸ mem_domain_of_kpair_mem hjx
    exact hc.value_injective hi hj ((value_eq_of_kpair_mem hix).trans (value_eq_of_kpair_mem hjx).symm)

theorem finiteDomainChain_selected_Q : R.representedQ {d : W | (R.equiv d).val ∈ range c} :=
  (R.representedQ_iff (R.finiteDomainChain_range_subset hc) (fun _ ↦ Iff.rfl)).mpr
    (R.finiteDomainChain_range_not_countable hc)

/-- This stronger form applies to every finite subset of `s`, whether selected or not. -/
theorem finiteDomainChain_selected_initial {e : W} (hefin : IsInternallyFinite e) (hes : e ⊆ s) :
    ¬R.representedQ {d : W | (R.equiv d).val ∈ range c ∧ d ⊆ e} := by
  let : IsFunction c := IsFunction.of_mem hc.1
  obtain ⟨i, hi, hei⟩ := hc.2.2 _ ((R.finiteDomain_mem_iff s e).mpr ⟨hefin, hes⟩)
  let : IsOrdinal i := IsOrdinal.of_mem hi
  let B := repl (fun j : V ↦ c ‘ j) (by definability) (succ i)
  have hB : IsInternallyCountable B := internallyCountable_repl _ _
    (by simpa [succ] using internallyCountable_insert (countable_of_mem_hartogs_omega hi) i)
  intro hQ
  apply hQ
  refine ⟨B, hB, fun d hd ↦ ?_⟩
  obtain ⟨j, hjd⟩ := mem_range_iff.mp hd.1
  have hj : j ∈ hartogsNumber (ω : V) := domain_eq_of_mem_function hc.1 ▸ mem_domain_of_kpair_mem hjd
  let : IsOrdinal j := IsOrdinal.of_mem hj
  have hjval : c ‘ j = (R.equiv d).val := value_eq_of_kpair_mem hjd
  have hde : ⟨c ‘ j, (R.equiv e).val⟩ₖ ∈ codedFiniteDomainOrder R.code (R.equiv s).val := by
    rw [hjval]
    exact (R.finiteDomainOrder_iff s d e).mpr ⟨R.finiteDomainChain_selected_finite hc hd.1, ⟨hefin, hes⟩, hd.2⟩
  have hji : j ⊆ i := hc.index_mono (R.finiteDomainOrder_poset s) hj hi
    ((R.finiteDomainOrder_poset s).1.2.2 _ (function_value_mem hc.1 hj)
      _ ((R.finiteDomain_mem_iff s e).mpr ⟨hefin, hes⟩) _ (function_value_mem hc.1 hi) hde hei)
  exact (repl_spec (by definability)).mpr
    ⟨j, mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hji), hjval.symm⟩

theorem finiteDomainChain_selected_clauses :
    (∀ d : W, (R.equiv d).val ∈ range c → IsInternallyFinite d ∧ d ⊆ s) ∧
    (∀ d e : W, (R.equiv d).val ∈ range c → (R.equiv e).val ∈ range c → d ⊆ e ∨ e ⊆ d) ∧
    (∀ a : W, IsInternallyFinite a → a ⊆ s → ∃ d : W, (R.equiv d).val ∈ range c ∧ a ⊆ d) ∧
    R.representedQ {d : W | (R.equiv d).val ∈ range c} ∧
    ∀ e : W, (R.equiv e).val ∈ range c →
      ¬R.representedQ {d : W | (R.equiv d).val ∈ range c ∧ d ⊆ e} := by
  refine ⟨fun _ hd ↦ R.finiteDomainChain_selected_finite hc hd,
    fun _ _ hd he ↦ R.finiteDomainChain_selected_linear hc hd he,
    fun _ ha hs ↦ R.finiteDomainChain_selected_cofinal hc ha hs,
    R.finiteDomainChain_selected_Q hc, fun e he ↦ ?_⟩
  have hf := R.finiteDomainChain_selected_finite hc he
  exact R.finiteDomainChain_selected_initial hc hf.1 hf.2

theorem finiteDomainChain_selectedDomainClausesWithQ :
    SelectedDomainClausesWithQ R.representedQ s (fun d ↦ (R.equiv d).val ∈ range c) := by
  obtain ⟨hfinite, hlinear, hcofinal, hlarge, hinitial⟩ := R.finiteDomainChain_selected_clauses hc
  exact ⟨hfinite, hlinear, hcofinal, hlarge, hinitial⟩

end ZFVP.BinaryRelationRepresentation
