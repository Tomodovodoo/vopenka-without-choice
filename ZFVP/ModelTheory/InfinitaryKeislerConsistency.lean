import ZFVP.ModelTheory.InfinitaryKeislerDeduction

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace KeislerDerivation
variable {L : Language} [L.Eq] {Γ Δ : Set (Sentence L)}

/-- Derive falsity from a formula and its negation using the actual Boolean schemas. -/
theorem contradiction {n} {φ : Formula L n} (d : KeislerDerivation Γ φ)
    (e : KeislerDerivation Γ (.neg φ)) : KeislerDerivation Γ (.neg (.fo .verum : Formula L n)) := by
  exact .mp (.mp (.boolean (.contraposition _ φ)) (e.weaken_imp _)) d

 theorem neg_of_imp_false {n} {φ : Formula L n}
    (d : KeislerDerivation Γ (φ.imp (.neg (.fo .verum)))) : KeislerDerivation Γ (.neg φ) := by
  have e := imp_trans (KeislerDerivation.boolean (.dne φ)) d
  exact .mp (.mp (.boolean (.contraposition (.neg φ) (.fo .verum))) e) .truth

 theorem exfalso {n} {φ : Formula L n}
    (d : KeislerDerivation Γ (.neg (.fo .verum : Formula L n))) : KeislerDerivation Γ φ := by
  exact .mp (.mp (.boolean (.contraposition φ (.fo .verum))) (d.weaken_imp _)) .truth

 theorem of_mem {φ : Sentence L} (h : φ ∈ Γ) : KeislerDerivation Γ φ := by
  have hid : (Fin.elim0 : Fin 0 → Fin 0) = id := Subsingleton.elim _ _
  simpa [hid] using (KeislerDerivation.hypothesis (n := 0) h)

 theorem consistent_mono (h : Γ ⊆ Δ) (hc : Consistent Δ) : Consistent Γ :=
  fun d ↦ hc (d.mono h)

/-- Consistency of one sentence extension is exactly absence of a proof of its negation. -/
theorem consistent_insert_iff (φ : Sentence L) :
    Consistent (insert φ Γ) ↔ ¬KeislerDerivation Γ (.neg φ) := by
  constructor
  · intro hc hn
    exact hc ((of_mem (Set.mem_insert φ Γ)).contradiction (hn.mono (Set.subset_insert φ Γ)))
  · intro hn hf
    apply hn
    apply neg_of_imp_false
    have hid : (Fin.elim0 : Fin 0 → Fin 0) = id := Subsingleton.elim _ _
    simpa [hid] using hf.deduction

/-- A consistent theory can decide any one sentence without becoming inconsistent. -/
theorem consistent_decide (hc : Consistent Γ) (φ : Sentence L) :
    Consistent (insert φ Γ) ∨ Consistent (insert (.neg φ) Γ) := by
  classical
  by_cases h : Consistent (insert φ Γ)
  · exact Or.inl h
  · right
    apply (consistent_insert_iff (.neg φ)).mpr
    intro hnn
    have hn : KeislerDerivation Γ (.neg φ) := by
      by_contra hneg
      exact h ((consistent_insert_iff φ).mpr hneg)
    exact hc ((KeislerDerivation.mp (.boolean (.dne φ)) hnn).contradiction hn)

/-- A consistent theory containing the negation of a countable conjunction has a
consistent extension selecting a negated conjunct. This is the infinitary witness step. -/
theorem consistent_neg_conj_witness (hc : Consistent Γ) (φ : ℕ → Sentence L)
    (h : KeislerDerivation Γ (.neg (.conj φ))) :
    ∃ i, Consistent (insert (.neg (φ i)) Γ) := by
  classical
  by_contra hh
  push_neg at hh
  have hi : ∀ i, KeislerDerivation Γ (φ i) := by
    intro i
    have hnn : KeislerDerivation Γ (.neg (.neg (φ i))) := by
      by_contra hn
      exact hh i ((consistent_insert_iff _).mpr hn)
    exact .mp (.boolean (.dne _)) hnn
  exact hc ((KeislerDerivation.conjunction φ hi).contradiction h)

end KeislerDerivation
end ZFVP.Infinitary
