import ZFVP.ModelTheory.InfinitaryHenkinWeakAxioms
import ZFVP.ModelTheory.InfinitaryWeakRewriting

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage KeislerDerivation FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))} (H : FragmentExtension Γ (FragmentClosure.carrier S))

theorem fiber_neg {φ : Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) : H.fiber (.neg φ) = (H.fiber φ)ᶜ := by
  ext x
  change Formula.neg (φ.substFirst x.out) ∈ H.carrier ↔ φ.substFirst x.out ∉ H.carrier
  exact H.neg_mem_iff (subst_closed hφ _)

theorem fiber_and {φ ψ : Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) (hψ : ⟨1, ψ⟩ ∈ FragmentClosure.carrier S) :
    H.fiber (φ.and ψ) = H.fiber φ ∩ H.fiber ψ := by
  ext x
  change (φ.and ψ).subst (Fin.cases x.out Semiterm.bvar) ∈ H.carrier ↔ _
  rw [Formula.subst_and]
  exact H.and_mem_iff (subst_closed hφ _) (subst_closed hψ _)

theorem fiber_or {φ ψ : Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) (hψ : ⟨1, ψ⟩ ∈ FragmentClosure.carrier S) :
    H.fiber (φ.or ψ) = H.fiber φ ∪ H.fiber ψ := by
  ext x
  change (φ.or ψ).subst (Fin.cases x.out Semiterm.bvar) ∈ H.carrier ↔ _
  rw [Formula.subst_or]
  exact H.or_mem_iff (subst_closed hφ _) (subst_closed hψ _)

theorem q_mem_or_iff {φ ψ : Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) (hψ : ⟨1, ψ⟩ ∈ FragmentClosure.carrier S) :
    .q (φ.or ψ) ∈ H.carrier ↔ .q φ ∈ H.carrier ∨ .q ψ ∈ H.carrier := by
  constructor
  · intro hq
    have hd := H.of_theorem (imp_closed (q_closed (or_closed hφ hψ))
      (or_closed (q_closed hφ) (q_closed hψ))) (qBinaryUnion φ ψ)
    exact (H.or_mem_iff (q_closed hφ) (q_closed hψ)).mp
      (H.mp_mem (or_closed (q_closed hφ) (q_closed hψ)) hd hq)
  · intro hq
    have hleft : H.fiber φ ⊆ H.fiber (φ.or ψ) := by
      rw [H.fiber_or hφ hψ]
      exact Set.subset_union_left
    have hright : H.fiber ψ ⊆ H.fiber (φ.or ψ) := by
      rw [H.fiber_or hφ hψ]
      exact Set.subset_union_right
    exact hq.elim (H.q_mem_mono hφ (or_closed hφ hψ) hleft)
      (H.q_mem_mono hψ (or_closed hφ hψ) hright)

/-- A Q-large finite condition can decide one further formula. -/
theorem q_mem_split {φ ψ : Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) (hψ : ⟨1, ψ⟩ ∈ FragmentClosure.carrier S)
    (hq : .q φ ∈ H.carrier) :
    .q (φ.and ψ) ∈ H.carrier ∨ .q (φ.and (.neg ψ)) ∈ H.carrier := by
  have he : H.fiber φ = H.fiber ((φ.and ψ).or (φ.and (.neg ψ))) := by
    rw [H.fiber_or (and_closed hφ hψ) (and_closed hφ (neg_closed hψ)),
      H.fiber_and hφ hψ, H.fiber_and hφ (neg_closed hψ), H.fiber_neg hψ]
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    tauto
  exact (H.q_mem_or_iff (and_closed hφ hψ) (and_closed hφ (neg_closed hψ))).mp
    ((H.q_mem_extensional hφ (or_closed (and_closed hφ hψ)
      (and_closed hφ (neg_closed hψ))) he).mp hq)

/-- Removing a Q-small definable set preserves a Q-large condition. -/
theorem q_mem_remove_small {φ ψ : Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) (hψ : ⟨1, ψ⟩ ∈ FragmentClosure.carrier S)
    (hq : .q φ ∈ H.carrier) (hn : .q ψ ∉ H.carrier) :
    .q (φ.and (.neg ψ)) ∈ H.carrier := by
  apply (H.q_mem_split hφ hψ hq).resolve_left
  intro hi
  apply hn
  apply H.q_mem_mono (and_closed hφ hψ) hψ ?_ hi
  rw [H.fiber_and hφ hψ]
  exact Set.inter_subset_right

theorem disj_mem_iff (f : ℕ → Sentence (limit L))
    (hf : ⟨0, Formula.disj f⟩ ∈ FragmentClosure.carrier S)
    (hfi : ∀ i, ⟨0, f i⟩ ∈ FragmentClosure.carrier S) :
    Formula.disj f ∈ H.carrier ↔ ∃ i, f i ∈ H.carrier := by
  classical
  have hc : ⟨0, Formula.conj (fun i ↦ .neg (f i))⟩ ∈ FragmentClosure.carrier S :=
    subformulas_closed hf (Or.inr (Formula.self_mem_subformulas _))
  rw [Formula.disj, H.neg_mem_iff hc,
    H.conj_mem_iff _ hc (fun i ↦ neg_closed (hfi i))]
  have hn (i : ℕ) : Formula.neg (f i) ∈ H.carrier ↔ f i ∉ H.carrier := H.neg_mem_iff (hfi i)
  simp only [hn, not_forall, not_not]

theorem fiber_disj (f : ℕ → Formula (limit L) 1)
    (hf : ⟨1, Formula.disj f⟩ ∈ FragmentClosure.carrier S)
    (hfi : ∀ i, ⟨1, f i⟩ ∈ FragmentClosure.carrier S) :
    H.fiber (Formula.disj f) = ⋃ i, H.fiber (f i) := by
  ext x
  simp only [Set.mem_iUnion]
  change Formula.disj (fun i ↦ (f i).substFirst x.out) ∈ H.carrier ↔ _
  exact H.disj_mem_iff _ (subst_closed hf _) (fun i ↦ subst_closed (hfi i) _)

/-- Countable-union density for a sequence whose required formulas are in the
chosen fragment; no closure under arbitrary external sequences is assumed. -/
theorem q_mem_disj_iff (f : ℕ → Formula (limit L) 1)
    (hf : ⟨1, Formula.disj f⟩ ∈ FragmentClosure.carrier S)
    (hfi : ∀ i, ⟨1, f i⟩ ∈ FragmentClosure.carrier S)
    (hQf : ⟨0, Formula.disj (fun i ↦ .q (f i))⟩ ∈ FragmentClosure.carrier S) :
    .q (Formula.disj f) ∈ H.carrier ↔ ∃ i, .q (f i) ∈ H.carrier := by
  constructor
  · intro hq
    have hd := H.of_theorem (imp_closed (q_closed hf) hQf) (.boolean (.qUnion f))
    exact (H.disj_mem_iff _ hQf (fun i ↦ q_closed (hfi i))).mp (H.mp_mem hQf hd hq)
  · rintro ⟨i, hi⟩
    apply H.q_mem_mono (hfi i) hf ?_ hi
    rw [H.fiber_disj f hf hfi]
    exact Set.subset_iUnion (fun j ↦ H.fiber (f j)) i

end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary

