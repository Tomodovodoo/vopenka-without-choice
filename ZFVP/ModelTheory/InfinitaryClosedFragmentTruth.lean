import ZFVP.ModelTheory.InfinitaryHenkinTermModel
import ZFVP.ModelTheory.InfinitaryFragmentSubstitution

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage KeislerDerivation FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))} (H : FragmentExtension Γ (FragmentClosure.carrier S))

theorem expanded_in_fragment {n} (φ : Semisentence (limit L) n) :
    ⟨n, Formula.expandFirstOrder φ⟩ ∈ FragmentClosure.carrier S :=
  firstOrder_subset_carrier S (Or.inr ⟨⟨n, φ⟩, rfl⟩)

theorem and_mem_iff {φ ψ : Sentence (limit L)}
    (hφ : ⟨0, φ⟩ ∈ FragmentClosure.carrier S) (hψ : ⟨0, ψ⟩ ∈ FragmentClosure.carrier S) :
    φ.and ψ ∈ H.carrier ↔ φ ∈ H.carrier ∧ ψ ∈ H.carrier := by
  have he := H.conj_mem_iff (fun i ↦ if i = 0 then φ else ψ) (and_closed hφ hψ)
    (by intro i; split_ifs <;> assumption)
  change Formula.conj (fun i ↦ if i = 0 then φ else ψ) ∈ H.carrier ↔ _
  rw [he]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨hp, hq⟩ i
    split_ifs <;> assumption

theorem or_mem_iff {φ ψ : Sentence (limit L)}
    (hφ : ⟨0, φ⟩ ∈ FragmentClosure.carrier S) (hψ : ⟨0, ψ⟩ ∈ FragmentClosure.carrier S) :
    φ.or ψ ∈ H.carrier ↔ φ ∈ H.carrier ∨ ψ ∈ H.carrier := by
  classical
  rw [Formula.or, H.neg_mem_iff (and_closed (neg_closed hφ) (neg_closed hψ)),
    H.and_mem_iff (neg_closed hφ) (neg_closed hψ), H.neg_mem_iff hφ, H.neg_mem_iff hψ]
  tauto

theorem imp_mem_iff {φ ψ : Sentence (limit L)}
    (hφ : ⟨0, φ⟩ ∈ FragmentClosure.carrier S) (hψ : ⟨0, ψ⟩ ∈ FragmentClosure.carrier S) :
    φ.imp ψ ∈ H.carrier ↔ (φ ∈ H.carrier → ψ ∈ H.carrier) := by
  classical
  rw [Formula.imp, H.or_mem_iff (neg_closed hφ) hψ, H.neg_mem_iff hφ]
  tauto

theorem iff_mem_iff {φ ψ : Sentence (limit L)}
    (hφ : ⟨0, φ⟩ ∈ FragmentClosure.carrier S) (hψ : ⟨0, ψ⟩ ∈ FragmentClosure.carrier S) :
    φ.iff ψ ∈ H.carrier ↔ (φ ∈ H.carrier ↔ ψ ∈ H.carrier) := by
  rw [Formula.iff, H.and_mem_iff (imp_closed hφ hψ) (imp_closed hψ hφ),
    H.imp_mem_iff hφ hψ, H.imp_mem_iff hψ hφ]
  exact Iff.symm iff_def

theorem all_mem_iff {φ : Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) :
    Formula.all φ ∈ H.carrier ↔ ∀ t : Semiterm (limit L) Empty 0, φ.substFirst t ∈ H.carrier := by
  classical
  rw [Formula.all, H.neg_mem_iff (exs_closed (neg_closed hφ)),
    H.exs_mem_iff (.neg φ) (exs_closed (neg_closed hφ))]
  change (¬ ∃ t, .neg (φ.substFirst t) ∈ H.carrier) ↔ _
  simp only [not_exists]
  apply forall_congr'
  intro t
  have ht : ⟨0, φ.substFirst t⟩ ∈ FragmentClosure.carrier S := subst_closed hφ _
  rw [H.neg_mem_iff ht]
  exact not_not

theorem expansion_mem_iff (φ : Semisentence (limit L) 0) :
    Formula.fo φ ∈ H.carrier ↔ Formula.expandFirstOrder φ ∈ H.carrier :=
  (H.iff_mem_iff (fo_in_fragment _) (expanded_in_fragment _)).mp
    (H.of_theorem (iff_closed (fo_in_fragment _) (expanded_in_fragment _)) (.expansion φ))

end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary


