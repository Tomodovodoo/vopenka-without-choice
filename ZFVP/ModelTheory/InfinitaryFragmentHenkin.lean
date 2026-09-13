import ZFVP.ModelTheory.InfinitaryHenkinExtension
import ZFVP.ModelTheory.InfinitaryFiniteSupport

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction
open HenkinLanguage
variable {L : Language} [L.Eq]

/-- The scheduling requirements visible at a finite language stage. -/
def requirements (T : Set (TaggedFormula (limit L))) :
    (n : ℕ) → Set (Sentence (stage L n))
  | 0 => ∅
  | n + 1 => {φ | ⟨0, φ.lMap (intoLimit (n + 1))⟩ ∈ T}

theorem intoLimit_injective (n k : ℕ) :
    Function.Injective (Formula.lMap (intoLimit (L := L) (n + 1)) :
      Formula (stage L (n + 1)) k → Formula (limit L) k) := by
  intro φ ψ h
  have he := congrArg (Formula.lMap (fromLimit n)) h
  simpa only [LanguageMap.formula_retract _ _ (fromLimit_intoLimit_func n)
    (fromLimit_intoLimit_rel n)] using he

theorem requirements_countable {T : Set (TaggedFormula (limit L))} (hT : T.Countable)
    (n : ℕ) : (requirements T n).Countable := by
  cases n with
  | zero => exact Set.countable_empty
  | succ n =>
    apply hT.preimage
    intro φ ψ h
    exact intoLimit_injective n 0 (by simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h)

/-- A Henkin theory deciding every sentence of a specified fragment. -/
structure FragmentExtension (Γ : Set (Sentence L)) (T : Set (TaggedFormula (limit L))) where
  carrier : Set (Sentence (limit L))
  countable : carrier.Countable
  includes : Formula.lMap (Language.Hom.add₁ L (Language.constant ℕ)) '' Γ ⊆ carrier
  finite_consistent : ∀ s : Finset (Sentence (limit L)), (∀ φ ∈ s, φ ∈ carrier) →
    KeislerDerivation.Consistent (s : Set (Sentence (limit L)))
  decides : ∀ φ, ⟨0, φ⟩ ∈ T → φ ∈ carrier ∨ .neg φ ∈ carrier
  conjunction_witness : ∀ f : ℕ → Sentence (limit L), ⟨0, .conj f⟩ ∈ T →
    .conj f ∈ carrier ∨ ∃ i, .neg (f i) ∈ carrier
  existential_witness : ∀ f : Formula (limit L) 1, ⟨0, .exs f⟩ ∈ T →
    .neg (.exs f) ∈ carrier ∨ ∃ t : Semiterm (limit L) Empty 0, f.substFirst t ∈ carrier

theorem exists_fragmentExtension (Γ : Set (Sentence L))
    (hc : KeislerDerivation.Consistent Γ) (hΓ : Γ.Countable)
    (T : Set (TaggedFormula (limit L))) (hT : T.Countable)
    (hfinite : ∀ a ∈ T, FiniteSupport a.2) : Nonempty (FragmentExtension Γ T) := by
  obtain ⟨H⟩ := exists_extension Γ hc hΓ (requirements T) (requirements_countable hT)
  refine ⟨⟨H.carrier, H.countable, H.includes, H.finite_consistent, ?_, ?_, ?_⟩⟩
  · intro φ hφ
    obtain ⟨n, ψ, hψ⟩ := finiteSupport_has_stage (hfinite ⟨0, φ⟩ hφ)
    have hr : ψ ∈ requirements T (n + 1) := by
      change ⟨0, ψ.lMap (intoLimit (n + 1))⟩ ∈ T
      rwa [hψ]
    simpa only [hψ] using H.decides (n + 1) ψ hr
  · intro f hf
    obtain ⟨n, hn⟩ := (hfinite ⟨0, .conj f⟩ hf).exists
    have he : ∀ i, ((f i).lMap (fromLimit n)).lMap (intoLimit (n + 1)) = f i := by
      intro i
      rw [LanguageMap.formula_comp]
      exact congrFun (Formula.conj.inj hn) i
    have hr : Formula.conj (fun i ↦ (f i).lMap (fromLimit n)) ∈ requirements T (n + 1) := by
      change ⟨0, Formula.conj (fun i ↦ ((f i).lMap (fromLimit n)).lMap (intoLimit (n + 1)))⟩ ∈ T
      simpa only [he] using hf
    simpa only [he] using H.conjunction_witness (n + 1) _ hr
  · intro f hf
    obtain ⟨n, hn⟩ := (hfinite ⟨0, .exs f⟩ hf).exists
    have he : (f.lMap (fromLimit n)).lMap (intoLimit (n + 1)) = f := by
      rw [LanguageMap.formula_comp]
      exact Formula.exs.inj hn
    have hr : Formula.exs (f.lMap (fromLimit n)) ∈ requirements T (n + 1) := by
      change ⟨0, Formula.exs ((f.lMap (fromLimit n)).lMap (intoLimit (n + 1)))⟩ ∈ T
      rwa [he]
    simpa only [he] using H.existential_witness (n + 1) _ hr

/-- The closure of any countable, finitely supported seed admits a Henkin extension. -/
theorem exists_closedFragmentExtension [L.Encodable] (Γ : Set (Sentence L))
    (hc : KeislerDerivation.Consistent Γ) (hΓ : Γ.Countable)
    (S : Set (TaggedFormula (limit L))) (hS : S.Countable)
    (hfinite : ∀ a ∈ S, FiniteSupport a.2) :
    Nonempty (FragmentExtension Γ (FragmentClosure.carrier S)) :=
  exists_fragmentExtension Γ hc hΓ _ (FragmentClosure.carrier_countable hS)
    (fun _ ha ↦ finiteSupport_fragment hfinite ha)

end HenkinConstruction
end ZFVP.Infinitary

