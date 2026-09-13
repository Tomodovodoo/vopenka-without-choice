import ZFVP.ModelTheory.UsubaSingularCollapseDCAt
import ZFVP.ModelTheory.UsubaRestorationIterand

/-! The canonical restoration collapse gains DC at the previous least
failure. If Choice still fails, the next least failure is strictly larger. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace UsubaCollapseModel

theorem canonical_dependentChoiceAt [Countable V]
    (hLS : ∀ β : V, IsOrdinal β → ∃ lam : V, β ∈ lam ∧ IsLSCardinal lam)
    {G : Set V}
    (hG : IsExternalForcingGeneric
      (usubaCollapse woodinSeedCardinal (hierarchy (usubaLeastTarget woodinSeedCardinal)))
      (usubaCollapseOrder woodinSeedCardinal (hierarchy (usubaLeastTarget woodinSeedCardinal))) G) :
    InternalDependentChoiceAt ((usubaCollapseContext woodinSeedCardinal_regular
      (hierarchy (usubaLeastTarget woodinSeedCardinal)) G hG).check woodinSeedCardinal) := by
  obtain ⟨hlam, hsing, hκcf, ν, hν, hκν, hνcf⟩ := usubaLeastTarget_spec hLS woodinSeedCardinal
  exact dependentChoiceAt_of_singular_LS woodinSeedCardinal_regular woodinSeedCardinal_DC
    hlam hsing hκcf hν hκν hνcf hG

end UsubaCollapseModel

namespace ForcingContext

theorem restoration_dependentChoiceAt [Countable V] (A : ForcingContext V)
    (hLS : ∀ β : V, IsOrdinal β → ∃ lam : V, β ∈ lam ∧ IsLSCardinal lam)
    (hAC : ¬InternalChoice V) (hP : A.P = usubaRestorationPoset)
    (hR : A.R = reverseInclusionOrder A.P) (hone : A.one = ∅) :
    InternalDependentChoiceAt (A.check woodinSeedCardinal) := by
  have hPc := hP.trans (usubaRestorationPoset_of_not_choice hAC)
  rcases A with ⟨P, R, one, G, order, top, generic⟩
  dsimp only at hPc hR hone ⊢
  subst P R one
  exact UsubaCollapseModel.canonical_dependentChoiceAt hLS generic

theorem restoration_seed_strictly_increases [Countable V] (A : ForcingContext V)
    (hLS : ∀ β : V, IsOrdinal β → ∃ lam : V, β ∈ lam ∧ IsLSCardinal lam)
    (hAC : ¬InternalChoice V) (hP : A.P = usubaRestorationPoset)
    (hR : A.R = reverseInclusionOrder A.P) (hone : A.one = ∅)
    (hAC' : ¬InternalChoice A.Model) :
    A.check woodinSeedCardinal ∈ (woodinSeedCardinal : A.Model) := by
  have hgain := A.restoration_dependentChoiceAt hLS hAC hP hR hone
  have hnew := woodinSeedCardinal_spec hAC'
  have hPc := hP.trans (usubaRestorationPoset_of_not_choice hAC)
  have hbelow : ∀ γ ∈ A.check woodinSeedCardinal, InternalDependentChoiceAt γ := by
    rcases A with ⟨P, R, one, G, order, top, generic⟩
    dsimp only at hPc hR hone ⊢
    subst P R one
    exact UsubaCollapseModel.dependentChoice_below woodinSeedCardinal_regular generic
      woodinSeedCardinal_DC
  rcases IsOrdinal.mem_trichotomy (A.check woodinSeedCardinal)
    (woodinSeedCardinal : A.Model) with h | he | h
  · exact h
  · exact False.elim (hnew.2.1 (he ▸ hgain))
  · exact False.elim (hnew.2.1 (hbelow _ h))

end ForcingContext
end ZFVP
