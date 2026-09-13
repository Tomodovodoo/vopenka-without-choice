import ZFVP.ModelTheory.InfinitaryHenkinQDensity

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace FragmentClosure
variable {L : Language} [L.Encodable]

theorem rename_closed {S : Set (TaggedFormula L)} {n m} {φ : Formula L n}
    (hφ : ⟨n, φ⟩ ∈ carrier S) (ρ : Fin n → Fin m) : ⟨m, φ.rename ρ⟩ ∈ carrier S := by
  rw [← Formula.subst_bvar_eq_rename]
  exact subst_closed hφ _

theorem swapFirstTwo_closed {S : Set (TaggedFormula L)} {n} {φ : Formula L (n + 2)}
    (hφ : ⟨n + 2, φ⟩ ∈ carrier S) : ⟨n + 2, φ.swapFirstTwo⟩ ∈ carrier S :=
  rename_closed hφ _

theorem qInterchange_closed {S : Set (TaggedFormula L)} {n} {φ : Formula L (n + 2)}
    (hφ : ⟨n + 2, φ⟩ ∈ carrier S) : ⟨n, Formula.qInterchange φ⟩ ∈ carrier S :=
  imp_closed (q_closed (exs_closed hφ))
    (or_closed (exs_closed (q_closed (swapFirstTwo_closed hφ)))
      (q_closed (exs_closed (swapFirstTwo_closed hφ))))

end FragmentClosure
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage KeislerDerivation FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))} (H : FragmentExtension Γ (FragmentClosure.carrier S))

theorem q_interchange_mem {φ : Formula (limit L) 2}
    (hφ : ⟨2, φ⟩ ∈ FragmentClosure.carrier S) (hq : .q (.exs φ) ∈ H.carrier) :
    .exs (.q φ.swapFirstTwo) ∈ H.carrier ∨ .q (.exs φ.swapFirstTwo) ∈ H.carrier := by
  have hs := swapFirstTwo_closed hφ
  have hd := H.of_theorem (qInterchange_closed hφ) (.qInterchange φ)
  exact (H.or_mem_iff (exs_closed (q_closed hs)) (q_closed (exs_closed hs))).mp
    (H.mp_mem (or_closed (exs_closed (q_closed hs)) (q_closed (exs_closed hs))) hd hq)

/-- If the projection onto possible witnesses is Q-small, Q interchange selects
an old closed-term witness that retains Q-many choices in the other coordinate. -/
theorem q_large_witness_over_small_projection {φ : Formula (limit L) 2}
    (hφ : ⟨2, φ⟩ ∈ FragmentClosure.carrier S) (hq : .q (.exs φ) ∈ H.carrier)
    (hsmall : .q (.exs φ.swapFirstTwo) ∉ H.carrier) :
    ∃ t : Semiterm (limit L) Empty 0, (Formula.q φ.swapFirstTwo).substFirst t ∈ H.carrier := by
  have he := (H.q_interchange_mem hφ hq).resolve_right hsmall
  exact (H.exs_mem_iff _ (exs_closed (q_closed (swapFirstTwo_closed hφ)))).mp he

/-- A definable small bound on the witness coordinate supplies the small
projection hypothesis, so the witness can be taken from the old model. -/
theorem q_large_witness_in_small_bound {φ : Formula (limit L) 2} {ψ : Formula (limit L) 1}
    (hφ : ⟨2, φ⟩ ∈ FragmentClosure.carrier S) (hψ : ⟨1, ψ⟩ ∈ FragmentClosure.carrier S)
    (hq : .q (.exs φ) ∈ H.carrier) (hsmall : .q ψ ∉ H.carrier)
    (hbound : H.fiber (.exs φ.swapFirstTwo) ⊆ H.fiber ψ) :
    ∃ t : Semiterm (limit L) Empty 0, (Formula.q φ.swapFirstTwo).substFirst t ∈ H.carrier :=
  H.q_large_witness_over_small_projection hφ hq
    (fun hp ↦ hsmall (H.q_mem_mono (exs_closed (swapFirstTwo_closed hφ)) hψ hbound hp))

end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary
