import ZFVP.ModelTheory.InfinitaryFragmentHenkin

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace KeislerDerivation
variable {L : Language} [L.Eq] {Γ : Set (Sentence L)}

theorem existentialIntroduction {n} (φ : Formula L (n + 1)) (t : Semiterm L Empty n) :
    KeislerDerivation Γ ((φ.substFirst t).imp (.exs φ)) := by
  have hi : KeislerDerivation Γ
      ((φ.substFirst t).imp (.exs (.neg (.neg φ)))) :=
    .mp (.boolean (.contraposition (.exs (.neg (.neg φ))) (φ.substFirst t)))
      (.instantiation (.neg φ) t)
  have he : KeislerDerivation Γ ((Formula.exs (.neg (.neg φ))).imp (.exs φ)) :=
    .mp (.exDistribution _ _) (.generalization (.boolean (.dne φ)))
  exact imp_trans hi he

theorem iff_left {n} {φ ψ : Formula L n} (h : KeislerDerivation Γ (φ.iff ψ)) :
    KeislerDerivation Γ (φ.imp ψ) := by
  have hp := KeislerDerivation.boolean (Γ := Γ)
    (BooleanDerivation.projection (fun i ↦ if i = 0 then φ.imp ψ else ψ.imp φ) 0)
  exact .mp (by simpa [Formula.countableProjection, Formula.iff, Formula.and] using hp) h

theorem iff_right {n} {φ ψ : Formula L n} (h : KeislerDerivation Γ (φ.iff ψ)) :
    KeislerDerivation Γ (ψ.imp φ) := by
  have hp := KeislerDerivation.boolean (Γ := Γ)
    (BooleanDerivation.projection (fun i ↦ if i = 0 then φ.imp ψ else ψ.imp φ) 1)
  exact .mp (by simpa [Formula.countableProjection, Formula.iff, Formula.and] using hp) h
end KeislerDerivation

namespace HenkinConstruction.FragmentExtension
open HenkinLanguage KeislerDerivation
variable {L : Language} [L.Eq] {Γ : Set (Sentence L)}
  {T : Set (TaggedFormula (limit L))} (H : FragmentExtension Γ T)

def toBoolean : BooleanHenkinExtension
    (Formula.lMap (Language.Hom.add₁ L (Language.constant ℕ)) '' Γ)
    {φ | ⟨0, φ⟩ ∈ T} :=
  ⟨H.carrier, H.countable, H.includes, H.finite_consistent, H.decides, H.conjunction_witness⟩

theorem not_both (φ : Sentence (limit L)) (hφ : φ ∈ H.carrier)
    (hn : .neg φ ∈ H.carrier) : False := H.toBoolean.not_both φ hφ hn

theorem neg_mem_iff {φ : Sentence (limit L)} (hφ : ⟨0, φ⟩ ∈ T) :
    .neg φ ∈ H.carrier ↔ φ ∉ H.carrier := H.toBoolean.neg_mem_iff hφ

theorem conj_mem_iff (f : ℕ → Sentence (limit L)) (hf : ⟨0, .conj f⟩ ∈ T)
    (hfi : ∀ i, ⟨0, f i⟩ ∈ T) : .conj f ∈ H.carrier ↔ ∀ i, f i ∈ H.carrier :=
  H.toBoolean.conj_mem_iff f hf hfi

/-- Finite consistency suffices to close fragment membership under a proof from
finitely many members, even when that proof itself branches countably. -/
theorem of_finite_proof (s : Finset (Sentence (limit L)))
    (hs : ∀ φ ∈ s, φ ∈ H.carrier) {φ : Sentence (limit L)} (hφ : ⟨0, φ⟩ ∈ T)
    (d : KeislerDerivation (s : Set (Sentence (limit L))) φ) : φ ∈ H.carrier := by
  classical
  by_contra hn
  have hneg := (H.neg_mem_iff hφ).mpr hn
  have hc := H.finite_consistent (insert (.neg φ) s) (by
    intro ψ hψ
    rcases Finset.mem_insert.mp hψ with rfl | hψ
    · exact hneg
    · exact hs ψ hψ)
  apply hc
  apply (d.mono ?_).contradiction (of_mem (by simp))
  intro ψ hψ
  exact Finset.mem_insert_of_mem hψ

theorem of_theorem {φ : Sentence (limit L)} (hφ : ⟨0, φ⟩ ∈ T)
    (d : KeislerDerivation ∅ φ) : φ ∈ H.carrier :=
  H.of_finite_proof ∅ (by simp) hφ (by simpa only [Finset.coe_empty] using d)

theorem mp_mem {φ ψ : Sentence (limit L)} (hψ : ⟨0, ψ⟩ ∈ T)
    (hi : φ.imp ψ ∈ H.carrier) (hφ : φ ∈ H.carrier) : ψ ∈ H.carrier := by
  classical
  refine H.of_finite_proof {φ.imp ψ, φ} ?_ hψ ?_
  · intro χ hχ
    rcases Finset.mem_insert.mp hχ with rfl | hχ
    · exact hi
    · have he := Finset.mem_singleton.mp hχ
      subst χ
      exact hφ
  · exact .mp (φ := φ) (of_mem (by simp)) (of_mem (by simp))

theorem exs_mem_iff (φ : Formula (limit L) 1) (hφ : ⟨0, .exs φ⟩ ∈ T) :
    .exs φ ∈ H.carrier ↔ ∃ t : Semiterm (limit L) Empty 0, φ.substFirst t ∈ H.carrier := by
  classical
  constructor
  · intro hp
    exact (H.existential_witness φ hφ).resolve_left (fun hn ↦ H.not_both _ hp hn)
  · rintro ⟨t, ht⟩
    apply H.of_finite_proof {φ.substFirst t} (by simpa) hφ
    exact .mp (existentialIntroduction φ t) (of_mem (by simp))

end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary


