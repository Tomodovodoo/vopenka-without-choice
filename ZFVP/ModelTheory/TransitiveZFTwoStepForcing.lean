import ZFVP.ModelTheory.TransitiveZFBoundedForcing
import ZFVP.ModelTheory.TransitiveZFAtomicForcing
import ZFVP.SetTheory.TwoStepForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingName_of_twoStepNames {P Q t τ : V} (hQ : IsForcingName P Q)
    (ht : IsForcingName P t) (hτ : τ ∈ twoStepNames Q t) : IsForcingName P τ := by
  rcases mem_union_iff.mp hτ with hτ | hτ
  · obtain ⟨p, hp⟩ := mem_domain_iff.mp hτ
    exact forcingName_subname hQ hp
  · exact (mem_singleton_iff.mp hτ).symm ▸ ht

namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem twoStepNames_val (Q t : SetDomain U) :
    (twoStepNames Q t).val = twoStepNames Q.val t.val := by
  simp only [twoStepNames, union_val U, domain_val U, singleton_val U]

theorem twoStepConditions_val (P R Q t : SetDomain U) :
    (twoStepConditions P R Q t).val = twoStepConditions P.val R.val Q.val t.val := by
  unfold twoStepConditions
  rw [← twoStepNames_val U Q t, ← prod_val U]
  apply sep_val U
  intro z hz
  obtain ⟨p, _, τ, _, rfl⟩ := mem_prod_iff.mp hz
  simp only [kpair_val U, kpair.π₁_kpair, kpair.π₂_kpair]
  change p.val ∈ (atomicMembership P R τ Q).val ↔ _
  rw [atomicMembership_val U]

theorem twoStepOrder_val_of_names (P R Q S t : SetDomain U) (hR : IsForcingPreorder P R)
    (hQ : IsForcingName P Q) (hS : IsForcingName P S) (ht : IsForcingName P t) :
    (twoStepOrder P R Q S t).val = twoStepOrder P.val R.val Q.val S.val t.val := by
  unfold twoStepOrder
  rw [← twoStepConditions_val U P R Q t, ← prod_val U]
  apply sep_val U
  intro z hz
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_prod_iff.mp hz
  obtain ⟨p, _, τ, hτ, rfl, _⟩ := (mem_twoStepConditions P R Q t u).mp hu
  obtain ⟨q, _, σ, hσ, rfl, _⟩ := (mem_twoStepConditions P R Q t v).mp hv
  simp only [kpair_val U, kpair.π₁_kpair, kpair.π₂_kpair]
  apply and_congr (kpair_mem_val_iff U p q R)
  have hn : ∀ i, IsForcingName P ((![S, τ, σ] : Fin 3 → SetDomain U) i) := by
    intro i
    exact Fin.cases hS (fun j ↦ Fin.cases (forcingName_of_twoStepNames hQ ht hτ)
      (fun k ↦ Fin.cases (forcingName_of_twoStepNames hQ ht hσ) (fun l ↦ Fin.elim0 l) k) j) i
  have he := bounded_forcing_iff U P R p hR boundedPairMemberFormula_bounded ![S, τ, σ] hn
  have hv : (fun i : Fin 3 ↦ ((![S, τ, σ] : Fin 3 → SetDomain U) i).val) = ![S.val, τ.val, σ.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
  rwa [hv] at he

theorem twoStepOrder_val (P R Q S t : SetDomain U) (hR : IsForcingPreorder P R)
    (h : IsForcingIterand P R Q S t) :
    (twoStepOrder P R Q S t).val = twoStepOrder P.val R.val Q.val S.val t.val :=
  twoStepOrder_val_of_names U P R Q S t hR h.posetName h.orderName h.topName

end TransitiveZF
end ZFVP
