import ZFVP.SetTheory.ForcingRegular
import ZFVP.SetTheory.OrdinalDependentChoice

/-! Closure and intersections of dense open sets, with the required
ordinal instance of dependent choice stated explicitly. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsForcingDescending (P R α f : V) : Prop :=
  f ∈ P ^ α ∧ ∀ i ∈ α, ∀ j ∈ i, ⟨f ‘ i, f ‘ j⟩ₖ ∈ R

def IsForcingClosedAt (P R α : V) : Prop :=
  ∀ f, IsForcingDescending P R α f → ∃ p ∈ P, ∀ i ∈ α, ⟨p, f ‘ i⟩ₖ ∈ R

def IsForcingClosedBelow (P R κ : V) : Prop :=
  ∀ α ∈ κ, IsForcingClosedAt P R α

instance isForcingDescending_definable : ℒₛₑₜ-relation₄[V] IsForcingDescending := by
  unfold IsForcingDescending
  definability

instance isForcingClosedAt_definable : ℒₛₑₜ-relation₃[V] IsForcingClosedAt := by
  unfold IsForcingClosedAt
  definability

instance isForcingClosedBelow_definable : ℒₛₑₜ-relation₃[V] IsForcingClosedBelow := by
  unfold IsForcingClosedBelow
  definability

theorem forcingClosedAt_lowerBound_below {P R α f p : V}
    (hR : IsForcingPreorder P R) (hclosed : IsForcingClosedAt P R α)
    (hf : IsForcingDescending P R α f) (hp : p ∈ P)
    (hbelow : ∀ i ∈ α, ⟨f ‘ i, p⟩ₖ ∈ R) :
    ∃ q ∈ P, ⟨q, p⟩ₖ ∈ R ∧ ∀ i ∈ α, ⟨q, f ‘ i⟩ₖ ∈ R := by
  classical
  by_cases hn : ∃ i, i ∈ α
  · obtain ⟨i, hi⟩ := hn
    obtain ⟨q, hq, hbound⟩ := hclosed f hf
    exact ⟨q, hq, hR.2.2 q hq (f ‘ i) (function_value_mem hf.1 hi) p hp
      (hbound i hi) (hbelow i hi), hbound⟩
  · exact ⟨p, hp, hR.2.1 p hp, fun i hi ↦ False.elim (hn ⟨i, hi⟩)⟩

set_option maxHeartbeats 1600000 in
theorem forcingClosed_denseIntersection {P R γ D : V} [IsOrdinal γ]
    (hR : IsForcingPreorder P R) (hDC : InternalDependentChoiceAt γ)
    (hclosed : ∀ α, IsOrdinal α → α ⊆ γ → IsForcingClosedAt P R α)
    (hD : ∀ i ∈ γ, ForcingDense P R (D ‘ i) ∧ IsForcingDownwardClosed P R (D ‘ i)) :
    ForcingDense P R {q ∈ P ; ∀ i ∈ γ, q ∈ D ‘ i} := by
  classical
  refine ⟨fun q hq ↦ (mem_sep_iff.mp hq).1, fun p hp ↦ ?_⟩
  let Q : V := {z ∈ shorterSequences γ P ×ˢ P ;
    (IsForcingDescending P R (domain (kpair.π₁ z)) (kpair.π₁ z) ∧
      ∀ i ∈ domain (kpair.π₁ z), ⟨(kpair.π₁ z) ‘ i, p⟩ₖ ∈ R) →
    ⟨kpair.π₂ z, p⟩ₖ ∈ R ∧ kpair.π₂ z ∈ D ‘ (domain (kpair.π₁ z)) ∧
      ∀ i ∈ domain (kpair.π₁ z), ⟨kpair.π₂ z, (kpair.π₁ z) ‘ i⟩ₖ ∈ R}
  have hQ (s q : V) : ⟨s, q⟩ₖ ∈ Q ↔ s ∈ shorterSequences γ P ∧ q ∈ P ∧
      ((IsForcingDescending P R (domain s) s ∧ ∀ i ∈ domain s, ⟨s ‘ i, p⟩ₖ ∈ R) →
      ⟨q, p⟩ₖ ∈ R ∧ q ∈ D ‘ (domain s) ∧ ∀ i ∈ domain s, ⟨q, s ‘ i⟩ₖ ∈ R) := by
    simp only [Q, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
    tauto
  have hserial : ∀ s ∈ shorterSequences γ P, ∃ q ∈ P, ⟨s, q⟩ₖ ∈ Q := by
    intro s hs
    have hd := ((mem_shorterSequences_domain _ _ _).mp hs).1
    by_cases hg : IsForcingDescending P R (domain s) s ∧
        ∀ i ∈ domain s, ⟨s ‘ i, p⟩ₖ ∈ R
    · obtain ⟨q, hq, hqp, hbound⟩ := forcingClosedAt_lowerBound_below hR
        (hclosed _ (IsOrdinal.of_mem hd) (IsOrdinal.toIsTransitive.transitive _ hd)) hg.1 hp hg.2
      obtain ⟨r, hr, hrq⟩ := (hD _ hd).1.2 q hq
      have hrP := (hD _ hd).1.1 r hr
      exact ⟨r, hrP, (hQ s r).mpr ⟨hs, hrP, fun _ ↦
        ⟨hR.2.2 r hrP q hq p hp hrq hqp, hr, fun i hi ↦
          hR.2.2 r hrP q hq (s ‘ i) (function_value_mem hg.1.1 hi) hrq (hbound i hi)⟩⟩⟩
    · exact ⟨p, hp, (hQ s p).mpr ⟨hs, hp, fun hh ↦ False.elim (hg hh)⟩⟩
  obtain ⟨f, hf, hstep⟩ := hDC P Q ⟨p, hp⟩ hserial
  let := IsFunction.of_mem hf
  have hprogress : ∀ i : Ordinal V, i.val ∈ γ →
      ⟨f ‘ i.val, p⟩ₖ ∈ R ∧ f ‘ i.val ∈ D ‘ i.val ∧
        ∀ j ∈ i.val, ⟨f ‘ i.val, f ‘ j⟩ₖ ∈ R := by
    apply transfinite_induction (fun i ↦ i ∈ γ →
      ⟨f ‘ i, p⟩ₖ ∈ R ∧ f ‘ i ∈ D ‘ i ∧ ∀ j ∈ i, ⟨f ‘ i, f ‘ j⟩ₖ ∈ R)
      (by definability)
    intro i ih hi
    have hisub : i.val ⊆ γ := IsOrdinal.toIsTransitive.transitive _ hi
    have hfi := function_restrict_mem hf hisub
    have hval (j : V) (hj : j ∈ i.val) : (f ↾ i.val) ‘ j = f ‘ j :=
      value_restrict (by rw [domain_eq_of_mem_function hf]; exact hisub j hj) hj
    have hgood : IsForcingDescending P R i.val (f ↾ i.val) ∧
        ∀ j ∈ i.val, ⟨(f ↾ i.val) ‘ j, p⟩ₖ ∈ R := by
      refine ⟨⟨hfi, ?_⟩, ?_⟩
      · intro j hj k hk
        let := IsOrdinal.of_mem hj
        rw [hval j hj, hval k (IsOrdinal.toIsTransitive.mem_trans hk hj)]
        exact (ih (IsOrdinal.toOrdinal j) hj (hisub j hj)).2.2 k hk
      · intro j hj
        let := IsOrdinal.of_mem hj
        rw [hval j hj]
        exact (ih (IsOrdinal.toOrdinal j) hj (hisub j hj)).1
    have hh := ((hQ _ _).mp (hstep i.val hi)).2.2
    rw [domain_eq_of_mem_function hfi] at hh
    obtain ⟨hfp, hfD, hbound⟩ := hh hgood
    exact ⟨hfp, hfD, fun j hj ↦ by simpa only [hval j hj] using hbound j hj⟩
  have hprog (i : V) (hi : i ∈ γ) : ⟨f ‘ i, p⟩ₖ ∈ R ∧ f ‘ i ∈ D ‘ i ∧
      ∀ j ∈ i, ⟨f ‘ i, f ‘ j⟩ₖ ∈ R := by
    let := IsOrdinal.of_mem hi
    exact hprogress (IsOrdinal.toOrdinal i) hi
  obtain ⟨q, hq, hqp, hbound⟩ := forcingClosedAt_lowerBound_below hR
    (hclosed γ inferInstance (subset_refl _)) ⟨hf, fun i hi ↦ (hprog i hi).2.2⟩ hp
    (fun i hi ↦ (hprog i hi).1)
  exact ⟨q, mem_sep_iff.mpr ⟨hq, fun i hi ↦
    (hD i hi).2 (f ‘ i) (hprog i hi).2.1 q hq (hbound i hi)⟩, hqp⟩

end ZFVP
