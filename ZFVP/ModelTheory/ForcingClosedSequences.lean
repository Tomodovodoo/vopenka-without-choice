import ZFVP.ModelTheory.ForcingFunctionDecisionDensity
import ZFVP.SetTheory.ForcingClosure
import ZFVP.SetTheory.FunctionUnion

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingDenseExtension_downward {P R D p : V} (hR : IsForcingPreorder P R)
    (hD : IsForcingDownwardClosed P R D) :
    IsForcingDownwardClosed P R (forcingDenseExtension P R D p) := by
  intro q hq r hr hrq
  obtain ⟨hqP, hqD | hqinc⟩ := mem_sep_iff.mp hq
  · exact mem_sep_iff.mpr ⟨hr, Or.inl (hD q hqD r hr hrq)⟩
  · apply mem_sep_iff.mpr
    refine ⟨hr, Or.inr ?_⟩
    rintro ⟨s, hs, hsr, hsp⟩
    exact hqinc ⟨s, hs, hR.2.2 s hs r hr q hqP hsr hrq, hsp⟩

noncomputable def extendedCheckedValueDecisions (P R one τ X p a : V) : V :=
  forcingDenseExtension P R (checkedValueDecisions P R one τ X a) p

instance extendedCheckedValueDecisions_definable (P R one τ X p : V) :
    ℒₛₑₜ-function₁[V] (extendedCheckedValueDecisions P R one τ X p) := by
  have h : ℒₛₑₜ-relation[V] (fun D a ↦ ∀ q, q ∈ D ↔ q ∈ P ∧
      ((q ∈ P ∧ ∃ x ∈ X, ForcesCheckedFunctionValue P R one τ q a x) ∨
        ¬ForcingCompatible P R q p)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = extendedCheckedValueDecisions P R one τ X p (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [extendedCheckedValueDecisions, forcingDenseExtension,
    checkedValueDecisions, mem_sep_iff]

namespace ForcingContext

set_option maxHeartbeats 1600000 in
theorem function_eq_check_of_closed (S : ForcingContext V) {γ X : V} [IsOrdinal γ]
    (hDC : InternalDependentChoiceAt γ)
    (hclosed : ∀ α, IsOrdinal α → α ⊆ γ → IsForcingClosedAt S.P S.R α)
    {z : S.Model} (hz : z ∈ S.check X ^ S.check γ) :
    ∃ f ∈ X ^ γ, S.check f = z := by
  classical
  obtain ⟨τ, rfl⟩ := S.ofName_surjective z
  let u : ForcingName S.P := ⟨checkName S.one γ, checkName_isName S.top.1 γ⟩
  let v : ForcingName S.P := ⟨checkName S.one X, checkName_isName S.top.1 X⟩
  have he : boundedFunctionFormula.Evalb (fun i ↦ S.ofName (![τ, u, v] i)) :=
    (Defined.eval_iff _).mpr hz
  obtain ⟨p, hpG, hp⟩ := (S.formula_truth boundedFunctionFormula ![τ, u, v]).mp he
  let D := definableGraph γ
    (extendedCheckedValueDecisions S.P S.R S.one τ.val X p)
    (extendedCheckedValueDecisions_definable S.P S.R S.one τ.val X p)
  have hD (a : V) (ha : a ∈ γ) : D ‘ a =
      forcingDenseExtension S.P S.R (checkedValueDecisions S.P S.R S.one τ.val X a) p :=
    value_definableGraph _ _ _ ha
  have hInt : ℒₛₑₜ-predicate[V] (fun q ↦ ∀ a ∈ γ, q ∈ D ‘ a) := by
    have h : ∀ E : V, ℒₛₑₜ-predicate[V] (fun q ↦ ∀ a ∈ γ, q ∈ E ‘ a) := by
      intro E
      definability
    exact h D
  have hdense : ForcingDense S.P S.R (sep S.P (fun q ↦ ∀ a ∈ γ, q ∈ D ‘ a) hInt) := by
    apply forcingClosed_denseIntersection S.order hDC hclosed
    intro a ha
    rw [hD a ha]
    exact ⟨forcingDenseExtension_dense S.order
      (checkedValueDecisions_denseBelow S.order S.top τ.property ha hp),
      forcingDenseExtension_downward S.order (checkedValueDecisions_downward S.order)⟩
  obtain ⟨q, hqG, hq⟩ := S.generic.2 _ hdense
  have hqp : ForcingCompatible S.P S.R q p := by
    obtain ⟨r, hr, hrq, hrp⟩ := S.generic.1.2.2.2 q hqG p hpG
    exact ⟨r, S.generic.1.1 r hr, hrq, hrp⟩
  have hdec (a : V) (ha : a ∈ γ) :
      ∃ x ∈ X, ForcesCheckedFunctionValue S.P S.R S.one τ.val q a x := by
    have hh := (mem_sep_iff.mp hq).2 a ha
    rw [hD a ha] at hh
    rcases (mem_sep_iff.mp hh).2 with hh | hh
    · exact (mem_sep_iff.mp hh).2
    · exact False.elim (hh hqp)
  let f : V := {c ∈ γ ×ˢ X ;
    ForcesCheckedFunctionValue S.P S.R S.one τ.val q (kpair.π₁ c) (kpair.π₂ c)}
  have hgraph (a x : V) : ⟨a, x⟩ₖ ∈ f ↔ a ∈ γ ∧ x ∈ X ∧
      ForcesCheckedFunctionValue S.P S.R S.one τ.val q a x := by
    simp only [f, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
    tauto
  have hf : f ∈ X ^ γ := by
    apply mem_function.intro
    · exact fun c hc ↦ (mem_sep_iff.mp hc).1
    · intro a ha
      obtain ⟨x, hx, hqx⟩ := hdec a ha
      refine ⟨x, (hgraph a x).mpr ⟨ha, hx, hqx⟩, fun y hy ↦ ?_⟩
      exact forcesCheckedFunctionValue_unique S.order S.top τ.property
        ((hgraph a y).mp hy).2.2 hqx
  let := IsFunction.of_mem hf
  have hcf : S.check f ∈ S.check X ^ S.check γ := (S.check_function_iff f γ X).mpr hf
  let := IsFunction.of_mem hcf
  let := IsFunction.of_mem hz
  refine ⟨f, hf, functions_eq_of_domain_values ?_ ?_⟩
  · rw [domain_eq_of_mem_function hcf, domain_eq_of_mem_function hz]
  · intro a ha
    rw [domain_eq_of_mem_function hcf] at ha
    obtain ⟨i, hi, rfl⟩ := (S.mem_check_iff γ a).mp ha
    obtain ⟨x, hx, hqx⟩ := hdec i hi
    have hfx : f ‘ i = x := value_eq_of_kpair_mem ((hgraph i x).mpr ⟨hi, hx, hqx⟩)
    rw [S.check_value (by rw [domain_eq_of_mem_function hf]; exact hi), hfx]
    exact ((S.checkedFunctionValue_truth τ i x).mp ⟨q, hqG, hqx⟩).2.symm

end ForcingContext
end ZFVP
