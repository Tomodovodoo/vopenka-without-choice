import ZFVP.ModelTheory.ForcingClosedModelDomain
import ZFVP.SetTheory.CnSigmaClosure
import ZFVP.ModelTheory.ForcingLowRankNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneClosedModelNameFormula : SetTheorySemisentence 4 :=
  “ν P o U. (∀ z ∈ ν, ∃ τ ∈ U, !sigmaOneForcingNameFormula P τ ∧ !boundedKpairFormula z τ o) ∧
    ∀ τ ∈ U, ¬!piOneForcingNameFormula P τ ∨ ∃ z ∈ ν, !boundedKpairFormula z τ o”

theorem sigmaOneClosedModelNameFormula_sigmaOne : IsSigmaFormula 1 sigmaOneClosedModelNameFormula :=
  .and (.boundedAll (.bvar 0) (.boundedExs (.bvar 4)
    (.and (sigmaOneForcingNameFormula_sigmaOne.subst _) (.bounded (boundedKpairFormula_bounded.subst _)))))
    (.boundedAll (.bvar 3) (.or (piOneForcingNameFormula_piOne.subst _).neg
      (.boundedExs (.bvar 1) (.bounded (boundedKpairFormula_bounded.subst _)))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def closedModelName (P one U : V) : V :=
  repl (fun τ ↦ ⟨τ, one⟩ₖ) (by definability) {τ ∈ U ; IsForcingName P τ}

theorem mem_closedModelName (P one U z : V) :
    z ∈ closedModelName P one U ↔ ∃ τ ∈ U, IsForcingName P τ ∧ z = ⟨τ, one⟩ₖ := by
  simp only [closedModelName, repl_spec, mem_sep_iff]
  constructor
  · rintro ⟨τ, ⟨hτ, hn⟩, he⟩
    exact ⟨τ, hτ, hn, he⟩
  · rintro ⟨τ, hτ, hn, he⟩
    exact ⟨τ, ⟨hτ, hn⟩, he⟩

theorem eval_sigmaOneClosedModelNameFormula (ν P one U : V) :
    sigmaOneClosedModelNameFormula.Evalb ![ν, P, one, U] ↔ ν = closedModelName P one U := by
  have he : sigmaOneClosedModelNameFormula.Evalb ![ν, P, one, U] ↔
      (∀ z ∈ ν, ∃ τ ∈ U, IsForcingName P τ ∧ z = ⟨τ, one⟩ₖ) ∧
        ∀ τ ∈ U, IsForcingName P τ → ∃ z ∈ ν, z = ⟨τ, one⟩ₖ := by
    simp [sigmaOneClosedModelNameFormula, ← imp_iff_not_or]
  rw [he]
  constructor
  · intro h
    apply mem_ext
    intro z
    rw [mem_closedModelName]
    constructor
    · exact h.1 z
    · rintro ⟨τ, hτ, hn, rfl⟩
      obtain ⟨z, hz, rfl⟩ := h.2 τ hτ hn
      exact hz
  · rintro rfl
    exact ⟨fun z hz ↦ (mem_closedModelName _ _ _ _).mp hz,
      fun τ hτ hn ↦ ⟨⟨τ, one⟩ₖ, (mem_closedModelName _ _ _ _).mpr ⟨τ, hτ, hn, rfl⟩, rfl⟩⟩

theorem closedModelName_isName {P one U : V} (hone : one ∈ P) :
    IsForcingName P (closedModelName P one U) := by
  apply (forcingName_iff P _).mpr
  intro z hz
  obtain ⟨τ, _, hn, rfl⟩ := (mem_closedModelName _ _ _ _).mp hz
  exact ⟨τ, one, hone, rfl, hn⟩

theorem Cn.closedModelName_mem {γ P one U : V} (hγ : Cn 1 γ)
    (hP : P ∈ hierarchy γ) (hone : one ∈ hierarchy γ) (hU : U ∈ hierarchy γ) :
    closedModelName P one U ∈ hierarchy γ := by
  obtain ⟨ν, hν, he⟩ := hγ.sigmaOne_witness sigmaOneClosedModelNameFormula_sigmaOne ![P, one, U]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hP, hone, hU])
    ⟨closedModelName P one U, (eval_sigmaOneClosedModelNameFormula _ _ _ _).mpr rfl⟩
  exact (eval_sigmaOneClosedModelNameFormula _ _ _ _).mp he ▸ hν

theorem ForcingContext.closedModelName_value (A : ForcingContext V) (U : V) :
    A.ofName ⟨closedModelName A.P A.one U, closedModelName_isName A.top.1⟩ = A.closedModelDomain U := by
  apply mem_ext
  intro z
  rw [A.mem_ofName_iff, A.mem_closedModelDomain]
  constructor
  · rintro ⟨σ, p, _, hp, he⟩
    obtain ⟨τ, hτ, hn, hpair⟩ := (mem_closedModelName _ _ _ _).mp hp
    have hστ := (kpair_iff.mp hpair).1
    exact ⟨σ, hστ.symm ▸ hτ, he⟩
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨τ, A.one, externalForcingFilter_top A.generic.1 A.top,
      (mem_closedModelName _ _ _ _).mpr ⟨τ.val, hτ, τ.property, rfl⟩, rfl⟩

theorem ForcingContext.closedModelDomain_mem_rank (A : ForcingContext V)
    {γ U : V} (hγ : Cn 1 γ) (hP : A.P ∈ hierarchy γ) (hU : U ∈ hierarchy γ) :
    A.closedModelDomain U ∈ hierarchy (A.check γ) := by
  let := hγ.ordinal
  have hone : A.one ∈ hierarchy γ := (hierarchy_transitive γ).mem_trans A.top.1 hP
  rw [← A.closedModelName_value U]
  exact A.ofName_mem_checked_hierarchy _ (hγ.closedModelName_mem hP hone hU)

end ZFVP
