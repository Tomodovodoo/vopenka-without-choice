import ZFVP.ModelTheory.ForcingModelPairs
import ZFVP.SetTheory.NameEvaluationGraph

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

noncomputable def evaluationGraph (S : ForcingContext V) (C : V) (hC : ∀ σ ∈ C, IsForcingName S.P σ) : S.Model :=
  S.ofName ⟨nameEvaluationGraph S.one C, nameEvaluationGraph_isName S.top.1 hC⟩

theorem mem_evaluationGraph_iff (S : ForcingContext V) (C : V) (hC : ∀ σ ∈ C, IsForcingName S.P σ)
    (x : S.Model) : x ∈ S.evaluationGraph C hC ↔
      ∃ σ, ∃ hσ : σ ∈ C, x = ⟨S.check σ, S.ofName ⟨σ, hC σ hσ⟩⟩ₖ := by
  obtain ⟨ξ, rfl⟩ := forcingQuotientMk_surjective S.P S.R S.G S.order S.generic.1 x
  constructor
  · intro hx
    obtain ⟨ν, p, _, hp, he⟩ := (forcingQuotientMk_mem_subname_iff S.P S.R S.G S.order S.generic _ _).mp hx
    obtain ⟨σ, hσ, hpair⟩ := (mem_nameEvaluationGraph_iff _ _ _).mp hp
    let σ' : ForcingName S.P := ⟨σ, hC σ hσ⟩
    let checkσ : ForcingName S.P := ⟨checkName S.one σ, checkName_isName S.top.1 σ⟩
    have hν : ν = (⟨orderedPairName S.one checkσ.val σ'.val,
        orderedPairName_isName S.top.1 checkσ.property σ'.property⟩ : ForcingName S.P) :=
      Subtype.ext (kpair_iff.mp hpair).1
    refine ⟨σ, hσ, ?_⟩
    exact he.trans ((congrArg S.ofName hν).trans (S.of_orderedPair checkσ σ'))
  · rintro ⟨σ, hσ, he⟩
    let σ' : ForcingName S.P := ⟨σ, hC σ hσ⟩
    let checkσ : ForcingName S.P := ⟨checkName S.one σ, checkName_isName S.top.1 σ⟩
    let ν : ForcingName S.P := ⟨orderedPairName S.one checkσ.val σ'.val,
      orderedPairName_isName S.top.1 checkσ.property σ'.property⟩
    exact (forcingQuotientMk_mem_subname_iff S.P S.R S.G S.order S.generic _ _).mpr
      ⟨ν, S.one, externalForcingFilter_top S.generic.1 S.top,
        (mem_nameEvaluationGraph_iff _ _ _).mpr ⟨σ, hσ, rfl⟩,
        he.trans (S.of_orderedPair checkσ σ').symm⟩

theorem pair_mem_evaluationGraph_iff (S : ForcingContext V) (C : V) (hC : ∀ σ ∈ C, IsForcingName S.P σ)
    (x y : S.Model) : ⟨x, y⟩ₖ ∈ S.evaluationGraph C hC ↔
      ∃ σ, ∃ hσ : σ ∈ C, x = S.check σ ∧ y = S.ofName ⟨σ, hC σ hσ⟩ := by
  rw [S.mem_evaluationGraph_iff]
  simp only [kpair_iff]

theorem evaluationGraph_mem_function (S : ForcingContext V) (C : V) (hC : ∀ σ ∈ C, IsForcingName S.P σ) :
    S.evaluationGraph C hC ∈ range (S.evaluationGraph C hC) ^ S.check C := by
  apply mem_function.intro
  · intro z hz
    obtain ⟨σ, hσ, rfl⟩ := (S.mem_evaluationGraph_iff C hC z).mp hz
    exact kpair_mem_iff.mpr ⟨(S.check_mem_iff σ C).mpr hσ, mem_range_of_kpair_mem hz⟩
  · intro x hx
    obtain ⟨σ, hσ, rfl⟩ := (S.mem_check_iff C x).mp hx
    refine ⟨S.ofName ⟨σ, hC σ hσ⟩, (S.pair_mem_evaluationGraph_iff C hC _ _).mpr ⟨σ, hσ, rfl, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨τ, hτ, he, rfl⟩ := (S.pair_mem_evaluationGraph_iff C hC _ _).mp hy
    exact congrArg S.ofName (Subtype.ext ((S.check_eq_iff _ _).mp he).symm)

instance evaluationGraph_isFunction (S : ForcingContext V) (C : V) (hC : ∀ σ ∈ C, IsForcingName S.P σ) :
    IsFunction (S.evaluationGraph C hC) :=
  ⟨S.check C, range (S.evaluationGraph C hC), S.evaluationGraph_mem_function C hC⟩

theorem evaluationGraph_domain (S : ForcingContext V) (C : V) (hC : ∀ σ ∈ C, IsForcingName S.P σ) :
    domain (S.evaluationGraph C hC) = S.check C := domain_eq_of_mem_function (S.evaluationGraph_mem_function C hC)

theorem evaluationGraph_value (S : ForcingContext V) (C : V) (hC : ∀ σ ∈ C, IsForcingName S.P σ)
    (σ : V) (hσ : σ ∈ C) : (S.evaluationGraph C hC) ‘ (S.check σ) = S.ofName ⟨σ, hC σ hσ⟩ :=
  value_eq_of_kpair_mem ((S.pair_mem_evaluationGraph_iff C hC _ _).mpr ⟨σ, hσ, rfl, rfl⟩)

end ForcingContext
end ZFVP
