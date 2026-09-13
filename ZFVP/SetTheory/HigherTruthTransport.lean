import ZFVP.SetTheory.CorrectRankStages

/-! Elementary transport of the fixed higher-truth and correctness dictionaries. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V W : Type*} [SetStructure V] [SetStructure W] [Nonempty V] [Nonempty W]
  [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ElementaryMap

theorem map_correctDomain_iff (j : ElementaryMap V W) (k : ℕ) (A : V) :
    CorrectDomain k A ↔ CorrectDomain k (j A) :=
  j.map_defined (correctDomainFormula k) (fun v ↦ CorrectDomain k (v 0))
    (fun v ↦ CorrectDomain k (v 0)) ![A]

theorem map_correctRankStage_iff (j : ElementaryMap V W) (k : ℕ) (α : V) :
    IsCorrectRankStage k α ↔ IsCorrectRankStage k (j α) :=
  j.map_defined (correctRankStageFormula k) (fun v ↦ IsCorrectRankStage k (v 0))
    (fun v ↦ IsCorrectRankStage k (v 0)) ![α]

theorem map_domainSigmaTruth_iff (j : ElementaryMap V W) (k : ℕ) (n φ b : V) :
    DomainSigmaTruth k n φ b ↔ DomainSigmaTruth k (j n) (j φ) (j b) :=
  j.map_defined (domainSigmaTruthFormula (correctDomainFormula k)) (fun v ↦ DomainSigmaTruth k (v 0) (v 1) (v 2))
    (fun v ↦ DomainSigmaTruth k (v 0) (v 1) (v 2)) ![n, φ, b]

theorem map_domainPiTruth_iff (j : ElementaryMap V W) (k : ℕ) (n φ b : V) :
    DomainPiTruth k n φ b ↔ DomainPiTruth k (j n) (j φ) (j b) :=
  j.map_defined (domainPiTruthFormula (correctDomainFormula k)) (fun v ↦ DomainPiTruth k (v 0) (v 1) (v 2))
    (fun v ↦ DomainPiTruth k (v 0) (v 1) (v 2)) ![n, φ, b]

end ElementaryMap
end ZFVP
