import ZFVP.ModelTheory.SymmetricModelOrdinals
import ZFVP.SetTheory.OrdinalFiberBounds
import ZFVP.SetTheory.ProperClassRanks
import ZFVP.SetTheory.LeastRankWitnesses
import ZFVP.Syntax.RankedFormula

/-! Unbounded value-rank witnesses below one condition, with least-name-rank witness sets. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricContext

def RankWitness (S : SymmetricContext V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (b p α τ : V) : Prop := IsOrdinal α ∧ IsHereditarilySymmetricName S.P S.Γ S.F τ ∧
      p ∈ symmetricForcingFormula S.P S.R S.Γ S.F (rankedFormula φ)
        (assignmentPrepend (n + 1 : ℕ) (assignmentPrepend (n : V) b τ) (checkName S.one α))

instance rankWitness_definable (S : SymmetricContext V) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (b : V) : ℒₛₑₜ-relation₃[V] (S.RankWitness φ b) := by
  unfold RankWitness
  definability

theorem rankWitness_truth (S : SymmetricContext V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → S.Name) (α : V) [IsOrdinal α] (σ : S.Name) :
    (S.check α = rank (S.ofName σ) ∧ φ.Evalb (S.ofName σ :> fun i ↦ S.ofName (v i))) ↔
      ∃ p ∈ S.G, S.RankWitness φ (standardTuple (fun i ↦ (v i).val)) p α σ.val := by
  let ρ : S.Name := ⟨checkName S.one α, hereditarilySymmetric_checkName S.poset S.group S.normal S.top α⟩
  have ht := S.formula_truth (rankedFormula φ) (ρ :> σ :> v)
  rw [S.ofName_cons, S.ofName_cons, rankedFormula_eval] at ht
  constructor
  · intro hh
    obtain ⟨p, hpG, hpF⟩ := ht.mp hh
    exact ⟨p, hpG, inferInstance, σ.property, hpF⟩
  · rintro ⟨p, hpG, _, _, hpF⟩
    exact ht.mpr ⟨p, hpG, hpF⟩

theorem properClass_rankWitnesses_unbounded (S : SymmetricContext V) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (v : Fin n → S.Name)
    (hp : IsProperClass (fun x : S.Model ↦ φ.Evalb (x :> fun i ↦ S.ofName (v i)))) :
    ∀ δ : V, IsOrdinal δ → ∃ p ∈ S.G, ∃ α,
      (∃ τ, S.RankWitness φ (standardTuple (fun i ↦ (v i).val)) p α τ) ∧ δ ∈ α := by
  intro δ hδ
  have : IsOrdinal δ := hδ
  obtain ⟨x, hx, hr⟩ := hp.rank_unbounded (S.check δ)
  obtain ⟨α, hα, he⟩ := S.ordinal_eq_check (rank x)
  have : IsOrdinal α := hα
  obtain ⟨σ, rfl⟩ := S.ofName_surjective x
  obtain ⟨p, hpG, hpW⟩ := (S.rankWitness_truth φ v α σ).mp ⟨he.symm, hx⟩
  refine ⟨p, hpG, α, ⟨σ.val, hpW⟩, ?_⟩
  exact (S.check_mem_iff δ α).mp (he ▸ hr)

theorem exists_condition_unbounded_rankWitnesses (S : SymmetricContext V) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (v : Fin n → S.Name)
    (hp : IsProperClass (fun x : S.Model ↦ φ.Evalb (x :> fun i ↦ S.ofName (v i)))) :
    ∃ q ∈ S.G, ∀ δ : V, IsOrdinal δ → ∃ α,
      (∃ τ, S.RankWitness φ (standardTuple (fun i ↦ (v i).val)) q α τ) ∧ δ ∈ α :=
  exists_unbounded_ordinal_fiber S.P S.G S.generic.1.1
    (fun p α ↦ ∃ τ, S.RankWitness φ (standardTuple (fun i ↦ (v i).val)) p α τ)
    (by definability) (fun _ _ _ h ↦ by obtain ⟨τ, hτ⟩ := h; exact hτ.1)
    (S.properClass_rankWitnesses_unbounded φ v hp)

theorem leastNameRankWitnessSet_existsUnique (S : SymmetricContext V) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (b q α : V) (hex : ∃ τ, S.RankWitness φ b q α τ) :
    ∃! X : V, IsLeastRankWitnessSet (S.RankWitness φ b q) α X :=
  leastRankWitnessSet_existsUnique (S.RankWitness φ b q) (by definability) α hex

theorem leastNameRankWitnessSet_hs (S : SymmetricContext V) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) {b q α X τ : V}
    (hX : IsLeastRankWitnessSet (S.RankWitness φ b q) α X) (hτ : τ ∈ X) :
    IsHereditarilySymmetricName S.P S.Γ S.F τ := (hX.witness hτ).2.1

end SymmetricContext
end ZFVP
