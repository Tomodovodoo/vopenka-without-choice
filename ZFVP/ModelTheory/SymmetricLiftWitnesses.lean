import ZFVP.ModelTheory.SymmetricLift
import ZFVP.ModelTheory.SymmetricRankWitnesses

/-! A moved pair of full witness sets gives distinct class members related by the symmetric lift. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricLiftData

variable {S : SymmetricContext V} {U W f : V}
variable [IsTransitive U] [IsTransitive W]
variable [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
variable [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem distinct_witness_values (L : SymmetricLiftData S U W f)
    {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → S.Name)
    {q α β X Y : V} (hq : q ∈ S.G) (hne : α ≠ β)
    (hX : IsLeastRankWitnessSet (S.RankWitness φ (standardTuple (fun i ↦ (v i).val)) q) α X)
    (hY : IsLeastRankWitnessSet (S.RankWitness φ (standardTuple (fun i ↦ (v i).val)) q) β Y)
    (hXU : X ∈ U) (hXY : f ‘ X = Y) :
    ∃ σ : S.Name, ∃ hσ : σ.val ∈ U,
      S.ofName σ ≠ S.ofName (L.imageName σ hσ) ∧
      φ.Evalb (S.ofName σ :> fun i ↦ S.ofName (v i)) ∧
      φ.Evalb (S.ofName (L.imageName σ hσ) :> fun i ↦ S.ofName (v i)) := by
  obtain ⟨τ, hτX⟩ := hX.nonempty
  have hτ := hX.witness hτX
  let σ : S.Name := ⟨τ, hτ.2.1⟩
  have hτU : τ ∈ U := (inferInstance : IsTransitive U).mem_trans hτX hXU
  have hfτY : f ‘ τ ∈ Y := by
    rw [← hXY]
    exact (L.embedding.value_mem_iff hτU hXU).mpr hτX
  have hτ' := hY.witness hfτY
  let := hτ.1
  let := hτ'.1
  have hs := (S.rankWitness_truth φ v α σ).mpr ⟨q, hq, hτ⟩
  have ht := (S.rankWitness_truth φ v β (L.imageName σ hτU)).mpr ⟨q, hq, hτ'⟩
  refine ⟨σ, hτU, ?_, hs.2, ht.2⟩
  intro he
  apply hne
  exact (S.check_eq_iff α β).mp (hs.1.trans ((congrArg rank he).trans ht.1.symm))

theorem exists_distinct_witness_graph (L : SymmetricLiftData S U W f)
    {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → S.Name)
    {q α β X Y : V} (hq : q ∈ S.G) (hne : α ≠ β)
    (hX : IsLeastRankWitnessSet (S.RankWitness φ (standardTuple (fun i ↦ (v i).val)) q) α X)
    (hY : IsLeastRankWitnessSet (S.RankWitness φ (standardTuple (fun i ↦ (v i).val)) q) β Y)
    (hXU : X ∈ U) (hXY : f ‘ X = Y) :
    ∃ M N : S.Model, M ≠ N ∧
      φ.Evalb (M :> fun i ↦ S.ofName (v i)) ∧ φ.Evalb (N :> fun i ↦ S.ofName (v i)) ∧
      M ∈ domain L.graph ∧ L.graph ‘ M = N := by
  obtain ⟨σ, hσ, hne, hM, hN⟩ := L.distinct_witness_values φ v hq hne hX hY hXU hXY
  exact ⟨S.ofName σ, S.ofName (L.imageName σ hσ), hne, hM, hN,
    (L.graph_domain _).mpr ⟨σ, hσ, rfl⟩, L.graph_value σ hσ⟩

end SymmetricLiftData
end ZFVP
