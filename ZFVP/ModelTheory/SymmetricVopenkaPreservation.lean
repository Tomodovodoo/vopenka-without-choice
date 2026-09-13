import ZFVP.ModelTheory.SymmetricLiftLanguage
import ZFVP.ModelTheory.SymmetricLiftFixedClosure
import ZFVP.ModelTheory.SymmetricLiftWitnesses
import ZFVP.ModelTheory.SymmetricWitnessEmbedding
import ZFVP.ModelTheory.InternalZFExternal

/-! Full arbitrary-language Vopenka preservation in the symmetric quotient. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricContext

theorem vopenka_class (S : SymmetricContext V)
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → S.Name)
    (language : S.Model)
    (hp : IsProperClass (fun x : S.Model ↦ φ.Evalb (x :> fun i ↦ S.ofName (v i))))
    (hs : ∀ M : S.Model, φ.Evalb (M :> fun i ↦ S.ofName (v i)) → IsStructureCode language M) :
    ∃ M N e : S.Model, M ≠ N ∧
      φ.Evalb (M :> fun i ↦ S.ofName (v i)) ∧ φ.Evalb (N :> fun i ↦ S.ofName (v i)) ∧
      IsCodedElementaryEmbedding language M N e := by
  obtain ⟨ℓ, rfl⟩ := S.ofName_surjective language
  let code := symmetricSystemCode S.P S.R S.Γ S.F
  let ρ := rank ({succ (ω : V), code, standardTuple (fun i ↦ (v i).val), ℓ.val} : V)
  have hcode : code ∈ hierarchy ρ := subset_hierarchy_rank ({succ (ω : V), code, standardTuple (fun i ↦ (v i).val), ℓ.val} : V) code (by simp)
  have hℓ : ℓ.val ∈ hierarchy ρ := subset_hierarchy_rank ({succ (ω : V), code, standardTuple (fun i ↦ (v i).val), ℓ.val} : V) ℓ.val (by simp)
  obtain ⟨q, hq, α, β, X, Y, θ, η, f, hne, hθ, hη, hf, _, hXY, hfix⟩ :=
    S.exists_witnessRank_embedding hVP φ v hp ρ
  have : IsOrdinal θ := hθ.2.2.1
  have : IsOrdinal η := hη.2.2.1
  have := hierarchy_transitive ρ
  have := hierarchy_transitive θ
  have := hierarchy_transitive η
  have hU : IsInternalZFModel (hierarchy θ) := hθ.2.2.2.1.2
  have hW : IsInternalZFModel (hierarchy η) := hη.2.2.2.1.2
  have : Nonempty (SetDomain (hierarchy θ)) := by
    obtain ⟨x, hx⟩ := hU.1.1.nonempty
    exact ⟨⟨x, hx⟩⟩
  have : Nonempty (SetDomain (hierarchy η)) := by
    obtain ⟨x, hx⟩ := hW.1.1.nonempty
    exact ⟨⟨x, hx⟩⟩
  have := hU.models_zf
  have := hW.models_zf
  have hBU : hierarchy ρ ⊆ hierarchy θ := hierarchy_mono (IsOrdinal.toIsTransitive.transitive ρ hθ.bounds.1)
  have hTC : transitiveClosure ({code} : V) ⊆ hierarchy ρ :=
    transitiveClosure_minimal _ _ (by simpa using hcode) (hierarchy_transitive ρ)
  let L := SymmetricLiftData.of_fixedClosure (S := S) hf (hBU code hcode) (fun z hz ↦ hfix z (hTC z hz))
  have hXU : X ∈ hierarchy θ := (mem_hierarchy_iff_rank_mem X θ).mpr hθ.bounds.2.2
  obtain ⟨M, N, hMN, hM, hN, hm, he⟩ := L.exists_distinct_witness_graph φ v hq hne hθ.2.1 hη.2.1 hXU hXY
  refine ⟨M, N, L.graph ↾ (structureDomain M), hMN, hM, hN, ?_⟩
  rw [← he]
  exact L.structure_restriction_elementary_of_nameBound hBU hfix (hs M hM) hm ⟨ℓ, hℓ, rfl⟩

theorem vopenkaInstance (S : SymmetricContext V)
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (φ : SetTheorySemisentence 2) : VopenkaInstance (V := S.Model) φ := by
  intro language a hp hs
  obtain ⟨σ, rfl⟩ := S.ofName_surjective a
  have hv : (fun i ↦ S.ofName (![σ] i)) = ![S.ofName σ] := by
    funext i
    exact Fin.cases rfl (Fin.elim0 ·) i
  have hp' : IsProperClass (fun x : S.Model ↦ φ.Evalb (x :> fun i ↦ S.ofName (![σ] i))) := by
    simpa only [hv] using hp
  have hs' : ∀ M : S.Model, φ.Evalb (M :> fun i ↦ S.ofName (![σ] i)) → IsStructureCode language M := by
    simpa only [hv] using hs
  simpa only [hv] using S.vopenka_class hVP φ ![σ] language hp' hs'

end SymmetricContext
end ZFVP
