import ZFVP.ModelTheory.SymmetricVopenkaPreservation
import ZFVP.ModelTheory.PiSymmetricWitnessEmbedding

/-! Every positive Pi fragment of Vopenka is preserved by the symmetric quotient. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricContext

theorem pi_vopenka_class (S : SymmetricContext V) {n k : ℕ}
    (hVP : ∀ ψ : SetTheorySemisentence 2, IsPiFormula (k + 1) ψ → VopenkaInstance (V := V) ψ)
    {φ : SetTheorySemisentence (n + 1)} (hφ : IsPiFormula (k + 1) φ) (v : Fin n → S.Name)
    (language : S.Model)
    (hp : IsProperClass (fun x : S.Model ↦ φ.Evalb (x :> fun i ↦ S.ofName (v i))))
    (hs : ∀ M : S.Model, φ.Evalb (M :> fun i ↦ S.ofName (v i)) → IsStructureCode language M) :
    ∃ M N e : S.Model, M ≠ N ∧
      φ.Evalb (M :> fun i ↦ S.ofName (v i)) ∧ φ.Evalb (N :> fun i ↦ S.ofName (v i)) ∧
      IsCodedElementaryEmbedding language M N e := by
  obtain ⟨ℓ, rfl⟩ := S.ofName_surjective language
  let code := symmetricSystemCode S.P S.R S.Γ S.F
  let ρ := rank ({succ (ω : V), code, standardTuple (fun i ↦ (v i).val), ℓ.val} : V)
  have hcode : code ∈ hierarchy ρ := subset_hierarchy_rank
    ({succ (ω : V), code, standardTuple (fun i ↦ (v i).val), ℓ.val} : V) code (by simp)
  have hℓ : ℓ.val ∈ hierarchy ρ := subset_hierarchy_rank
    ({succ (ω : V), code, standardTuple (fun i ↦ (v i).val), ℓ.val} : V) ℓ.val (by simp)
  obtain ⟨q, hq, α, β, X, Y, θ, η, f, hne, hθ, hη, hρθ, _, hX, hY, hXU, _, hf, _, hXY, hfix⟩ :=
    S.exists_pi_witnessRank_embedding hVP hφ v hp ρ
  let := hθ.1
  let := hη.1
  let := hierarchy_transitive ρ
  let := hierarchy_transitive θ
  let := hierarchy_transitive η
  let := rankDomain_nonempty hθ.2.1
  let := rankDomain_nonempty hη.2.1
  let := hθ.models_zf
  let := hη.models_zf
  have hBU : hierarchy ρ ⊆ hierarchy θ := hierarchy_mono (IsOrdinal.toIsTransitive.transitive ρ hρθ)
  have hTC : transitiveClosure ({code} : V) ⊆ hierarchy ρ :=
    transitiveClosure_minimal _ _ (by simpa using hcode) (hierarchy_transitive ρ)
  let L := SymmetricLiftData.of_fixedClosure (S := S) hf (hBU code hcode) (fun z hz ↦ hfix z (hTC z hz))
  obtain ⟨M, N, hMN, hM, hN, hm, he⟩ := L.exists_distinct_witness_graph φ v hq hne hX hY hXU hXY
  refine ⟨M, N, L.graph ↾ (structureDomain M), hMN, hM, hN, ?_⟩
  rw [← he]
  exact L.structure_restriction_elementary_of_nameBound hBU hfix (hs M hM) hm ⟨ℓ, hℓ, rfl⟩

theorem pi_vopenkaInstance (S : SymmetricContext V) {k : ℕ}
    (hVP : ∀ ψ : SetTheorySemisentence 2, IsPiFormula (k + 1) ψ → VopenkaInstance (V := V) ψ)
    {φ : SetTheorySemisentence 2} (hφ : IsPiFormula (k + 1) φ) : VopenkaInstance (V := S.Model) φ := by
  intro language a hp hs
  obtain ⟨σ, rfl⟩ := S.ofName_surjective a
  have hv : (fun i ↦ S.ofName (![σ] i)) = ![S.ofName σ] := by
    funext i
    exact Fin.cases rfl (Fin.elim0 ·) i
  have hp' : IsProperClass (fun x : S.Model ↦ φ.Evalb (x :> fun i ↦ S.ofName (![σ] i))) := by
    simpa only [hv] using hp
  have hs' : ∀ M : S.Model, φ.Evalb (M :> fun i ↦ S.ofName (![σ] i)) → IsStructureCode language M := by
    simpa only [hv] using hs
  simpa only [hv] using S.pi_vopenka_class hVP hφ ![σ] language hp' hs'

theorem pi_vopenka_preservation (S : SymmetricContext V) {k : ℕ} (hk : 0 < k)
    (hVP : ∀ ψ : SetTheorySemisentence 2, IsPiFormula k ψ → VopenkaInstance (V := V) ψ) :
    ∀ φ : SetTheorySemisentence 2, IsPiFormula k φ → VopenkaInstance (V := S.Model) φ := by
  cases k with
  | zero => omega
  | succ k => exact fun _ hφ ↦ S.pi_vopenkaInstance hVP hφ

end SymmetricContext

end ZFVP
