import ZFVP.ModelTheory.ForcingIsomorphismGenericContext
import ZFVP.ModelTheory.CodedEmbeddingTransport
import ZFVP.SetTheory.UniformRank
import ZFVP.SetTheory.MembershipIso
import ZFVP.ModelTheory.EndExtensionCriticalPoint

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingContext.exists_internalLift_of_checkPreservingEquiv
    (A B : ForcingContext V) (e : A.Model ≃ B.Model)
    (hem : ∀ x y, e x ∈ e y ↔ x ∈ y)
    (hec : ∀ x : V, e (A.check x) = B.check x) {Ω γ ξ : V}
    (h : ∃ g ∈ hierarchy (A.check Ω),
      IsCodedMembershipEmbedding (hierarchy (A.check γ)) (hierarchy (A.check ξ)) g) :
    ∃ g ∈ hierarchy (B.check Ω),
      IsCodedMembershipEmbedding (hierarchy (B.check γ)) (hierarchy (B.check ξ)) g := by
  let j := ElementaryMap.ofMembershipIso e hem
  have hh (x : V) : j (hierarchy (A.check x)) = hierarchy (B.check x) := by
    rw [j.map_hierarchy]
    exact congrArg hierarchy (hec x)
  obtain ⟨g, hg, hjg⟩ := h
  refine ⟨j g, ?_, ?_⟩
  · rw [← hh Ω]
    exact (hem g (hierarchy (A.check Ω))).mpr hg
  · rw [← hh γ, ← hh ξ]
    exact (j.map_codedMembershipEmbedding_iff _ _ _).mpr hjg

theorem ForcingContext.exists_internalLift_of_checkPreservingEquiv_symm
    (A B : ForcingContext V) (e : A.Model ≃ B.Model)
    (hem : ∀ x y, e x ∈ e y ↔ x ∈ y)
    (hec : ∀ x : V, e (A.check x) = B.check x) {Ω γ ξ : V}
    (h : ∃ g ∈ hierarchy (B.check Ω),
      IsCodedMembershipEmbedding (hierarchy (B.check γ)) (hierarchy (B.check ξ)) g) :
    ∃ g ∈ hierarchy (A.check Ω),
      IsCodedMembershipEmbedding (hierarchy (A.check γ)) (hierarchy (A.check ξ)) g := by
  apply B.exists_internalLift_of_checkPreservingEquiv A e.symm ?_ ?_ h
  · intro x y
    simpa only [Equiv.apply_symm_apply] using (hem (e.symm x) (e.symm y)).symm
  · intro x
    exact (Equiv.symm_apply_eq e).mpr (hec x).symm

theorem ForcingContext.exists_criticalLift_of_checkPreservingEquiv
    (A B : ForcingContext V) (e : A.Model ≃ B.Model)
    (hem : ∀ x y, e x ∈ e y ↔ x ∈ y)
    (hec : ∀ x : V, e (A.check x) = B.check x) {Ω γ ξ κ f : V} [IsOrdinal γ]
    (h : ∃ g ∈ hierarchy (A.check Ω),
      IsCodedMembershipEmbedding (hierarchy (A.check γ)) (hierarchy (A.check ξ)) g ∧
      IsCriticalPoint (hierarchy (A.check γ)) g (A.check κ) ∧
      ∀ x ∈ hierarchy γ, g ‘ (A.check x) = A.check (f ‘ x)) :
    ∃ g ∈ hierarchy (B.check Ω),
      IsCodedMembershipEmbedding (hierarchy (B.check γ)) (hierarchy (B.check ξ)) g ∧
      IsCriticalPoint (hierarchy (B.check γ)) g (B.check κ) ∧
      ∀ x ∈ hierarchy γ, g ‘ (B.check x) = B.check (f ‘ x) := by
  let j := ElementaryMap.ofMembershipIso e hem
  let k : MembershipEndExtension A.Model B.Model := ⟨e, e.injective, hem, by
    intro x y hy
    refine ⟨e.symm y, ?_, (e.apply_symm_apply y).symm⟩
    exact (hem _ _).mp (by simpa only [Equiv.apply_symm_apply] using hy)⟩
  have hh (x : V) : j (hierarchy (A.check x)) = hierarchy (B.check x) := by
    rw [j.map_hierarchy]
    exact congrArg hierarchy (hec x)
  let := A.check_ordinal γ
  let := hierarchy_transitive (A.check γ)
  obtain ⟨g, hg, hge, hgc, hgv⟩ := h
  refine ⟨j g, ?_, ?_, ?_, ?_⟩
  · rw [← hh Ω]
    exact (hem g (hierarchy (A.check Ω))).mpr hg
  · rw [← hh γ, ← hh ξ]
    exact (j.map_codedMembershipEmbedding_iff _ _ _).mpr hge
  · have hc := k.criticalPoint_map hgc
    change IsCriticalPoint (j (hierarchy (A.check γ))) (j g) (e (A.check κ)) at hc
    rwa [hh γ, hec κ] at hc
  · intro x hx
    have hv := congrArg k (hgv x hx)
    rw [k.map_value_total] at hv
    change (j g) ‘ (e (A.check x)) = e (A.check (f ‘ x)) at hv
    rwa [hec x, hec (f ‘ x)] at hv

theorem ForcingContext.exists_criticalLift_of_checkPreservingEquiv_symm
    (A B : ForcingContext V) (e : A.Model ≃ B.Model)
    (hem : ∀ x y, e x ∈ e y ↔ x ∈ y)
    (hec : ∀ x : V, e (A.check x) = B.check x) {Ω γ ξ κ f : V} [IsOrdinal γ]
    (h : ∃ g ∈ hierarchy (B.check Ω),
      IsCodedMembershipEmbedding (hierarchy (B.check γ)) (hierarchy (B.check ξ)) g ∧
      IsCriticalPoint (hierarchy (B.check γ)) g (B.check κ) ∧
      ∀ x ∈ hierarchy γ, g ‘ (B.check x) = B.check (f ‘ x)) :
    ∃ g ∈ hierarchy (A.check Ω),
      IsCodedMembershipEmbedding (hierarchy (A.check γ)) (hierarchy (A.check ξ)) g ∧
      IsCriticalPoint (hierarchy (A.check γ)) g (A.check κ) ∧
      ∀ x ∈ hierarchy γ, g ‘ (A.check x) = A.check (f ‘ x) := by
  apply B.exists_criticalLift_of_checkPreservingEquiv A e.symm ?_ ?_ h
  · intro x y
    simpa only [Equiv.apply_symm_apply] using (hem (e.symm x) (e.symm y)).symm
  · intro x
    exact (Equiv.symm_apply_eq e).mpr (hec x).symm

end ZFVP


