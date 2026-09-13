import ZFVP.ModelTheory.WoodinSparseCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)

include hΩ hAC hθ in
theorem woodinSparsePrefixCode_sparse {i p : V} (hi : i ∈ θ)
    (hp : p ∈ (forcingCodeP (woodinSparsePrefixCode θ)) ‘ i) :
    IsSparseFunctionOn (succ (woodinSourceIndex i)) p := by
  simp only [woodinSparsePrefixCode, forcingRecodedCode, forcingCodeP_code] at hp
  exact woodinSparseHistory_sparse (fun i hi ↦ woodinSparseRecodingRec_correct hΩ hAC i (hθ i hi)) hi hp

include hΩ hAC hθ in
theorem woodinSparsePrefixCode_top {i : V} (hi : i ∈ θ) :
    (forcingCodet (woodinSparsePrefixCode θ)) ‘ i = ∅ := by
  simp only [woodinSparsePrefixCode, forcingRecodedCode, forcingCodet_code]
  exact woodinSparseHistory_top hΩ hAC hθ
    (fun i hi ↦ woodinSparseRecodingRec_correct hΩ hAC i (hθ i hi)) hi

include hΩ hAC hθ in
theorem woodinSparsePrefixCode_projection {i j p : V} (hi : i ∈ θ) (hj : j ∈ θ)
    (hij : i ⊆ j) (hp : p ∈ (forcingCodeP (woodinSparsePrefixCode θ)) ‘ j) :
    ((forcingCodeπ (woodinSparsePrefixCode θ)) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)) := by
  simp only [woodinSparsePrefixCode, forcingRecodedCode, forcingCodeP_code] at hp
  simp only [woodinSparsePrefixCode, forcingRecodedCode, forcingCodeπ_code]
  exact woodinSparseHistory_projection hΩ hAC hθ
    (fun i hi ↦ woodinSparseRecodingRec_correct hΩ hAC i (hθ i hi)) hi hj hij hp

include hΩ hAC hθ in
theorem woodinSparsePrefixCode_section {i j p : V} (hi : i ∈ θ) (hj : j ∈ θ)
    (hij : i ⊆ j) (hp : p ∈ (forcingCodeP (woodinSparsePrefixCode θ)) ‘ i) :
    ((forcingCodeE (woodinSparsePrefixCode θ)) ‘ ⟨i, j⟩ₖ) ‘ p = p := by
  simp only [woodinSparsePrefixCode, forcingRecodedCode, forcingCodeP_code] at hp
  simp only [woodinSparsePrefixCode, forcingRecodedCode, forcingCodeE_code]
  exact woodinSparseHistory_section hΩ hAC hθ
    (fun i hi ↦ woodinSparseRecodingRec_correct hΩ hAC i (hθ i hi)) hi hj hij hp

include hΩ hAC hθ in
theorem woodinSparsePrefixCode_carrier_mono {i j : V} (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j) :
    (forcingCodeP (woodinSparsePrefixCode θ)) ‘ i ⊆ (forcingCodeP (woodinSparsePrefixCode θ)) ‘ j := by
  intro p hp
  have he := (woodinSparsePrefixCode_valid hΩ hAC hθ).system.split.secMaps i hi j hj hij p hp
  rwa [woodinSparsePrefixCode_section hΩ hAC hθ hi hj hij hp] at he

end ZFVP
