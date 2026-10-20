module

public import AffineCurveCounting.HilbertTranscendenceBasis
public import AffineCurveCounting.HilbertLinearCoordinates

/-! Integral linear projections preserve actual Hilbert dimension and
do not increase its multiplicity. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem integral_projection_hilbert_dimension_eq
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]
    [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (ψ : MvPolynomial σ K →ₐ[K] (MvPolynomial τ K ⧸ I))
    (hint : ψ.IsIntegral) :
    (filteredHilbertPolynomial (RingHom.ker ψ)).natDegree =
      (filteredHilbertPolynomial I).natDegree := by
  let : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ.toRingHom
  exact integral_embedding_hilbert_dimension_eq (RingHom.ker ψ) I
    (Ideal.kerLiftAlg ψ) (Ideal.kerLiftAlg_injective ψ) hint.kerLift

theorem integral_linear_projection_multiplicity
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]
    [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (hint : (projectionCoordinateMap I a).IsIntegral) (d : ℕ)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial) :
    (filteredHilbertPolynomial (RingHom.ker (projectionCoordinateMap I a))).natDegree =
        (filteredHilbertPolynomial I).natDegree ∧
      ∃ e : ℕ, 0 < e ∧ e ≤ d ∧
        (filteredHilbertPolynomial (RingHom.ker (projectionCoordinateMap I a))).leadingCoeff =
          (e : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial := by
  let J := RingHom.ker (projectionCoordinateMap I a)
  have hJ : J ≠ ⊤ := RingHom.ker_ne_top _
  have hI : I ≠ ⊤ := Ideal.IsPrime.ne_top ‹I.IsPrime›
  have hdim := integral_projection_hilbert_dimension_eq I _ hint
  obtain ⟨e, he, _, hlc⟩ := filteredHilbertPolynomial_positive_multiplicity J hJ
  have hle := filteredHilbertPolynomial_leadingCoeff_le J I hJ hI hdim
    (fun N => linear_projection_filtered_finrank_le I a ha N)
  rw [hdim] at hlc
  refine ⟨hdim, e, he, ?_, hlc⟩
  rw [hlc, hdegree] at hle
  exact_mod_cast (div_le_div_iff_of_pos_right
    (by positivity : (0 : ℚ) < (filteredHilbertPolynomial I).natDegree.factorial)).mp hle

end
end AffineCurveCounting
