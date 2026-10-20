module

public import CCDN.GaloisComponentDegree
public import CCDN.GaloisComponentPoints
public import CCDN.ConjugatePrimeGridBound

/-! The positive-dimensional affine statements of CCDN 4.1.3 and 4.1.4.
Not being defined over the base field means that no base-field ideal extends
to the given ideal. The moving automorphism, geometric component and its
degree are all constructed in the proof. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem non_rational_prime_count_le_box
    {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K] [IsGalois ℚ K]
    {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (hundef : ¬ ∃ J : Ideal (CoordinatePolynomial n),
      J.map (map (algebraMap ℚ K)) = I)
    {B : ℝ} (hB : 0 ≤ B) :
    (count (rationalIdealZeroLocusOver I) B : ℝ) ≤
      (d : ℝ) ^ 2 * (2 * B + 1) ^ m := by
  obtain ⟨γ, hγ⟩ := exists_galois_moving_polynomial_ideal ℚ K I
    (fun h => hundef ⟨I.comap (map (algebraMap ℚ K)), h⟩)
  apply conjugate_prime_count_le_box I d hdim hdegree γ
  · have he : (mapEquiv (Fin n) γ.toRingEquiv :
        MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K) =
        map γ.toRingHom := by
      apply RingHom.ext
      intro f
      change mapEquiv (Fin n) γ.toRingEquiv f = map γ.toRingHom f
      simp only [mapEquiv_apply, RingEquiv.toRingHom_eq_coe]
    rw [← Ideal.map_coe, he]
    exact hγ
  · exact hB

/-- Every positive-dimensional rational prime variety that becomes nonprime
over an algebraic closure satisfies the exact quadratic-degree box bound. -/
theorem nonabsolute_variety_count_le_box
    {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K] [IsGalois ℚ K]
    {n m : ℕ} (I : Ideal (CoordinatePolynomial n)) [I.IsPrime]
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (hred : ¬ (I.map (map (algebraMap ℚ K))).IsPrime)
    {B : ℝ} (hB : 0 ≤ B) :
    (count (idealZeroLocus I) B : ℝ) ≤
      (d : ℝ) ^ 2 * (2 * B + 1) ^ m := by
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes
    (scalar_extension_ideal_ne_top (K := K) I (Ideal.IsPrime.ne_top ‹I.IsPrime›))
  let : P.IsPrime := hP.isPrime
  obtain ⟨e, _, hed, hedim, hedegree⟩ :=
    algebraic_component_degree_le ℚ K I d hdim hdegree P hP
  have hsubset : idealZeroLocus I ⊆ rationalIdealZeroLocusOver P := by
    intro x hx
    exact galois_base_point_on_every_component ℚ K I P hP x hx
  have hcount : (count (idealZeroLocus I) B : ℝ) ≤
      count (rationalIdealZeroLocusOver P) B := by
    exact_mod_cast count_mono hsubset le_rfl
  have hh := non_rational_prime_count_le_box P e hedim hedegree
    (galois_component_not_defined_over_base ℚ K I hred P hP) hB
  apply (hcount.trans hh).trans
  gcongr

end
end CCDN
