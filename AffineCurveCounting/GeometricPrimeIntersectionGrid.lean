module

public import AffineCurveCounting.IdealScalarDescent
public import AffineCurveCounting.ConjugatePrimeGridBound

/-! Sharp intersection bounds for geometrically prime ideals over a
characteristic-zero field, and the fixed-field conjugate specialization. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem distinct_geometrically_prime_grid_card_le
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    {n m : ℕ} (I J : Ideal (MvPolynomial (Fin n) K))
    [I.IsPrime] [J.IsPrime]
    [(I.map (map (algebraMap K L))).IsPrime]
    [(J.map (map (algebraMap K L))).IsPrime]
    (d e : ℕ)
    (hdimI : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hdimJ : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegreeI : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (hdegreeJ : (filteredHilbertPolynomial J).leadingCoeff = (e : ℚ) / (m + 1).factorial)
    (hne : J ≠ I)
    (S : Finset K) (s : Finset (Fin n → K))
    (hzeroI : ∀ x ∈ s, ∀ f ∈ I, eval x f = 0)
    (hzeroJ : ∀ x ∈ s, ∀ f ∈ J, eval x f = 0)
    (hgrid : ∀ x ∈ s, ∀ i, x i ∈ S) :
    s.card ≤ d * e * S.card ^ m := by
  have hnot := prime_ideal_not_le_of_same_positive_dimension J I hdimJ hdimI hne
  obtain ⟨f, hfJ, hfd, hfI⟩ := exists_low_degree_ideal_separator_of_geometrically_prime
    (L := L) J I e (by simpa only [hdimJ] using hdegreeJ) hnot
  have hh := principal_section_grid_card_le I d hdimI hdegreeI f hfI S s
    hzeroI (fun x hx => hzeroJ x hx f hfJ) hgrid
  exact hh.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left d hfd))

theorem conjugate_geometrically_prime_grid_card_le
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (e : K ≃+* K)
    [(I.map (map (algebraMap K L))).IsPrime]
    [((I.map (mapEquiv (Fin n) e)).map (map (algebraMap K L))).IsPrime]
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (hne : I.map (mapEquiv (Fin n) e) ≠ I)
    (S : Finset K) (s : Finset (Fin n → K))
    (hzero : ∀ x ∈ s, ∀ f ∈ I, eval x f = 0)
    (hfixed : ∀ x ∈ s, ∀ i, e (x i) = x i)
    (hgrid : ∀ x ∈ s, ∀ i, x i ∈ S) :
    s.card ≤ d ^ 2 * S.card ^ m := by
  let J := I.map (mapEquiv (Fin n) e)
  let : J.IsPrime := Ideal.map_isPrime_of_equiv _
  have hzJ (x) (hx : x ∈ s) : ∀ f ∈ J, eval x f = 0 := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective
      (mapEquiv (Fin n) e) (mapEquiv (Fin n) e).surjective).mp hf
    rw [eval_coefficientEquiv_of_fixed e x (hfixed x hx), hzero x hx g hg, map_zero]
  simpa only [pow_two] using distinct_geometrically_prime_grid_card_le (L := L) I J d d
    hdim (by simpa only [J, filteredHilbertPolynomial_coefficientEquiv] using hdim)
    hdegree (by simpa only [J, filteredHilbertPolynomial_coefficientEquiv] using hdegree)
    hne S s hzero hzJ hgrid

end
end AffineCurveCounting
