module

public import CCDN.ZeroDimensionalGoodCenter
public import CCDN.PolynomialPredicates

/-! Numerical bounds for the row-resultant good-center detector. Its degree
D(2d-1) is strictly smaller than D^2 in positive projective dimension; the
geometric dimension-zero boundary has d=1 and admits zero-one rows. -/

@[expose] public section
namespace CCDN
noncomputable section

lemma sharp_center_detector_degree_lt_square {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) :
    ((m + 1) * d) * (2 * d - 1) < ((m + 1) * d) ^ 2 := by
  have hD : 0 < (m + 1) * d := by positivity
  have hbig : 2 * d ≤ (m + 1) * d := by nlinarith
  have hsmall : 2 * d - 1 < (m + 1) * d := by omega
  nlinarith

lemma sharp_center_detector_degree_le_square {m d : ℕ}
    (hd : 1 ≤ d) (hboundary : 1 ≤ m ∨ d = 1) :
    max 1 (((m + 1) * d) * (2 * d - 1)) ≤ (m + 1) ^ 2 * d ^ 2 := by
  have hD : 1 ≤ (m + 1) * d := by nlinarith
  rw [← mul_pow]
  apply max_le (one_le_pow₀ hD)
  rcases hboundary with hm | rfl
  · exact (sharp_center_detector_degree_lt_square hm hd).le
  · simp only [mul_one, Nat.reduceSub]
    nlinarith

/-- The printed projection-height exponent also covers the empty center. -/
lemma center_projection_source_exponent_all_rows {m n r d : ℕ}
    (hrn : r ≤ n + 1) (hmn : m + 1 ≤ n + 1) (hd : 1 ≤ d) :
    (n + 1) * (2 * r.factorial * ((m + 1) ^ 2 * d ^ 2) ^ r) ≤
      centerProjectionHeightConstant n * d ^ (2 * r ^ 2) := by
  by_cases hr : r = 0
  · subst r
    norm_num only [Nat.factorial_zero, mul_one, pow_zero]
    unfold centerProjectionHeightConstant
    have hf : 1 ≤ (n + 1).factorial := Nat.factorial_pos _
    have hp : 1 ≤ (n + 1) ^ (2 * (n + 1)) := one_le_pow₀ (by omega)
    calc
      (n + 1) * 2 = 2 * (n + 1) * 1 * 1 := by ring
      _ ≤ 2 * (n + 1) * (n + 1).factorial * (n + 1) ^ (2 * (n + 1)) := by gcongr
  · exact center_projection_source_exponent (by omega) hrn hmn hd

lemma geometric_projective_multiplicity_boundary
    {K : Type*} [Field K] [CharZero K] {n m d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial) :
    1 ≤ m ∨ d = 1 := by
  by_cases hm : m = 0
  · right
    subst m
    exact geometric_projective_dimension_zero_multiplicity_one J hJ d hdim
      (by simpa only [Nat.zero_add,Nat.factorial_one,Nat.cast_one,div_one] using hdegree)
  · exact Or.inl (by omega)

lemma geometric_affine_multiplicity_boundary
    {K : Type*} [Field K] [CharZero K] {n m d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
    1 ≤ m ∨ d = 1 := by
  by_cases hm : m = 0
  · right
    rw [hm] at hdim hdegree
    obtain ⟨_,_,hpoly⟩ := zero_dimensional_geometrically_integral_point (L := AlgebraicClosure K) I hdim
    have hh : (1 : ℚ) = d := by
      simpa only [hpoly,Polynomial.leadingCoeff_one,Nat.factorial_zero,Nat.cast_one,div_one] using hdegree
    exact_mod_cast hh.symm
  · exact Or.inl (by omega)

end
end CCDN
