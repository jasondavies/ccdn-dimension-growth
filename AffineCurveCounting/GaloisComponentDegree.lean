module

public import AffineCurveCounting.AlgebraicHilbertDimension
public import AffineCurveCounting.GaloisStableIdealDescent
public import AffineCurveCounting.IdealScalarDescent
public import AffineCurveCounting.PrincipalSectionGridBound

/-! Actual components after algebraic coefficient extension retain the
source dimension and have degree at most its degree. If an extended prime
ideal is not prime, every minimal component is moved by a Galois automorphism. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem scalar_extension_ideal_ne_top
    {k K : Type*} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) (hI : I ≠ ⊤) :
    I.map (map (algebraMap k K)) ≠ ⊤ := by
  intro h
  apply hI
  apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
  apply (mem_ideal_scalar_extension_iff (L := K) I 1).mp
  rw [h]
  trivial

theorem algebraic_component_degree_le
    (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime]
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial)
    (P : Ideal (MvPolynomial (Fin n) K))
    (hP : P ∈ (I.map (map (algebraMap k K))).minimalPrimes) :
    ∃ e : ℕ, 0 < e ∧ e ≤ d ∧
      (filteredHilbertPolynomial P).natDegree = m ∧
      (filteredHilbertPolynomial P).leadingCoeff = (e : ℚ) / m.factorial := by
  let : P.IsPrime := hP.isPrime
  have hPdim := (algebraic_polynomial_minimalPrime_dimension k K (Fin n) I P hP).trans hdim
  obtain ⟨e, he, _, helc⟩ := filteredHilbertPolynomial_positive_multiplicity P hP.isPrime.ne_top
  rw [hPdim] at helc
  refine ⟨e, he, ?_, hPdim, helc⟩
  have hle := filteredHilbertPolynomial_leadingCoeff_le P
    (I.map (map (algebraMap k K))) hP.isPrime.ne_top
    (scalar_extension_ideal_ne_top I (Ideal.IsPrime.ne_top ‹I.IsPrime›))
    (by simpa only [filteredHilbertPolynomial_scalar_extension, hdim] using hPdim)
    (filteredCoordinateSpace_finrank_antitone_ideal _ _ hP.le)
  rw [filteredHilbertPolynomial_scalar_extension, helc, hdegree] at hle
  have hfac : (0 : ℚ) < m.factorial := by positivity
  exact_mod_cast (div_le_div_iff_of_pos_right hfac).mp hle

theorem galois_component_not_defined_over_base
    (k K : Type*) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime]
    (hred : ¬ (I.map (map (algebraMap k K))).IsPrime)
    (P : Ideal (MvPolynomial (Fin n) K))
    (hP : P ∈ (I.map (map (algebraMap k K))).minimalPrimes) :
    ¬ ∃ J : Ideal (MvPolynomial (Fin n) k),
      J.map (map (algebraMap k K)) = P := by
  rintro ⟨J, hJ⟩
  have hcontract : P.comap (map (algebraMap k K)) = J := by
    rw [← hJ]
    ext f
    exact mem_ideal_scalar_extension_iff J f
  have hbase := algebraic_polynomial_minimalPrime_under k K (Fin n) I P hP
  have he : J = I := hcontract.symm.trans hbase
  exact hred ((he ▸ hJ).symm ▸ hP.isPrime)

end
end AffineCurveCounting
