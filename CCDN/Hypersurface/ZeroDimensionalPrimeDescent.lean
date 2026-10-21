/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Hilbert.AffineCurveDegree
public import CCDN.Hypersurface.ConjugatePrimeGridBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.Galois.Basic
import CCDN.Hilbert.AlgebraicHilbertDimension
import CCDN.Hilbert.CoefficientEquiv
import CCDN.Hilbert.PolynomialComparison
import CCDN.Hilbert.ProperSectionHilbert
import CCDN.Hypersurface.GaloisComponentDegree
import CCDN.Hypersurface.GaloisComponentPoints
import CCDN.Hypersurface.GaloisPolynomialPrimes
import CCDN.Hypersurface.GaloisStableIdealDescent

/-! Zero-dimensional affine prime ideals with a rational point descend to
the rational field. This supplies the zero-dimensional boundary cases of
CCDN 4.1.3 and 4.1.4. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem prime_ideal_eq_of_le_of_hilbert_dimension_zero
    {K : Type*} [Field K] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = 0)
    (hJ : J ≠ ⊤) (hIJ : I ≤ J) :
    I = J := by
  by_contra hne
  obtain ⟨f, hfJ, hfI⟩ := IsConcreteLE.not_le_iff_exists.mp
    (not_le_of_gt (lt_of_le_of_ne hIJ hne))
  let S := I ⊔ Ideal.span {f}
  have hSJ : S ≤ J := sup_le hIJ
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfJ))
  have hS : S ≠ ⊤ := fun h => hJ (top_le_iff.mp (h ▸ hSJ))
  let P := (filteredHilbertPolynomial S).comp
    (Polynomial.X + Polynomial.C (f.totalDegree : ℚ))
  have hPlc : P.leadingCoeff = (filteredHilbertPolynomial S).leadingCoeff := by
    exact Polynomial.leadingCoeff_taylor _ _
  have hPpos : 0 < P.leadingCoeff := hPlc.symm ▸
    filteredHilbertPolynomial_leadingCoeff_pos S hS
  have hnon : 0 ≤ (-P).leadingCoeff := by
    apply leadingCoeff_nonneg_of_eventual_nat_eval_nonneg
    obtain ⟨N, hN⟩ := proper_section_hilbert_polynomial_difference I f hfI
    refine ⟨N, fun M hM => ?_⟩
    have hh := hN M hM
    have hconst := Polynomial.eq_C_of_natDegree_eq_zero hdim
    have hdiff : (filteredHilbertPolynomial I).comp
        (Polynomial.X + Polynomial.C (f.totalDegree : ℚ)) -
          filteredHilbertPolynomial I = 0 := by
      rw [hconst, Polynomial.C_comp, sub_self]
    rw [hdiff, Polynomial.eval_zero] at hh
    simpa only [Polynomial.eval_neg, P, S] using neg_nonneg.mpr hh
  rw [Polynomial.leadingCoeff_neg] at hnon
  linarith

/-- A zero-dimensional prime ideal is the ideal of polynomials vanishing at any of its zeros. -/
theorem zero_dimensional_prime_eq_eval_kernel
    {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = 0)
    (x : Fin n → K) (hx : x ∈ idealZeroLocus I) :
    I = RingHom.ker (eval x) :=
  prime_ideal_eq_of_le_of_hilbert_dimension_zero I _ hdim
    (RingHom.ker_ne_top _) hx

private theorem zero_dimensional_prime_with_base_point_descends
    (k K : Type*) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = 0)
    (x : Fin n → k) (hx : algebraMap k K ∘ x ∈ idealZeroLocus I) :
    (I.comap (map (algebraMap k K))).map (map (algebraMap k K)) = I := by
  apply galois_stable_polynomial_ideal_descends k K I
  intro γ
  have hIker := zero_dimensional_prime_eq_eval_kernel I hdim _ hx
  let J := I.map (map γ.toRingHom)
  have hJprime : J.IsPrime := by
    change (I.map (mapEquiv (Fin n) γ.toRingEquiv)).IsPrime
    infer_instance
  have : J.IsPrime := hJprime
  have hJdim : (filteredHilbertPolynomial J).natDegree = 0 := by
    change (filteredHilbertPolynomial
      (I.map (mapEquiv (Fin n) γ.toRingEquiv))).natDegree = 0
    rwa [filteredHilbertPolynomial_coefficientEquiv]
  have hxJ : algebraMap k K ∘ x ∈ idealZeroLocus J := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective
      (map γ.toRingHom) (map_surjective _ γ.surjective)).mp hf
    rw [eval_coefficient_galois_at_base_point, hx g hg, map_zero]
  exact (zero_dimensional_prime_eq_eval_kernel J hJdim _ hxJ).trans hIker.symm

/-- A zero-dimensional prime ideal over a Galois extension of `ℚ` that is not the extension of an
ideal over `ℚ` has no rational zeros. -/
theorem non_rational_zero_dimensional_locus_empty
    {K : Type*} [Field K] [Algebra ℚ K] [IsGalois ℚ K]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = 0)
    (hundef : ¬ ∃ J : Ideal (CoordinatePolynomial n),
      J.map (map (algebraMap ℚ K)) = I) :
    rationalIdealZeroLocusOver I = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hundef ⟨I.comap (map (algebraMap ℚ K)),
    zero_dimensional_prime_with_base_point_descends ℚ K I hdim x hx⟩

/-- A zero-dimensional rational prime ideal that does not stay prime over a Galois extension of
`ℚ` has no rational zeros. -/
theorem nonabsolute_zero_dimensional_locus_empty
    {K : Type*} [Field K] [Algebra ℚ K] [IsGalois ℚ K]
    {n : ℕ} (I : Ideal (CoordinatePolynomial n)) [I.IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = 0)
    (hred : ¬ (I.map (map (algebraMap ℚ K))).IsPrime) :
    idealZeroLocus I = ∅ := by
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes
    (scalar_extension_ideal_ne_top (K := K) I (Ideal.IsPrime.ne_top ‹I.IsPrime›))
  have : P.IsPrime := hP.isPrime
  have hPdim := (algebraic_polynomial_minimalPrime_dimension ℚ K (Fin n) I P hP).trans hdim
  have hPempty := non_rational_zero_dimensional_locus_empty P hPdim
    (galois_component_not_defined_over_base ℚ K I hred P hP)
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hmem : x ∈ rationalIdealZeroLocusOver P :=
    galois_base_point_on_every_component ℚ K I P hP x hx
  simp only [hPempty, Set.mem_empty_iff_false] at hmem

end
end CCDN
