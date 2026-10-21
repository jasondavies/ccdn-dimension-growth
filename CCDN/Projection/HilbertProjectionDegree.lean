/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.HilbertProjectionKernel
public import CCDN.Hilbert.PrincipalHilbertPolynomial
/-! Degree bounds for hypersurface equations of linear projections.
The degree is bounded by the factorial-normalized leading coefficient of
the original quotient's filtered Hilbert polynomial. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem hypersurface_projection_equation_degree_le
    {K τ : Type*} [Field K] [Fintype τ] [LinearOrder τ] {n : ℕ}
    (I : Ideal (MvPolynomial τ K)) (hI : I ≠ ⊤)
    (a : Fin (n + 1) → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = n)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / n.factorial)
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f ≠ 0) (hfdeg : 0 < f.totalDegree)
    (hker : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f}) :
    f.totalDegree ≤ d := by
  have hp : Ideal.span {f} ≠ ⊤ := by
    rw [← hker]
    let : Nontrivial (MvPolynomial τ K ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
    exact RingHom.ker_ne_top _
  have hh := filteredHilbertPolynomial_leadingCoeff_le (Ideal.span {f}) I hp hI
    ((principal_filteredHilbertPolynomial_natDegree f hf hfdeg).trans hdim.symm)
    (fun N => by
      rw [← hker]
      exact linear_projection_filtered_finrank_le I a ha N)
  rw [principal_filteredHilbertPolynomial_leadingCoeff f hf hfdeg, hdegree] at hh
  have hfac : (0 : ℚ) < n.factorial := by positivity
  exact_mod_cast (div_le_div_iff_of_pos_right hfac).mp hh

/-- The equation and its degree bound are constructed from the projection. -/
theorem exists_hypersurface_projection_equation_degree_le
    {K τ : Type*} [Field K] [Fintype τ] [LinearOrder τ] {n : ℕ}
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : Fin (n + 2) → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I n d)
    (b : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hb : ∀ i, (b i).totalDegree ≤ 1)
    (hi : AlgebraicIndependent K (fun i => projectionCoordinateMap I a (b i))) :
    ∃ f : MvPolynomial (Fin (n + 2)) K, Irreducible f ∧
      0 < f.totalDegree ∧ f.totalDegree ≤ d ∧
      RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f} := by
  obtain ⟨hdim, hdegree⟩ := hdimdeg
  obtain ⟨f, hf, hker⟩ := exists_hypersurface_projection_equation I a ha
    (by rw [hdim]; omega) b hb hi
  have hfdeg : 0 < f.totalDegree := by
    by_contra hn
    have he := totalDegree_eq_zero_iff_eq_C.mp (show f.totalDegree = 0 by omega)
    have hc : f.coeff 0 ≠ 0 := by
      intro hc
      apply hf.ne_zero
      rw [he, hc, map_zero]
    apply hf.not_isUnit
    rw [he]
    exact (isUnit_iff_ne_zero.mpr hc).map C
  exact ⟨f, hf, hfdeg, hypersurface_projection_equation_degree_le I
    (Ideal.IsPrime.ne_top ‹I.IsPrime›) a ha d hdim hdegree f hf.ne_zero hfdeg hker, hker⟩

end
end CCDN
