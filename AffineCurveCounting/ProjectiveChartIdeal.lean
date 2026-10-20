module

public import AffineCurveCounting.ProjectiveChartDegree

/-! The actual prime affine-chart ideal and the transport of projective
points and Hilbert degree to that ideal. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem affineChart_mem_coordinate_kernel_iff {K F : Type*} [Field K] [Field F]
    [Algebra K F] {n M : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (q : (MvPolynomial (Fin (n + 1)) K ⧸ I) →ₐ[K] F) (hq : Function.Injective q)
    (h0 : q ((Ideal.Quotient.mk I) (X 0)) ≠ 0)
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous M) :
    affineChart n f ∈ RingHom.ker (projectiveChartCoordinateMap I q) ↔ f ∈ I := by
  rw [RingHom.mem_ker, projectiveChartCoordinateMap_chart I q h0 f hf,
    mul_eq_zero_iff_left (pow_ne_zero _ (inv_ne_zero h0))]
  rw [show q ((Ideal.Quotient.mk I) f) = 0 ↔ (Ideal.Quotient.mk I) f = 0 from
    ⟨fun h => hq (by simpa using h), fun h => by rw [h, map_zero]⟩]
  exact Ideal.Quotient.eq_zero_iff_mem

theorem coordinate_kernel_mem_iff_homogenize {K F : Type*} [Field K] [Field F]
    [Algebra K F] {n M : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (q : (MvPolynomial (Fin (n + 1)) K ⧸ I) →ₐ[K] F) (hq : Function.Injective q)
    (h0 : q ((Ideal.Quotient.mk I) (X 0)) ≠ 0)
    (f : MvPolynomial (Fin n) K) (hf : f.totalDegree ≤ M) :
    f ∈ RingHom.ker (projectiveChartCoordinateMap I q) ↔ boundedHomogenize M f ∈ I := by
  have h := affineChart_mem_coordinate_kernel_iff I q hq h0 (boundedHomogenize M f)
    (boundedHomogenize_homogeneous f hf)
  rwa [affineChart_boundedHomogenize] at h

theorem projective_point_chart_vanishes {K F : Type*} [Field K] [Field F]
    [Algebra K F] {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (q : (MvPolynomial (Fin (n + 1)) K ⧸ I) →ₐ[K] F) (hq : Function.Injective q)
    (h0 : q ((Ideal.Quotient.mk I) (X 0)) ≠ 0)
    (x : Projectivization K (Fin (n + 1) → K))
    (hx : x ∈ projectiveIdealZeroLocus I) (hx0 : x.rep 0 ≠ 0) :
    ∀ f ∈ RingHom.ker (projectiveChartCoordinateMap I q),
      eval (projectiveAffineCoordinates x) f = 0 := by
  intro f hf
  have hh := (coordinate_kernel_mem_iff_homogenize I q hq h0 f le_rfl).mp hf
  have hz := projectiveAffineCoordinates_zero (boundedHomogenize f.totalDegree f)
    (boundedHomogenize_homogeneous f le_rfl) x hx0 (projectiveIdealZeroLocus_rep hx _ hh)
  rwa [affineChart_boundedHomogenize] at hz

def projectiveChartIdeal {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime] :
    Ideal (MvPolynomial (Fin n) K) :=
  RingHom.ker (projectiveChartCoordinateMap I
    (IsScalarTower.toAlgHom K (MvPolynomial (Fin (n + 1)) K ⧸ I)
      (FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ I))))

instance projectiveChartIdeal_isPrime {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime] :
    (projectiveChartIdeal I).IsPrime :=
  RingHom.ker_isPrime _

theorem projectiveChartIdeal_degree {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime] (hX : X 0 ∉ I)
    (hdegree : HasProjectiveCurveDegree I d) :
    HasAffineCurveDegree (projectiveChartIdeal I) d := by
  apply projective_chart_degree I _ (IsFractionRing.injective _ _) _ hdegree
  intro h
  exact hX (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h))

theorem projectiveChartIdeal_point {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime] (hX : X 0 ∉ I)
    (x : ProjectivePoint n) (hx : x ∈ projectiveIdealZeroLocus I) (hx0 : x.rep 0 ≠ 0) :
    projectiveAffineCoordinates x ∈ idealZeroLocus (projectiveChartIdeal I) := by
  apply projective_point_chart_vanishes I _ (IsFractionRing.injective _ _) _ x hx hx0
  intro h
  exact hX (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h))

end
end AffineCurveCounting
