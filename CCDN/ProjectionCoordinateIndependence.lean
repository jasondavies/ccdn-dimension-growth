module

public import CCDN.ProjectionScalarExtension
public import CCDN.BoundedBirationalHypersurfaceProjection
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! A hypersurface image of degree at least two forces linear independence
of the projection coordinates. Thus its actual linear kernel has the
dimension required of a projection center. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem projection_coordinates_linearIndependent
    {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (a : Fin m → MvPolynomial (Fin n) K)
    (f : MvPolynomial (Fin m) K) (hfdeg : 2 ≤ f.totalDegree)
    (hker : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f}) :
    LinearIndependent K a := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  let l : MvPolynomial (Fin m) K := ∑ j, c j • X j
  have hlmap : aeval a l = 0 := by
    simpa only [l, map_sum, map_smul, aeval_X] using hc
  have hlker : l ∈ RingHom.ker (projectionCoordinateMap I a) := by
    rw [mem_projectionCoordinateMap_ker, hlmap]
    exact I.zero_mem
  have hdiv : f ∣ l := Ideal.mem_span_singleton.mp (hker ▸ hlker)
  have hldeg : l.totalDegree ≤ 1 := by
    apply IsHomogeneous.totalDegree_le
    apply IsHomogeneous.sum
    intro j _
    simpa only [Algebra.smul_def, algebraMap_eq] using isHomogeneous_C_mul_X (c j) j
  have hlzero : l = 0 := by
    by_contra h
    have hh := totalDegree_le_of_dvd_of_isDomain hdiv h
    omega
  have hcoeff := congrArg (fun p : MvPolynomial (Fin m) K => p.coeff (Finsupp.single i 1)) hlzero
  simpa [l, coeff_X, Finsupp.single_left_inj one_ne_zero] using hcoeff

theorem integer_projection_rows_linearIndependent
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ))
    (b : Fin m → Fin n → ℤ) (f : MvPolynomial (Fin m) ℚ)
    (hfdeg : 2 ≤ f.totalDegree)
    (hker : RingHom.ker (projectionCoordinateMap I
      (fun i => integerLinearForm (b i))) = Ideal.span {f}) :
    LinearIndependent ℚ (fun i => fun j => (b i j : ℚ)) := by
  let L : (Fin n → ℚ) →ₗ[ℚ] MvPolynomial (Fin n) ℚ :=
    (Pi.basisFun ℚ (Fin n)).constr ℚ X
  have hL (v : Fin n → ℚ) : L v = ∑ j, v j • X j := by
    simp [L]
  apply LinearIndependent.of_comp L
  convert projection_coordinates_linearIndependent I
    (fun i => integerLinearForm (b i)) f hfdeg hker using 1
  funext i
  change L (fun j => (b i j : ℚ)) = integerLinearForm (b i)
  rw [hL]
  simp only [integerLinearForm, Algebra.smul_def, algebraMap_eq]

theorem integer_projection_kernel_dimension
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ))
    (b : Fin m → Fin n → ℤ) (f : MvPolynomial (Fin m) ℚ)
    (hfdeg : 2 ≤ f.totalDegree)
    (hker : RingHom.ker (projectionCoordinateMap I
      (fun i => integerLinearForm (b i))) = Ideal.span {f}) :
    let P : Matrix (Fin m) (Fin n) ℚ := fun i j => (b i j : ℚ)
    Function.Surjective P.mulVec ∧ Module.finrank ℚ P.mulVecLin.ker + m = n := by
  let P : Matrix (Fin m) (Fin n) ℚ := fun i j => (b i j : ℚ)
  have hi : LinearIndependent ℚ P.row :=
    integer_projection_rows_linearIndependent I b f hfdeg hker
  have hs := hi.mulVec_surjective
  refine ⟨hs, ?_⟩
  have hh := P.mulVecLin.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hh
  simpa only [Module.finrank_pi, Fintype.card_fin, Nat.add_comm] using hh

end
end CCDN
