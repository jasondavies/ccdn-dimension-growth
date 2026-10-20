module

public import CCDN.ProjectiveChowIncidence
public import CCDN.PolynomialPredicates

/-! Passing between nonzero vectors on a homogeneous affine cone and
actual projective points preserves hyperplane incidence. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem homogeneous_cone_point_projectivize {K : Type*} [Field K] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : IsHomogeneousIdeal J)
    (x : Fin (n + 1) → K) (hx : x ≠ 0) (hz : ∀ f ∈ J, eval x f = 0) :
    Projectivization.mk K x hx ∈ projectiveIdealZeroLocus J := by
  intro v hv he f hf
  have hcomp (N : ℕ) : eval v (homogeneousComponent N f) = 0 :=
    (homogeneous_eval_zero_iff_projective_eq (homogeneousComponent_isHomogeneous N f)
      hv hx he).mpr (hz _ (hJ f hf N))
  conv_lhs => rw [← sum_homogeneousComponent (φ := f)]
  rw [map_sum]
  exact Finset.sum_eq_zero (fun N _ => hcomp N)

theorem homogeneous_cone_zero_of_no_projective_incidence
    {K : Type*} [Field K] {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : IsHomogeneousIdeal J)
    (u : Fin r × Fin (n + 1) → K)
    (hu : u ∉ projectiveChowIncidenceLocus r J)
    (x : Fin (n + 1) → K) (hx : ∀ f ∈ J, eval x f = 0)
    (hux : ∀ i, ∑ j, u (i,j) * x j = 0) : x = 0 := by
  by_contra hne
  let p := Projectivization.mk K x hne
  apply hu
  refine ⟨p,homogeneous_cone_point_projectivize J hJ x hne hx,?_⟩
  intro i
  let f : MvPolynomial (Fin (n + 1)) K := ∑ j, C (u (i,j)) * X j
  have hf : f.IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ j)
  have heval (v : Fin (n + 1) → K) : eval v f = ∑ j, u (i,j) * v j := by simp [f]
  have hz : eval x f = 0 := (heval x).trans (hux i)
  have hh := (homogeneous_eval_zero_iff_projective_eq hf p.rep_nonzero hne p.mk_rep).mpr hz
  rwa [heval] at hh

end
end CCDN
