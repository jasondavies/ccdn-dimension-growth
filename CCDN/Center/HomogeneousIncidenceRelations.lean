module

public import CCDN.Hilbert.HomogeneousHilbert
public import CCDN.Algebra.PolynomialPredicates
/-! Homogeneous certificates for membership in an ideal together with finitely
many linear equations. These retain the degree needed for a finite coefficient
matrix certificate of empty projective incidence. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def incidenceLinearForm {K : Type*} [CommSemiring K] {n r : ℕ}
    (U : Fin r × Fin (n + 1) → K) (i : Fin r) : MvPolynomial (Fin (n + 1)) K :=
  ∑ j, C (U (i,j)) * X j

lemma incidenceLinearForm_homogeneous {K : Type*} [CommSemiring K] {n r : ℕ}
    (U : Fin r × Fin (n + 1) → K) (i : Fin r) :
    (incidenceLinearForm U i).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ j)

lemma incidenceLinearForm_eval {K : Type*} [CommSemiring K] {n r : ℕ}
    (U : Fin r × Fin (n + 1) → K) (i : Fin r) (x : Fin (n + 1) → K) :
    eval x (incidenceLinearForm U i) = ∑ j, U (i,j) * x j := by
  simp [incidenceLinearForm]

/-- A homogeneous member of a homogeneous ideal plus linear equations admits
an expression whose multipliers have exactly the preceding degree. -/
theorem homogeneous_incidence_relation {K : Type*} [Field K] {n r t : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : IsHomogeneousIdeal J)
    (U : Fin r × Fin (n + 1) → K)
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous (t + 1))
    (hmem : f ∈ J ⊔ Ideal.span (Set.range (incidenceLinearForm U))) :
    ∃ q : MvPolynomial (Fin (n + 1)) K,
      ∃ p : Fin r → MvPolynomial (Fin (n + 1)) K,
        q ∈ J ∧ q.IsHomogeneous (t + 1) ∧
        (∀ i, (p i).IsHomogeneous t) ∧
        q + ∑ i, incidenceLinearForm U i * p i = f := by
  classical
  obtain ⟨q, hq, z, hz, he⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨p, hp⟩ := Ideal.mem_span_range_iff_exists_fun.mp hz
  refine ⟨homogeneousComponent (t + 1) q, fun i => homogeneousComponent t (p i),
    hJ q hq _, homogeneousComponent_isHomogeneous _ _,
    fun i => homogeneousComponent_isHomogeneous _ _, ?_⟩
  have h := congrArg (homogeneousComponent (t + 1)) he
  rw [← hp, map_add, map_sum, homogeneousComponent_eq_self hf] at h
  convert h using 2
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (p i), show t + 1 = 1 + t by omega,
    homogeneousComponent_mul_of_isHomogeneous_left (incidenceLinearForm_homogeneous U i)]

end
end CCDN
