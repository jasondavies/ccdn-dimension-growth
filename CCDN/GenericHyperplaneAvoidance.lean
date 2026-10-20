module

public import CCDN.ChowIncidenceNonzero
public import CCDN.ChowIncidenceBaseChange
public import CCDN.ProjectiveChowIncidence

/-! Algebraically independent hyperplane coefficients have no common
projective point on the closure once their number exceeds its dimension.
The obstruction is constructed from the incidence elimination ideal. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem independent_hyperplanes_avoid_projective_closure
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    {n r : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K L))).IsPrime]
    (hr : (filteredHilbertPolynomial I).natDegree < r)
    (u : Fin r × Fin (n + 1) → L) (hu : AlgebraicIndependent K u) :
    u ∉ projectiveChowIncidenceLocus r
      (projectiveClosureIdeal (I.map (map (algebraMap K L)))) := by
  have hne := chowIncidenceIdeal_ne_bot I hr
  obtain ⟨R,hR,hR0⟩ := (Submodule.ne_bot_iff _).mp hne
  have hm : map (algebraMap K L) R ∈ chowIncidenceIdeal r
      (I.map (map (algebraMap K L))) := by
    rw [← chowIncidenceIdeal_scalar_extension]
    exact Ideal.mem_map_of_mem _ hR
  rw [chowIncidenceIdeal_eq_projective_vanishingIdeal] at hm
  intro hinc
  have hz : eval u (map (algebraMap K L) R) = 0 := by
    simpa only [aeval_eq_eval] using hm u hinc
  have he : aeval u R = 0 := by simpa only [eval_map,aeval_def] using hz
  have hi : Function.Injective (aeval u : MvPolynomial (Fin r × Fin (n + 1)) K →ₐ[K] L) := hu
  exact hR0 ((injective_iff_map_eq_zero _).mp hi R he)

end
end CCDN
