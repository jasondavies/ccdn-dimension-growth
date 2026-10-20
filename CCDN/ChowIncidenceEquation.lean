module

public import CCDN.ChowIncidenceNonzero
public import CCDN.ChowIncidenceLocus
public import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky

/-! An actual irreducible incidence equation is constructed from the
nonzero prime elimination ideal. Principality and the exact Chow
multidegree are separate geometric obligations. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem exists_irreducible_incidence_equation {K : Type*} [Field K] [IsAlgClosed K]
    {n r : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hr : (filteredHilbertPolynomial I).natDegree < r) :
    ∃ R : MvPolynomial (Fin r × Fin (n + 1)) K,
      Irreducible R ∧ R ∈ chowIncidenceIdeal r I ∧
      ∀ U ∈ chowIncidenceLocus r I, eval U R = 0 := by
  obtain ⟨R,hR,hprime⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot
    (inferInstance : (chowIncidenceIdeal r I).IsPrime) (chowIncidenceIdeal_ne_bot I hr)
  refine ⟨R,hprime.irreducible,hR,?_⟩
  rw [chowIncidenceIdeal_eq_vanishingIdeal] at hR
  intro U hU
  simpa only [aeval_eq_eval] using hR U hU

end
end CCDN
