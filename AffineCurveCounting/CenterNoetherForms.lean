module

public import AffineCurveCounting.NoetherCoefficientFamily
public import AffineCurveCounting.UniversalCenterChowRestriction

/-! Actual finite Noether forms on Plücker coordinates for the universal
center restriction. Their composed degree is D(D^2-1) for D at least two;
linear source equations use a degree-one coefficient detector. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Matrix

lemma universalCenterChowMap_homogeneous
    {K : Type*} [Field K] {r n s q D : ℕ}
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin n))
    (F : MvPolynomial (Fin q × Fin n) K) (hF : F.IsHomogeneous D) :
    (universalCenterChowMap e F).IsHomogeneous D := by
  have hh : (universalCenterChowMap e F).IsHomogeneous (1 * D) := by
    apply hF.eval₂
    · intro c
      exact isHomogeneous_C _ (C c)
    · intro p
      apply IsHomogeneous.sum
      intro i _
      simpa only [Nat.zero_add] using
        (isHomogeneous_C _ (centerPluckerCoefficient (e i) p.2)).mul
          (isHomogeneous_X _ (p.1, i))
  simpa only [one_mul] using hh

lemma irreducible_map_algebraicClosure_iff_of_isAlgClosed
    {K σ : Type*} [Field K] [IsAlgClosed K] (f : MvPolynomial σ K) :
    Irreducible (map (algebraMap K (AlgebraicClosure K)) f) ↔ Irreducible f := by
  let e : K ≃+* AlgebraicClosure K := RingEquiv.ofBijective
    (algebraMap K (AlgebraicClosure K)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact MulEquiv.irreducible_iff (mapEquiv σ e)

/-- The detector is a finite family of genuine polynomials in the maximal
minor coordinates, chosen before the center matrix. Its evaluations detect
absolute irreducibility of the actual restricted source equation. -/
theorem exists_center_noether_forms
    {K : Type*} [Field K] [CharZero K] {r n s m D : ℕ}
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin (n + 1)))
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 1)) K)
    (hD : 0 < D) (hF : F.IsHomogeneous D) :
    ∃ Φ : Finset (MvPolynomial (Fin r ↪ Fin (n + 1)) K),
      (∀ g ∈ Φ, g.IsHomogeneous (D * max 1 (D ^ 2 - 1))) ∧
      (∀ g ∈ Φ, g.totalDegree ≤ D * max 1 (D ^ 2 - 1)) ∧
      ∀ A : Matrix (Fin r) (Fin (n + 1)) K,
        (∃ g ∈ Φ, eval (fun c : Fin r ↪ Fin (n + 1) => (A.submatrix id c).det) g ≠ 0) ↔
          Irreducible (map (algebraMap K (AlgebraicClosure K))
            (chowLinearSubstitution (centerMinorProjectionMatrix A e) F)) := by
  classical
  obtain ⟨Φ, hΦ, hdet⟩ := exists_homogeneous_coefficient_detector D D hD
    (universalCenterChowMap e F) (universalCenterChowMap_homogeneous e F hF)
    (universalCenterChowMap_coefficient_homogeneous e F hF)
  refine ⟨Φ, hΦ, fun g hg => (hΦ g hg).totalDegree_le, fun A => ?_⟩
  simpa only [universalCenterChowMap_specialize] using
    hdet (fun c : Fin r ↪ Fin (n + 1) => (A.submatrix id c).det)

end
end AffineCurveCounting
