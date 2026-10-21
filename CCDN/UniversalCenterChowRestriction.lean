module

public import CCDN.CenterMinorMatrix
public import CCDN.UniversalPlaneDegree

/-! The Chow restriction for the literal maximal-minor center projection as a
polynomial family in Plücker coordinates. Its specialization is proved,
and every coefficient has degree at most the source equation's total degree;
for a homogeneous source equation every coefficient is homogeneous of that
same degree (allowing zero coefficients). -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- Universal restriction: target hyperplane coefficients are variables and
center Plücker coordinates are polynomial coefficients. -/
def universalCenterChowMap {K : Type*} [Field K] {r n s q : ℕ}
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin n)) :
    MvPolynomial (Fin q × Fin n) K →+*
      MvPolynomial (Fin q × Fin (s + 1)) (MvPolynomial (Fin r ↪ Fin n) K) :=
  eval₂Hom (C.comp C) (fun p => ∑ i, C (centerPluckerCoefficient (e i) p.2) * X (p.1,i))

lemma universalCenterChowMap_comm {K : Type*} [Field K] {r n s q : ℕ}
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin n))
    (F : MvPolynomial (Fin q × Fin n) K) :
    commAlgEquiv K (Fin q × Fin (s + 1)) (Fin r ↪ Fin n) (universalCenterChowMap e F) =
      eval₂Hom (C.comp (C : K →+* MvPolynomial (Fin q × Fin (s + 1)) K))
        (fun p => ∑ i, map C (centerPluckerCoefficient (e i) p.2) * C (X (p.1,i))) F := by
  have he : (commAlgEquiv K (Fin q × Fin (s + 1)) (Fin r ↪ Fin n)).toRingHom.comp
      (universalCenterChowMap (K := K) (q := q) e) =
      eval₂Hom (C.comp (C : K →+* MvPolynomial (Fin q × Fin (s + 1)) K))
        (fun p => ∑ i, map C (centerPluckerCoefficient (e i) p.2) * C (X (p.1,i))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [universalCenterChowMap]
    · intro p
      simp [universalCenterChowMap]
  exact RingHom.congr_fun he F

lemma universalCenterChowMap_comm_homogeneous
    {K : Type*} [Field K] {r n s q D : ℕ}
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin n))
    (F : MvPolynomial (Fin q × Fin n) K) (hF : F.IsHomogeneous D) :
    (commAlgEquiv K (Fin q × Fin (s + 1)) (Fin r ↪ Fin n)
      (universalCenterChowMap e F)).IsHomogeneous D := by
  rw [universalCenterChowMap_comm]
  have hforms (p : Fin q × Fin n) :
      (∑ i : Fin (s + 1), map (C : K →+* MvPolynomial (Fin q × Fin (s + 1)) K)
        (centerPluckerCoefficient (e i) p.2) * C (X (p.1,i))).IsHomogeneous 1 := by
    apply IsHomogeneous.sum
    intro i _
    simpa only [Nat.add_zero] using
      ((centerPluckerCoefficient_homogeneous (K := K) (e i) p.2).map C).mul
        (isHomogeneous_C _ (X (p.1,i)))
  rw [coe_eval₂Hom]
  simpa only [one_mul] using hF.eval₂ (C.comp C) _ (fun a => isHomogeneous_C _ (C a)) hforms

lemma coefficient_isHomogeneous_of_commAlgEquiv
    {K σ τ : Type*} [CommRing K] {D : ℕ}
    (f : MvPolynomial σ (MvPolynomial τ K))
    (hf : (commAlgEquiv K σ τ f).IsHomogeneous D) (a : σ →₀ ℕ) :
    (f.coeff a).IsHomogeneous D := by
  intro b hb
  apply hf
  intro hz
  apply hb
  rw [← commAlgEquiv_coeff_coeff, hz]
  rfl

/-- Each coefficient is homogeneous in the Plücker variables, with
precisely the source equation's total homogeneous degree. -/
theorem universalCenterChowMap_coefficient_homogeneous
    {K : Type*} [Field K] {r n s q D : ℕ}
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin n))
    (F : MvPolynomial (Fin q × Fin n) K) (hF : F.IsHomogeneous D)
    (a : (Fin q × Fin (s + 1)) →₀ ℕ) :
    ((universalCenterChowMap e F).coeff a).IsHomogeneous D :=
  coefficient_isHomogeneous_of_commAlgEquiv _ (universalCenterChowMap_comm_homogeneous e F hF) a

end
end CCDN
