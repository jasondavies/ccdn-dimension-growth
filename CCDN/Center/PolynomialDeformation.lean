module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! A polynomial deformation whose constant specialization is injective
remains injective, including after adjoining the deformation parameters.
The proof uses the first nonzero coefficient. -/

@[expose] public section
namespace CCDN
noncomputable section

theorem polynomial_deformation_injective
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (φ : R →+* Polynomial S)
    (hφ : Function.Injective (Polynomial.constantCoeff.comp φ)) :
    Function.Injective (Polynomial.eval₂RingHom φ Polynomial.X) := by
  let Φ := Polynomial.eval₂RingHom φ Polynomial.X
  have hc : Polynomial.constantCoeff.comp Φ =
      (Polynomial.constantCoeff.comp φ).comp Polynomial.constantCoeff := by
    apply Polynomial.ringHom_ext'
    · ext r
      simp [Φ]
    · simp [Φ]
  apply (injective_iff_map_eq_zero Φ).mpr
  intro P hP
  by_contra hne
  obtain ⟨Q,hQ⟩ := Polynomial.X_pow_dvd_iff.mpr
    (fun j hj => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (p := P) hj)
  have hQ0 : Q.coeff 0 ≠ 0 := by
    have hh := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hne
    have he : P.coeff P.natTrailingDegree = Q.coeff 0 := by
      calc
        P.coeff P.natTrailingDegree =
            (Polynomial.X ^ P.natTrailingDegree * Q).coeff (0 + P.natTrailingDegree) := by
          simpa only [Nat.zero_add] using congrArg (fun f : Polynomial R => f.coeff P.natTrailingDegree) hQ
        _ = Q.coeff 0 := Polynomial.coeff_X_pow_mul _ _ _
    rwa [he] at hh
  have hmapQ : Φ Q = 0 := by
    rw [hQ,map_mul,map_pow] at hP
    have hX : Φ Polynomial.X = Polynomial.X := by simp [Φ]
    rw [hX] at hP
    exact (mul_eq_zero.mp hP).resolve_left (pow_ne_zero _ Polynomial.X_ne_zero)
  have hz := RingHom.congr_fun hc Q
  rw [RingHom.comp_apply,hmapQ,map_zero] at hz
  have hzero : (Polynomial.constantCoeff.comp φ) (Q.coeff 0) = 0 := hz.symm
  exact hQ0 ((injective_iff_map_eq_zero (Polynomial.constantCoeff.comp φ)).mp hφ _ hzero)

end
end CCDN
