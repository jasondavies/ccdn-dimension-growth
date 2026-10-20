module

public import CCDN.GenericBlockLineIrreducible
public import CCDN.ResultantCoefficientFamily
public import CCDN.ChowPolynomialPower

/-! When a polynomial has the same hypersurface as an irreducible equation,
a generic block-line derivative resultant detects its irreducibility.
The positive block degree is the degree of the line polynomial. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem genericBlockLine_derivativeResultant_irreducible_iff
    {K σ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Finite σ]
    (b : σ → Bool) (G R : MvPolynomial σ K) (hG : Irreducible G)
    (hzero : ∀ z : σ → K, eval z R = 0 ↔ eval z G = 0)
    (d : ℕ) (hd : 0 < d)
    (hdegree : R.weightedTotalDegree (genericBlockWeight b) = d) :
    derivativeResultant (genericBlockLine b R) d ≠ 0 ↔ Irreducible R := by
  let A := MvPolynomial (σ ⊕ σ) K
  let F := FractionRing A
  let θ : A →+* F := algebraMap A F
  let ρ : MvPolynomial σ K →+* Polynomial F :=
    (Polynomial.mapRingHom θ).comp (genericBlockLine b)
  have hρdegree : (ρ R).natDegree = d := by
    change ((genericBlockLine b R).map θ).natDegree = d
    rw [Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective A F),
      genericBlockLine_natDegree, hdegree]
  have hresult : derivativeResultant (genericBlockLine b R) d ≠ 0 ↔ (ρ R).Separable := by
    have hh := derivativeResultant_ne_zero_iff_separable (ρ R) d hd hρdegree
    change derivativeResultant ((genericBlockLine b R).map θ) d ≠ 0 ↔ _ at hh
    rw [derivativeResultant_map] at hh
    exact (map_ne_zero_iff θ (IsFractionRing.injective A F)).symm.trans hh
  rw [hresult]
  constructor
  · intro hsep
    obtain ⟨a,r,ha,hr,he⟩ := polynomial_eq_scalar_pow_of_same_zeros G R hG hzero
    have hunit : IsUnit (C a : MvPolynomial σ K) := (isUnit_iff_ne_zero.mpr ha).map C
    have hnot : ¬ IsUnit (ρ G) := by
      intro hunitG
      have hunitR : IsUnit (ρ R) := by
        rw [he,map_mul,map_pow]
        exact (hunit.map ρ).mul (hunitG.pow r)
      have hz := Polynomial.natDegree_eq_zero_of_isUnit hunitR
      omega
    have hpow : ((ρ G) ^ r).Separable := by
      rw [he,map_mul,map_pow] at hsep
      exact hsep.of_mul_right
    have hr1 := (Polynomial.Separable.of_pow hnot (Nat.ne_zero_of_lt hr) hpow).2
    rw [he,hr1,pow_one]
    exact (irreducible_isUnit_mul hunit).mpr hG
  · intro hR
    exact genericBlockLine_fraction_separable (F := F) b R hR (by omega)

end
end CCDN
