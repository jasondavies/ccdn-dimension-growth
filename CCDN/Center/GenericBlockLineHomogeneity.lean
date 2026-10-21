/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.GenericBlockLine
public import CCDN.Center.ResultantCoefficientFamily

/-! Generic affine-line restriction preserves homogeneity in coefficient
parameters. The resulting derivative-resultant coefficient family therefore
has the sharp quadratic degree needed for center avoidance. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def PolynomialCoefficientwiseHomogeneous {R σ τ : Type*} [CommRing R]
    (f : Polynomial (MvPolynomial σ (MvPolynomial τ R))) (D : ℕ) : Prop :=
  ∀ i, CoefficientwiseHomogeneous (f.coeff i) D

namespace PolynomialCoefficientwiseHomogeneous

variable {R σ τ : Type*} [CommRing R]

private theorem zero (D : ℕ) :
    PolynomialCoefficientwiseHomogeneous (0 : Polynomial (MvPolynomial σ (MvPolynomial τ R))) D := by
  intro i
  simpa only [Polynomial.coeff_zero] using CoefficientwiseHomogeneous.zero (R := R) (σ := σ) (τ := τ) D

private theorem add {f g : Polynomial (MvPolynomial σ (MvPolynomial τ R))} {D : ℕ}
    (hf : PolynomialCoefficientwiseHomogeneous f D)
    (hg : PolynomialCoefficientwiseHomogeneous g D) :
    PolynomialCoefficientwiseHomogeneous (f + g) D := by
  intro i
  rw [Polynomial.coeff_add]
  exact (hf i).add (hg i)

private theorem C_of_isHomogeneous {f : MvPolynomial σ (MvPolynomial τ R)} {D : ℕ}
    (hf : CoefficientwiseHomogeneous f D) :
    PolynomialCoefficientwiseHomogeneous (Polynomial.C f) D := by
  intro i
  rw [Polynomial.coeff_C]
  split_ifs
  · exact hf
  · exact CoefficientwiseHomogeneous.zero D

private theorem one :
    PolynomialCoefficientwiseHomogeneous (1 : Polynomial (MvPolynomial σ (MvPolynomial τ R))) 0 := by
  simpa only [map_one] using C_of_isHomogeneous (CoefficientwiseHomogeneous.one (R := R) (σ := σ) (τ := τ))

theorem X :
    PolynomialCoefficientwiseHomogeneous (Polynomial.X : Polynomial (MvPolynomial σ (MvPolynomial τ R))) 0 := by
  intro i
  rw [Polynomial.coeff_X]
  split_ifs
  · exact CoefficientwiseHomogeneous.one
  · exact CoefficientwiseHomogeneous.zero 0

private theorem sum {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial (MvPolynomial σ (MvPolynomial τ R))) (D : ℕ)
    (hf : ∀ i ∈ s, PolynomialCoefficientwiseHomogeneous (f i) D) :
    PolynomialCoefficientwiseHomogeneous (∑ i ∈ s, f i) D := by
  intro j
  rw [Polynomial.finsetSum_coeff]
  exact CoefficientwiseHomogeneous.sum _ _ _ (fun i hi => hf i hi j)

private theorem mul {f g : Polynomial (MvPolynomial σ (MvPolynomial τ R))} {D E : ℕ}
    (hf : PolynomialCoefficientwiseHomogeneous f D)
    (hg : PolynomialCoefficientwiseHomogeneous g E) :
    PolynomialCoefficientwiseHomogeneous (f * g) (D + E) := by
  intro i
  rw [Polynomial.coeff_mul]
  exact CoefficientwiseHomogeneous.sum _ _ _ (fun ab _ => (hf ab.1).mul (hg ab.2))

private theorem prod {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial (MvPolynomial σ (MvPolynomial τ R)))
    (hf : ∀ i ∈ s, PolynomialCoefficientwiseHomogeneous (f i) 0) :
    PolynomialCoefficientwiseHomogeneous (∏ i ∈ s, f i) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using one (R := R) (σ := σ) (τ := τ)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem pow {f : Polynomial (MvPolynomial σ (MvPolynomial τ R))}
    (hf : PolynomialCoefficientwiseHomogeneous f 0) (n : ℕ) :
    PolynomialCoefficientwiseHomogeneous (f ^ n) 0 := by
  induction n with
  | zero => simpa only [pow_zero] using one (R := R) (σ := σ) (τ := τ)
  | succ n ih => rw [pow_succ]; exact ih.mul hf

end PolynomialCoefficientwiseHomogeneous

private theorem genericBlockLine_coefficientwise_homogeneous
    {R σ τ : Type*} [CommRing R] (b : σ → Bool)
    (f : MvPolynomial σ (MvPolynomial τ R)) (D : ℕ)
    (hf : CoefficientwiseHomogeneous f D) :
    PolynomialCoefficientwiseHomogeneous (genericBlockLine b f) D := by
  classical
  have hx (i : σ ⊕ σ) :
      CoefficientwiseHomogeneous (X i : MvPolynomial (σ ⊕ σ) (MvPolynomial τ R)) 0 := by
    simpa only [map_X] using CoefficientwiseHomogeneous.map_C (τ := τ) (X i : MvPolynomial (σ ⊕ σ) R)
  have hv (i : σ) : PolynomialCoefficientwiseHomogeneous
      (Polynomial.C (X (Sum.inl i)) +
        if b i then Polynomial.C (X (Sum.inr i)) * Polynomial.X else 0 :
          Polynomial (MvPolynomial (σ ⊕ σ) (MvPolynomial τ R))) 0 := by
    apply PolynomialCoefficientwiseHomogeneous.add (PolynomialCoefficientwiseHomogeneous.C_of_isHomogeneous (hx _))
    split_ifs
    · exact (PolynomialCoefficientwiseHomogeneous.C_of_isHomogeneous (hx _)).mul PolynomialCoefficientwiseHomogeneous.X
    · exact PolynomialCoefficientwiseHomogeneous.zero 0
  conv => arg 1; rw [f.as_sum, map_sum]
  apply PolynomialCoefficientwiseHomogeneous.sum
  intro e _
  rw [genericBlockLine, eval₂Hom_monomial]
  have hc := PolynomialCoefficientwiseHomogeneous.C_of_isHomogeneous
    (CoefficientwiseHomogeneous.C_of_isHomogeneous (σ := σ ⊕ σ) (hf e))
  have hp := PolynomialCoefficientwiseHomogeneous.prod e.support
    (fun i => (Polynomial.C (X (Sum.inl i)) +
      if b i then Polynomial.C (X (Sum.inr i)) * Polynomial.X else 0) ^ e i)
    (fun i _ => (hv i).pow (e i))
  simpa only [RingHom.comp_apply, add_zero, Finsupp.prod] using hc.mul hp

theorem genericBlockLine_resultant_family_homogeneous
    {R σ τ : Type*} [CommRing R] (b : σ → Bool)
    (f : MvPolynomial σ (MvPolynomial τ R)) (d D : ℕ) (hd : 0 < d)
    (hf : CoefficientwiseHomogeneous f D) :
    ∀ g ∈ derivativeResultantCoefficientFamily (genericBlockLine b f) d,
      g.IsHomogeneous (D * (2 * d - 1)) :=
  derivativeResultantCoefficientFamily_homogeneous _ d D hd
    (genericBlockLine_coefficientwise_homogeneous b f D hf)

end
end CCDN
