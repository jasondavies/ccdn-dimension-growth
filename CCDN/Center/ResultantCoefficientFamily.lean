module

public import CCDN.Algebra.CoefficientwiseHomogeneous
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.FieldTheory.Separable

/-! Fixed-size derivative resultants give a finite family of coefficient
conditions, homogeneous of degree D(2d-1) in the original parameters. The
Sylvester sizes stay fixed under specialization, including degree drops. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

namespace CoefficientwiseHomogeneous

theorem det_of_degree {R σ τ : Type*} [CommRing R] {r D : ℕ}
    (M : Matrix (Fin r) (Fin r) (MvPolynomial σ (MvPolynomial τ R)))
    (hM : ∀ i j, CoefficientwiseHomogeneous (M i j) D) :
    CoefficientwiseHomogeneous M.det (D * r) := by
  classical
  rw [Matrix.det_apply']
  apply sum
  intro π _
  have hp := prod Finset.univ (fun i => M (π i) i) (fun _ => D) (fun i _ => hM _ i)
  have hp' : CoefficientwiseHomogeneous (∏ i, M (π i) i) (D * r) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Nat.mul_comm] using hp
  have hc : CoefficientwiseHomogeneous
      (MvPolynomial.C (MvPolynomial.C ((Equiv.Perm.sign π : ℤ) : R)) :
        MvPolynomial σ (MvPolynomial τ R)) 0 := C_of_isHomogeneous (isHomogeneous_C τ _)
  simpa only [zero_add, map_intCast] using hc.mul hp'

theorem natCast_mul {R σ τ : Type*} [CommRing R]
    {f : MvPolynomial σ (MvPolynomial τ R)} {D : ℕ}
    (hf : CoefficientwiseHomogeneous f D) (n : ℕ) :
    CoefficientwiseHomogeneous ((n : MvPolynomial σ (MvPolynomial τ R)) * f) D := by
  have hc : CoefficientwiseHomogeneous
      (MvPolynomial.C (MvPolynomial.C (n : R)) : MvPolynomial σ (MvPolynomial τ R)) 0 :=
    C_of_isHomogeneous (isHomogeneous_C τ _)
  simpa only [map_natCast, zero_add] using hc.mul hf

end CoefficientwiseHomogeneous

theorem resultant_coefficientwise_homogeneous
    {R σ τ : Type*} [CommRing R]
    (f g : Polynomial (MvPolynomial σ (MvPolynomial τ R))) (m n D : ℕ)
    (hf : ∀ i, CoefficientwiseHomogeneous (f.coeff i) D)
    (hg : ∀ i, CoefficientwiseHomogeneous (g.coeff i) D) :
    CoefficientwiseHomogeneous (Polynomial.resultant f g m n) (D * (m + n)) := by
  apply CoefficientwiseHomogeneous.det_of_degree
  intro i j
  induction j using Fin.addCases <;>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
  · split_ifs
    · exact hg _
    · exact CoefficientwiseHomogeneous.zero D
  · split_ifs
    · exact hf _
    · exact CoefficientwiseHomogeneous.zero D

def derivativeResultant {R : Type*} [CommRing R] (f : Polynomial R) (d : ℕ) : R :=
  Polynomial.resultant f f.derivative d (d - 1)

theorem derivativeResultant_coefficientwise_homogeneous
    {R σ τ : Type*} [CommRing R]
    (f : Polynomial (MvPolynomial σ (MvPolynomial τ R))) (d D : ℕ) (hd : 0 < d)
    (hf : ∀ i, CoefficientwiseHomogeneous (f.coeff i) D) :
    CoefficientwiseHomogeneous (derivativeResultant f d) (D * (2 * d - 1)) := by
  have hh := resultant_coefficientwise_homogeneous f f.derivative d (d - 1) D hf
    (fun i => ?_)
  · simpa only [derivativeResultant, show d + (d - 1) = 2 * d - 1 by omega] using hh
  · rw [Polynomial.coeff_derivative, mul_comm]
    simpa only [Nat.cast_add, Nat.cast_one] using (hf (i + 1)).natCast_mul (i + 1)

def derivativeResultantCoefficientFamily {R σ τ : Type*} [CommRing R]
    (f : Polynomial (MvPolynomial σ (MvPolynomial τ R))) (d : ℕ) :
    Finset (MvPolynomial τ R) := by
  classical
  exact (derivativeResultant f d).support.image (derivativeResultant f d).coeff

theorem derivativeResultantCoefficientFamily_homogeneous
    {R σ τ : Type*} [CommRing R]
    (f : Polynomial (MvPolynomial σ (MvPolynomial τ R))) (d D : ℕ) (hd : 0 < d)
    (hf : ∀ i, CoefficientwiseHomogeneous (f.coeff i) D) :
    ∀ g ∈ derivativeResultantCoefficientFamily f d, g.IsHomogeneous (D * (2 * d - 1)) := by
  classical
  intro g hg
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hg
  exact derivativeResultant_coefficientwise_homogeneous f d D hd hf a

theorem derivativeResultant_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Polynomial R) (d : ℕ) :
    derivativeResultant (f.map φ) d = φ (derivativeResultant f d) := by
  rw [derivativeResultant, Polynomial.derivative_map, Polynomial.resultant_map_map]
  rfl

/-- The finite coefficient family detects nonvanishing of the
specialized fixed-size resultant, over any coefficient-ring extension. -/
theorem derivativeResultantCoefficientFamily_nonvanishing_iff
    {R S σ τ : Type*} [CommRing R] [CommRing S]
    (f : Polynomial (MvPolynomial σ (MvPolynomial τ R))) (d : ℕ)
    (φ : R →+* S) (a : τ → S) :
    (∃ g ∈ derivativeResultantCoefficientFamily f d, eval₂ φ a g ≠ 0) ↔
      derivativeResultant (f.map (MvPolynomial.map (eval₂Hom φ a))) d ≠ 0 := by
  classical
  rw [derivativeResultant_map]
  constructor
  · rintro ⟨g, hg, hne⟩ hz
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hg
    have hh := congrArg (fun p : MvPolynomial σ S => p.coeff b) hz
    rw [coeff_map] at hh
    exact hne hh
  · intro hne
    by_contra h
    apply hne
    ext b
    change (MvPolynomial.map (eval₂Hom φ a) (derivativeResultant f d)).coeff b = 0
    rw [coeff_map]
    by_cases hb : (derivativeResultant f d).coeff b = 0
    · rw [hb, map_zero]
    · have hg : (derivativeResultant f d).coeff b ∈ derivativeResultantCoefficientFamily f d :=
        Finset.mem_image.mpr ⟨b, mem_support_iff.mpr hb, rfl⟩
      exact not_ne_iff.mp (fun hh => h ⟨_, hg, hh⟩)

theorem derivativeResultant_zero {R : Type*} [CommRing R] (d : ℕ) (hd : 0 < d) :
    derivativeResultant (0 : Polynomial R) d = 0 := by
  change Polynomial.resultant (0 : Polynomial R) 0 d (d - 1) = 0
  rw [Polynomial.resultant_zero_zero]
  exact zero_pow (by omega : d + (d - 1) ≠ 0)

theorem derivativeResultant_ne_zero_iff_separable
    {K : Type*} [Field K] [CharZero K]
    (f : Polynomial K) (d : ℕ) (hd : 0 < d) (hf : f.natDegree = d) :
    derivativeResultant f d ≠ 0 ↔ f.Separable := by
  have hf0 : f ≠ 0 := by
    intro hz
    simp only [hz, Polynomial.natDegree_zero] at hf
    omega
  have hder : f.derivative.natDegree = d - 1 := by
    rw [Polynomial.natDegree_derivative, hf]
  change Polynomial.resultant f f.derivative d (d - 1) ≠ 0 ↔ _
  rw [← hder, ← hf, ne_eq, Polynomial.resultant_eq_zero_iff,
    Polynomial.separable_def]
  simp only [hf0, ne_eq, not_false_eq_true, true_or, true_and, not_not]

end
end CCDN
