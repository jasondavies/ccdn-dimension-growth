module

public import CCDN.Noether.EulerUniversalForms
/-! Homogeneity in the coefficient variables, while retaining independent
polynomial parameters. This property survives determinant expansion and
extraction of any parameter coefficient. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def CoefficientwiseHomogeneous {R σ τ : Type*} [CommRing R]
    (f : MvPolynomial σ (MvPolynomial τ R)) (d : ℕ) : Prop :=
  ∀ m, (f.coeff m).IsHomogeneous d

namespace CoefficientwiseHomogeneous

variable {R σ τ : Type*} [CommRing R]

lemma zero (d : ℕ) : CoefficientwiseHomogeneous (0 : MvPolynomial σ (MvPolynomial τ R)) d := by
  intro m
  simpa only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using isHomogeneous_zero τ R d

lemma add {f g : MvPolynomial σ (MvPolynomial τ R)} {d : ℕ}
    (hf : CoefficientwiseHomogeneous f d) (hg : CoefficientwiseHomogeneous g d) :
    CoefficientwiseHomogeneous (f + g) d := by
  intro m
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  exact (hf m).add (hg m)

lemma neg {f : MvPolynomial σ (MvPolynomial τ R)} {d : ℕ}
    (hf : CoefficientwiseHomogeneous f d) :
    CoefficientwiseHomogeneous (-f) d := by
  intro m
  rw [coeff_neg]
  exact (hf m).neg

lemma sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ (MvPolynomial τ R)) (d : ℕ)
    (hf : ∀ i ∈ s, CoefficientwiseHomogeneous (f i) d) :
    CoefficientwiseHomogeneous (∑ i ∈ s, f i) d := by
  intro m
  rw [coeff_sum]
  exact IsHomogeneous.sum s _ d (fun i hi => hf i hi m)

lemma mul {f g : MvPolynomial σ (MvPolynomial τ R)} {d e : ℕ}
    (hf : CoefficientwiseHomogeneous f d) (hg : CoefficientwiseHomogeneous g e) :
    CoefficientwiseHomogeneous (f * g) (d + e) := by
  classical
  intro m
  rw [coeff_mul]
  exact IsHomogeneous.sum _ _ _ (fun ij _ => (hf ij.1).mul (hg ij.2))

lemma C_of_isHomogeneous {f : MvPolynomial τ R} {d : ℕ} (hf : f.IsHomogeneous d) :
    CoefficientwiseHomogeneous (MvPolynomial.C f : MvPolynomial σ (MvPolynomial τ R)) d := by
  classical
  intro m
  rw [coeff_C]
  split_ifs
  · exact hf
  · exact isHomogeneous_zero τ R d

lemma one : CoefficientwiseHomogeneous (1 : MvPolynomial σ (MvPolynomial τ R)) 0 := by
  simpa only [map_one] using C_of_isHomogeneous (σ := σ) (isHomogeneous_one τ R)

lemma map_C (f : MvPolynomial σ R) :
    CoefficientwiseHomogeneous (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) f) 0 := by
  intro m
  rw [coeff_map]
  exact isHomogeneous_C _ _

lemma prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ (MvPolynomial τ R))
    (d : ι → ℕ) (hf : ∀ i ∈ s, CoefficientwiseHomogeneous (f i) (d i)) :
    CoefficientwiseHomogeneous (∏ i ∈ s, f i) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using one (R := R) (σ := σ) (τ := τ)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).mul
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma det {r : ℕ} (M : Matrix (Fin r) (Fin r) (MvPolynomial σ (MvPolynomial τ R)))
    (hM : ∀ i j, CoefficientwiseHomogeneous (M i j) 1) :
    CoefficientwiseHomogeneous M.det r := by
  classical
  rw [Matrix.det_apply']
  apply sum
  intro π _
  have hp := prod Finset.univ (fun i => M (π i) i) (fun _ => 1) (fun i _ => hM _ i)
  have hp' : CoefficientwiseHomogeneous (∏ i, M (π i) i) r := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hp
  have hc : CoefficientwiseHomogeneous
      (MvPolynomial.C (MvPolynomial.C ((Equiv.Perm.sign π : ℤ) : R)) :
        MvPolynomial σ (MvPolynomial τ R)) 0 :=
    C_of_isHomogeneous (isHomogeneous_C τ _)
  have hh := hc.mul hp'
  simpa only [zero_add, map_intCast] using hh

end CoefficientwiseHomogeneous
end
end CCDN
