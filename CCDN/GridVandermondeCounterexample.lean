module

public import CCDN.MixedDegreeProjectiveExample
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Data.Finset.Prod

/-! Primitive points and homogeneous columns of differing degrees on one
fixed projective line. Their evaluation matrix is a Kronecker product
of two Vandermonde matrices. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset
open scoped BigOperators Kronecker

lemma fin_sum_card_Ioi (N : ℕ) :
    (∑ i : Fin N, (Ioi i).card) = N.choose 2 := by
  have he (i : Fin N) : (Ioi i).card = i.rev.val := by
    rw [Fin.card_Ioi, Fin.val_rev]
    omega
  simp_rw [he]
  rw [show (∑ i : Fin N, i.rev.val) = ∑ i : Fin N, i.val from
    Equiv.sum_comp Fin.revPerm (fun i : Fin N => i.val)]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id, Nat.choose_two_right]


lemma integer_vandermonde_pos_le {N : ℕ} (v : Fin N → ℤ) (R : ℤ)
    (hv : ∀ i j, i < j → 0 < v j - v i ∧ v j - v i ≤ R) :
    0 < (Matrix.vandermonde v).det ∧ (Matrix.vandermonde v).det ≤ R ^ N.choose 2 := by
  rw [Matrix.det_vandermonde]
  have hpos : ∀ i j, j ∈ Ioi i → 0 < v j - v i := fun i j h => (hv i j (mem_Ioi.mp h)).1
  refine ⟨prod_pos (fun i _ => prod_pos (hpos i)), ?_⟩
  calc
    _ ≤ ∏ i : Fin N, R ^ (Ioi i).card := by
      apply prod_le_prod₀
      · intro i _
        exact (prod_pos (hpos i)).le
      · intro i _
        calc
          _ ≤ ∏ _j ∈ Ioi i, R := prod_le_prod₀ (fun j hj => (hpos i j hj).le)
            (fun j hj => (hv i j (mem_Ioi.mp hj)).2)
          _ = _ := by simp
    _ = R ^ N.choose 2 := by rw [prod_pow_eq_pow_sum, fin_sum_card_Ioi]

def globalMixedDegreePoint (N : ℕ) (i : Fin N × Fin N) : Fin 3 → ℤ :=
  ![(i.1.val : ℤ) * N.factorial + 1, (i.2.val : ℤ) + 1, 0]

def globalMixedDegreeForm {N : ℕ} (j : Fin N × Fin N) : MvPolynomial (Fin 3) ℤ :=
  X 0 ^ j.1.val * X 1 ^ j.2.val

def globalMixedDegreeMatrix (N : ℕ) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℤ :=
  Matrix.of fun i j => eval (globalMixedDegreePoint N i) (globalMixedDegreeForm j)

lemma globalMixedDegreePoint_primitive (N : ℕ) (i : Fin N × Fin N) :
    univ.gcd (globalMixedDegreePoint N i) = 1 := by
  have hda := gcd_dvd (f := globalMixedDegreePoint N i) (mem_univ (0 : Fin 3))
  have hdb := gcd_dvd (f := globalMixedDegreePoint N i) (mem_univ (1 : Fin 3))
  have hdiv : (i.2.val + 1 : ℤ) ∣ (N.factorial : ℤ) := by
    exact_mod_cast Nat.dvd_factorial (by omega : 0 < i.2.val + 1) (by omega : i.2.val + 1 ≤ N)
  have hdQ := hdb.trans hdiv
  have hd : univ.gcd (globalMixedDegreePoint N i) ∣ (1 : ℤ) := by
    have hh := dvd_sub hda (dvd_mul_of_dvd_right hdQ (i.1.val : ℤ))
    simpa [globalMixedDegreePoint] using hh
  rw [← Finset.normalize_gcd, normalize_eq_one]
  exact isUnit_of_dvd_one hd

lemma globalMixedDegreePoint_zero (N : ℕ) (i : Fin N × Fin N) :
    eval (globalMixedDegreePoint N i) (X (2 : Fin 3)) = 0 := by
  simp [globalMixedDegreePoint]

lemma globalMixedDegreeForm_homogeneous {N : ℕ} (j : Fin N × Fin N) :
    (globalMixedDegreeForm j).IsHomogeneous (j.1.val + j.2.val) :=
  (isHomogeneous_X_pow _ _).mul (isHomogeneous_X_pow _ _)

lemma globalMixedDegreeMatrix_eq_kronecker (N : ℕ) :
    globalMixedDegreeMatrix N =
      Matrix.vandermonde (fun i : Fin N => (i.val : ℤ) * N.factorial + 1) ⊗ₖ
        Matrix.vandermonde (fun j : Fin N => (j.val : ℤ) + 1) := by
  ext i j
  simp [globalMixedDegreeMatrix, globalMixedDegreePoint, globalMixedDegreeForm,
    Matrix.vandermonde]

lemma globalMixedDegreeMatrix_det (N : ℕ) :
    (globalMixedDegreeMatrix N).det =
      (Matrix.vandermonde (fun i : Fin N => (i.val : ℤ) * N.factorial + 1)).det ^ N *
        (Matrix.vandermonde (fun j : Fin N => (j.val : ℤ) + 1)).det ^ N := by
  rw [globalMixedDegreeMatrix_eq_kronecker, Matrix.det_kronecker]
  simp

lemma globalMixedDegreeMatrix_det_pos_le (N : ℕ) :
    0 < (globalMixedDegreeMatrix N).det ∧
      (globalMixedDegreeMatrix N).det ≤
        ((N : ℤ) * N.factorial) ^ (N.choose 2 * N) * (N : ℤ) ^ (N.choose 2 * N) := by
  have hQ : (0 : ℤ) < N.factorial := by positivity
  have hx := integer_vandermonde_pos_le
    (fun i : Fin N => (i.val : ℤ) * N.factorial + 1) ((N : ℤ) * N.factorial) (by
      intro i j hij
      have hlt : (i.val : ℤ) < j.val := by exact_mod_cast hij
      have hj : (j.val : ℤ) < N := by exact_mod_cast j.isLt
      have hi : (0 : ℤ) ≤ i.val := by positivity
      constructor
      · nlinarith
      · nlinarith)
  have hy := integer_vandermonde_pos_le
    (fun j : Fin N => (j.val : ℤ) + 1) (N : ℤ) (by
      intro i j hij
      have hlt : (i.val : ℤ) < j.val := by exact_mod_cast hij
      have hj : (j.val : ℤ) < N := by exact_mod_cast j.isLt
      have hi : (0 : ℤ) ≤ i.val := by positivity
      constructor <;> omega)
  rw [globalMixedDegreeMatrix_det]
  refine ⟨mul_pos (pow_pos hx.1 _) (pow_pos hy.1 _), ?_⟩
  simpa only [pow_mul] using mul_le_mul
    (pow_le_pow_left₀ hx.1.le hx.2 N) (pow_le_pow_left₀ hy.1.le hy.2 N)
    (pow_nonneg hy.1.le N) (by positivity)

end
end CCDN
