module

public import CCDN.AffinePointZariski
public import CCDN.ZeroColumnMinorSpecialization

/-! Zariski density of good full-row-rank matrices inside a
prescribed-zero-column subspace. In particular this covers centers lying
at infinity, without inferring density there from density in the ambient
matrix space. A maximal minor is multiplied into the condition to preserve
row independence. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix
attribute [local instance] affinePointZariskiTopology

def matrixMinorPolynomial (K : Type*) [Field K] {r n : ℕ} (c : Fin r ↪ Fin n) :
    MvPolynomial (Fin r × Fin n) K :=
  (Matrix.of fun i j : Fin r => X (i,c j)).det

lemma matrixMinorPolynomial_eval {K : Type*} [Field K] {r n : ℕ}
    (c : Fin r ↪ Fin n) (x : Fin r × Fin n → K) :
    eval x (matrixMinorPolynomial K c) = (Matrix.of fun i j : Fin r => x (i,c j)).det := by
  rw [matrixMinorPolynomial,RingHom.map_det]
  congr 1
  ext i j
  exact eval_X _

lemma matrix_rows_independent_of_minor
    {K : Type*} [Field K] {r n : ℕ} (c : Fin r ↪ Fin n)
    (x : Fin r × Fin n → K) (hx : eval x (matrixMinorPolynomial K c) ≠ 0) :
    LinearIndependent K (fun i : Fin r => fun j : Fin n => x (i,j)) := by
  rw [matrixMinorPolynomial_eval] at hx
  apply LinearIndependent.of_comp (LinearMap.funLeft K K c)
  exact Matrix.linearIndependent_rows_of_det_ne_zero hx


def zeroColumnPoint {K : Type*} [Field K] {r n : ℕ}
    (Z : Finset (Fin n)) (x : Fin r × Fin n → K) : Fin r × Fin n → K :=
  fun q => if q.2 ∈ Z then 0 else x q

def zeroColumnSubstitution {K : Type*} [Field K] {r n : ℕ}
    (Z : Finset (Fin n)) :
    MvPolynomial (Fin r × Fin n) K →ₐ[K] MvPolynomial (Fin r × Fin n) K :=
  aeval (fun q => if q.2 ∈ Z then 0 else X q)

lemma eval_zeroColumnSubstitution {K : Type*} [Field K] {r n : ℕ}
    (Z : Finset (Fin n)) (x : Fin r × Fin n → K)
    (p : MvPolynomial (Fin r × Fin n) K) :
    eval x (zeroColumnSubstitution Z p) = eval (zeroColumnPoint Z x) p := by
  have he : (eval x).comp (zeroColumnSubstitution Z).toRingHom = eval (zeroColumnPoint Z x) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [zeroColumnSubstitution]
    · intro q
      simp only [RingHom.comp_apply,zeroColumnSubstitution,AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe,aeval_X]
      by_cases hq : q.2 ∈ Z <;> simp [hq,zeroColumnPoint]
  exact RingHom.congr_fun he p

lemma zeroColumnPoint_fixed {K : Type*} [Field K] {r n : ℕ}
    (Z : Finset (Fin n)) (x : Fin r × Fin n → K)
    (hx : ∀ i j, j ∈ Z → x (i,j) = 0) : zeroColumnPoint Z x = x := by
  funext q
  rcases q with ⟨i,j⟩
  by_cases hj : j ∈ Z <;> simp [zeroColumnPoint,hj,hx i j]

/-- Every point of the zero-column subspace is in the closure of the good
full-rank locus. Nonvanishing is required on this subspace itself. -/
theorem zero_column_polynomial_locus_closure
    {K : Type*} [Field K] [Infinite K] {r n : ℕ}
    (Z : Finset (Fin n)) (A : Matrix (Fin r) (Fin n) K)
    (hA : LinearIndependent K A.row) (hAz : ∀ i j, j ∈ Z → A i j = 0)
    (p : MvPolynomial (Fin r × Fin n) K) (hp : zeroColumnSubstitution Z p ≠ 0)
    (x : Fin r × Fin n → K) (hx : ∀ i j, j ∈ Z → x (i,j) = 0) :
    x ∈ closure {y : Fin r × Fin n → K |
      (∀ i j, j ∈ Z → y (i,j) = 0) ∧
      LinearIndependent K (fun i : Fin r => fun j : Fin n => y (i,j)) ∧ eval y p ≠ 0} := by
  obtain ⟨c,hc,hd⟩ := Matrix.exists_det_submatrix_ne_zero_of_linearIndependent_row A hA
  let minor := matrixMinorPolynomial K ⟨c,hc⟩
  have hm : zeroColumnSubstitution Z minor ≠ 0 := by
    intro hz
    have he := congrArg (eval (fun q => A q.1 q.2)) hz
    rw [eval_zeroColumnSubstitution,zeroColumnPoint_fixed Z _ hAz,map_zero] at he
    rw [matrixMinorPolynomial_eval] at he
    exact hd he
  let H := zeroColumnSubstitution Z p * zeroColumnSubstitution Z minor
  have hH : H ≠ 0 := mul_ne_zero hp hm
  have hD := affine_principal_open_dense H hH
  rw [affine_point_mem_closure_iff]
  intro g hg
  have hzero : ∀ y ∈ {y : Fin r × Fin n → K | eval y H ≠ 0},
      eval y (zeroColumnSubstitution Z g) = 0 := by
    intro y hy
    change eval y H ≠ 0 at hy
    rw [show H = zeroColumnSubstitution Z p * zeroColumnSubstitution Z minor from rfl,
      eval_mul,eval_zeroColumnSubstitution,eval_zeroColumnSubstitution] at hy
    rw [eval_zeroColumnSubstitution]
    apply hg
    refine ⟨?_,matrix_rows_independent_of_minor ⟨c,hc⟩ _ (mul_ne_zero_iff.mp hy).2,
      (mul_ne_zero_iff.mp hy).1⟩
    intro i j hj
    simp [zeroColumnPoint,hj]
  have he := (affine_point_mem_closure_iff _ x).mp (hD x)
    (zeroColumnSubstitution Z g) hzero
  rwa [eval_zeroColumnSubstitution,zeroColumnPoint_fixed Z x hx] at he

theorem zero_column_polynomial_locus_dense_subspace
    {K : Type*} [Field K] [Infinite K] {r n : ℕ}
    (Z : Finset (Fin n)) (A : Matrix (Fin r) (Fin n) K)
    (hA : LinearIndependent K A.row) (hAz : ∀ i j, j ∈ Z → A i j = 0)
    (p : MvPolynomial (Fin r × Fin n) K) (hp : zeroColumnSubstitution Z p ≠ 0) :
    Dense {x : {x : Fin r × Fin n → K //
      (∀ i j, j ∈ Z → x (i,j) = 0) ∧
      LinearIndependent K (fun i : Fin r => fun j : Fin n => x (i,j))} | eval x.val p ≠ 0} := by
  apply (Subtype.dense_iff (s := {x : Fin r × Fin n → K |
    (∀ i j, j ∈ Z → x (i,j) = 0) ∧
    LinearIndependent K (fun i : Fin r => fun j : Fin n => x (i,j))})).mpr
  intro x hx
  have hcl := zero_column_polynomial_locus_closure Z A hA hAz p hp x hx.1
  apply closure_mono (fun y hy => ?_) hcl
  exact ⟨⟨y,hy.1,hy.2.1⟩,hy.2.2,rfl⟩

end
end CCDN
