module

public import CCDN.MatrixGoodCenterDensity

/-! Zariski density of good full-row-rank matrices inside a
prescribed-zero-column subspace. In particular this covers centers lying
at infinity, without inferring density there from density in the ambient
matrix space. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix
attribute [local instance] affinePointZariskiTopology

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

theorem zero_column_polynomial_locus_isOpen_subspace
    {K : Type*} [Field K] {r n : ℕ}
    (Z : Finset (Fin n)) (p : MvPolynomial (Fin r × Fin n) K) :
    IsOpen {x : {x : Fin r × Fin n → K //
      (∀ i j, j ∈ Z → x (i,j) = 0) ∧
      LinearIndependent K (fun i : Fin r => fun j : Fin n => x (i,j))} | eval x.val p ≠ 0} :=
  (affine_polynomial_nonzero_set_open p).preimage continuous_subtype_val

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
  obtain ⟨c,hc,hd⟩ := exists_nonzero_minor_of_independent_rows A hA
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

/-- Nonvanishing at a full-rank matrix in the prescribed subspace
supplies the polynomial nonzero premise used by the density theorem. -/
theorem zero_column_minor_locus_dense
    {r n : ℕ} (Z : Finset (Fin n))
    (F : MvPolynomial (Fin r ↪ Fin n) ℚ)
    (A : Matrix (Fin r) (Fin n) ℚ) (hA : LinearIndependent ℚ A.row)
    (hAz : ∀ i j, j ∈ Z → A i j = 0)
    (hF : eval (fun c : Fin r ↪ Fin n => (A.submatrix id c).det) F ≠ 0) :
    Dense {x : {x : Fin r × Fin n → ℚ //
      (∀ i j, j ∈ Z → x (i,j) = 0) ∧
      LinearIndependent ℚ (fun i : Fin r => fun j : Fin n => x (i,j))} |
      eval (fun c : Fin r ↪ Fin n =>
        ((Matrix.of fun i j => x.val (i,j)).submatrix id c).det) F ≠ 0} := by
  let p := aeval universalMaximalMinor F
  have hp : zeroColumnSubstitution Z p ≠ 0 := by
    intro hz
    have he := congrArg (eval (fun q => A q.1 q.2)) hz
    rw [eval_zeroColumnSubstitution,zeroColumnPoint_fixed Z _ hAz,map_zero] at he
    have hh := eval_minor_substitution F A
    exact hF (hh.symm.trans he)
  have hd := zero_column_polynomial_locus_dense_subspace Z A hA hAz p hp
  convert hd using 1
  ext x
  have he := eval_minor_substitution F (Matrix.of fun i j => x.val (i,j))
  change eval x.val p = _ at he
  simp only [Set.mem_ofPred_eq,he]

end
end CCDN
