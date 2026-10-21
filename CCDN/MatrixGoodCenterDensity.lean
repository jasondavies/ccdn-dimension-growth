module

public import CCDN.AffinePointZariski
public import CCDN.ZeroColumnMinorSpecialization

/-! Nonzero polynomial conditions are dense on the full-row-rank
matrix parameter space. A maximal minor is multiplied into the condition
to preserve row independence, including constant conditions. -/

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

lemma matrixMinorPolynomial_ne_zero {K : Type*} [Field K] {r n : ℕ}
    (c : Fin r ↪ Fin n) : matrixMinorPolynomial K c ≠ 0 := by
  classical
  let x : Fin r × Fin n → K := fun q => if c q.1 = q.2 then 1 else 0
  have hmat : (Matrix.of fun i j : Fin r => x (i,c j)) = 1 := by
    ext i j
    simp [x,c.injective.eq_iff,Matrix.one_apply]
  intro hz
  have he := congrArg (eval x) hz
  rw [matrixMinorPolynomial_eval,hmat,Matrix.det_one,map_zero] at he
  exact one_ne_zero he

lemma matrix_rows_independent_of_minor
    {K : Type*} [Field K] {r n : ℕ} (c : Fin r ↪ Fin n)
    (x : Fin r × Fin n → K) (hx : eval x (matrixMinorPolynomial K c) ≠ 0) :
    LinearIndependent K (fun i : Fin r => fun j : Fin n => x (i,j)) := by
  rw [matrixMinorPolynomial_eval] at hx
  apply LinearIndependent.of_comp (LinearMap.funLeft K K c)
  exact Matrix.linearIndependent_rows_of_det_ne_zero hx

theorem full_row_rank_polynomial_locus_dense
    {K : Type*} [Field K] [Infinite K] {r n : ℕ}
    (c : Fin r ↪ Fin n) (p : MvPolynomial (Fin r × Fin n) K) (hp : p ≠ 0) :
    Dense {x : Fin r × Fin n → K |
      LinearIndependent K (fun i : Fin r => fun j : Fin n => x (i,j)) ∧ eval x p ≠ 0} := by
  have hprod : p * matrixMinorPolynomial K c ≠ 0 :=
    mul_ne_zero hp (matrixMinorPolynomial_ne_zero c)
  apply (affine_principal_open_dense _ hprod).mono
  intro x hx
  change eval x (p * matrixMinorPolynomial K c) ≠ 0 at hx
  rw [eval_mul] at hx
  exact ⟨matrix_rows_independent_of_minor c x (mul_ne_zero_iff.mp hx).2,
    (mul_ne_zero_iff.mp hx).1⟩

/-- Density in the full-row-rank space itself, with its induced Zariski
topology; this is stronger than existence of a rational specialization. -/
theorem full_row_rank_polynomial_locus_dense_subspace
    {K : Type*} [Field K] [Infinite K] {r n : ℕ}
    (c : Fin r ↪ Fin n) (p : MvPolynomial (Fin r × Fin n) K) (hp : p ≠ 0) :
    Dense {x : {x : Fin r × Fin n → K //
      LinearIndependent K (fun i : Fin r => fun j : Fin n => x (i,j))} |
        eval x.val p ≠ 0} := by
  apply (Subtype.dense_iff (s := {x : Fin r × Fin n → K |
    LinearIndependent K (fun i : Fin r => fun j : Fin n => x (i,j))})).mpr
  have hd := full_row_rank_polynomial_locus_dense c p hp
  intro x _
  apply closure_mono (fun y hy => ?_) (hd x)
  exact ⟨⟨y,hy.1⟩,hy.2,rfl⟩

end
end CCDN
