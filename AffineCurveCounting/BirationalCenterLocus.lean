module

public import AffineCurveCounting.BirationalCenterNonvanishing
public import AffineCurveCounting.ZeroColumnCenterDensity

/-! The actual geometrically disjoint birational-center condition, and its
independence from the enumeration used for the minor projection. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Matrix
attribute [local instance] affinePointZariskiTopology

/-- A polynomial in maximal minors, pulled back to matrix entries. -/
def centerMinorPolynomial {K : Type*} [Field K] {r n : ℕ}
    (G : MvPolynomial (Fin r ↪ Fin n) K) : MvPolynomial (Fin r × Fin n) K :=
  aeval (matrixMinorPolynomial K) G

lemma eval_centerMinorPolynomial {K : Type*} [Field K] {r n : ℕ}
    (G : MvPolynomial (Fin r ↪ Fin n) K) (x : Fin r × Fin n → K) :
    eval x (centerMinorPolynomial G) =
      eval (fun c : Fin r ↪ Fin n =>
        ((Matrix.of fun i j => x (i,j)).submatrix id c).det) G := by
  have he : (eval x).comp (aeval (matrixMinorPolynomial K)).toRingHom =
      eval (fun c : Fin r ↪ Fin n =>
        ((Matrix.of fun i j => x (i,j)).submatrix id c).det) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro c
      simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,RingHom.coe_coe,aeval_X,eval_X]
      exact matrixMinorPolynomial_eval c x
  exact RingHom.congr_fun he G

/-- The matrix rows span a center disjoint from the geometric variety, and
its literal minor projection generates the source function field. -/
def IsBirationalMatrixCenter {K : Type*} [Field K] {n r s : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) [J.IsPrime]
    (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 1)))
    (A : Matrix (Fin r) (Fin (n + 1)) K) : Prop :=
  (∀ p ∈ projectiveIdealZeroLocus (J.map (map (algebraMap K (AlgebraicClosure K)))),
    p.rep ∉ Submodule.span (AlgebraicClosure K)
      (Set.range (A.map (algebraMap K (AlgebraicClosure K))).row)) ∧
  projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ J)) J
    (chowProjectionForms (centerMinorProjectionMatrix A e)) = ⊤

lemma isBirationalMatrixCenter_iff_enumeration
    {K : Type*} [Field K] {n r s t : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) [J.IsPrime]
    (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 1)))
    (e' : Fin (t + 2) ≃ (Fin (r + 1) ↪ Fin (n + 1)))
    (A : Matrix (Fin r) (Fin (n + 1)) K) (hA : LinearIndependent K A.row) :
    IsBirationalMatrixCenter J e A ↔ IsBirationalMatrixCenter J e' A := by
  have hker : (centerMinorProjectionMatrix A e).mulVecLin.ker =
      (centerMinorProjectionMatrix A e').mulVecLin.ker := by
    rw [centerMinorProjectionMatrix_ker A hA e,centerMinorProjectionMatrix_ker A hA e']
  unfold IsBirationalMatrixCenter
  rw [projectionImageField_eq_of_matrix_kernel_eq J _ _ hker]

/-- Full-row-rank matrices carry the topology induced by the Zariski
topology on their entries. -/
abbrev IndependentCenterMatrix (K : Type*) [Field K] (r n : ℕ) :=
  {x : Fin r × Fin n → K //
    LinearIndependent K (fun i : Fin r => fun j : Fin n => x (i,j))}

/-- The actual good-center locus; no detector polynomial is part of its
definition. -/
def birationalMatrixCenterLocus {K : Type*} [Field K] {n r s : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) [J.IsPrime]
    (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 1))) :
    Set (IndependentCenterMatrix K r (n + 1)) :=
  {x | IsBirationalMatrixCenter J e (Matrix.of fun i j => x.val (i,j))}

end
end AffineCurveCounting
