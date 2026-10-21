module

public import CCDN.Center.GoodCenterWitness
public import CCDN.Hilbert.ProjectiveClosureHilbertPolynomial
public import CCDN.Center.ZeroColumnCenterDensity
public import CCDN.Center.GeometricProjectionHilbert
/-! The geometrically disjoint birational-center condition on center matrices. -/

@[expose] public section
namespace CCDN
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
      eval (matrixPluckerCoordinates (Matrix.of fun i j => x (i,j))) G := by
  have he : (eval x).comp (aeval (matrixMinorPolynomial K)).toRingHom =
      eval (matrixPluckerCoordinates (Matrix.of fun i j => x (i,j))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro c
      simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,RingHom.coe_coe,aeval_X,eval_X]
      exact matrixMinorPolynomial_eval c x
  exact RingHom.congr_fun he G

/-- The matrix rows span a center disjoint from the variety over an algebraic
closure, and the center projection generates the function field. -/
def IsBirationalMatrixCenter {K : Type*} [Field K] {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) [J.IsPrime]
    (A : Matrix (Fin r) (Fin (n + 1)) K) : Prop :=
  (∀ p ∈ projectiveIdealZeroLocus (J.map (map (algebraMap K (AlgebraicClosure K)))),
    p.rep ∉ Submodule.span (AlgebraicClosure K)
      (Set.range (A.map (algebraMap K (AlgebraicClosure K))).row)) ∧
  projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ J)) J
    (centerMinorProjectionForm A) = ⊤

lemma isBirationalMatrixCenter_congr {K : Type*} [Field K] {n r : ℕ}
    {J J' : Ideal (MvPolynomial (Fin (n + 1)) K)} [J.IsPrime] [J'.IsPrime] (h : J = J')
    (A : Matrix (Fin r) (Fin (n + 1)) K) :
    IsBirationalMatrixCenter J A ↔ IsBirationalMatrixCenter J' A := by
  subst h
  rfl

/-- A geometrically disjoint center gives an integral center projection. -/
theorem IsBirationalMatrixCenter.isIntegral {K : Type*} [Field K] {n r : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) K)} [J.IsPrime]
    {A : Matrix (Fin r) (Fin (n + 1)) K} (hgood : IsBirationalMatrixCenter J A)
    (hJ : IsHomogeneousIdeal J) (hA : LinearIndependent K A.row) (hr : r + 2 ≤ n + 1) :
    (projectionCoordinateMap J (centerMinorProjectionForm A)).IsIntegral := by
  obtain ⟨s, ⟨e⟩⟩ := exists_center_minor_coordinate_enumeration hr
  rw [← centerMinorProjectionMatrix_isIntegral_iff J A e]
  apply projection_integral_of_geometric_center_disjoint (L := AlgebraicClosure K) J hJ
  rw [centerMinorProjectionMatrix_map]
  exact centerMinorProjectionMatrix_disjoint _ _
    (linearIndependent_matrix_rows_map _ A hA) e hgood.1

/-- Full-row-rank matrices carry the topology induced by the Zariski
topology on their entries. -/
abbrev IndependentCenterMatrix (K : Type*) [Field K] (r n : ℕ) :=
  {x : Fin r × Fin n → K //
    LinearIndependent K (fun i : Fin r => fun j : Fin n => x (i,j))}

/-- The good-center locus: independent center matrices satisfying the
good-center condition. -/
def birationalMatrixCenterLocus {K : Type*} [Field K] {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) [J.IsPrime] :
    Set (IndependentCenterMatrix K r (n + 1)) :=
  {x | IsBirationalMatrixCenter J (Matrix.of fun i j => x.val (i,j))}

end
end CCDN
