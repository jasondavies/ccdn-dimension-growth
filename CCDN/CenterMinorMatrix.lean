module

public import CCDN.CenterMinorProjection
public import CCDN.PolynomialPredicates

/-! Enumerating the maximal-minor coordinates turns the source's
Plücker projection into a matrix with exactly the center as its kernel.
This connects the literal center projection to the Chow specialization results. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

lemma exists_center_minor_coordinate_enumeration {r n : ℕ} (hr : r + 2 ≤ n) :
    ∃ s : ℕ, Nonempty (Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin n)) := by
  classical
  let e₀ : Fin (r + 1) ↪ Fin n :=
    ⟨fun i => Fin.castLE hr i.castSucc,
      (Fin.castLE_injective hr).comp (Fin.castSucc_injective (r + 1))⟩
  let e₁ : Fin (r + 1) ↪ Fin n :=
    ⟨fun i => Fin.castLE hr i.succ,
      (Fin.castLE_injective hr).comp (Fin.succ_injective (r + 1))⟩
  have hne : e₀ ≠ e₁ := by
    intro he
    have hh := congrArg (fun e : Fin (r + 1) ↪ Fin n => (e 0).val) he
    change 0 = 1 at hh
    omega
  have hcard : 2 ≤ Fintype.card (Fin (r + 1) ↪ Fin n) :=
    Fintype.one_lt_card_iff.mpr ⟨e₀, e₁, hne⟩
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hcard
  refine ⟨s, ⟨?_⟩⟩
  have he : s + 2 = Fintype.card (Fin (r + 1) ↪ Fin n) := by omega
  exact (finCongr he).trans (Fintype.equivFin _).symm

/-- Every entry is a degree-one polynomial evaluated at the center
Plücker coordinates. The enumeration only orders the maximal minors. -/
def centerMinorProjectionMatrix {K : Type*} [Field K] {r n s : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin n)) :
    Matrix (Fin (s + 1)) (Fin n) K :=
  fun i j => eval (fun c : Fin r ↪ Fin n => (A.submatrix id c).det)
    (centerPluckerCoefficient (e i) j)

lemma centerMinorProjectionMatrix_form {K : Type*} [Field K] {r n s : ℕ}
    (A : Matrix (Fin r) (Fin (n + 1)) K)
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin (n + 1))) (i : Fin (s + 1)) :
    chowProjectionForms (centerMinorProjectionMatrix A e) i = centerMinorProjectionForm A (e i) :=
  (centerMinorProjectionForm_eq_plucker_coefficients A (e i)).symm

lemma centerMinorProjectionMatrix_mulVec {K : Type*} [Field K] {r n s : ℕ}
    (A : Matrix (Fin r) (Fin (n + 1)) K)
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin (n + 1))) (x : Fin (n + 1) → K) :
    centerMinorProjectionMatrix A e *ᵥ x = fun i => centerMinorProjection A x (e i) := by
  funext i
  rw [← chowProjectionForms_eval, centerMinorProjectionMatrix_form,
    centerMinorProjectionForm_eval]

/-- The matrix kernel equals the linear center specified by its rows. -/
theorem centerMinorProjectionMatrix_ker {K : Type*} [Field K] {r n s : ℕ}
    (A : Matrix (Fin r) (Fin (n + 1)) K) (hA : LinearIndependent K A.row)
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin (n + 1))) :
    (centerMinorProjectionMatrix A e).mulVecLin.ker =
      Submodule.span K (Set.range A.row) := by
  ext x
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, centerMinorProjectionMatrix_mulVec,
    ← centerMinorProjection_eq_zero_iff A hA]
  constructor
  · intro h
    funext c
    simpa only [e.apply_symm_apply, Pi.zero_apply] using congrFun h (e.symm c)
  · intro h
    funext i
    exact congrFun h (e i)

lemma centerMinorProjectionMatrix_disjoint {K : Type*} [Field K] {r n s : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (A : Matrix (Fin r) (Fin (n + 1)) K) (hA : LinearIndependent K A.row)
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin (n + 1)))
    (hcenter : ∀ p ∈ projectiveIdealZeroLocus J,
      p.rep ∉ Submodule.span K (Set.range A.row)) :
    ∀ p ∈ projectiveIdealZeroLocus J, centerMinorProjectionMatrix A e *ᵥ p.rep ≠ 0 := by
  intro p hp hz
  apply hcenter p hp
  rw [← centerMinorProjectionMatrix_ker A hA e]
  exact hz

end
end CCDN
