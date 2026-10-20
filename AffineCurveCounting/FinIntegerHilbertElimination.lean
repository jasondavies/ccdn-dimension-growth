module

public import AffineCurveCounting.IntegerHilbertElimination
public import AffineCurveCounting.IntegerLinearForms
public import AffineCurveCounting.FilteredHilbertEquiv

/-! One bounded integer-matrix elimination step on the standard Fin-indexed
polynomial rings, ready for iteration. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

def finEliminationMatrix {n : ℕ} (b : Option (Fin n) → ℤ) :
    Fin n → Fin (n + 1) → ℤ :=
  fun i => Fin.cases (-b (some i)) (fun j => if j = i then b none else 0)

lemma integerLinearForm_finEliminationMatrix {n : ℕ}
    (b : Option (Fin n) → ℤ) (i : Fin n) :
    integerLinearForm (finEliminationMatrix b i) =
      C (b none : ℚ) * X i.succ - C (b (some i) : ℚ) * X 0 := by
  rw [integerLinearForm, Fin.sum_univ_succ]
  simp [finEliminationMatrix, apply_ite, ite_mul, sub_eq_add_neg, add_comm]

lemma finEliminationMatrix_height {n d : ℕ} (b : Option (Fin n) → ℤ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ d + 1) (i : Fin n) (j : Fin (n + 1)) :
    |finEliminationMatrix b i j| ≤ d + 1 := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [finEliminationMatrix, Fin.cases_zero, abs_neg,
      abs_of_nonneg (hb (some i)).1] using (hb (some i)).2
  · by_cases he : j = i
    · simpa only [finEliminationMatrix, Fin.cases_succ, he, ite_true,
        abs_of_nonneg (hb none).1] using (hb none).2
    · simp only [finEliminationMatrix, Fin.cases_succ, ite_eq_right he, abs_zero]
      positivity

theorem exists_fin_integer_elimination_step {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime] (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hcodim : m < n)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (m + 1).factorial) :
    ∃ (c : Fin n → Fin (n + 1) → ℤ) (e : ℕ),
      (∀ i j, |c i j| ≤ d + 1) ∧ 0 < e ∧ e ≤ d ∧
      let ψ := projectionCoordinateMap I (fun i => integerLinearForm (c i))
      ψ.IsIntegral ∧ (RingHom.ker ψ).IsPrime ∧
      (filteredHilbertPolynomial (RingHom.ker ψ)).natDegree = m + 1 ∧
      (filteredHilbertPolynomial (RingHom.ker ψ)).leadingCoeff =
        (e : ℚ) / (m + 1).factorial := by
  let e := renameEquiv ℚ (finSuccEquiv n)
  let : LinearOrder (Option (Fin n)) :=
    LinearOrder.lift' (finSuccEquiv n).symm (finSuccEquiv n).symm.injective
  let J := I.map e
  have hJ : J = I.map
      (e : MvPolynomial (Fin (n + 1)) ℚ →+* MvPolynomial (Option (Fin n)) ℚ) := rfl
  let : J.IsPrime := Ideal.map_isPrime_of_equiv e
  have hpoly : filteredHilbertPolynomial I = filteredHilbertPolynomial J :=
    filteredHilbertPolynomial_renameEquiv I (finSuccEquiv n)
  obtain ⟨b, hb, hbound, hint⟩ :=
    exists_multiplicity_bounded_integral_linear_elimination J d
      (by rw [← hpoly]; exact hdim) (by simpa only [Fintype.card_fin] using hcodim)
      (by rw [← hpoly]; exact hdegree)
  rw [coordinateEliminationMap_eq_projection] at hint
  have hint' := integerEliminationMap_isIntegral J b hb hint
  let φ := (Ideal.quotientEquivAlg I J e hJ).symm
  have hφ : φ.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ φ.surjective
  have hcomp := RingHom.IsIntegral.trans
    (projectionCoordinateMap J (integerEliminationCoordinates b)).toRingHom φ.toRingHom hint' hφ
  let c := finEliminationMatrix b
  have heq : φ.toAlgHom.comp (projectionCoordinateMap J (integerEliminationCoordinates b)) =
      projectionCoordinateMap I (fun i => integerLinearForm (c i)) := by
    ext i
    simp only [AlgHom.comp_apply, projectionCoordinateMap, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    change φ ((Ideal.Quotient.mk J) (integerEliminationCoordinates b i)) =
      (Ideal.Quotient.mk I) (integerLinearForm (c i))
    dsimp only [φ]
    rw [Ideal.quotientEquivAlg_symm, Ideal.quotientEquivAlg_mk]
    apply congrArg (Ideal.Quotient.mk I)
    rw [integerLinearForm_finEliminationMatrix]
    simp [e, integerEliminationCoordinates]
  change (φ.toAlgHom.comp
    (projectionCoordinateMap J (integerEliminationCoordinates b))).IsIntegral at hcomp
  rw [heq] at hcomp
  obtain ⟨hdim', e', he', hed, hdegree'⟩ :=
    integral_linear_projection_multiplicity I (fun i => integerLinearForm (c i))
      (fun i => integerLinearForm_degree (c i)) hcomp d (by simpa only [hdim] using hdegree)
  exact ⟨c, e', finEliminationMatrix_height b hbound, he', hed, hcomp,
    RingHom.ker_isPrime _, hdim'.trans hdim, by simpa only [hdim] using hdegree'⟩

end
end AffineCurveCounting
