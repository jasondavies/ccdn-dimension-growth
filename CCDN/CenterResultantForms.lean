module

public import CCDN.GenericBlockLineHomogeneity
public import CCDN.UniversalCenterChowRestriction
public import CCDN.ChowProjectionCriterion

/-! A derivative-resultant family for one hyperplane block of the actual
universal center restriction. The Pluecker degree is D(2d-1). -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

def chowRowBlock {q s : ℕ} (i : Fin q) : Fin q × Fin s → Bool :=
  fun p => decide (p.1 = i)

lemma genericBlockWeight_chowRowBlock {q s : ℕ} (i : Fin q) :
    genericBlockWeight (chowRowBlock (s := s) i) = chowRowWeight i := by
  funext p
  simp [genericBlockWeight,chowRowBlock,chowRowWeight]

lemma weightedTotalDegree_of_nonzero_homogeneous
    {R σ : Type*} [CommSemiring R] (w : σ → ℕ)
    (f : MvPolynomial σ R) (d : ℕ)
    (hf : f.IsWeightedHomogeneous w d) (hf0 : f ≠ 0) :
    f.weightedTotalDegree w = d := by
  have he := hf.weighted_total_degree hf0
  rw [weightedTotalDegree_coe w f hf0] at he
  exact WithBot.coe_injective he

lemma genericBlockLine_chowRow_natDegree
    {K : Type*} [Field K] {n s q : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K) (i : Fin q)
    (F : MvPolynomial (Fin q × Fin (n + 1)) K) (d : ℕ)
    (hF : F.IsWeightedHomogeneous (chowRowWeight i) d)
    (hR : chowLinearSubstitution A F ≠ 0) :
    (genericBlockLine (chowRowBlock i) (chowLinearSubstitution A F)).natDegree = d := by
  rw [genericBlockLine_natDegree,genericBlockWeight_chowRowBlock]
  exact weightedTotalDegree_of_nonzero_homogeneous _ _ d
    (chowLinearSubstitution_row_homogeneous A i F d hF) hR

def centerRowResultantFamily
    {K : Type*} [Field K] {r n s q : ℕ}
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin n)) (i : Fin q)
    (F : MvPolynomial (Fin q × Fin n) K) (d : ℕ) :
    Finset (MvPolynomial (Fin r ↪ Fin n) K) :=
  derivativeResultantCoefficientFamily
    (genericBlockLine (chowRowBlock i) (universalCenterChowMap e F)) d

theorem centerRowResultantFamily_homogeneous
    {K : Type*} [Field K] {r n s q D : ℕ}
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin n)) (i : Fin q)
    (F : MvPolynomial (Fin q × Fin n) K) (d : ℕ) (hd : 0 < d)
    (hF : F.IsHomogeneous D) :
    ∀ g ∈ centerRowResultantFamily e i F d, g.IsHomogeneous (D * (2 * d - 1)) :=
  genericBlockLine_resultant_family_homogeneous _ _ d D hd
    (universalCenterChowMap_coefficient_homogeneous e F hF)

theorem centerRowResultantFamily_totalDegree_le
    {K : Type*} [Field K] {r n s q D : ℕ}
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin n)) (i : Fin q)
    (F : MvPolynomial (Fin q × Fin n) K) (d : ℕ) (hd : 0 < d)
    (hF : F.IsHomogeneous D) :
    ∀ g ∈ centerRowResultantFamily e i F d, g.totalDegree ≤ D * (2 * d - 1) := by
  intro g hg
  exact (centerRowResultantFamily_homogeneous e i F d hd hF g hg).totalDegree_le

/-- Specialization is exact even when the restricted source equation is
zero; no disjointness or degree-preservation premise is hidden here. -/
theorem centerRowResultantFamily_nonvanishing_iff
    {K : Type*} [Field K] {r n s q : ℕ}
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin (n + 1))) (i : Fin q)
    (F : MvPolynomial (Fin q × Fin (n + 1)) K) (d : ℕ)
    (A : Matrix (Fin r) (Fin (n + 1)) K) :
    (∃ g ∈ centerRowResultantFamily e i F d,
      eval (fun c : Fin r ↪ Fin (n + 1) => (A.submatrix id c).det) g ≠ 0) ↔
    derivativeResultant (genericBlockLine (chowRowBlock i)
      (chowLinearSubstitution (centerMinorProjectionMatrix A e) F)) d ≠ 0 := by
  have he := derivativeResultantCoefficientFamily_nonvanishing_iff
    (genericBlockLine (chowRowBlock i) (universalCenterChowMap e F)) d (RingHom.id K)
    (fun c : Fin r ↪ Fin (n + 1) => (A.submatrix id c).det)
  change (∃ g ∈ centerRowResultantFamily e i F d,
    eval (fun c : Fin r ↪ Fin (n + 1) => (A.submatrix id c).det) g ≠ 0) ↔
    derivativeResultant
      ((genericBlockLine (chowRowBlock i) (universalCenterChowMap e F)).map
        (MvPolynomial.map (eval (fun c : Fin r ↪ Fin (n + 1) => (A.submatrix id c).det)))) d ≠ 0 at he
  rwa [genericBlockLine_map,universalCenterChowMap_specialize] at he

end
end CCDN
