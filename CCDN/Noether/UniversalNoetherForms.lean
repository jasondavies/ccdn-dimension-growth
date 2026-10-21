module

public import CCDN.Noether.AmbientNoetherHeight
public import CCDN.Noether.AmbientNoetherNonvanishing
/-! A finite family of universal integer Noether forms, with the exact
degree and coefficient bound of CCDN Theorem 3.2.2. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma finite_homogeneous_coefficientL1_bounded (σ : Type*) [Fintype σ] [DecidableEq σ]
    (r H : ℕ) :
    {f : MvPolynomial σ ℤ | f.IsHomogeneous r ∧ l1Norm f ≤ H}.Finite := by
  classical
  let C := ↥(Finset.Icc (-(H : ℤ)) (H : ℤ))
  let F : (Sym σ r → C) → MvPolynomial σ ℤ :=
    fun c => ∑ i, monomial (homogeneousCoefficientExponent σ r i) (c i).val
  apply (Set.finite_range F).subset
  intro f hf
  let c : Sym σ r → C := fun i => ⟨f.coeff (homogeneousCoefficientExponent σ r i), by
    have hh := (natAbs_coeff_le_l1Norm f (homogeneousCoefficientExponent σ r i)).trans hf.2
    have ha : |f.coeff (homogeneousCoefficientExponent σ r i)| ≤ (H : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hh
    exact Finset.mem_Icc.mpr (abs_le.mp ha)⟩
  refine ⟨c, ?_⟩
  exact homogeneousCoefficientData_reconstruct r f hf.1

lemma finite_ambientNoetherForms (σ : Type*) [Fintype σ] [DecidableEq σ] (k : ℕ) :
    {f | ∃ rows cols m, f = ambientNoetherForm σ k rows cols m}.Finite := by
  apply (finite_homogeneous_coefficientL1_bounded (Sym σ (k + 2))
    ((k + 2) ^ 2 - 1)
    ((k + 2) ^ (3 * (k + 2) ^ 2 - 3) *
      (Fintype.card (Sym σ (k + 2)) * 3 ^ (k + 2)) ^ ((k + 2) ^ 2 - 1))).subset
  rintro f ⟨rows,cols,m,rfl⟩
  exact ⟨ambientNoetherForm_homogeneous σ k rows cols m,
    ambientNoetherForm_coefficientL1_le σ k rows cols m⟩

/-- The finite collection consists precisely of the extracted coefficients
of all Euler minors of the universal plane restriction. -/
def universalNoetherForms (σ : Type*) [Fintype σ] [DecidableEq σ] (k : ℕ) :
    Finset (MvPolynomial (Sym σ (k + 2)) ℤ) :=
  (finite_ambientNoetherForms σ k).toFinset

lemma mem_universalNoetherForms {σ : Type*} [Fintype σ] [DecidableEq σ]
    (k : ℕ) (f : MvPolynomial (Sym σ (k + 2)) ℤ) :
    f ∈ universalNoetherForms σ k ↔ ∃ rows cols m, f = ambientNoetherForm σ k rows cols m := by
  exact Set.Finite.mem_toFinset _

theorem universalNoetherForms_homogeneous {σ : Type*} [Fintype σ] [DecidableEq σ]
    (k : ℕ) (g : MvPolynomial (Sym σ (k + 2)) ℤ)
    (hg : g ∈ universalNoetherForms σ k) :
    g.IsHomogeneous ((k + 2) ^ 2 - 1) := by
  obtain ⟨rows,cols,m,rfl⟩ := (mem_universalNoetherForms k g).mp hg
  exact ambientNoetherForm_homogeneous σ k rows cols m

lemma card_homogeneousCoefficientIndices (n d : ℕ) :
    Fintype.card (Sym (Option (Fin n)) d) = (n + d).choose n := by
  rw [Sym.card_sym_eq_choose, Fintype.card_option, Fintype.card_fin]
  have he : n + 1 + d - 1 = n + d := by omega
  rw [he, ← Nat.choose_symm (show d ≤ n + d by omega)]
  congr 1
  omega

/-- The printed integer coefficient bound, with n+1 homogeneous variables. -/
theorem universalNoetherForms_coefficientL1_le (n k : ℕ)
    (g : MvPolynomial (Sym (Option (Fin n)) (k + 2)) ℤ)
    (hg : g ∈ universalNoetherForms (Option (Fin n)) k) :
    l1Norm g ≤
      (k + 2) ^ (3 * (k + 2) ^ 2 - 3) *
        ((n + (k + 2)).choose n * 3 ^ (k + 2)) ^ ((k + 2) ^ 2 - 1) := by
  obtain ⟨rows,cols,m,rfl⟩ := (mem_universalNoetherForms k g).mp hg
  simpa only [card_homogeneousCoefficientIndices] using
    ambientNoetherForm_coefficientL1_le (Option (Fin n)) k rows cols m

/-- Every form vanishes on a geometrically reducible equation, over an
arbitrary field, with no characteristic assumption. -/
theorem universalNoetherForms_vanish {K σ : Type*} [Field K]
    [Fintype σ] [DecidableEq σ]
    (k : ℕ) (f : MvPolynomial σ K) (hf : f.IsHomogeneous (k + 2))
    (hred : ¬Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (g : MvPolynomial (Sym σ (k + 2)) ℤ)
    (hg : g ∈ universalNoetherForms σ k) :
    homogeneousCoefficientSpecialization (k + 2) f g = 0 := by
  obtain ⟨rows,cols,m,rfl⟩ := (mem_universalNoetherForms k g).mp hg
  exact ambientNoetherForm_eq_zero_of_not_absolutely_irreducible k f hf hred rows cols m

/-- In characteristic zero, an absolutely irreducible equation makes at
least one member of the same finite universal collection nonzero. -/
theorem universalNoetherForms_nonvanishing {K σ : Type*} [Field K] [CharZero K]
    [Fintype σ] [DecidableEq σ]
    (k : ℕ) (f : MvPolynomial (Option σ) K) (hf : f.IsHomogeneous (k + 2))
    (hir : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f)) :
    ∃ g ∈ universalNoetherForms (Option σ) k,
      homogeneousCoefficientSpecialization (k + 2) f g ≠ 0 := by
  obtain ⟨rows,cols,m,hne⟩ := exists_ambientNoetherForm_nonzero k f hf hir
  exact ⟨_, (mem_universalNoetherForms _ _).mpr ⟨rows,cols,m,rfl⟩, hne⟩

/-- The finite universal family detects absolute irreducibility exactly
in characteristic zero. The reverse implication is valid in all characteristics. -/
theorem universalNoetherForms_irreducible_iff {K σ : Type*} [Field K] [CharZero K]
    [Fintype σ] [DecidableEq σ]
    (k : ℕ) (f : MvPolynomial (Option σ) K) (hf : f.IsHomogeneous (k + 2)) :
    Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f) ↔
      ∃ g ∈ universalNoetherForms (Option σ) k,
        homogeneousCoefficientSpecialization (k + 2) f g ≠ 0 := by
  refine ⟨universalNoetherForms_nonvanishing k f hf, ?_⟩
  rintro ⟨g,hg,hne⟩
  by_contra hred
  exact hne (universalNoetherForms_vanish k f hf hred g hg)

end
end CCDN
