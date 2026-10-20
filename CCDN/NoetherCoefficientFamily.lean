module

public import CCDN.UniversalNoetherForms
public import CCDN.CoefficientwiseSubstitution
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-! Finite Noether detectors for polynomial coefficient families.
Composition multiplies the coefficient degree by D^2-1; no quadratic
degree bound for the composed equations is assumed. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma coefficient_homogeneous_rename_equiv
    {K σ τ υ : Type*} [CommRing K] (e : τ ≃ υ)
    (p : MvPolynomial τ (MvPolynomial σ K)) (E : ℕ)
    (hp : ∀ a, (p.coeff a).IsHomogeneous E) :
    ∀ a, ((rename e p).coeff a).IsHomogeneous E := by
  intro a
  have he : (a.mapDomain e.symm).mapDomain e = a := by
    rw [← Finsupp.mapDomain_comp]
    simp only [Equiv.self_comp_symm, Finsupp.mapDomain_id]
  rw [← he, coeff_rename_mapDomain e e.injective]
  exact hp _

lemma homogeneousCoefficientSpecialization_homogeneous_field
    {K σ τ : Type*} [Field K] [Fintype τ] [DecidableEq τ]
    (d E r : ℕ) (p : MvPolynomial τ (MvPolynomial σ K))
    (hp : ∀ a, (p.coeff a).IsHomogeneous E)
    (Φ : MvPolynomial (Sym τ d) ℤ) (hΦ : Φ.IsHomogeneous r) :
    (homogeneousCoefficientSpecialization d p Φ).IsHomogeneous (E * r) := by
  apply hΦ.eval₂
  · intro z
    simpa using isHomogeneous_C σ (z : K)
  · intro i
    exact hp (homogeneousCoefficientExponent τ d i)

/-- The finite equations are constructed by substitution into the
universal integer Noether forms. All of them have homogeneous degree
E(D^2-1), and their common zero set is exactly the locus of geometrically
reducible specialized equations. Polynomial variables may be any nonempty
finite type; the temporary distinguished variable is chosen internally. -/
theorem exists_noether_coefficient_family
    {K σ τ : Type*} [Field K] [CharZero K] [Fintype τ] [Nonempty τ]
    (k E : ℕ) (p : MvPolynomial τ (MvPolynomial σ K))
    (hp : p.IsHomogeneous (k + 2))
    (hc : ∀ a, (p.coeff a).IsHomogeneous E) :
    ∃ Φ : Finset (MvPolynomial σ K),
      (∀ g ∈ Φ, g.IsHomogeneous (E * ((k + 2) ^ 2 - 1))) ∧
      ∀ u : σ → K,
        (∃ g ∈ Φ, eval u g ≠ 0) ↔
          Irreducible (map (algebraMap K (AlgebraicClosure K)) (map (eval u) p)) := by
  classical
  let t : τ := Classical.choice ‹Nonempty τ›
  let e := (Equiv.optionSubtypeNe t).symm
  let q := rename e p
  have hq : q.IsHomogeneous (k + 2) := hp.rename_isHomogeneous
  have hqc : ∀ a, (q.coeff a).IsHomogeneous E :=
    coefficient_homogeneous_rename_equiv e p E hc
  let Φ := (universalNoetherForms (Option {i : τ // i ≠ t}) k).image
    (homogeneousCoefficientSpecialization (k + 2) q)
  refine ⟨Φ, ?_, ?_⟩
  · intro g hg
    obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hg
    exact homogeneousCoefficientSpecialization_homogeneous_field _ _ _ q hqc φ
      (universalNoetherForms_homogeneous k φ hφ)
  · intro u
    have hi := universalNoetherForms_irreducible_iff k (map (eval u) q) (hq.map (eval u))
    have heq : Irreducible (map (algebraMap K (AlgebraicClosure K)) (map (eval u) q)) ↔
        Irreducible (map (algebraMap K (AlgebraicClosure K)) (map (eval u) p)) := by
      dsimp only [q]
      rw [map_rename, map_rename]
      exact MulEquiv.irreducible_iff (renameEquiv (AlgebraicClosure K) e)
    rw [← heq, hi]
    constructor
    · rintro ⟨g, hg, hne⟩
      obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hg
      exact ⟨φ, hφ, by rwa [← homogeneousCoefficientSpecialization_map]⟩
    · rintro ⟨φ, hφ, hne⟩
      refine ⟨_, Finset.mem_image.mpr ⟨φ, hφ, rfl⟩, ?_⟩
      rwa [homogeneousCoefficientSpecialization_map]

lemma homogeneous_linear_irreducible_iff_ne_zero
    {K τ : Type*} [Field K] (p : MvPolynomial τ K) (hp : p.IsHomogeneous 1) :
    Irreducible p ↔ p ≠ 0 := by
  refine ⟨fun h => h.ne_zero, fun h => ?_⟩
  apply irreducible_of_totalDegree_eq_one (hp.totalDegree h)
  intro c hc
  apply isUnit_iff_ne_zero.mpr
  intro hc0
  subst c
  apply h
  ext m
  simpa using hc m

/-- A detector in every positive degree. The degree-one boundary uses the
coefficients, so its degree is E rather than the impossible bound zero. -/
theorem exists_homogeneous_coefficient_detector
    {K σ τ : Type*} [Field K] [CharZero K] [Fintype τ] [Nonempty τ]
    (D E : ℕ) (hD : 0 < D) (p : MvPolynomial τ (MvPolynomial σ K))
    (hp : p.IsHomogeneous D) (hc : ∀ a, (p.coeff a).IsHomogeneous E) :
    ∃ Φ : Finset (MvPolynomial σ K),
      (∀ g ∈ Φ, g.IsHomogeneous (E * max 1 (D ^ 2 - 1))) ∧
      ∀ u : σ → K,
        (∃ g ∈ Φ, eval u g ≠ 0) ↔
          Irreducible (map (algebraMap K (AlgebraicClosure K)) (map (eval u) p)) := by
  classical
  by_cases hD1 : D = 1
  · subst D
    refine ⟨p.support.image p.coeff, ?_, ?_⟩
    · intro g hg
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hg
      simpa using hc a
    · intro u
      rw [homogeneous_linear_irreducible_iff_ne_zero _
        ((hp.map (eval u)).map (algebraMap K (AlgebraicClosure K)))]
      rw [map_ne_zero_iff (map (algebraMap K (AlgebraicClosure K)))
        (map_injective (algebraMap K (AlgebraicClosure K))
          (algebraMap K (AlgebraicClosure K)).injective)]
      constructor
      · rintro ⟨g, hg, hne⟩ hz
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hg
        apply hne
        have hh := congrArg (fun q => q.coeff a) hz
        simpa only [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hh
      · intro hne
        obtain ⟨a, ha⟩ := exists_coeff_ne_zero hne
        rw [coeff_map] at ha
        have hm : a ∈ p.support := mem_support_iff.mpr (fun hz => ha (by rw [hz, map_zero]))
        exact ⟨p.coeff a, Finset.mem_image.mpr ⟨a, hm, rfl⟩, ha⟩
  · obtain ⟨k, rfl⟩ : ∃ k, D = k + 2 := ⟨D - 2, by omega⟩
    have hmax : max 1 ((k + 2) ^ 2 - 1) = (k + 2) ^ 2 - 1 := by
      apply max_eq_right
      have hh : 4 ≤ (k + 2) ^ 2 := by nlinarith
      omega
    simpa only [hmax] using exists_noether_coefficient_family k E p hp hc

end
end CCDN
