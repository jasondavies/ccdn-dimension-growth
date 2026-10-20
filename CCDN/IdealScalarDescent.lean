module

public import CCDN.HilbertScalarExtension
public import CCDN.LowDegreePointSeparation

/-! Coefficient-linear descent detects nonmembership in scalar-extended
ideals, and descends degree-bounded separating equations. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma coefficientLinearPolynomial_sub {K L : Type*}
    [Field K] [Field L] [Algebra K L] {n : ℕ}
    (φ : L →ₗ[K] K) (f g : MvPolynomial (Fin n) L) :
    coefficientLinearPolynomial φ (f - g) =
      coefficientLinearPolynomial φ f - coefficientLinearPolynomial φ g := by
  ext a
  simp [coefficientLinearPolynomial_coeff]

lemma coefficientLinearPolynomial_map_of_one {K L : Type*}
    [Field K] [Field L] [Algebra K L] {n : ℕ}
    (φ : L →ₗ[K] K) (hφ : φ 1 = 1) (f : MvPolynomial (Fin n) K) :
    coefficientLinearPolynomial φ (map (algebraMap K L) f) = f := by
  ext a
  rw [coefficientLinearPolynomial_coeff, coeff_map]
  have hh := φ.map_smul (f.coeff a) (1 : L)
  simpa only [Algebra.smul_def, mul_one, hφ, Algebra.algebraMap_self,
    RingHom.id_apply] using hh

theorem mem_ideal_scalar_extension_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin n) K) :
    map (algebraMap K L) f ∈ I.map (map (algebraMap K L)) ↔ f ∈ I := by
  constructor
  · intro h
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : L) ≠ 0)
    have hh := coefficientLinearPolynomial_mem_scalar_extension I _ h φ
    rwa [coefficientLinearPolynomial_map_of_one φ hφ] at hh
  · exact Ideal.mem_map_of_mem _

theorem scalar_extension_not_le
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) K)) (hIJ : ¬ I ≤ J) :
    ¬ I.map (map (algebraMap K L)) ≤ J.map (map (algebraMap K L)) := by
  intro h
  apply hIJ
  intro f hf
  exact (mem_ideal_scalar_extension_iff J f).mp (h (Ideal.mem_map_of_mem _ hf))

/-- Some coefficient functional detects nonmembership in an extended ideal.
No basis, coefficient decomposition or separating functional is supplied. -/
theorem exists_coefficientLinearPolynomial_not_mem
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) K)) (g : MvPolynomial (Fin n) L)
    (hg : g ∉ J.map (map (algebraMap K L))) :
    ∃ φ : L →ₗ[K] K, coefficientLinearPolynomial φ g ∉ J := by
  classical
  let J' := J.map (map (algebraMap K L))
  obtain ⟨r, hrstd, _, hrJ⟩ := exists_standard_representative J' g
  have hr0 : r ≠ 0 := by intro h; exact hg (by simpa only [h, sub_zero] using hrJ)
  obtain ⟨a, ha⟩ := exists_coeff_ne_zero hr0
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero K ha
  refine ⟨φ, ?_⟩
  intro hgJ
  have hdJ := coefficientLinearPolynomial_mem_scalar_extension J (g - r) hrJ φ
  rw [coefficientLinearPolynomial_sub] at hdJ
  have hrmem : coefficientLinearPolynomial φ r ∈ J := by
    have hh := J.sub_mem hgJ hdJ
    simpa only [sub_sub_cancel] using hh
  have hrstdK : coefficientLinearPolynomial φ r ∈
      restrictSupport K (standardExponents J MonomialOrder.degLex) := by
    intro b hb
    have hbr : b ∈ r.support := by
      change b ∈ (coefficientLinearPolynomial φ r).support at hb
      rw [mem_support_iff] at hb ⊢
      intro hzero
      apply hb
      rw [coefficientLinearPolynomial_coeff, hzero, map_zero]
    have hh := hrstd hbr
    simpa only [J', standardExponents_scalar_extension] using hh
  have hrzero := standard_polynomial_eq_zero J MonomialOrder.degLex hrstdK hrmem
  have hc := coefficientLinearPolynomial_coeff φ r a
  have hz : φ (r.coeff a) = 0 := by simpa [hrzero] using hc.symm
  exact hφ hz

/-- Low-degree separation descends from any algebraically closed extension
over which both actual ideals stay prime. -/
theorem exists_low_degree_ideal_separator_of_geometrically_prime
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) K))
    [I.IsPrime] [J.IsPrime]
    [(I.map (map (algebraMap K L))).IsPrime]
    [(J.map (map (algebraMap K L))).IsPrime]
    (d : ℕ)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial)
    (hIJ : ¬ I ≤ J) :
    ∃ f : MvPolynomial (Fin n) K, f ∈ I ∧ f.totalDegree ≤ d ∧ f ∉ J := by
  let : CharZero L := Algebra.charZero_of_charZero K L
  obtain ⟨g, hgI, hgd, hgJ⟩ := exists_low_degree_ideal_separator
    (I.map (map (algebraMap K L))) (J.map (map (algebraMap K L))) d
    (by simpa only [filteredHilbertPolynomial_scalar_extension] using hdegree)
    (scalar_extension_not_le I J hIJ)
  obtain ⟨φ, hφ⟩ := exists_coefficientLinearPolynomial_not_mem J g hgJ
  exact ⟨coefficientLinearPolynomial φ g,
    coefficientLinearPolynomial_mem_scalar_extension I g hgI φ,
    (coefficientLinearPolynomial_degree φ g).trans hgd, hφ⟩

end
end CCDN
