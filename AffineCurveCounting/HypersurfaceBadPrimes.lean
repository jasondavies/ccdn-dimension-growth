module

public import AffineCurveCounting.UniversalPlaneBadReduction
public import Mathlib.Data.Nat.PrimeFin

/-! The actual finite set of bad primes of an integer hypersurface. The
coefficient-height estimate for its charge is a separate remaining step. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

def HypersurfaceBadReduction {σ : Type*} (f : MvPolynomial σ ℤ) (p : ℕ) : Prop :=
  ∃ hp : p.Prime, let _ : Fact p.Prime := ⟨hp⟩
    (MvPolynomial.map (Int.castRingHom (AlgebraicClosure (ZMod p))) f).totalDegree ≠ f.totalDegree ∨
      ¬Irreducible (MvPolynomial.map (Int.castRingHom (AlgebraicClosure (ZMod p))) f)

/-- A positive actual integer and the exact finite bad-prime set above the
degree. No height, finite-set or reduction assumptions are supplied. -/
theorem exists_hypersurface_bad_prime_set
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) :
    ∃ (D : ℤ) (B : Finset ℕ), 0 < D ∧
      (∀ p, p ∈ B ↔ f.totalDegree < p ∧ HypersurfaceBadReduction f p) ∧
      (∀ p ∈ B, (p : ℤ) ∣ D) := by
  classical
  obtain ⟨rows, cols, e, he, hdiv⟩ := exists_integer_hypersurface_bad_prime_witness f hf hpos
  let D := |(universalPlaneBadWitness f rows cols).coeff e|
  have hD : 0 < D := abs_pos.mpr he
  have hdiv' (p : ℕ) (hp : f.totalDegree < p) (hbad : HypersurfaceBadReduction f p) :
      (p : ℤ) ∣ D := by
    obtain ⟨hpp, hbad⟩ := hbad
    let : Fact p.Prime := ⟨hpp⟩
    exact (dvd_abs _ _).mpr (hdiv p hp hbad)
  let B := D.natAbs.primeFactors.filter (fun p => f.totalDegree < p ∧ HypersurfaceBadReduction f p)
  have hmem (p : ℕ) : p ∈ B ↔ f.totalDegree < p ∧ HypersurfaceBadReduction f p := by
    constructor
    · exact fun h => (Finset.mem_filter.mp h).2
    · intro hp
      apply Finset.mem_filter.mpr
      refine ⟨Nat.mem_primeFactors.mpr ⟨hp.2.choose, ?_, Int.natAbs_ne_zero.mpr hD.ne'⟩, hp⟩
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr (hdiv' p hp.1 hp.2)
  exact ⟨D, B, hD, hmem, fun p hp => hdiv' p ((hmem p).mp hp).1 ((hmem p).mp hp).2⟩

/-- Finiteness of the paper's bad-prime set above 27*d^4. A stronger set above
d is finite; filtering it gives the exact prescribed cutoff. -/
theorem finite_hypersurface_bad_primes
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) :
    {p : ℕ | 27 * f.totalDegree ^ 4 < p ∧ HypersurfaceBadReduction f p}.Finite := by
  obtain ⟨_, B, _, hmem, _⟩ := exists_hypersurface_bad_prime_set f hf hpos
  apply B.finite_toSet.subset
  intro p hp
  apply (hmem p).mpr
  refine ⟨?_, hp.2⟩
  have h1 := Nat.le_mul_self f.totalDegree
  have h2 := Nat.le_mul_self (f.totalDegree * f.totalDegree)
  nlinarith [hp.1]

end
end AffineCurveCounting
