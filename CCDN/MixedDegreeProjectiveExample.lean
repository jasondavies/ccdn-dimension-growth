module

public import CCDN.ProjectiveReduction
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Why primitive projective evaluation requires a common column degree.

For every prime `p > s`, the primitive points `(i+1,p,0)`, `0 ≤ i < s`,
lie on the line `X₂ = 0` and all reduce to `[1:0:0]`. Nevertheless the
homogeneous columns `1,X₀,...,X₀^(s-1)` have determinant prime to `p`.
Thus arbitrary column degrees require chart-normalized evaluation; the
normalizing powers cannot be removed as one unit factor per row. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def mixedDegreeLinePoint (p a : ℕ) : Fin 3 → ℤ := ![(a : ℤ), (p : ℤ), 0]

lemma mixedDegreeLinePoint_primitive {p a : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hap : a < p) :
    Finset.univ.gcd (mixedDegreeLinePoint p a) = 1 := by
  have hcop : IsCoprime (p : ℤ) (a : ℤ) :=
    (Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr (by
      exact_mod_cast Nat.not_dvd_of_pos_of_lt ha hap)
  obtain ⟨u, v, huv⟩ := hcop
  have hda := Finset.gcd_dvd (f := mixedDegreeLinePoint p a)
    (Finset.mem_univ (0 : Fin 3))
  have hdp := Finset.gcd_dvd (f := mixedDegreeLinePoint p a)
    (Finset.mem_univ (1 : Fin 3))
  have hd : Finset.univ.gcd (mixedDegreeLinePoint p a) ∣ (1 : ℤ) := by
    rw [← huv]
    exact dvd_add (dvd_mul_of_dvd_right hdp u) (dvd_mul_of_dvd_right hda v)
  rw [← Finset.normalize_gcd, normalize_eq_one]
  exact isUnit_of_dvd_one hd

lemma mixedDegreeLinePoint_zero (p a : ℕ) :
    eval (mixedDegreeLinePoint p a) (X (2 : Fin 3)) = 0 := by
  simp [mixedDegreeLinePoint]

lemma mixedDegreeLinePoint_reduction {p a : ℕ} [Fact p.Prime] :
    (fun j => (mixedDegreeLinePoint p a j : ZMod p)) =
      (a : ZMod p) • (![1, 0, 0] : Fin 3 → ZMod p) := by
  ext j
  fin_cases j <;> simp [mixedDegreeLinePoint]

lemma mixedDegreeLinePoint_reduction_scalar_ne_zero {p a : ℕ} [Fact p.Prime]
    (ha : 0 < a) (hap : a < p) :
    (a : ZMod p) ≠ 0 := by
  intro h
  have hval := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt hap, ZMod.val_zero] at hval
  omega

/-- Equality in the actual projective residue space, not merely equality of
some informally normalized coordinates. -/
lemma mixedDegreeLinePoint_projective_reduction {p a : ℕ} [Fact p.Prime]
    (ha : 0 < a) (hap : a < p) :
    primitiveProjectiveReduction (mixedDegreeLinePoint p a)
        (mixedDegreeLinePoint_primitive Fact.out ha hap) =
      Projectivization.mk (ZMod p) (![1, 0, 0] : Fin 3 → ZMod p)
        (by intro h; have h0 := congrFun h 0; simp at h0) := by
  apply (Projectivization.mk_eq_mk_iff' (ZMod p) _ _ _ _).mpr
  exact ⟨a, mixedDegreeLinePoint_reduction.symm⟩

lemma mixedDegreeLineForm_homogeneous (j : ℕ) :
    (X (0 : Fin 3) ^ j : MvPolynomial (Fin 3) ℤ).IsHomogeneous j :=
  isHomogeneous_X_pow _ _

/-- The unnormalized determinant is a Vandermonde determinant whose entries
are pairwise distinct modulo `p`. This holds for arbitrarily many rows. -/
theorem mixedDegreeLinePoint_det_not_dvd {p s : ℕ} [Fact p.Prime] (hsp : s < p) :
    ¬ (p : ℤ) ∣
      (Matrix.of fun i j : Fin s =>
        eval (mixedDegreeLinePoint p (i.val + 1))
          (X (0 : Fin 3) ^ j.val : MvPolynomial (Fin 3) ℤ)).det := by
  let A : Matrix (Fin s) (Fin s) ℤ := Matrix.of fun i j =>
    eval (mixedDegreeLinePoint p (i.val + 1))
      (X (0 : Fin 3) ^ j.val : MvPolynomial (Fin 3) ℤ)
  have hA : A.map (Int.castRingHom (ZMod p)) =
      Matrix.vandermonde (fun i : Fin s => ((i.val + 1 : ℕ) : ZMod p)) := by
    ext i j
    simp [A, mixedDegreeLinePoint, Matrix.vandermonde]
  have hinj : Function.Injective (fun i : Fin s => ((i.val + 1 : ℕ) : ZMod p)) := by
    intro i j hij
    have h := congrArg ZMod.val hij
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h
    exact Fin.ext (by omega)
  have hn := Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  intro hd
  have hz : (A.det : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd A.det p).mpr hd
  change (Int.castRingHom (ZMod p)) A.det = 0 at hz
  rw [(Int.castRingHom (ZMod p)).map_det] at hz
  change (A.map (Int.castRingHom (ZMod p))).det = 0 at hz
  rw [hA] at hz
  exact hn hz

/-- No dimension-only linear error can rescue the unnormalized varying-degree
version of the local bound. The equation is always the same smooth line. -/
theorem no_uniform_mixed_degree_local_error (C : ℝ) :
    ∃ s p : ℕ, p.Prime ∧ s < p ∧ ∀ e : ℕ,
      (s : ℝ) ^ 2 / 2 - C * s ≤ e →
        ¬ (p : ℤ) ^ e ∣
          (Matrix.of fun i j : Fin s =>
            eval (mixedDegreeLinePoint p (i.val + 1))
              (X (0 : Fin 3) ^ j.val : MvPolynomial (Fin 3) ℤ)).det := by
  obtain ⟨s, hs⟩ := exists_nat_gt (max (2 * C) 0)
  have hspos : (0 : ℝ) < s := lt_of_le_of_lt (le_max_right _ _) hs
  have hsC : 2 * C < s := lt_of_le_of_lt (le_max_left _ _) hs
  obtain ⟨p, hsp, hp⟩ := Nat.exists_infinite_primes (s + 1)
  have hsp' : s < p := by omega
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨s, p, hp, hsp', ?_⟩
  intro e he hd
  have hmain : 0 < (s : ℝ) ^ 2 / 2 - C * s := by
    nlinarith [mul_pos hspos (sub_pos.mpr hsC)]
  have hepos : 0 < e := by exact_mod_cast (hmain.trans_le he)
  apply mixedDegreeLinePoint_det_not_dvd hsp'
  exact (show (p : ℤ) ∣ (p : ℤ) ^ e from
    dvd_pow_self _ (Nat.ne_of_gt hepos)).trans hd

end
end CCDN
