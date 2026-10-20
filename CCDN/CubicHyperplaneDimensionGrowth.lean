module

public import CCDN.CubicIntegerHyperplaneSlices
public import CCDN.HyperplaneSliceCoordinates
public import CCDN.PolynomialPredicates

/-! A dimension induction with a cubic degree cost per hyperplane slice,
using the constructed universal Noether detector. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A normal of height at most `d^3` costs three powers of the degree
and one power of the box radius in a dimension induction. -/
theorem count_le_of_cubic_integer_hyperplane_slices {n d e r : ℕ}
    (X : Set (RatPoint (n + 1))) (a : IntPoint (n + 1))
    (j : Fin (n + 1)) (hj : a j ≠ 0) (Y : ℤ → Set (RatPoint n))
    (hd : 1 ≤ d) {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (ha : ∀ i, |(a i : ℝ)| ≤ (d : ℝ) ^ 3)
    (hmap : ∀ k x, x ∈ integerSlicePoints X B a k →
      rationalPoint (deleteIntegerCoordinate j x) ∈ Y k)
    (hcount : ∀ k, (count (Y k) B : ℝ) ≤ C * (d : ℝ) ^ e * B ^ r) :
    (count X B : ℝ) ≤
      (2 * (n + 1 : ℕ) + 1) * C * (d : ℝ) ^ (e + 3) * B ^ (r + 1) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hB0 : 0 ≤ B := by linarith
  have hK : 0 ≤ C * (d : ℝ) ^ e * B ^ r := by positivity
  have hD : 1 ≤ (d : ℝ) ^ 3 := one_le_pow₀ hdR
  have hDB : 1 ≤ (d : ℝ) ^ 3 * B := one_le_mul_of_one_le_of_one_le hD hB
  have hfactor :
      2 * (n + 1 : ℕ) * ((d : ℝ) ^ 3) * B + 1 ≤
        (2 * (n + 1 : ℕ) + 1) * (d : ℝ) ^ 3 * B := by
    nlinarith
  calc
    _ ≤ (2 * (n + 1 : ℕ) * ((d : ℝ) ^ 3) * B + 1) *
        (C * (d : ℝ) ^ e * B ^ r) :=
      count_le_of_integer_hyperplane_slices X a j hj Y
        (by positivity) hB0 hK ha hmap hcount
    _ ≤ ((2 * (n + 1 : ℕ) + 1) * (d : ℝ) ^ 3 * B) *
        (C * (d : ℝ) ^ e * B ^ r) := mul_le_mul_of_nonneg_right hfactor hK
    _ = _ := by rw [pow_add, pow_succ]; ring


/-- Bounded good hyperplanes lift any coefficient-uniform surface bound
through all higher dimensions. Every slicing step costs three powers of
the degree and one power of the box radius. -/
theorem top_form_hypersurface_count_cubic_of_surface_bound (t e : ℕ) (ht : 2 ≤ t)
    (hbase : ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      t ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ e * B) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (3 + n)) ℤ,
      HasAbsIrreducibleTopForm f →
      t ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (e + 3 * n) * B ^ (n + 1) := by
  classical
  induction n with
  | zero =>
    obtain ⟨C, hC, hbound⟩ := hbase
    refine ⟨C, hC, ?_⟩
    intro f hir hd B hB
    simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, pow_one] using hbound f hir hd B hB
  | succ n ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    refine ⟨(2 * (3 + n + 1 : ℕ) + 1) * C, by positivity, ?_⟩
    intro f hir hd B hB
    let indexEquiv : Fin (3 + n + 1) ≃ Option (Fin (3 + n)) := finSuccEquiv' 0
    let F := rename indexEquiv f
    have hFdegree : F.totalDegree = f.totalDegree := totalDegree_renameEquiv indexEquiv f
    have hFir : HasAbsIrreducibleTopForm F := integer_top_irreducible_rename indexEquiv f hir
    obtain ⟨D, a, g, hD, hDb, hab, hg⟩ :=
      exists_cubic_good_integer_hyperplane_slices F hFir
        (by rw [hFdegree]; omega)
    rw [hFdegree] at hDb hab
    let b := graphIntegerNormal D a
    have hb0 : b 0 ≠ 0 := hD
    have hbheight (i : Fin (3 + n + 1)) :
        |(b i : ℝ)| ≤ (f.totalDegree : ℝ) ^ 3 := by
      simpa only [Nat.cast_pow] using graphIntegerNormal_height D a hDb hab i
    let Y : ℤ → Set (RatPoint (3 + n)) :=
      fun k => zeroLocus (map (Int.castRingHom ℚ) (g k))
    have hmap (k : ℤ) (x : IntPoint (3 + n + 1))
        (hx : x ∈ integerSlicePoints (zeroLocus (map (Int.castRingHom ℚ) f)) B b k) :
        rationalPoint (deleteIntegerCoordinate 0 x) ∈ Y k := by
      exact integer_slice_map_of_option_equations f D a g
        (fun k => (hg k).2.2) B k x hx
    have hcount (k : ℤ) :
        (count (Y k) B : ℝ) ≤ C * (f.totalDegree : ℝ) ^ (e + 3 * n) * B ^ (n + 1) := by
      have hdegree : (g k).totalDegree = f.totalDegree := (hg k).1.trans hFdegree
      have hh := hbound (g k) (hg k).2.1 (by omega) B hB
      simpa only [hdegree, Y] using hh
    have hh := count_le_of_cubic_integer_hyperplane_slices
      (zeroLocus (map (Int.castRingHom ℚ) f)) b 0 hb0 Y
      (show 1 ≤ f.totalDegree by omega) hB hC.le hbheight hmap hcount
    convert hh using 1

end
end CCDN
