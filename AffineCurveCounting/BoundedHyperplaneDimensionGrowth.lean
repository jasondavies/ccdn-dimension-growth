module

public import AffineCurveCounting.IntegerGoodHyperplaneSlices
public import AffineCurveCounting.HyperplaneSliceCoordinates

/-! A reusable bounded-hyperplane induction from surfaces to affine
hypersurfaces in every higher dimension. The threshold and initial
degree exponent are parameters. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- Bounded good hyperplanes lift any coefficient-uniform surface bound
through all higher dimensions. Every slicing step costs nine powers of
the degree and one power of the box radius. -/
theorem top_form_hypersurface_count_of_surface_bound (t e : ℕ) (ht : 1 ≤ t)
    (hbase : ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ))
        (homogeneousComponent f.totalDegree f)) →
      t ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ e * B) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (3 + n)) ℤ,
      Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ))
        (homogeneousComponent f.totalDegree f)) →
      t ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (e + 9 * n) * B ^ (n + 1) := by
  classical
  induction n with
  | zero =>
    obtain ⟨C, hC, hbound⟩ := hbase
    refine ⟨C, hC, ?_⟩
    intro f hir hd B hB
    simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, pow_one] using hbound f hir hd B hB
  | succ n ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    refine ⟨(1500 * (3 + n + 1 : ℕ) + 1) * C, by positivity, ?_⟩
    intro f hir hd B hB
    let indexEquiv : Fin (3 + n + 1) ≃ Option (Fin (3 + n)) := finSuccEquiv' 0
    let F := rename indexEquiv f
    have hFdegree : F.totalDegree = f.totalDegree := totalDegree_renameEquiv indexEquiv f
    have hFir : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ))
        (homogeneousComponent F.totalDegree F)) := integer_top_irreducible_rename indexEquiv f hir
    obtain ⟨D, a, g, hD, hDb, hab, hg⟩ :=
      exists_bounded_good_integer_hyperplane_slices F hFir
        (by rw [hFdegree]; omega)
    rw [hFdegree] at hDb hab
    let b := graphIntegerNormal D a
    have hb0 : b 0 ≠ 0 := hD
    have hbheight (i : Fin (3 + n + 1)) :
        |(b i : ℝ)| ≤ 750 * (f.totalDegree : ℝ) ^ 9 := by
      have hh := graphIntegerNormal_height D a hDb hab i
      have hh' : (goodHyperplaneHeight f.totalDegree : ℝ) ≤
          750 * (f.totalDegree : ℝ) ^ 9 := by
        exact_mod_cast goodHyperplaneHeight_le (show 1 ≤ f.totalDegree by omega)
      exact hh.trans hh'
    let Y : ℤ → Set (RatPoint (3 + n)) :=
      fun k => zeroLocus (map (Int.castRingHom ℚ) (g k))
    have hmap (k : ℤ) (x : IntPoint (3 + n + 1))
        (hx : x ∈ integerSlicePoints (zeroLocus (map (Int.castRingHom ℚ) f)) B b k) :
        rationalPoint (deleteIntegerCoordinate 0 x) ∈ Y k := by
      exact integer_slice_map_of_option_equations f D a g
        (fun k => (hg k).2.2) B k x hx
    have hcount (k : ℤ) :
        (count (Y k) B : ℝ) ≤ C * (f.totalDegree : ℝ) ^ (e + 9 * n) * B ^ (n + 1) := by
      have hdegree : (g k).totalDegree = f.totalDegree := (hg k).1.trans hFdegree
      have hh := hbound (g k) (hg k).2.1 (by omega) B hB
      simpa only [hdegree, Y] using hh
    have hh := count_le_of_bounded_integer_hyperplane_slices
      (zeroLocus (map (Int.castRingHom ℚ) f)) b 0 hb0 Y
      (show 1 ≤ f.totalDegree by omega) hB hC.le hbheight hmap hcount
    convert hh using 1

end
end AffineCurveCounting
