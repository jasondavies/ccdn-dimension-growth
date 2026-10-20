module

public import CCDN.GraphHyperplaneRestriction
public import CCDN.HyperplanePlaneAvoidance
public import CCDN.ThreeRowHyperplane
public import CCDN.IntegerPlaneHeight

/-! Constructing a good rational hyperplane with a bounded integer normal.
The degree-nine bound is a polynomial replacement for the precise avoidance
polynomial in corrected CCDN Lemma 4.3.7. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
local notation "K" => AlgebraicClosure ℚ

def goodHyperplaneHeight (d : ℕ) : ℕ := 6 * (2 * d ^ 3 + 3) ^ 3

/-- In at least four variables there is a hyperplane
`D*x₀ = ∑ aᵢ*xᵢ` whose restriction is geometrically irreducible of full
degree. Its integer normal has height polynomial in the degree and is
independent of the coefficient height of the original equation. -/
theorem exists_bounded_geometrically_good_hyperplane {n : ℕ}
    (f : MvPolynomial (Option (Fin (3 + n))) ℤ)
    (hir : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f))
    (hd : 0 < f.totalDegree) :
    ∃ (D : ℤ) (a : Fin (3 + n) → ℤ),
      D ≠ 0 ∧ |D| ≤ (goodHyperplaneHeight f.totalDegree : ℤ) ∧
      (∀ i, |a i| ≤ (goodHyperplaneHeight f.totalDegree : ℤ)) ∧
      (graphHyperplaneRestriction (fun i => (a i : ℚ) / D)
        (map (Int.castRingHom ℚ) f)).totalDegree = f.totalDegree ∧
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ))
        (graphHyperplaneRestriction (fun i => (a i : ℚ) / D)
          (map (Int.castRingHom ℚ) f))) := by
  classical
  let T := 2 * f.totalDegree ^ 3 + 3
  obtain ⟨v, hv, hminor, _, hplanedegree, hplaneir⟩ :=
    exists_integer_good_plane_with_anchor f hir hd
  let M : Matrix (Fin 3) (Fin 3) ℤ :=
    Matrix.of (fun i j => v (some (i.castAdd n), j))
  let w : Fin 3 → ℤ := fun j => v (none, j)
  have hvT (p : PlaneParameters (Option (Fin (3 + n)))) : |v p| ≤ (T : ℤ) := by
    rw [abs_of_nonneg (hv p).1]
    simpa only [T, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using (hv p).2
  obtain ⟨b, hrelation, hb, hD, hDb⟩ := exists_bounded_three_row_relation M w T
    (fun i j => hvT (some (i.castAdd n), j)) (fun j => hvT (none, j)) hminor
  let D := M.det
  let a : Fin (3 + n) → ℤ := Fin.addCases b (fun _ : Fin n => 0)
  have hrel (j : Fin 3) : D * v (none, j) = ∑ i, a i * v (some i, j) := by
    rw [Fin.sum_univ_add]
    simpa only [a, Fin.addCases_left, Fin.addCases_right, zero_mul,
      Finset.sum_const_zero, add_zero, M, w, D, Matrix.of_apply] using (hrelation j).symm
  have hheight : (6 : ℤ) * (T : ℤ) ^ 3 = (goodHyperplaneHeight f.totalDegree : ℤ) := by
    simp only [goodHyperplaneHeight, T, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat]
  have haheight (i : Fin (3 + n)) : |a i| ≤ (goodHyperplaneHeight f.totalDegree : ℤ) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [a, Fin.addCases_left, hheight] using hb j
    · simp only [a, Fin.addCases_right, abs_zero]
      exact Nat.cast_nonneg _
  let α : Fin (3 + n) → ℚ := fun i => (a i : ℚ) / D
  let αK : Fin (3 + n) → K := fun i => (a i : K) / D
  let vK : PlaneParameters (Option (Fin (3 + n))) → K := (Int.castRingHom K) ∘ v
  have hDK : (D : K) ≠ 0 := by exact_mod_cast hD
  have hcontain (j : Fin 3) : vK (none, j) = ∑ i, αK i * vK (some i, j) := by
    have hh : (D : K) * (v (none, j) : K) = ∑ i, (a i : K) * (v (some i, j) : K) := by
      exact_mod_cast hrel j
    change (v (none, j) : K) = ∑ i, ((a i : K) / D) * (v (some i, j) : K)
    calc
      _ = ((D : K) * (v (none, j) : K)) / D := by field_simp [hDK]
      _ = (∑ i, (a i : K) * (v (some i, j) : K)) / D := by rw [hh]
      _ = _ := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hfdegree : (map (Int.castRingHom K) f).totalDegree = f.totalDegree := by
    unfold totalDegree
    rw [support_map_of_injective _ Int.cast_injective]
  have hsection := universalPlaneSection_map (Int.castRingHom K) f v
  have hgood := graphHyperplaneRestriction_irreducible_of_plane
    (map (Int.castRingHom K) f) αK vK hcontain
    (by simpa only [vK, hsection] using hplaneir)
    (by simpa only [vK, hsection, hfdegree] using hplanedegree)
  let φ : ℚ →+* K := algebraMap ℚ K
  have hmapf : map φ (map (Int.castRingHom ℚ) f) = map (Int.castRingHom K) f := by
    rw [map_map]
    congr 1
  have hα : φ ∘ α = αK := by
    funext i
    simp [φ, α, αK]
  have hmap : map φ (graphHyperplaneRestriction α (map (Int.castRingHom ℚ) f)) =
      graphHyperplaneRestriction αK (map (Int.castRingHom K) f) := by
    rw [graphHyperplaneRestriction_map, hα, hmapf]
  have hmapdegree (g : MvPolynomial (Fin (3 + n)) ℚ) :
      (map φ g).totalDegree = g.totalDegree := by
    unfold totalDegree
    rw [support_map_of_injective _ φ.injective]
  refine ⟨D, a, hD, hDb.trans_eq hheight, haheight, ?_, ?_⟩
  · rw [← hmapdegree, hmap, hgood.1, hfdegree]
  · change Irreducible (map φ (graphHyperplaneRestriction α (map (Int.castRingHom ℚ) f)))
    rw [hmap]
    exact hgood.2

end
end CCDN
