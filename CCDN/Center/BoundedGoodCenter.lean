/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveClosureIdeal
public import CCDN.Center.BirationalCenterLocus
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Center.DetectorBounds
import CCDN.Center.DetectorExtension
import CCDN.Center.GoodCenterWitness
import CCDN.Center.ZeroColumnMinorSpecialization
import CCDN.Hilbert.ProjectiveClosureHilbertPolynomial
/-! Integer good centers with the quadratic row bound from the
row-resultant detector. Dimension zero is included using its proved degree
one. Prescribed zero columns of a witness center are preserved, which gives
centers in X0=0 for affine sources. -/

@[expose] public section
namespace CCDN
noncomputable section

section

/-! A member of the sharp resultant detector family that is nonzero at a
given good center. Every independent center at which it is nonzero is good. -/

open MvPolynomial Matrix

private theorem exists_nonzero_center_detector
    {K : Type*} [Field K] [CharZero K] {n m r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d)
    (hr : r + 2 ≤ n + 2)
    (A : Matrix (Fin r) (Fin (n + 2)) K) (hA : LinearIndependent K A.row)
    (hgood : IsBirationalMatrixCenter J A) :
    ∃ G : MvPolynomial (Fin r ↪ Fin (n + 2)) K,
      G.IsHomogeneous (((m + 1) * d) * (2 * d - 1)) ∧
      G.totalDegree ≤ ((m + 1) * d) * (2 * d - 1) ∧
      eval (matrixPluckerCoordinates A) G ≠ 0 ∧
      ∀ B : Matrix (Fin r) (Fin (n + 2)) K, LinearIndependent K B.row →
        eval (matrixPluckerCoordinates B) G ≠ 0 → IsBirationalMatrixCenter J B := by
  obtain ⟨Φ, hhom, hdeg, hΦ⟩ := exists_birational_center_detector J hJ d hdimdeg hr
  obtain ⟨G, hG, heval⟩ := (hΦ A hA).mpr hgood
  exact ⟨G, hhom G hG, hdeg G hG, heval, fun B hB hGB => (hΦ B hB).mp ⟨G, hG, hGB⟩⟩

end

open MvPolynomial Matrix

def centerMinorBound (r m d : ℕ) : ℕ := r.factorial * ((m + 1) ^ 2 * d ^ 2) ^ r

/-- A good center with zero columns `S` yields a good center with bounded
nonnegative integer entries and the same zero columns. -/
private theorem exists_bounded_integer_center_of_witness
    {n m : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d)
    (S : Finset (Fin (n + 2))) (A : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) ℚ)
    (hA : LinearIndependent ℚ A.row) (hAS : ∀ i j, j ∈ S → A i j = 0)
    (hgood : IsBirationalMatrixCenter J A) :
    ∃ M : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) ℤ,
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ ((m + 1) ^ 2 * d ^ 2)) ∧
      (∀ c : Fin (n + 1 - m - 1) ↪ Fin (n + 2),
        |(M.submatrix id c).det| ≤ centerMinorBound (n + 1 - m - 1) m d) ∧
      (∀ i j, j ∈ S → M i j = 0) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      IsBirationalMatrixCenter J (M.map (Int.castRingHom ℚ)) := by
  obtain ⟨G,hhom,hdeg,hvalue,hgoodG⟩ :=
    exists_nonzero_center_detector J hJ d hdimdeg (by omega) A hA hgood
  have hG : G ≠ 0 := by intro hz; simp [hz] at hvalue
  have hhom' : G.IsHomogeneous G.totalDegree := (hhom.totalDegree hG) ▸ hhom
  obtain ⟨M,hM,hM0,hli,hv,hminor⟩ :=
    exists_integer_minor_specialization_zero_columns S G hhom' A hA hAS hvalue
  have hbound : max 1 G.totalDegree ≤ ((m + 1) ^ 2 * d ^ 2) :=
    (max_le_max_left 1 hdeg).trans (center_detector_degree_le_square
      (hilbert_multiplicity_pos_of_prime J hdimdeg.leadingCoeff_eq)
      (geometric_projective_multiplicity_boundary J hJ hdimdeg))
  have hb : ((max 1 G.totalDegree : ℕ) : ℤ) ≤ ((m + 1) ^ 2 * d ^ 2) := by exact_mod_cast hbound
  refine ⟨M,fun i j => ⟨(hM i j).1,(hM i j).2.trans hb⟩,fun c => ?_,hM0,hli,hgoodG _ hli hv⟩
  apply (hminor c).trans
  simp only [centerMinorBound, Nat.cast_mul, Nat.cast_pow]
  gcongr
  exact_mod_cast hbound

/-- The geometric good center has bounded integer independent rows. -/
theorem exists_bounded_integer_birational_center
    {n m : ℕ} (hmn : m + 2 ≤ n + 1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d) :
    ∃ M : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) ℤ,
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ ((m + 1) ^ 2 * d ^ 2)) ∧
      (∀ c : Fin (n + 1 - m - 1) ↪ Fin (n + 2),
        |(M.submatrix id c).det| ≤ centerMinorBound (n + 1 - m - 1) m d) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      IsBirationalMatrixCenter J (M.map (Int.castRingHom ℚ)) := by
  obtain ⟨A,hA,hdis,_,hfield⟩ :=
    exists_birational_minor_center (L := AlgebraicClosure ℚ) m (n + 1) hmn J hJ d hdimdeg
  obtain ⟨M,hM,hminor,_,hli,hgood⟩ := exists_bounded_integer_center_of_witness J hJ d
    hdimdeg ∅ A hA (fun _ _ h => absurd h (Finset.notMem_empty _)) ⟨hdis,hfield⟩
  exact ⟨M,hM,hminor,hli,hgood⟩

/-- For an affine prime ideal of dimension `m` and degree `d` that stays prime over `ℚ̄`,
there is a linearly independent integer center matrix for its projective closure whose first
column vanishes (so the center lies in the hyperplane `X₀ = 0`), with entries in
`[0, (m+1)²d²]`, maximal minors bounded by `centerMinorBound`, and birational projection. -/
theorem exists_bounded_integer_fixed_coordinate_center
    {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hmn : m + 1 ≤ n + 1) (d : ℕ)
    (hdimdeg : HasAffineDimensionDegree I m d) :
    ∃ M : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) ℤ,
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ ((m + 1) ^ 2 * d ^ 2)) ∧
      (∀ c : Fin (n + 1 - m - 1) ↪ Fin (n + 2),
        |(M.submatrix id c).det| ≤ centerMinorBound (n + 1 - m - 1) m d) ∧
      (∀ i, M i 0 = 0) ∧ LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      IsBirationalMatrixCenter (projectiveClosureIdeal I) (M.map (Int.castRingHom ℚ)) := by
  have := projectiveClosureIdeal_geometrically_prime (L := AlgebraicClosure ℚ) I
  have hc := projectiveClosureIdeal_hilbertPolynomial_parameters I m d hdimdeg
  obtain ⟨A,hA,hA0,hdis,_,hfield⟩ :=
    exists_fixed_coordinate_birational_minor_center (L := AlgebraicClosure ℚ) I hmn d hdimdeg
  obtain ⟨M,hM,hminor,hM0,hli,hgood⟩ := exists_bounded_integer_center_of_witness
    (projectiveClosureIdeal I) (projectiveClosureIdeal_homogeneous I) d hc {0} A hA
    (fun i j hj => by simpa only [Finset.mem_singleton.mp hj] using hA0 i) ⟨hdis,hfield⟩
  exact ⟨M,hM,hminor,fun i => hM0 i 0 (Finset.mem_singleton_self 0),hli,hgood⟩

end
end CCDN
