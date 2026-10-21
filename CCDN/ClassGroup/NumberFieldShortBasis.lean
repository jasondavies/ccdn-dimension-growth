/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.LatticePrescribedMinima
public import CCDN.ClassGroup.NumberFieldEuclideanLattice
import CCDN.ClassGroup.EuclideanNumberFieldBasis
import CCDN.ClassGroup.FieldBasisMultiplicationProduct
import CCDN.ClassGroup.LatticeDiscriminantNumerics
import CCDN.ClassGroup.LatticePrescribedProduct
/-! Short independent algebraic integers at the uniform discriminant-root
scale, from greedy lattice vectors, the multiplication pairing, and the
covolume estimate. -/

@[expose] public section
namespace CCDN
noncomputable section
open Module NumberField
open scoped NumberField Classical

variable (K : Type*) [Field K] [NumberField K]

theorem euclidean_prescribed_basis_last_minimum_pow
    {n : ℕ} (b : Basis (Fin (n + 2)) ℝ (mixedEmbedding.euclidean.mixedSpace K))
    (hb : IsPrescribedGreedyLatticeFamily (mixedEmbedding.euclidean.integerLattice K)
      (euclideanNumberFieldEmbedding K 1) b) :
    ‖b (Fin.last (n + 1))‖ ^ (n + 2) ≤ (∏ i, ‖b i‖) ^ 2 := by
  classical
  obtain ⟨v, q, hq, hmap⟩ :=
    exists_field_basis_of_euclidean_lattice_basis K b hb.mem
  have hpq : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
    intro he
    have := congrArg Fin.val he
    simp at this
  have hq0 : q 0 = 1 := by
    apply euclideanNumberFieldEmbedding_injective K
    rw [hmap, hb.first_eq]
  have hunit : 1 ≤ ‖euclideanNumberFieldEmbedding K (q 0)‖ := by
    rw [hq0]
    exact one_le_euclidean_norm_integer K (x := 1) one_ne_zero
  have hmin (i j : {i : Fin (n + 2) // i ≠ 0 ∧ i ≠ Fin.last (n + 1)})
      (hij : q.coord (Fin.last (n + 1)) (q i * q j) ≠ 0) :
      ‖euclideanNumberFieldEmbedding K (q (Fin.last (n + 1)))‖ ≤
        ‖euclideanNumberFieldEmbedding K (q i * q j)‖ := by
    rw [hmap]
    apply hb.norm_le hpq.symm
    · simpa only [hq, RingOfIntegers.coe_eq_algebraMap, map_mul] using
        euclideanNumberFieldEmbedding_mem_integerLattice K (v i * v j)
    · exact euclidean_notMem_basis_span_of_coordinate_ne_zero K b q hmap hij
        (by simp)
  have hh := field_basis_multiplication_minimum_product q 0 (Fin.last (n + 1))
    hpq hq0 (fun x => ‖euclideanNumberFieldEmbedding K x‖) (fun _ => norm_nonneg _)
    (euclideanNumberFieldEmbedding_norm_mul_le K) hunit hmin
  simpa only [Fintype.card_fin, hmap] using hh

theorem exists_numberField_short_basis_of_degree
    (n : ℕ) (hn : Module.finrank ℚ K = n + 2) :
    ∃ b : Basis (Fin (n + 2)) ℝ (mixedEmbedding.euclidean.mixedSpace K),
      (∀ i, b i ∈ mixedEmbedding.euclidean.integerLattice K) ∧
      ∀ i, ‖b i‖ ≤ (n + 2 : ℝ) ^ 3 * |(discr K : ℝ)| ^ (1 / (n + 2 : ℝ)) := by
  classical
  let L := mixedEmbedding.euclidean.integerLattice K
  let w := euclideanNumberFieldEmbedding K 1
  have hw : w ∈ L := euclideanNumberFieldEmbedding_mem_integerLattice K 1
  have hw0 : w ≠ 0 := by
    exact (map_ne_zero (euclideanNumberFieldEmbedding K)).mpr one_ne_zero
  have hdim : Module.finrank ℝ (mixedEmbedding.euclidean.mixedSpace K) = (n + 1) + 1 := by
    rw [mixedEmbedding.euclidean.finrank, hn]
  obtain ⟨b, hb⟩ := exists_prescribed_greedy_lattice_basis L w hw hw0 hdim
  have hprod := prescribed_greedy_lattice_basis_product_le L b hb
    (by norm_num : (0 : ℝ) < 1)
    (fun x hx hx0 => one_le_euclidean_integerLattice_norm K hx hx0)
  have hD : 1 ≤ |(discr K : ℝ)| := by
    have hz : (0 : ℤ) < |discr K| := abs_pos.mpr (discr_ne_zero K)
    have hz' : (1 : ℤ) ≤ |discr K| := by omega
    exact_mod_cast hz'
  have hcov : ZLattice.covolume L ≤ Real.sqrt |(discr K : ℝ)| := by
    change ZLattice.covolume (mixedEmbedding.euclidean.integerLattice K) ≤ _
    rw [euclidean_integerLattice_covolume]
    exact mul_le_of_le_one_left (Real.sqrt_nonneg _)
      (pow_le_one₀ (by norm_num) (by norm_num))
  have hwbound : ‖w‖ ≤ Real.sqrt (n + 2 : ℕ) := by
    simpa only [hn] using euclideanNumberFieldEmbedding_one_norm_le K
  have hprod' : (∏ i, ‖b i‖) ≤
      Real.sqrt (n + 2 : ℕ) * ((n + 2 : ℕ) : ℝ) ^ (n + 2) *
        Real.sqrt |(discr K : ℝ)| := by
    have hp : (∏ i, ‖b i‖) ≤
        ‖w‖ * ((n + 2 : ℕ) : ℝ) ^ (n + 2) * ZLattice.covolume L := by
      simpa only [div_one, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
        show n + 1 + 1 = n + 2 by omega, show (n : ℝ) + 1 + 1 = n + 2 by ring]
        using hprod
    exact hp.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right hwbound (by positivity)) hcov
      (ZLattice.covolume_pos L _).le (by positivity))
  have hlast : ‖b (Fin.last (n + 1))‖ ≤
      (n + 2 : ℝ) ^ 3 * |(discr K : ℝ)| ^ (1 / (n + 2 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      largest_minimum_le_discriminant_root (n := n + 2) (by omega)
        (Finset.prod_nonneg (fun i _ => norm_nonneg (b i))) (abs_nonneg _)
        (euclidean_prescribed_basis_last_minimum_pow K b hb) hprod'
  refine ⟨b, hb.mem, ?_⟩
  intro i
  by_cases hi : i = 0
  · rw [hi, hb.first_eq]
    apply hwbound.trans
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      sqrt_degree_le_discriminant_root (n := n + 2) (by omega) hD
  · apply (hb.norm_le hi (hb.mem _)
      (b.linearIndependent.notMem_span_image (not_lt_of_ge (Fin.le_last i)))).trans hlast

/-- A real basis of integral lattice vectors with an explicit
constant depending only on the field degree. -/
theorem exists_numberField_short_basis
    (hd : 2 ≤ Module.finrank ℚ K) :
    ∃ b : Basis (Fin (Module.finrank ℚ K)) ℝ (mixedEmbedding.euclidean.mixedSpace K),
      (∀ i, b i ∈ mixedEmbedding.euclidean.integerLattice K) ∧
      ∀ i, ‖b i‖ ≤ (Module.finrank ℚ K : ℝ) ^ 3 *
        |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Module.finrank ℚ K = n + 2 :=
    ⟨Module.finrank ℚ K - 2, by omega⟩
  rw [hn]
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    exists_numberField_short_basis_of_degree K n hn

end
end CCDN
