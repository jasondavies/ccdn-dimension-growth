/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
public import Mathlib.FieldTheory.Galois.Basic
import CCDN.Hilbert.ScalarExtension
import CCDN.Hypersurface.ZeroDimensionalPrimeDescent
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.FieldTheory.Galois.Infinite

/-! A geometrically integral zero-dimensional affine variety over a
characteristic-zero field is a single rational point, of degree one. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem eval_kernel_filtered_finrank {K σ : Type*}
    [Field K] [Fintype σ] (x : σ → K) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace (RingHom.ker (eval x)) N) = 1 := by
  let I := RingHom.ker (eval x)
  have heval : RingHom.ker (aeval (R := K) x) = I := by
    ext f
    simp only [RingHom.mem_ker, aeval_def, Algebra.algebraMap_self,
      eval₂_id]
    rfl
  let e := Ideal.quotientKerAlgEquivOfSurjective
    (f := aeval (R := K) x) (fun c => ⟨C c, by simp⟩)
  have htop : filteredCoordinateSpace I N = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine Submodule.mem_map.mpr ⟨C (eval x f), ?_, ?_⟩
    · exact (mem_restrictTotalDegree _ _ _).mpr (by simp)
    · apply Ideal.Quotient.eq.mpr
      change eval x (C (eval x f) - f) = 0
      simp
  rw [htop, finrank_top]
  let e' := (Ideal.quotientEquivAlgOfEq K heval.symm).trans e
  simpa using e'.toLinearEquiv.finrank_eq

private theorem eval_kernel_filteredHilbertPolynomial {K σ : Type*}
    [Field K] [Fintype σ] [LinearOrder σ] (x : σ → K) :
    filteredHilbertPolynomial (RingHom.ker (eval x)) = 1 := by
  apply filteredHilbertPolynomial_eq_of_eventual
  exact ⟨0, fun N _ => by rw [eval_kernel_filtered_finrank]; simp⟩

private lemma eval_map_galois_coordinates {K L σ : Type*}
    [Field K] [Field L] [Algebra K L] (γ : Gal(L/K)) (x : σ → L)
    (f : MvPolynomial σ K) :
    eval (γ ∘ x) (map (algebraMap K L) f) =
      γ (eval x (map (algebraMap K L) f)) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [γ.commutes]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf => simp only [map_mul, map_X, eval_X, hf, Function.comp_apply]

/-- The rational point is constructed by uniqueness over a Galois
algebraic closure. -/
theorem zero_dimensional_geometrically_integral_point
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] [IsGalois K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K L))).IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = 0) :
    ∃ x : Fin n → K, I = RingHom.ker (eval x) ∧ filteredHilbertPolynomial I = 1 := by
  classical
  let J := I.map (map (algebraMap K L))
  have hJdim : (filteredHilbertPolynomial J).natDegree = 0 := by
    rw [show filteredHilbertPolynomial J = filteredHilbertPolynomial I from
      filteredHilbertPolynomial_scalar_extension (L := L) I]
    exact hdim
  have hnonempty : (MvPolynomial.zeroLocus L J).Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    have hvan := MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := L) J
    rw [he, MvPolynomial.vanishingIdeal_empty] at hvan
    exact Ideal.IsPrime.ne_top (inferInstance : J.IsPrime) hvan.symm
  obtain ⟨y, hy⟩ := hnonempty
  have hy' : y ∈ idealZeroLocus J := by
    intro f hf
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hy f hf
  have hJker := zero_dimensional_prime_eq_eval_kernel J hJdim y hy'
  have hunique (z : Fin n → L) (hz : z ∈ idealZeroLocus J) : z = y := by
    funext i
    have hmem : X i - C (y i) ∈ J := by
      rw [hJker]
      change eval y (X i - C (y i)) = 0
      simp
    have hh := hz _ hmem
    simpa only [map_sub, eval_X, eval_C, sub_eq_zero] using hh
  have hfixed (i : Fin n) : y i ∈ Set.range (algebraMap K L) := by
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
    intro γ
    have hγ : (γ ∘ y) ∈ idealZeroLocus J := by
      have hle : J ≤ RingHom.ker (eval (γ ∘ y)) := by
        apply Ideal.map_le_iff_le_comap.mpr
        intro f hf
        change eval (γ ∘ y) (map (algebraMap K L) f) = 0
        rw [eval_map_galois_coordinates, hy' _ (Ideal.mem_map_of_mem _ hf), map_zero]
      exact hle
    exact congrFun (hunique (γ ∘ y) hγ) i
  choose x hx using hfixed
  have hxzero : x ∈ idealZeroLocus I := by
    intro f hf
    apply (algebraMap K L).injective
    have hh := hy' _ (Ideal.mem_map_of_mem (map (algebraMap K L)) hf)
    have he : algebraMap K L ∘ x = y := funext hx
    rw [← he, eval_map, ← eval₂_comp] at hh
    simpa only [map_zero] using hh
  have hIker := zero_dimensional_prime_eq_eval_kernel I hdim x hxzero
  exact ⟨x, hIker, hIker ▸ eval_kernel_filteredHilbertPolynomial x⟩

end
end CCDN
