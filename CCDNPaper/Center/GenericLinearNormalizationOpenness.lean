/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Hilbert.LinearProjectionFiltration
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import CCDN.Hilbert.HomogeneousPrimeComponents
import CCDNPaper.Center.BalancedParameterFiniteness
import CCDNPaper.Center.GenericHomogeneousGeneration
import CCDNPaper.Center.HomogeneousParameterCertificates
import CCDNPaper.Center.HomogeneousParameterPowers

/-! Finiteness of homogeneous linear parameters at one coefficient
specialization implies finiteness at algebraically independent coefficients.
The proof constructs a full homogeneous coefficient determinant internally. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Homogeneous finite normalization is open at its generic
coefficient tuple. This also permits fixed rows such as the homogenizing
coordinate, since the family may have arbitrary polynomial coefficients. -/
theorem generic_linear_projection_integral_of_specialization
    {K L σ τ : Type*} [Field K] [Field L] [Algebra K L] [Fintype τ] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : IsHomogeneousIdeal I)
    (a : τ → MvPolynomial (Fin (n + 1)) (MvPolynomial σ K))
    (ha : ∀ i, (a i).IsHomogeneous 1)
    (c : σ → K)
    (hc : (projectionCoordinateMap I (fun i => map (eval c) (a i))).IsIntegral)
    (u : σ → L) (hu : AlgebraicIndependent K u) :
    (projectionCoordinateMap (I.map (map (algebraMap K L)))
      (fun i => map (aeval u).toRingHom (a i))).IsIntegral := by
  classical
  let a₀ := fun i => map (eval c) (a i)
  have ha₀ (i) : (a₀ i).IsHomogeneous 1 := (ha i).map (eval c)
  obtain ⟨D,hD,hfull⟩ := integral_homogeneous_parameters_full_degree I hI a₀ ha₀ hc
  have hcert (j : Fin ((n + D).choose D)) := homogeneous_parameter_certificate hD I hI a₀ ha₀
    (monomial (homogeneousMonomials n D j) 1)
    (isHomogeneous_monomial _ (homogeneousMonomials_degree n D j))
    (hfull _ (isHomogeneous_monomial _ (homogeneousMonomials_degree n D j)))
  choose g s hg hghom hshom heq using hcert
  let p : Fin ((n + D).choose D) → MvPolynomial (Fin (n + 1)) (MvPolynomial σ K) :=
    fun j => map C (g j) + ∑ i, a i * map C (s j i)
  have hp (j) : (p j).IsHomogeneous D := by
    apply ((hghom j).map C).add
    apply IsHomogeneous.sum
    intro i _
    have hh := (ha i).mul ((hshom j i).map (C : K →+* MvPolynomial σ K))
    simpa only [show 1 + (D - 1) = D by omega] using hh
  have hce : (eval c).comp (C : K →+* MvPolynomial σ K) = RingHom.id K := by
    ext k
    simp
  have hpc (j) : map (eval c) (p j) = monomial (homogeneousMonomials n D j) 1 := by
    simp only [p, map_add, map_sum, map_mul, map_map, hce, map_id]
    exact heq j
  let IL := I.map (map (algebraMap K L))
  let aL := fun i => map (aeval u).toRingHom (a i)
  let H := IL ⊔ Ideal.span (Set.range aL)
  have hue : (aeval u).toRingHom.comp (C : K →+* MvPolynomial σ K) = algebraMap K L := by
    ext k
    simp
  have hpH (j) : map (aeval u).toRingHom (p j) ∈ H := by
    simp only [p, map_add, map_sum, map_mul, map_map, hue]
    apply H.add_mem
    · exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (hg j))
    · apply H.sum_mem
      intro i _
      exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i,rfl⟩))
  have hpow (j : Fin (n + 1)) : X j ^ D ∈ H :=
    homogeneous_generation_of_basis_specialization p hp c hpc u hu H hpH _
      (isHomogeneous_X_pow j D)
  apply integral_projection_of_balanced_power_reductions IL aL D hD
  intro j
  exact homogeneous_parameter_power_reduction IL (homogeneous_ideal_scalar_extension I hI)
    aL (fun i => (ha i).map (aeval u).toRingHom) j D hD (hpow j)

end
end CCDN
