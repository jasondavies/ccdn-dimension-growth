/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.LinearProjectionFiltration
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-! Integrality supplies a monic equation for each coordinate of
every geometric fiber. The equation is chosen before the points of that
fiber and works over any extension of the base field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem exists_monic_integral_projection_fiber_equation
    {K L σ τ : Type*} [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial σ K)) (a : τ → MvPolynomial σ K)
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (z : τ → L) (i : σ) :
    ∃ p : Polynomial L, p.Monic ∧
      ∀ x : σ → L, (∀ f ∈ I, aeval x f = 0) →
        (∀ j, aeval x (a j) = z j) → p.eval (x i) = 0 := by
  let ψ := projectionCoordinateMap I a
  obtain ⟨p, hp, he⟩ := hint ((Ideal.Quotient.mk I) (X i))
  refine ⟨p.map (aeval z).toRingHom, hp.map _, ?_⟩
  intro x hx hz
  let q : (MvPolynomial σ K ⧸ I) →ₐ[K] L :=
    Ideal.Quotient.liftₐ I (aeval x) hx
  have hq (f : MvPolynomial σ K) : q ((Ideal.Quotient.mk I) f) = aeval x f := rfl
  have hcomp : q.comp ψ = aeval z := by
    ext j
    simp only [AlgHom.comp_apply, ψ, projectionCoordinateMap, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk]
    exact (hq (a j)).trans (hz j)
  have hh := congrArg q he
  change q.toRingHom (p.eval₂ ψ.toRingHom ((Ideal.Quotient.mk I) (X i))) =
    q.toRingHom 0 at hh
  rw [Polynomial.hom_eval₂ p ψ.toRingHom q.toRingHom, map_zero] at hh
  have hcomp' : q.toRingHom.comp ψ.toRingHom = (aeval z).toRingHom :=
    congrArg AlgHom.toRingHom hcomp
  rw [hcomp'] at hh
  change p.eval₂ (aeval z).toRingHom (aeval x (X i)) = 0 at hh
  rw [aeval_X] at hh
  simpa only [Polynomial.eval_map] using hh

end
end CCDN
