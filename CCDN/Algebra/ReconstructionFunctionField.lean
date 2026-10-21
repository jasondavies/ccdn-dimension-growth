/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
/-! Polynomial reconstruction identities prove generation of the
source function field. This is the converse to the rational-inverse
construction, and makes birationality explicit in counting projections. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem reconstruction_generates_functionField
    {K F σ τ : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    [Algebra (MvPolynomial τ K ⧸ I) F]
    [IsScalarTower K (MvPolynomial τ K ⧸ I) F]
    [IsFractionRing (MvPolynomial τ K ⧸ I) F]
    (a : σ → MvPolynomial τ K)
    (Q : MvPolynomial σ K) (P : τ → MvPolynomial σ K)
    (hQ : aeval a Q ∉ I)
    (hP : ∀ i, aeval a Q * X i - aeval a (P i) ∈ I) :
    IntermediateField.adjoin K
      (Set.range (fun i => algebraMap (MvPolynomial τ K ⧸ I) F
        ((Ideal.Quotient.mk I) (a i)))) = ⊤ := by
  let A := MvPolynomial τ K ⧸ I
  let φ := IsScalarTower.toAlgHom K A F
  let θ := φ.comp (Ideal.Quotient.mkₐ K I)
  let u := fun i => θ (a i)
  let E := IntermediateField.adjoin K (Set.range u)
  have heval (p : MvPolynomial σ K) : θ (aeval a p) ∈ E := by
    rw [comp_aeval_apply]
    exact (IntermediateField.mem_adjoin_range_iff K u _).mpr ⟨p, 1, by simp [u]⟩
  have hQne : θ (aeval a Q) ≠ 0 := by
    intro hz
    change algebraMap A F ((Ideal.Quotient.mk I) (aeval a Q)) = 0 at hz
    apply hQ
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (IsFractionRing.injective A F) (by simpa only [map_zero] using hz)
  have hcoord (i : τ) : θ (X i) ∈ E := by
    have hh : θ (aeval a Q * X i - aeval a (P i)) = 0 := by
      change φ ((Ideal.Quotient.mk I) _) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hP i), map_zero]
    rw [map_sub, map_mul, sub_eq_zero] at hh
    have he : θ (X i) = θ (aeval a (P i)) / θ (aeval a Q) := by
      apply (eq_div_iff hQne).mpr
      simpa only [mul_comm] using hh
    rw [he]
    exact E.div_mem (heval (P i)) (heval Q)
  have hpoly (p : MvPolynomial τ K) : θ p ∈ E := by
    induction p using MvPolynomial.induction_on with
    | C c =>
        change θ (algebraMap K (MvPolynomial τ K) c) ∈ E
        rw [AlgHom.commutes]
        exact E.algebraMap_mem c
    | add p q hp hq => rw [map_add]; exact E.add_mem hp hq
    | mul_X p i hp => rw [map_mul]; exact E.mul_mem hp (hcoord i)
  change E = ⊤
  apply top_unique
  intro x _
  obtain ⟨r, s, _, rfl⟩ := IsFractionRing.div_surjective A x
  apply E.div_mem
  · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact hpoly p
  · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact hpoly p

end
end CCDN
