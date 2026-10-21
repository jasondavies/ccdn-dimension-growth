/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.Tactic.Measurability.Init

/-! Ideal-class notation for finite products of nonzero integral ideals.
The value at the zero ideal is set to one only to make the indexing
function total; multiplicativity below explicitly requires nonzero ideals. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped nonZeroDivisors Classical

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

def integralIdealClass (I : Ideal R) : ClassGroup R :=
  if h : I = 0 then 1 else ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr h⟩

lemma integralIdealClass_eq (I : Ideal R) (hI : I ≠ 0) :
    integralIdealClass I = ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ := by
  simp only [integralIdealClass, dite_eq_right hI]

@[simp] lemma integralIdealClass_one : integralIdealClass (1 : Ideal R) = 1 := by
  rw [integralIdealClass_eq _ one_ne_zero]
  exact map_one ClassGroup.mk0

lemma integralIdealClass_mk0 (I : (Ideal R)⁰) :
    integralIdealClass (I : Ideal R) = ClassGroup.mk0 I := by
  exact integralIdealClass_eq _ (mem_nonZeroDivisors_iff_ne_zero.mp I.property)

lemma integralIdealClass_mul {I J : Ideal R} (hI : I ≠ 0) (hJ : J ≠ 0) :
    integralIdealClass (I * J) = integralIdealClass I * integralIdealClass J := by
  rw [integralIdealClass_eq _ (mul_ne_zero hI hJ),
    integralIdealClass_eq _ hI, integralIdealClass_eq _ hJ]
  exact map_mul (ClassGroup.mk0 (R := R))
    (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ : (Ideal R)⁰)
    (⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ⟩ : (Ideal R)⁰)

lemma integralIdealClass_prod (s : Finset (Ideal R)) (hs : ∀ I ∈ s, I ≠ 0) :
    integralIdealClass (∏ I ∈ s, I) = ∏ I ∈ s, integralIdealClass I := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using (integralIdealClass_one (R := R))
  | @insert I s hIs ih =>
    have hI := hs I (Finset.mem_insert_self I s)
    have hs' : ∀ J ∈ s, J ≠ 0 := fun J hJ ↦ hs J (Finset.mem_insert_of_mem hJ)
    rw [Finset.prod_insert hIs, integralIdealClass_mul hI (Finset.prod_ne_zero_iff.mpr hs'),
      ih hs', Finset.prod_insert hIs]

lemma integralIdealClass_extension
    (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
    [Module.IsTorsionFree R S] (I : Ideal R) (hI : I ≠ 0) :
    integralIdealClass (I.map (algebraMap R S)) =
      ClassGroup.extendedHom R S (integralIdealClass I) := by
  let I₀ : (Ideal R)⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  rw [integralIdealClass_eq _ hI, ClassGroup.extendedHom_mk0]
  exact integralIdealClass_mk0 (ClassGroup.extendedIdeal R S I₀)

end
end CCDN
