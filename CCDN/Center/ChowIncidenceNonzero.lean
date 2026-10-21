/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ChowIncidenceIdeal
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Hilbert.HilbertTranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
/-! More hyperplanes than the affine Hilbert dimension satisfy a
nonzero incidence equation. The equation is constructed from the
elimination kernel, by a transcendence-degree count. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The incidence elimination ideal is nonzero as soon as the number of
hyperplanes exceeds the dimension of the affine coordinate domain. -/
theorem chowIncidenceIdeal_ne_bot {K : Type*} [Field K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hr : (filteredHilbertPolynomial I).natDegree < r) :
    chowIncidenceIdeal r I ≠ ⊥ := by
  classical
  intro hbot
  have hinj : Function.Injective (chowIncidenceMap r I) :=
    (RingHom.injective_iff_ker_eq_bot (chowIncidenceMap r I)).mpr hbot
  have hAI : AlgebraicIndependent K (fun q : Fin r × Fin (n + 1) =>
      chowIncidenceMap r I (X q)) :=
    (algebraicIndependent_X (Fin r × Fin (n + 1)) K).map' hinj
  obtain ⟨U,hU,hTB⟩ := exists_hilbert_coordinate_transcendence_basis I
  let A := MvPolynomial (Fin n) K ⧸ I
  have hP := IsTranscendenceBasis.mvPolynomial (Fin r × Fin n) A
  have htarget := hTB.sumElim_comp hP
  have hle := hAI.lift_cardinalMk_le_trdeg
  have heq := htarget.lift_cardinalMk_eq_trdeg
  have hcard : Fintype.card (Fin r × Fin (n + 1)) ≤
      Fintype.card ((Fin r × Fin n) ⊕ U) := by
    simpa only [Cardinal.mk_fintype,Cardinal.lift_natCast,Nat.cast_le] using hle.trans_eq heq.symm
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_sum] at hcard
  rw [Nat.card_eq_fintype_card] at hU
  nlinarith

end
end CCDN
