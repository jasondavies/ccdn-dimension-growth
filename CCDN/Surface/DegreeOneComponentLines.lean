/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.AffineCurveDegree
public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Height.Box
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CCDN.Plane.IntegralAffineLine
public import Mathlib.RingTheory.Ideal.Height
import CCDN.Plane.DegreeOneAffineLine
/-! A finite family of degree-one prime components gives a finite
set of rational affine lines with the same rational zero-set union. Empty
rational loci are discarded, and repeated line sets are counted only once. -/

@[expose] public section
namespace CCDN
noncomputable section

theorem degree_one_components_line_cover
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (hcurve : ∀ P ∈ S, P.IsPrime ∧ P.height = 2 ∧ HasAffineCurveDegree P 1) :
    ∃ lines : Finset (Set (RatPoint 3)),
      (⋃ P ∈ S, idealZeroLocus P) = (⋃ L ∈ lines, L) ∧
      lines.card ≤ S.card ∧
      ∀ L ∈ lines, (∃ P ∈ S, L = idealZeroLocus P) ∧
        ∃ a v : RatPoint 3, v ≠ 0 ∧ L = rationalAffineLine a v := by
  classical
  let T := S.filter (fun P => (idealZeroLocus P).Nonempty)
  let lines := T.image idealZeroLocus
  refine ⟨lines, ?_, (Finset.card_image_le).trans (Finset.card_le_card
    (Finset.filter_subset _ _)), ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨P, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hPS, hxP⟩ := Set.mem_iUnion.mp hx
      have hPT : P ∈ T := Finset.mem_filter.mpr ⟨hPS, ⟨x, hxP⟩⟩
      exact Set.mem_iUnion.mpr ⟨idealZeroLocus P,
        Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨P, hPT, rfl⟩, hxP⟩⟩
    · intro hx
      obtain ⟨L, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hLs, hxL⟩ := Set.mem_iUnion.mp hx
      obtain ⟨P, hPT, rfl⟩ := Finset.mem_image.mp hLs
      exact Set.mem_iUnion.mpr ⟨P,
        Set.mem_iUnion.mpr ⟨(Finset.mem_filter.mp hPT).1, hxL⟩⟩
  · intro L hL
    obtain ⟨P, hPT, rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨hPS, z, hz⟩ := Finset.mem_filter.mp hPT
    obtain ⟨hp, hheight, hdegree⟩ := hcurve P hPS
    have : P.IsPrime := hp
    obtain ⟨v, hv, he, _⟩ :=
      degree_one_zeroLocus_eq_rationalAffineLine P hheight hdegree z hz
    exact ⟨⟨P, hPS, rfl⟩, z, v, hv, he⟩

end
end CCDN
