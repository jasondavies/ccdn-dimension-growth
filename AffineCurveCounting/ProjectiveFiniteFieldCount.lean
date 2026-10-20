module

public import AffineCurveCounting.ProjectiveResidueCardinality
public import AffineCurveCounting.HomogeneousChartIrreducible
public import AffineCurveCounting.SharpPlaneCount

/-! A sharp finite-field count for an actual irreducible homogeneous plane
curve. Chart irreducibility, its full degree and the infinity correction
are proved; the affine input is the formalized Stepanov estimate. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem projective_plane_finite_field_card_bound {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hsize : 27 * (d : ℝ) ^ 4 < p) :
    (Fintype.card (ProjectivePlaneResidue f p) : ℝ) ≤
      p + 162 * (d : ℝ) ^ 2 * Real.sqrt p := by
  classical
  let q := map (Int.castRingHom (ZMod p)) f
  have hX := variable_not_dvd_irreducible_homogeneous q (hf.map _) hir hd 0
  have hchart := affineChart_irreducible_of_not_variable_dvd q (hf.map _) hir hX
  have hdeg := affineChart_degree_of_not_variable_dvd q (hf.map _) hX
  have hproper := irreducible_homogeneous_not_dvd_variable q (hf.map _) hir hd 0
  have hcard := projectivePlaneResidue_card_le_affine_add_degree f hf hir hproper
  have hz (a : PlaneResidue (planeAffineChart f) p) :
      eval a.val (affineChart 2 q) = 0 := by
    rw [affineChart_map, eval_map]
    exact a.property
  have ha := plane_finite_field_card_bound p (affineChart 2 q) hchart
    (by rwa [hdeg]) (fun a : PlaneResidue (planeAffineChart f) p => a.val)
    Subtype.val_injective hz
  rw [hdeg] at ha
  have hcardR : (Fintype.card (ProjectivePlaneResidue f p) : ℝ) ≤
      Fintype.card (PlaneResidue (planeAffineChart f) p) + d := by exact_mod_cast hcard
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hsqrt : 1 ≤ Real.sqrt (p : ℝ) := Real.one_le_sqrt.mpr
    (by exact_mod_cast (Fact.out : p.Prime).one_le)
  have hdsqrt : (d : ℝ) ≤ (d : ℝ) ^ 2 * Real.sqrt p := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt (sq_nonneg (d : ℝ))
    nlinarith
  linarith

end
end AffineCurveCounting
