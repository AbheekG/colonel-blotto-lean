import Blotto.GeneralPaperSourceRowsExecution

/-! Native decoding and hard-budget checks consume the actual retained
full pre-update candidate table. Their rational output is the exact table
already used by the source-security and quantization arguments. -/
namespace Blotto.GeneralPaperSourceRowsContract
open GeneralPaperCodeAlphabet GeneralPaperSourceRowsExecution
open GeneralPaperCatalogueChosenMixture GeneralPaperCodeMixturePhysical
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem code_bound {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (i : Fin (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (j : Fin m) :
    ((GeneralPaperCatalogueFullTrajectory.table a k Qv weights Bc Br).read i).read j≤8*a.C := by
  rw [←candidate_table_code]
  exact ((empirical false a k Qv weights Bc Br).rows i j).isLt.le.trans_eq a.dyadic.symm

theorem source_data {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv qbar : ℕ)
    (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (run bits model W a (GeneralPaperCatalogueFullTrajectory.table a k Qv weights Bc Br) Bc).1.1=
      GeneralPaperCatalogueRationalTrajectory.rows a k Qv qbar weights Bc Br := by
  rw [data bits model W qbar]
  rfl

theorem source_checks {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv q qbar : ℕ)
    (a : Alphabet) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hw : ∑ j,weights.read j=Qv) (Bc Br : ℚ) (hB : 0≤Bc)
    (hq : 0<q) (hCap : q≤qbar) (hDen : Bc.den∣q) :
    (run bits model W a (GeneralPaperCatalogueFullTrajectory.table a k Qv weights Bc Br) Bc).1.2=true := by
  apply (checks bits model W a _ Bc).2
  rw [source_data bits model W k Qv qbar]
  intro i
  have h := GeneralPaperCatalogueRationalTrajectory.every_row_feasible a k Qv q qbar hm hQv weights hw Bc Br hB hq hCap hDen i
  dsimp only [Feasible] at h
  constructor
  · intro j
    exact_mod_cast h.1 j
  · exact_mod_cast h.2

theorem zero_field_checks {T : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable 0 ℕ)) (B : ℚ) (hB : 0≤B) :
    (run bits model W a codes B).1.2=true := by
  apply (checks bits model W a codes B).2
  intro i
  exact ⟨fun j => Fin.elim0 j,by simpa using hB⟩

theorem native_table {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (produced : Array (FixedArrayTable m ℕ))
    (hp : produced=(GeneralPaperGeometricSourceExecution.run bits (index bits) model W k Qv a c hc
      (GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br)
      (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs).1.2)
    (hs : produced.size=(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) :
    (⟨produced,hs⟩ : FixedArrayTable _ _)=GeneralPaperCatalogueFullTrajectory.table a k Qv weights Bc Br := by
  have h := congrArg Prod.snd (GeneralPaperGeometricSourceExecution.data bits (index bits) model W k Qv a c hc
    weights Bc Br (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs le_rfl)
  unfold GeneralPaperCatalogueFullTrajectory.table
  congr 1
  exact hp.trans h

theorem native_postprocessing {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv q qbar : ℕ)
    (a : Alphabet) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (produced : Array (FixedArrayTable m ℕ))
    (hp : produced=(GeneralPaperGeometricSourceExecution.run bits (index bits) model W k Qv a c hc
      (GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br)
      (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs).1.2)
    (hs : produced.size=(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows)
    (hm : 0<m) (hQv : 0<Qv) (hw : ∑ j,weights.read j=Qv) (hB : 0≤Bc)
    (hq : 0<q) (hCap : q≤qbar) (hDen : Bc.den∣q) :
    (run bits model W a ⟨produced,hs⟩ Bc).1.1=
      GeneralPaperCatalogueRationalTrajectory.rows a k Qv qbar weights Bc Br ∧
    (run bits model W a ⟨produced,hs⟩ Bc).1.2=true := by
  rw [native_table bits model W k Qv a c hc weights Bc Br produced hp hs]
  exact ⟨source_data bits model W k Qv qbar a weights Bc Br,
    source_checks bits model W k Qv q qbar a hm hQv weights hw Bc Br hB hq hCap hDen⟩

theorem source_bit_work {m : ℕ} (model : RationalCostModel) (W k Qv t : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hB : RationalHeight Bc t) :
    (run true model W a (GeneralPaperCatalogueFullTrajectory.table a k Qv weights Bc Br) Bc).2≤
      bitProfile model W (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows m t a :=
  bit_work model W t a _ Bc hB (code_bound a k Qv weights Bc Br)

theorem source_arithmetic_work {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (run false model 1 a (GeneralPaperCatalogueFullTrajectory.table a k Qv weights Bc Br) Bc).2≤
      arithmeticProfile (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows m a :=
  arithmetic_work model a _ Bc

end Blotto.GeneralPaperSourceRowsContract
