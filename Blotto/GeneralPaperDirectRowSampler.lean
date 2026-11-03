import Blotto.GeneralPaperUnreplacedShape
import Blotto.AveragedBitMixtures

/-! Direct whole-row sampling for the identity reduction branch. Only one
selected dictionary row is extracted and scaled. A uniform shift block is
consumed but does not change that row, preserving the paper's common
power-of-two row/shift interface. No full support is materialized. -/
namespace Blotto.GeneralPaperDirectRowSampler
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def draw {n m T K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hm : m=n) (c : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) : FixedArrayTable n ℚ×ℕ :=
  let row := GeneralPaperStoredDictionaryRows.row index A (GeneralPaperPhysicalFieldCast.columns hm columns) i
  let scaled := GeneralPaperRationalOutputScale.run price index A c row.1
  (scaled.1,row.2+scaled.2+64*A)

theorem real_draw {n m T K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hm : m=n) (c : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (hT : 0<T) (i : Fin T) :
    (fun j => ((draw price index A hm c columns i).1.read j:ℝ))=
      GeneralPaperFieldRelabel.allocation (finCongr hm.symm)
        (scaleAllocation (c:ℝ) ((GeneralPaperDictionary.law (GeneralPaperRowQuantizer.dictionary columns) hT).realRow i)) := by
  dsimp only [draw]
  rw [GeneralPaperRationalOutputScale.real_data,GeneralPaperStoredDictionaryRows.real_row,
    GeneralPaperPhysicalFieldCast.real_row]
  rfl

theorem feasible {n m T K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hm : m=n) (c : ℚ) (hc : 0≤c)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (hT : 0<T) (hK : 0<K)
    (hUnit : GeneralPaperTransferPreparation.UnitDictionary (GeneralPaperRowQuantizer.dictionary columns) hT hK) (i : Fin T) :
    Feasible (c:ℝ) (fun j => ((draw price index A hm c columns i).1.read j:ℝ)) := by
  rw [real_draw price index A hm c columns hT i]
  apply (GeneralPaperFieldRelabel.feasible_iff _ _ _).mpr
  simpa only [mul_one] using scaleAllocation_feasible (by exact_mod_cast hc : (0:ℝ)≤c) (hUnit.feasible i)

theorem height {n m T K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hm : m=n) (c : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (C H : ℕ)
    (hc : RationalHeight c C) (hColumns : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H) (i : Fin T) (j : Fin n) :
    RationalHeight ((draw price index A hm c columns i).1.read j) (C+H) :=
  GeneralPaperRationalOutputScale.height price index A c _ C H hc
    (GeneralPaperStoredDictionaryRows.row_height index A _ H (GeneralPaperPhysicalFieldCast.height hm columns H hColumns) i) j

theorem work {n m T K : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A : ℕ) (hA : 1≤A)
    (hm : m=n) (c : ℚ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (C H : ℕ)
    (hc : RationalHeight c C) (hColumns : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H)
    (hIndex : ∀ j≤n,index (binaryWordWidth (j+1))≤A) (i : Fin T) :
    (draw price index A hm c columns i).2≤n*(2*price (1+2*(C+H))+192*A)+88*(n+1)*A+64*A := by
  have hr := GeneralPaperStoredDictionaryRows.row_work index A hA (GeneralPaperPhysicalFieldCast.columns hm columns) i hIndex
  have hs := GeneralPaperRationalOutputScale.work price index hMono A C H hA c _ hc
    (GeneralPaperStoredDictionaryRows.row_height index A _ H (GeneralPaperPhysicalFieldCast.height hm columns H hColumns) i) hIndex
  unfold draw
  dsimp only
  nlinarith only [hr,hs]

theorem arithmetic_work {n m T K : ℕ} (hm : m=n) (c : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) :
    (draw (fun _ => 1) (fun _ => 1) 1 hm c columns i).2≤282*n+152 := by
  have hr := GeneralPaperStoredDictionaryRows.row_work (fun _ => 1) 1 (by decide)
    (GeneralPaperPhysicalFieldCast.columns hm columns) i (fun _ _ => le_rfl)
  have hs := GeneralPaperRationalOutputScale.arithmetic_work c
    (GeneralPaperStoredDictionaryRows.row (fun _ => 1) 1 (GeneralPaperPhysicalFieldCast.columns hm columns) i).1
  unfold draw
  dsimp only
  nlinarith only [hr,hs]

def run {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (hm : m=n) (c : ℚ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (fresh : Fin (R+L) → Bool) : GeneralPaperNativeFairSampler.Result n :=
  let buffer := GeneralPaperNativeFreshBuffer.run primitive A fresh
  let selected := GeneralPaperNativeDyadicBlocks.run primitive A R L T S hT hS buffer.1.1
  let sampled := draw price index A hm c columns selected.row
  ⟨sampled.1,buffer.1.2,selected.reads,buffer.2+selected.work+sampled.2+64*A⟩

theorem data {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (hm : m=n) (c : ℚ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (fresh : Fin (R+L) → Bool) :
    (run price index primitive A R L T S hT hS hm c columns fresh).output=
      (draw price index A hm c columns (Fin.cast hT.symm (bitIndex R (firstBitBlock R L fresh)))).1 := by
  dsimp only [run]
  rw [GeneralPaperNativeFreshBuffer.run_data,GeneralPaperNativeDyadicBlocks.row_data]

theorem fresh_reads {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (hm : m=n) (c : ℚ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (fresh : Fin (R+L) → Bool) :
    (run price index primitive A R L T S hT hS hm c columns fresh).freshReads=R+L :=
  GeneralPaperNativeFreshBuffer.run_reads primitive A fresh

theorem buffer_reads {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (hm : m=n) (c : ℚ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (fresh : Fin (R+L) → Bool) :
    (run price index primitive A R L T S hT hS hm c columns fresh).bufferReads=R+L :=
  GeneralPaperNativeDyadicBlocks.reads primitive A R L T S hT hS _

theorem logarithmic_bits {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (hm : m=n) (c : ℚ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (fresh : Fin (R+L) → Bool) :
    (run price index primitive A R L T S hT hS hm c columns fresh).freshReads=Nat.log2 (T*S) := by
  rw [fresh_reads,hT,hS,←pow_add,Nat.log2_two_pow]

noncomputable def law {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (hm : m=n) (c : ℚ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) : Mixed n :=
  (fairBitLaw (R+L)).map (fun fresh j => ((run price index primitive A R L T S hT hS hm c columns fresh).output.read j:ℝ))

theorem relabel_uniform {n m T : ℕ} (e : Fin n ≃ Fin m) (hT : 0<T) (rows : Fin T → Allocation m) :
    GeneralPaperFieldRelabel.law e (GeneralPaperUniformRowLaw.law hT rows)=
      GeneralPaperUniformRowLaw.law hT (fun i => GeneralPaperFieldRelabel.allocation e (rows i)) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (GeneralPaperFieldRelabel.allocation e) (mixtureMeasure (fun _:Fin T => 1/(T:ℝ))
    (fun i => GeneralPaperUniformRowLaw.point (rows i)))=
      mixtureMeasure (fun _:Fin T => 1/(T:ℝ)) (fun i => GeneralPaperUniformRowLaw.point (GeneralPaperFieldRelabel.allocation e (rows i)))
  rw [mixtureMeasure_map _ _ _ (GeneralPaperFieldRelabel.measurable_allocation e)]
  change Measure.sum _=Measure.sum _
  congr 1
  funext i
  change ENNReal.ofReal (1/(T:ℝ)) • Measure.map (GeneralPaperFieldRelabel.allocation e) (Measure.dirac (rows i))=_
  rw [Measure.map_dirac' (GeneralPaperFieldRelabel.measurable_allocation e)]
  rfl

theorem uniform {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (hm : m=n) (c : ℚ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    law price index primitive A R L T S hT hS hm c columns=
      GeneralPaperUniformRowLaw.law (hT ▸ Nat.two_pow_pos R) (fun i =>
        GeneralPaperFieldRelabel.allocation (finCongr hm.symm)
          (scaleAllocation (c:ℝ) ((GeneralPaperDictionary.law (GeneralPaperRowQuantizer.dictionary columns)
            (hT ▸ Nat.two_pow_pos R)).realRow i))) := by
  subst T
  subst S
  unfold law
  have hDraw : (fun fresh j => ((run price index primitive A R L (2^R) (2^L) rfl rfl hm c columns fresh).output.read j:ℝ))=
      (fun fresh => GeneralPaperFieldRelabel.allocation (finCongr hm.symm)
        (scaleAllocation (c:ℝ) ((GeneralPaperDictionary.law (GeneralPaperRowQuantizer.dictionary columns)
          (Nat.two_pow_pos R)).realRow (bitIndex R (firstBitBlock R L fresh))))) := by
    funext fresh
    rw [data]
    exact real_draw price index A hm c columns (Nat.two_pow_pos R) _
  rw [hDraw]
  rw [fairBitBlocks_law R L (fun row _ => GeneralPaperFieldRelabel.allocation (finCongr hm.symm)
    (scaleAllocation (c:ℝ) ((GeneralPaperDictionary.law (GeneralPaperRowQuantizer.dictionary columns) (Nat.two_pow_pos R)).realRow (bitIndex R row))))]
  rw [averaged_fairBit_constant]
  exact GeneralPaperFairIndexLaw.uniform R (fun i => GeneralPaperFieldRelabel.allocation (finCongr hm.symm)
    (scaleAllocation (c:ℝ) ((GeneralPaperDictionary.law (GeneralPaperRowQuantizer.dictionary columns) (Nat.two_pow_pos R)).realRow i)))

theorem law_data {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (hm : m=n) (c : ℚ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    law price index primitive A R L T S hT hS hm c columns=
      GeneralPaperFieldRelabel.law (finCongr hm.symm) (scaleLaw (c:ℝ)
        (GeneralPaperDictionary.law (GeneralPaperRowQuantizer.dictionary columns) (hT ▸ Nat.two_pow_pos R)).law) := by
  rw [uniform,←GeneralPaperDictionaryUniformLaw.dictionary,GeneralPaperDictionaryUniformLaw.scaled_uniform,relabel_uniform]


theorem run_feasible {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (hm : m=n) (c : ℚ) (hc : 0≤c) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (hK : 0<K)
    (hUnit : GeneralPaperTransferPreparation.UnitDictionary (GeneralPaperRowQuantizer.dictionary columns) (hT ▸ Nat.two_pow_pos R) hK)
    (fresh : Fin (R+L) → Bool) :
    Feasible (c:ℝ) (fun j => ((run price index primitive A R L T S hT hS hm c columns fresh).output.read j:ℝ)) := by
  rw [data]
  exact feasible price index A hm c hc columns (hT ▸ Nat.two_pow_pos R) hK hUnit _

theorem run_arithmetic_work {n m K : ℕ} (R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (hm : m=n) (c : ℚ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (fresh : Fin (R+L) → Bool) :
    (run (fun _ => 1) (fun _ => 1) (fun _ => 1) 1 R L T S hT hS hm c columns fresh).work≤282*n+144*(R+L)+410 := by
  have hf := GeneralPaperNativeFreshBuffer.arithmetic_work 1 fresh
  have hb := GeneralPaperNativeDyadicBlocks.arithmetic_work 1 R L T S hT hS
    (GeneralPaperNativeFreshBuffer.run (fun _ => 1) 1 fresh).1.1
  have hd := arithmetic_work hm c columns
    (GeneralPaperNativeDyadicBlocks.run (fun _ => 1) 1 R L T S hT hS
      (GeneralPaperNativeFreshBuffer.run (fun _ => 1) 1 fresh).1.1).row
  unfold run
  dsimp only
  nlinarith only [hf,hb,hd]

theorem independent_players {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (hm : m=n) (c d : ℚ) (rich poor : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    Measure.map (fun fresh =>
      ((fun j => ((run price index primitive A R L T S hT hS hm c rich (firstBitBlock (R+L) (R+L) fresh)).output.read j:ℝ)),
        (fun j => ((run price index primitive A R L T S hT hS hm d poor (secondBitBlock (R+L) (R+L) fresh)).output.read j:ℝ))))
      (fairBitLaw ((R+L)+(R+L)) : Measure (Fin ((R+L)+(R+L)) → Bool))=
      (law price index primitive A R L T S hT hS hm c rich : Measure (Allocation n)).prod
        (law price index primitive A R L T S hT hS hm d poor : Measure (Allocation n)) :=
  fairBitBlocks_map_product (R+L) (R+L)
    (fun fresh j => ((run price index primitive A R L T S hT hS hm c rich fresh).output.read j:ℝ))
    (fun fresh j => ((run price index primitive A R L T S hT hS hm d poor fresh).output.read j:ℝ))

end Blotto.GeneralPaperDirectRowSampler
