import Blotto.GeneralPaperCachedCircleRows
import Blotto.GeneralPaperNamedCircleBitDraw

/-! A fresh draw reads one selected cached row and the shared original
light-field metadata. The old complete Prepared table is an erased law
specification only; no full-table map or preparation executes on a draw. -/
namespace Blotto.GeneralPaperCachedCircleSampler
open GeneralPaperCachedCircleRows
open GeneralPaperOriginalDrawEquilibrium GeneralPaperNativeSelectedSecurity
open GeneralPaperOriginalSourceValueDriver
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def draw {n T K S : ℕ} (bits : Bool) (model : RationalCostModel) (A : ℕ)
    (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : Pair T o.representatives K o.classified) (reciprocal : Bool) (i : Fin T) (l : Fin S) : FixedArrayTable n ℚ×ℕ :=
  let rows := if reciprocal then prepared.poor else prepared.rich
  if bits then
    let selected := materialize (fun w => w) A o.classified rows prepared.common i
    let output := GeneralPaperNamedCircleBitDraw.run model A o.classified.lightWeight S o.classified hR c selected.1 l
    (output.1,selected.2+output.2+64*A)
  else
    let selected := materialize (fun _ => 1) 1 o.classified rows prepared.common i
    let output := GeneralPaperNamedCircleExecution.drawArithmetic model o.classified.lightWeight S o.classified hR c selected.1 l
    (output.1,selected.2+output.2+64)

theorem draw_data {n T K S : ℕ} (bits : Bool) (model : RationalCostModel) (A : ℕ)
    (price index : ℕ → ℕ) (Ap : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives) (hR : 0<o.representatives) (c : ℚ)
    (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K) (reciprocal : Bool) (i : Fin T) (l : Fin S) :
    (draw bits model A o hR c (pair price index Ap o hm columns).1 reciprocal i l).1=
      (GeneralPaperOriginalCirclePreparation.draw model o hR c
        (GeneralPaperOriginalCirclePreparation.run price index Ap o hm (if reciprocal then columns.poor else columns.rich)).1 i l).1 := by
  cases bits
  · dsimp only [draw,Bool.false_eq_true,ite_false]
    rw [pair_materialize price index (fun _ => 1) Ap 1 o hm columns reciprocal i]
    rfl
  · dsimp only [draw,ite_true]
    rw [GeneralPaperNamedCircleBitDraw.data,pair_materialize price index (fun w => w) Ap A o hm columns reciprocal i]
    rfl

def run {n K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : Pair T o.representatives K o.classified) (reciprocal : Bool) (fresh : Fin (R+L) → Bool) :
    GeneralPaperNativeFairSampler.Result n :=
  let buffer := GeneralPaperNativeFreshBuffer.run primitive A fresh
  let selected := GeneralPaperNativeDyadicBlocks.run primitive A R L T S hT hS buffer.1.1
  let sampled := draw bits model A o hR c prepared reciprocal selected.row selected.shift
  ⟨sampled.1,buffer.1.2,selected.reads,buffer.2+selected.work+sampled.2+64*A⟩

theorem data {n K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (price index : ℕ → ℕ) (Ap : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives) (hR : 0<o.representatives) (c : ℚ)
    (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K) (reciprocal : Bool) (fresh : Fin (R+L) → Bool) :
    (run bits primitive A R L T S hT hS model o hR c (pair price index Ap o hm columns).1 reciprocal fresh).output=
      (GeneralPaperNativeFairSampler.run primitive A R L T S hT hS model o hR c
        (GeneralPaperOriginalCirclePreparation.run price index Ap o hm (if reciprocal then columns.poor else columns.rich)).1 fresh).output := by
  dsimp only [run]
  rw [draw_data]
  rfl

theorem fresh_reads {n K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : Pair T o.representatives K o.classified) (reciprocal : Bool) (fresh : Fin (R+L) → Bool) :
    (run bits primitive A R L T S hT hS model o hR c prepared reciprocal fresh).freshReads=R+L :=
  GeneralPaperNativeFreshBuffer.run_reads primitive A fresh

theorem buffer_reads {n K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : Pair T o.representatives K o.classified) (reciprocal : Bool) (fresh : Fin (R+L) → Bool) :
    (run bits primitive A R L T S hT hS model o hR c prepared reciprocal fresh).bufferReads=R+L :=
  GeneralPaperNativeDyadicBlocks.reads primitive A R L T S hT hS _

theorem logarithmic_bits {n K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : Pair T o.representatives K o.classified) (reciprocal : Bool) (fresh : Fin (R+L) → Bool) :
    (run bits primitive A R L T S hT hS model o hR c prepared reciprocal fresh).freshReads=Nat.log2 (T*S) := by
  rw [fresh_reads,hT,hS,←pow_add,Nat.log2_two_pow]

noncomputable def law {n K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : Pair T o.representatives K o.classified) (reciprocal : Bool) : Mixed n :=
  (fairBitLaw (R+L)).map (fun fresh => fun j =>
    ((run bits primitive A R L T S hT hS model o hR c prepared reciprocal fresh).output.read j:ℝ))

theorem law_data {n K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (price index : ℕ → ℕ) (Ap : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives) (hR : 0<o.representatives) (c : ℚ)
    (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K) (reciprocal : Bool) :
    law bits primitive A R L T S hT hS model o hR c (pair price index Ap o hm columns).1 reciprocal=
      GeneralPaperNativeFairSamplerLaw.law primitive A R L T S hT hS model o hR c
        (GeneralPaperOriginalCirclePreparation.run price index Ap o hm (if reciprocal then columns.poor else columns.rich)).1 := by
  unfold law GeneralPaperNativeFairSamplerLaw.law
  congr 1
  funext fresh j
  rw [data]

theorem independent_players {n K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c d : ℚ)
    (prepared : Pair T o.representatives K o.classified) :
    MeasureTheory.Measure.map (fun fresh =>
      ((fun j => ((run bits primitive A R L T S hT hS model o hR c prepared false (firstBitBlock (R+L) (R+L) fresh)).output.read j:ℝ)),
        (fun j => ((run bits primitive A R L T S hT hS model o hR d prepared true (secondBitBlock (R+L) (R+L) fresh)).output.read j:ℝ))))
      (fairBitLaw ((R+L)+(R+L)) : MeasureTheory.Measure (Fin ((R+L)+(R+L)) → Bool))=
      (law bits primitive A R L T S hT hS model o hR c prepared false : MeasureTheory.Measure (Allocation n)).prod
        (law bits primitive A R L T S hT hS model o hR d prepared true : MeasureTheory.Measure (Allocation n)) :=
  fairBitBlocks_map_product (R+L) (R+L)
    (fun fresh j => ((run bits primitive A R L T S hT hS model o hR c prepared false fresh).output.read j:ℝ))
    (fun fresh j => ((run bits primitive A R L T S hT hS model o hR d prepared true fresh).output.read j:ℝ))


theorem original_bit_epsilon {n : ℕ} (bits : Bool) (model : RationalCostModel) (Wv Ws k : ℕ) (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1)
    (hk : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index primitive : ℕ → ℕ) (A : ℕ)
    (hReplace : (GeneralPaperOriginalValueReduction.run true model Wv k values).1.replaced=true) :
    let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
    let redValues := GeneralPaperOriginalValueReduction.selector true model Wv k values v hv
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    let hR := GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values
    ∃ (hm:o.m=o.classified.heavy.size+o.representatives),∃ (physical : Columns
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      o.m (GeneralPaperProxyParameters.prepare o.m k).K),∃ pair,
      (bit model Wv Ws k values v hv b hb).1.physical=some physical ∧
      GeneralPaperRoundedValueCanonical.run true model Wv k o.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧ Matches physical pair ∧
      let cached := (GeneralPaperCachedCircleRows.pair price index A o hm physical).1
      let μ := law bits primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift model o hR 1 cached false
      let ν := law bits primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift model o hR b cached true
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧
      security v.values 1 ν+security v.values (b:ℝ) μ<1+179*(1/(2:ℝ)^k)/320 ∧
      regret v.values 1 μ ν≤(epsilon:ℝ) ∧ regret v.values (b:ℝ) ν μ≤(epsilon:ℝ) := by
  obtain ⟨hm,physical,pair,hRun,hSource,hMatches,hA,hB,hSec,hRich,hPoor⟩ :=
    GeneralPaperOriginalSourceValueContract.sampled_original_bit_epsilon model Wv Ws k epsilon hE hOne hk values v hv b hb price index primitive A hReplace
  dsimp only
  refine ⟨hm,physical,pair,hRun,hSource,hMatches,?_⟩
  simpa only [law_data,Bool.false_eq_true,ite_false,ite_true] using
    (And.intro hA (And.intro hB (And.intro hSec (And.intro hRich hPoor))))

theorem original_arithmetic_epsilon {n : ℕ} (bits : Bool) (model : RationalCostModel) (k : ℕ) (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1)
    (hk : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index primitive : ℕ → ℕ) (A : ℕ)
    (hReplace : (GeneralPaperOriginalValueReduction.run false model 1 k values).1.replaced=true) :
    let o := (GeneralPaperOriginalValueReduction.run false model 1 k values).1
    let redValues := GeneralPaperOriginalValueReduction.selector false model 1 k values v hv
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    let hR := GeneralPaperNativeCircleLoss.original_representatives_positive false model 1 k values
    ∃ (hm:o.m=o.classified.heavy.size+o.representatives),∃ (physical : Columns
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      o.m (GeneralPaperProxyParameters.prepare o.m k).K),∃ pair,
      (GeneralPaperOriginalSourceValueDriver.arithmetic model k values v hv (b:ℝ)).1.physical=some physical ∧
      GeneralPaperRoundedValueCanonical.run false model 1 k o.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧ Matches physical pair ∧
      let cached := (GeneralPaperCachedCircleRows.pair price index A o hm physical).1
      let μ := law bits primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift model o hR 1 cached false
      let ν := law bits primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift model o hR b cached true
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧
      security v.values 1 ν+security v.values (b:ℝ) μ<1+179*(1/(2:ℝ)^k)/320 ∧
      regret v.values 1 μ ν≤(epsilon:ℝ) ∧ regret v.values (b:ℝ) ν μ≤(epsilon:ℝ) := by
  obtain ⟨hm,physical,pair,hRun,hSource,hMatches,hA,hB,hSec,hRich,hPoor⟩ :=
    GeneralPaperOriginalSourceValueContract.sampled_original_arithmetic_epsilon model k epsilon hE hOne hk values v hv b hb price index primitive A hReplace
  dsimp only
  refine ⟨hm,physical,pair,hRun,hSource,hMatches,?_⟩
  simpa only [law_data,Bool.false_eq_true,ite_false,ite_true] using
    (And.intro hA (And.intro hB (And.intro hSec (And.intro hRich hPoor))))

end Blotto.GeneralPaperCachedCircleSampler
