import Blotto.GeneralPaperMixedRationalLengthStorage

/-! Actual A-priced value scans with physical word W. Each recursive frame
keeps actual child/parent prices; input and index lists are shared once. -/
namespace Blotto.GeneralPaperMixedValueLengthStorage
open GeneralPaperEncodedScalarStorage (fields)
open GeneralPaperValueInputWordLength (scan size)
open GeneralPaperValueInputLengthLifetime (metadata frameProfile metadata_bound)
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def frame {n : ℕ} (model : RationalCostModel) (W A : ℕ) (values : FixedArrayTable n ℚ) : List (Fin n) → ℕ
  | [] => fields W [n, 0, 0, 64 * A + 64] + 128 * W
  | j :: rest =>
    let measured := GeneralPaperStoredRationalWordLength.run model A (values.read j)
    let later := scan model A values rest
    let joined := GeneralPaperNaturalScalarStep.run model A .add measured.1 later.1
    let header := GeneralPaperEqualPackingExecution.unit A n + 64 * A + 64
    GeneralPaperMixedRationalLengthStorage.footprint model W A (values.read j) +
      GeneralPaperMixedPrimitiveStorage.scalarFoot model W A measured.1 later.1 joined.1 +
      metadata W n j.val measured.1 later.1 joined.1 measured.2 later.2 joined.2 header
        (scan model A values (j :: rest)).2

def frames {n : ℕ} (model : RationalCostModel) (W A : ℕ) (values : FixedArrayTable n ℚ) : List (Fin n) → ℕ
  | [] => frame model W A values []
  | j :: rest => frame model W A values (j :: rest) + frames model W A values rest

theorem frame_cons_bound {n : ℕ} (model : RationalCostModel) (W A S F : ℕ) (h : A ≤ W)
    (values : FixedArrayTable n ℚ) (j : Fin n) (rest : List (Fin n)) (hS : size values (j :: rest) ≤ S)
    (hF : (scan model W values (j :: rest)).2 ≤ F) :
    frame model W A values (j :: rest) ≤ rationalWordWidth (values.read j) +
      256 * (GeneralPaperStoredRationalWordLength.run model W (values.read j)).2 +
      32 * (GeneralPaperNaturalScalarStep.run model W .add (rationalWordWidth (values.read j)) (size values rest)).2 +
      frameProfile W n S F := by
  have hSize : rationalWordWidth (values.read j) + size values rest ≤ S := hS
  have hFA := (GeneralPaperMeasuredInitializerMonotonicity.value_scan model A W h values (j :: rest)).trans hF
  have hQ := GeneralPaperMixedRationalLengthStorage.bounded model W A h (values.read j)
  have hJ := GeneralPaperMixedPrimitiveStorage.scalar_bound model W A (rationalWordWidth (values.read j))
    (size values rest) (rationalWordWidth (values.read j) + size values rest) h
  change _ ≤ 32 * (GeneralPaperNaturalScalarStep.run model W .add (rationalWordWidth (values.read j))
    (size values rest)).2 at hJ
  have hM := metadata_bound W n j.val (rationalWordWidth (values.read j)) (size values rest)
    (rationalWordWidth (values.read j) + size values rest)
    (GeneralPaperStoredRationalWordLength.run model A (values.read j)).2 (scan model A values rest).2
    (GeneralPaperNaturalScalarStep.run model A .add (rationalWordWidth (values.read j)) (size values rest)).2
    (GeneralPaperEqualPackingExecution.unit A n + 64 * A + 64)
    (scan model A values (j :: rest)).2 S j.isLt.le (by omega) (by omega) (by omega) (by
      simp only [scan, GeneralPaperStoredRationalWordLength.data, GeneralPaperValueInputWordLength.scan_data]
      omega)
  have hCap : frameProfile W n S (scan model A values (j :: rest)).2 ≤ frameProfile W n S F := by
    unfold frameProfile GeneralPaperEncodedScalarStorage.natBits
    gcongr
  simp only [frame, GeneralPaperStoredRationalWordLength.data, GeneralPaperValueInputWordLength.scan_data,
    GeneralPaperNaturalScalarStep.data, GeneralPaperNaturalScalarStep.Op.apply]
  exact (Nat.add_le_add (Nat.add_le_add hQ hJ) hM).trans (by omega)

theorem frames_bound {n : ℕ} (model : RationalCostModel) (W A S F : ℕ) (h : A ≤ W)
    (values : FixedArrayTable n ℚ) (items : List (Fin n)) (hS : size values items ≤ S)
    (hF : (scan model W values items).2 ≤ F) :
    frames model W A values items ≤ size values items + 256 * (scan model W values items).2 +
      (items.length + 1) * frameProfile W n S F := by
  induction items with
  | nil =>
    have hf := GeneralPaperExpressionArrayReturns.fields_mono_cap W (n + S + F + 1) [n, 0, 0, 64 * A + 64] (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      change 64 * W + 64 ≤ F at hF
      rcases hz with rfl | rfl | rfl | rfl <;> omega)
    change fields W _ ≤ 4 * (GeneralPaperEncodedScalarStorage.natBits (n + S + F + 1) + W) + 32 * W at hf
    simp only [frames, frame, scan, size, List.map_nil, List.sum_nil, List.length_nil]
    unfold frameProfile
    omega
  | cons j rest ih =>
    have hSize : rationalWordWidth (values.read j) + size values rest ≤ S := hS
    have hRestF : (scan model W values rest).2 ≤ F := by
      simp only [scan, GeneralPaperStoredRationalWordLength.data, GeneralPaperValueInputWordLength.scan_data] at hF
      omega
    have hRest := ih (by omega) hRestF
    have hHead := frame_cons_bound model W A S F h values j rest hS hF
    simp only [frames]
    change frame model W A values (j :: rest) + frames model W A values rest ≤
      (rationalWordWidth (values.read j) + size values rest) + 256 * (scan model W values (j :: rest)).2 +
      (rest.length + 1 + 1) * frameProfile W n S F
    simp only [scan, GeneralPaperStoredRationalWordLength.data, GeneralPaperValueInputWordLength.scan_data]
    nlinarith only [hRest, hHead]

def window {n : ℕ} (model : RationalCostModel) (W A : ℕ) (values : FixedArrayTable n ℚ) (borrowed : ℕ) : ℕ :=
  borrowed + GeneralPaperPackingAllocationLifetime.indicesLive W n n + frames model W A values (List.finRange n) +
    fields W [n, (GeneralPaperValueInputWordLength.run model A values).1,
      (GeneralPaperValueInputWordLength.run model A values).2] + 128 * W

theorem bounded {n : ℕ} (model : RationalCostModel) (W A : ℕ) (h : A ≤ W)
    (values : FixedArrayTable n ℚ) (borrowed : ℕ) :
    window model W A values borrowed ≤ GeneralPaperValueInputLengthLifetime.profile model W n
      (GeneralPaperValueRoundingInputPrice.inputSize values) borrowed := by
  let S := GeneralPaperValueRoundingInputPrice.inputSize values
  let F := GeneralPaperValueInputWordLength.profile model W n S
  have hWork := GeneralPaperValueInputWordLength.work model W values
  change (GeneralPaperValueInputWordLength.run model W values).2 ≤ F at hWork
  have hActual : (GeneralPaperValueInputWordLength.run model A values).2 ≤ F :=
    (GeneralPaperMeasuredInitializerMonotonicity.values model A W h values).trans hWork
  have hScan : (scan model W values (List.finRange n)).2 ≤ F := by
    unfold GeneralPaperValueInputWordLength.run at hWork
    dsimp only at hWork
    omega
  have hFrames := frames_bound model W A S F h values (List.finRange n)
    (GeneralPaperValueInputWordLength.full_size values).le hScan
  simp only [GeneralPaperValueInputWordLength.full_size, List.length_finRange] at hFrames
  have hIndices := GeneralPaperPackingAllocationLifetime.indices_bound W n n le_rfl
  have hf := GeneralPaperExpressionArrayReturns.fields_mono_cap W (n + S + F + 1)
    [n, (GeneralPaperValueInputWordLength.run model A values).1, (GeneralPaperValueInputWordLength.run model A values).2] (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · omega
      · rw [GeneralPaperValueInputWordLength.data]; change S ≤ _; omega
      · omega)
  change fields W _ ≤ 3 * (GeneralPaperEncodedScalarStorage.natBits (n + S + F + 1) + W) + 32 * W at hf
  unfold window GeneralPaperValueInputLengthLifetime.profile
  change _ ≤ borrowed + GeneralPaperPackingAllocationLifetime.indicesProfile W n + S + 256 * F +
    (n + 1) * frameProfile W n S F + 3 * (GeneralPaperEncodedScalarStorage.natBits (n + S + F + 1) + W) + 160 * W
  omega

end Blotto.GeneralPaperMixedValueLengthStorage
