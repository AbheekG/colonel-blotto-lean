import Blotto.GeneralPaperSelfReferenceCapacity

/-! Literal frames of the measured original-value length pass. Every reached
rational scan and natural accumulation is reserved once. Pending frames keep
only shared input references and short scalars/encoded work records, with one
owned index list. No complete input or child-work payload is copied per frame. -/
namespace Blotto.GeneralPaperValueInputLengthLifetime
open GeneralPaperEncodedScalarStorage (natBits fields)
open GeneralPaperValueInputWordLength (scan size)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def metadata (A n j a b out pq pl pj header F : ℕ) : ℕ :=
  fields A [n, j, a, b, out, pq, pl, pj, header, pq + pl, pq + pl + pj, F, pq + pl + pj + header] + 128 * A

def frameProfile (A n S F : ℕ) : ℕ := 13 * (natBits (n + S + F + 1) + A) + 160 * A

theorem metadata_bound (A n j a b out pq pl pj header F S : ℕ)
    (hj : j ≤ n) (ha : a ≤ S) (hb : b ≤ S) (ho : out ≤ S)
    (hF : pq + pl + pj + header ≤ F) : metadata A n j a b out pq pl pj header F ≤ frameProfile A n S F := by
  have h := GeneralPaperExpressionArrayReturns.fields_mono_cap A (n + S + F + 1)
    [n, j, a, b, out, pq, pl, pj, header, pq + pl, pq + pl + pj, F, pq + pl + pj + header] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 13 * (natBits (n + S + F + 1) + A) + 32 * A at h
  unfold metadata frameProfile
  omega

def frame {n : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) : List (Fin n) → ℕ
  | [] => fields A [n, 0, 0, 64 * A + 64] + 128 * A
  | j :: rest =>
    let measured := GeneralPaperStoredRationalWordLength.run model A (values.read j)
    let later := scan model A values rest
    let joined := GeneralPaperNaturalScalarStep.run model A .add measured.1 later.1
    let header := GeneralPaperEqualPackingExecution.unit A n + 64 * A + 64
    GeneralPaperWordLengthLifetime.rationalFoot model A (values.read j) +
      GeneralPaperNaturalScalarLifetime.footprint model A .add measured.1 later.1 +
      metadata A n j.val measured.1 later.1 joined.1 measured.2 later.2 joined.2 header
        (scan model A values (j :: rest)).2

def frames {n : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) : List (Fin n) → ℕ
  | [] => frame model A values []
  | j :: rest => frame model A values (j :: rest) + frames model A values rest

theorem frame_cons_bound {n : ℕ} (model : RationalCostModel) (A S F : ℕ) (values : FixedArrayTable n ℚ)
    (j : Fin n) (rest : List (Fin n)) (hS : size values (j :: rest) ≤ S)
    (hF : (scan model A values (j :: rest)).2 ≤ F) :
    frame model A values (j :: rest) ≤ rationalWordWidth (values.read j) +
      256 * (GeneralPaperStoredRationalWordLength.run model A (values.read j)).2 +
      32 * (GeneralPaperNaturalScalarStep.run model A .add (rationalWordWidth (values.read j)) (size values rest)).2 +
      frameProfile A n S F := by
  have hSize : rationalWordWidth (values.read j) + size values rest ≤ S := hS
  have hQ := GeneralPaperWordLengthLifetime.rational_bounded model A (values.read j)
  have hJ := GeneralPaperNaturalScalarLifetime.bounded model A .add (rationalWordWidth (values.read j)) (size values rest)
  have hM := metadata_bound A n j.val (rationalWordWidth (values.read j)) (size values rest)
    (rationalWordWidth (values.read j) + size values rest)
    (GeneralPaperStoredRationalWordLength.run model A (values.read j)).2
    (scan model A values rest).2
    (GeneralPaperNaturalScalarStep.run model A .add (rationalWordWidth (values.read j)) (size values rest)).2
    (GeneralPaperEqualPackingExecution.unit A n + 64 * A + 64)
    (scan model A values (j :: rest)).2 S j.isLt.le (by omega) (by omega) (by omega) (by
      simp only [scan, GeneralPaperStoredRationalWordLength.data, GeneralPaperValueInputWordLength.scan_data]
      omega)
  have hCap : frameProfile A n S (scan model A values (j :: rest)).2 ≤ frameProfile A n S F := by
    unfold frameProfile natBits
    gcongr
  simp only [frame, GeneralPaperStoredRationalWordLength.data, GeneralPaperValueInputWordLength.scan_data,
    GeneralPaperNaturalScalarStep.data, GeneralPaperNaturalScalarStep.Op.apply]
  exact (Nat.add_le_add (Nat.add_le_add hQ hJ) hM).trans (by omega)

theorem frames_bound {n : ℕ} (model : RationalCostModel) (A S F : ℕ) (values : FixedArrayTable n ℚ)
    (items : List (Fin n)) (hS : size values items ≤ S) (hF : (scan model A values items).2 ≤ F) :
    frames model A values items ≤ size values items + 256 * (scan model A values items).2 +
      (items.length + 1) * frameProfile A n S F := by
  induction items with
  | nil =>
    have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (n + S + F + 1) [n, 0, 0, 64 * A + 64] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      change 64 * A + 64 ≤ F at hF
      rcases hx with rfl | rfl | rfl | rfl <;> omega)
    change fields A _ ≤ 4 * (natBits (n + S + F + 1) + A) + 32 * A at hFields
    simp only [frames, frame, scan, size, List.map_nil, List.sum_nil, List.length_nil]
    unfold frameProfile
    omega
  | cons j rest ih =>
    have hSize : rationalWordWidth (values.read j) + size values rest ≤ S := hS
    have hRestF : (scan model A values rest).2 ≤ F := by
      simp only [scan, GeneralPaperStoredRationalWordLength.data, GeneralPaperValueInputWordLength.scan_data] at hF
      omega
    have hRest := ih (by omega) hRestF
    have hHead := frame_cons_bound model A S F values j rest hS hF
    simp only [frames]
    change frame model A values (j :: rest) + frames model A values rest ≤
      (rationalWordWidth (values.read j) + size values rest) +
      256 * (scan model A values (j :: rest)).2 + (rest.length + 1 + 1) * frameProfile A n S F
    simp only [scan, GeneralPaperStoredRationalWordLength.data, GeneralPaperValueInputWordLength.scan_data]
    nlinarith only [hRest, hHead]

def window {n : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) (borrowed : ℕ) : ℕ :=
  borrowed + GeneralPaperPackingAllocationLifetime.indicesLive A n n + frames model A values (List.finRange n) +
    fields A [n, (GeneralPaperValueInputWordLength.run model A values).1,
      (GeneralPaperValueInputWordLength.run model A values).2] + 128 * A

def profile (model : RationalCostModel) (A n S borrowed : ℕ) : ℕ :=
  let F := GeneralPaperValueInputWordLength.profile model A n S
  borrowed + GeneralPaperPackingAllocationLifetime.indicesProfile A n + S + 256 * F +
    (n + 1) * frameProfile A n S F + 3 * (natBits (n + S + F + 1) + A) + 160 * A

theorem bounded {n : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) (borrowed : ℕ) :
    window model A values borrowed ≤ profile model A n (GeneralPaperValueRoundingInputPrice.inputSize values) borrowed := by
  let S := GeneralPaperValueRoundingInputPrice.inputSize values
  let F := GeneralPaperValueInputWordLength.profile model A n S
  have hWork := GeneralPaperValueInputWordLength.work model A values
  have hScan : (scan model A values (List.finRange n)).2 ≤ F := by
    change (GeneralPaperValueInputWordLength.run model A values).2 ≤ F at hWork
    unfold GeneralPaperValueInputWordLength.run at hWork
    dsimp only at hWork
    omega
  have hFrames := frames_bound model A S F values (List.finRange n) (GeneralPaperValueInputWordLength.full_size values).le hScan
  simp only [GeneralPaperValueInputWordLength.full_size, List.length_finRange] at hFrames
  have hIndices := GeneralPaperPackingAllocationLifetime.indices_bound A n n le_rfl
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (n + S + F + 1)
    [n, (GeneralPaperValueInputWordLength.run model A values).1, (GeneralPaperValueInputWordLength.run model A values).2] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · omega
      · rw [GeneralPaperValueInputWordLength.data]; change S ≤ _; omega
      · change (GeneralPaperValueInputWordLength.run model A values).2 ≤ F at hWork; omega)
  change fields A _ ≤ 3 * (natBits (n + S + F + 1) + A) + 32 * A at hFields
  unfold window profile
  change _ ≤ borrowed + GeneralPaperPackingAllocationLifetime.indicesProfile A n + S + 256 * F +
    (n + 1) * frameProfile A n S F + 3 * (natBits (n + S + F + 1) + A) + 160 * A
  omega

end Blotto.GeneralPaperValueInputLengthLifetime
