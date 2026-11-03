import Blotto.IndexedLoopMetadataWork
import Blotto.BinaryFrameEncodingCost
import Blotto.BinaryPrefixCounterWork
import Blotto.BinaryPayloadBufferMetadata

/-! Additional iterator/buffer/control costs for output framing. Literal
payload/sign/test-bit costs are preserved in the existing encoder ledger.
Conservative full-prefix buffer copying avoids an ownership assumption;
physical addresses/backend/allocator records remain separate. -/

namespace Blotto.BinaryNatFrame

def encodingMetadataBitWork (primitive : ℕ → ℕ) (n : ℕ) : ℕ :=
  let width := binaryWordWidth n
  indexedLoopMetadataBitWork primitive 0 width + prefixCounterBitWork primitive width (List.replicate width false) +
    BinaryPayload.bufferCopyWork width 0 + 2 * width

def encodingMetadataBound (c width : ℕ) : ℕ :=
  indexedLoopMetadataBound c width + (width + 1) * ((4 + 2 * c) * binaryWordWidth width + 1) +
    width * (width + 1) + 2 * width

theorem encodingMetadataBound_mono (c : ℕ) : Monotone (encodingMetadataBound c) := by
  intro a b hab
  have hLoop := indexedLoopMetadataBound_mono c hab
  have hWidth := binaryWordWidth_mono hab
  unfold encodingMetadataBound
  gcongr

theorem encodingMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (n : ℕ) :
    encodingMetadataBitWork primitive n ≤ encodingMetadataBound c (binaryWordWidth n) := by
  have hLoop := indexedLoopMetadataBitWork_bound primitive c hPrimitive (binaryWordWidth n)
  have hRuler := prefixCounterBitWork_bound primitive c hPrimitive (binaryWordWidth n) (List.replicate (binaryWordWidth n) false)
  simp only [List.length_replicate] at hRuler
  unfold encodingMetadataBitWork encodingMetadataBound
  dsimp only
  rw [BinaryPayload.bufferCopyWork_eq]
  simp only [Nat.mul_zero, Nat.zero_add]
  omega

end Blotto.BinaryNatFrame
namespace Blotto.BinaryRatFrame

def encodingMetadataBitWork (primitive : ℕ → ℕ) (q : ℚ) : ℕ :=
  BinaryNatFrame.encodingMetadataBitWork primitive q.num.natAbs + BinaryNatFrame.encodingMetadataBitWork primitive q.den + 2

theorem encodingMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (q : ℚ) (W : ℕ) (hWidth : rationalWordWidth q ≤ W) :
    encodingMetadataBitWork primitive q ≤ 2 * BinaryNatFrame.encodingMetadataBound c W + 2 := by
  have hNum : binaryWordWidth q.num.natAbs ≤ W := by unfold rationalWordWidth at hWidth; omega
  have hDen : binaryWordWidth q.den ≤ W := by unfold rationalWordWidth at hWidth; omega
  have hN := (BinaryNatFrame.encodingMetadataBitWork_bound primitive c hPrimitive q.num.natAbs).trans
    (BinaryNatFrame.encodingMetadataBound_mono c hNum)
  have hD := (BinaryNatFrame.encodingMetadataBitWork_bound primitive c hPrimitive q.den).trans
    (BinaryNatFrame.encodingMetadataBound_mono c hDen)
  unfold encodingMetadataBitWork
  omega

end Blotto.BinaryRatFrame
namespace Blotto.BinaryRatListFrame

def encodingMetadataBitWork (primitive : ℕ → ℕ) (values : List ℚ) : ℕ :=
  (values.map (BinaryRatFrame.encodingMetadataBitWork primitive)).sum +
    indexedLoopMetadataBitWork primitive 0 (values.length + concatenationCopyWork values 0) +
      indexedLoopMetadataBitWork primitive 0 (encode values).length

theorem encodingMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (values : List ℚ) (W : ℕ)
    (hWidth : ∀ q ∈ values, rationalWordWidth q ≤ W) :
    encodingMetadataBitWork primitive values ≤ values.length * (2 * BinaryNatFrame.encodingMetadataBound c W + 2) +
      indexedLoopMetadataBound c (values.length + (values.length + 1) * values.length * (2 * W + 1)) +
        indexedLoopMetadataBound c (values.length * (2 * W + 1)) := by
  have hFrames : (values.map (BinaryRatFrame.encodingMetadataBitWork primitive)).sum ≤
      values.length * (2 * BinaryNatFrame.encodingMetadataBound c W + 2) := by
    induction values with
    | nil => simp
    | cons q rest ih =>
      have hQ := BinaryRatFrame.encodingMetadataBitWork_bound primitive c hPrimitive q W (hWidth q (by simp))
      have hRest := ih (fun x hx => hWidth x (by simp [hx]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  have hWords : (values.map rationalWordWidth).sum ≤ values.length * W := by
    clear hFrames
    induction values with
    | nil => simp
    | cons q rest ih =>
      have hQ := hWidth q (by simp)
      have hRest := ih (fun x hx => hWidth x (by simp [hx]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  have hBits : (encode values).length ≤ values.length * (2 * W + 1) := by rw [encode_length]; nlinarith
  have hConcat := concatenationCopyWork_bound values 0
  simp only [Nat.zero_add] at hConcat
  have hCopy := Nat.mul_le_mul_left (values.length + 1) hBits
  have hVisits : values.length + concatenationCopyWork values 0 ≤
      values.length + (values.length + 1) * values.length * (2 * W + 1) := by nlinarith
  have hLoop := (indexedLoopMetadataBitWork_bound primitive c hPrimitive (values.length + concatenationCopyWork values 0)).trans
    (indexedLoopMetadataBound_mono c hVisits)
  have hOutput := (indexedLoopMetadataBitWork_bound primitive c hPrimitive (encode values).length).trans
    (indexedLoopMetadataBound_mono c hBits)
  unfold encodingMetadataBitWork
  omega

def rowEncodingMetadataBitWork {n : ℕ} (primitive : ℕ → ℕ) (row : Fin n → ℚ) : ℕ :=
  BinaryNatFrame.encodingMetadataBitWork primitive n + indexedLoopMetadataBitWork primitive 0 n +
    encodingMetadataBitWork primitive (List.ofFn row) + indexedLoopMetadataBitWork primitive 0 (BinaryNatFrame.encode n).length

def rowEncodingMetadataBound (c n W : ℕ) : ℕ :=
  BinaryNatFrame.encodingMetadataBound c (binaryWordWidth n) + indexedLoopMetadataBound c n +
    n * (2 * BinaryNatFrame.encodingMetadataBound c W + 2) +
      indexedLoopMetadataBound c (n + (n + 1) * n * (2 * W + 1)) + indexedLoopMetadataBound c (n * (2 * W + 1)) +
        indexedLoopMetadataBound c (2 * binaryWordWidth n + 1)

theorem rowEncodingMetadataBound_mono (c : ℕ) {n N W V : ℕ} (hn : n ≤ N) (hW : W ≤ V) :
    rowEncodingMetadataBound c n W ≤ rowEncodingMetadataBound c N V := by
  have hWidth := binaryWordWidth_mono hn
  have hDimension := BinaryNatFrame.encodingMetadataBound_mono c hWidth
  have hFields := BinaryNatFrame.encodingMetadataBound_mono c hW
  have hRows := indexedLoopMetadataBound_mono c hn
  have hAppend := indexedLoopMetadataBound_mono c
    (show n + (n + 1) * n * (2 * W + 1) ≤ N + (N + 1) * N * (2 * V + 1) by gcongr)
  have hOutput := indexedLoopMetadataBound_mono c (show n * (2 * W + 1) ≤ N * (2 * V + 1) by gcongr)
  have hHeader := indexedLoopMetadataBound_mono c (show 2 * binaryWordWidth n + 1 ≤ 2 * binaryWordWidth N + 1 by omega)
  unfold rowEncodingMetadataBound
  gcongr

theorem rowEncodingMetadataBitWork_bound {n : ℕ} (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (row : Fin n → ℚ) (W : ℕ)
    (hWidth : ∀ j, rationalWordWidth (row j) ≤ W) :
    rowEncodingMetadataBitWork primitive row ≤ rowEncodingMetadataBound c n W := by
  have hDimension := BinaryNatFrame.encodingMetadataBitWork_bound primitive c hPrimitive n
  have hRowLoop := indexedLoopMetadataBitWork_bound primitive c hPrimitive n
  have hFrames := encodingMetadataBitWork_bound primitive c hPrimitive (List.ofFn row) W
    (by intro q hq; rcases List.mem_ofFn.mp hq with ⟨j, rfl⟩; exact hWidth j)
  simp only [List.length_ofFn] at hFrames
  have hHeader := indexedLoopMetadataBitWork_bound primitive c hPrimitive (BinaryNatFrame.encode n).length
  rw [BinaryNatFrame.encode_length] at hHeader
  unfold rowEncodingMetadataBitWork rowEncodingMetadataBound
  rw [BinaryNatFrame.encode_length]
  omega

end Blotto.BinaryRatListFrame
