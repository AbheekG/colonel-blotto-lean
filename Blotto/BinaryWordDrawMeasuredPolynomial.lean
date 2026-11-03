import Blotto.BinaryWordGroupDrawMeasured
import Blotto.BinaryGroupFactoryMeasuredPolynomial
import Blotto.BinaryWordTerminalLifetimePolynomial

/-! Source-height/seed parameters derive polynomial measured segment and
complete factory/draw work for two and three groups. No intermediate probability width,
selected-row width or execution-price oracle is an input. Native machine joins,
four-variable factories and complete terminal adoption remain separate. -/

namespace Blotto.BinaryWordDrawMeasuredPolynomial
open BinaryPRGHeapResourcePolynomial BinaryRationalNormalization BinaryRationalEncoding
set_option autoImplicit false
set_option maxHeartbeats 3500000

macro "unfold_measured_draw_work" : tactic => `(tactic|
  simp only [BinaryWordGroupDrawMeasured.uniformPrice,BinaryWordGroupDrawMeasured.mixedPrice,
    BinaryWordSegmentMeasured.workEnvelope,BinaryWordSegmentMeasured.selectionPrice,
    BinaryWordSegmentMeasured.sourceStepPrice,BinaryPhysicalPointMeasured.price,BinaryTapePointLifetime.bound]
  <;> (try unfold_measured_group_factory)
  <;> unfold_word_terminal_envelope)

theorem segment_diagonal : NaturalPolynomialEnvelope inputSize (fun p =>
    BinaryWordSegmentMeasured.workEnvelope p.wordWidth p.wordWidth p.wordWidth p.wordWidth p.wordWidth p.wordWidth) := by
  unfold_measured_draw_work
  resource_polynomial

theorem uniform_diagonal : NaturalPolynomialEnvelope inputSize (fun p =>
    BinaryWordGroupDrawMeasured.uniformPrice p.wordWidth p.wordWidth p.wordWidth p.wordWidth p.wordWidth) := by
  unfold_measured_draw_work
  resource_polynomial

theorem mixed_diagonal : NaturalPolynomialEnvelope inputSize (fun p =>
    BinaryWordGroupDrawMeasured.mixedPrice p.wordWidth p.wordWidth p.wordWidth p.wordWidth) := by
  unfold_measured_draw_work
  resource_polynomial

theorem segment_mono {n k s K i b N L t T I B : ℕ}
    (hn : n ≤ N) (hk : k ≤ L) (hs : s ≤ t) (hK : K ≤ T) (hi : i ≤ I) (hb : b ≤ B) :
    BinaryWordSegmentMeasured.workEnvelope n k s K i b ≤ BinaryWordSegmentMeasured.workEnvelope N L t T I B := by
  unfold_measured_draw_work
  try unfold expressionHeightBudget
  gcongr

theorem uniform_mono {m s K i b M t T I B : ℕ}
    (hm : m ≤ M) (hs : s ≤ t) (hK : K ≤ T) (hi : i ≤ I) (hb : b ≤ B) :
    BinaryWordGroupDrawMeasured.uniformPrice m s K i b ≤ BinaryWordGroupDrawMeasured.uniformPrice M t T I B := by
  unfold_measured_draw_work
  unfold expressionHeightBudget
  gcongr

theorem mixed_mono {s K i b t T I B : ℕ} (hs : s ≤ t) (hK : K ≤ T) (hi : i ≤ I) (hb : b ≤ B) :
    BinaryWordGroupDrawMeasured.mixedPrice s K i b ≤ BinaryWordGroupDrawMeasured.mixedPrice t T I B := by
  unfold_measured_draw_work
  unfold expressionHeightBudget
  gcongr

theorem segment_polynomial : ∃ C d : ℕ, ∀ n k s K i b,
    BinaryWordSegmentMeasured.workEnvelope n k s K i b ≤ C*(n+k+s+K+i+b+2)^d := by
  obtain ⟨C,d,hBound⟩ := segment_diagonal
  refine ⟨C,d,?_⟩
  intro n k s K i b
  let T := n+k+s+K+i+b
  have hm : BinaryWordSegmentMeasured.workEnvelope n k s K i b ≤ BinaryWordSegmentMeasured.workEnvelope T T T T T T :=
    segment_mono (by dsimp only [T]; omega) (by dsimp only [T]; omega) (by dsimp only [T]; omega)
      (by dsimp only [T]; omega) (by dsimp only [T]; omega) (by dsimp only [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : inputSize ⟨0,T,0,0,0⟩+1 = T+2 := by simp [inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hm.trans h

theorem uniform_polynomial : ∃ C d : ℕ, ∀ m s K i b,
    BinaryWordGroupDrawMeasured.uniformPrice m s K i b ≤ C*(m+s+K+i+b+2)^d := by
  obtain ⟨C,d,hBound⟩ := uniform_diagonal
  refine ⟨C,d,?_⟩
  intro m s K i b
  let T := m+s+K+i+b
  have hm : BinaryWordGroupDrawMeasured.uniformPrice m s K i b ≤ BinaryWordGroupDrawMeasured.uniformPrice T T T T T :=
    uniform_mono (by dsimp only [T]; omega) (by dsimp only [T]; omega)
      (by dsimp only [T]; omega) (by dsimp only [T]; omega) (by dsimp only [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : inputSize ⟨0,T,0,0,0⟩+1 = T+2 := by simp [inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hm.trans h

theorem mixed_polynomial : ∃ C d : ℕ, ∀ s K i b,
    BinaryWordGroupDrawMeasured.mixedPrice s K i b ≤ C*(s+K+i+b+2)^d := by
  obtain ⟨C,d,hBound⟩ := mixed_diagonal
  refine ⟨C,d,?_⟩
  intro s K i b
  let T := s+K+i+b
  have hm : BinaryWordGroupDrawMeasured.mixedPrice s K i b ≤ BinaryWordGroupDrawMeasured.mixedPrice T T T T :=
    mixed_mono (by dsimp only [T]; omega) (by dsimp only [T]; omega)
      (by dsimp only [T]; omega) (by dsimp only [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : inputSize ⟨0,T,0,0,0⟩+1 = T+2 := by simp [inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hm.trans h

end Blotto.BinaryWordDrawMeasuredPolynomial
