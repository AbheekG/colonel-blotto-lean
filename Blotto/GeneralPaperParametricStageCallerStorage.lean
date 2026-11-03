import Blotto.GeneralPaperParametricRunStorage

/-! Actual stage caller counters: pair-batch return, refinement return,
optional midpoint/layer returns, both failure/success prices and every
native partial sum. All are encoded scalar fields, never whole-work scratch.
Data owners are counted by the enclosing checked phase reservations. -/
namespace Blotto.GeneralPaperParametricStageCallerStorage
open RationalOrderCell GeneralPaperRayAffineScoreStep GeneralPaperRayUniformSize
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def window {m K S : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (h : ℕ) (beta : ℚ) (field : Field K) (previous : GeneralPaperRayAffineScoreStep.Table S K) (lo hi : ℚ) : ℕ :=
  let points := GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous
  let refined := GeneralPaperRayBitRefinement.run model W matrix x w S h beta lo hi points.1
  let result := GeneralPaperParametricStageBits.run model W matrix x w h beta field previous lo hi
  fields W [S,K,h,points.1.length,points.2,refined.work,result.2,points.2+refined.work,points.2+refined.work+8*W]+256*W+
    match refined.bracket with
    | none => 0
    | some b =>
      let midpoint := GeneralPaperRayMidpointPrice.run model.rat W b.lower b.upper
      let selected := GeneralPaperAffineStepPrice.run model.rat W midpoint.1 field previous
      fields W [midpoint.2,selected.2,points.2+refined.work+midpoint.2,
        points.2+refined.work+midpoint.2+selected.2,points.2+refined.work+midpoint.2+selected.2+16*W]+128*W

def metadataCap (W K S N C : ℕ) : ℕ := K+2*S+N+1+3*C+32*W
def profile (W K S N C : ℕ) : ℕ := 14*(natBits (metadataCap W K S N C)+W)+448*W

theorem bounded {m K S : ℕ} (model : RationalCostModel) (W N C : ℕ) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (h : ℕ) (beta : ℚ) (hhS : h≤S) (field : Field K)
    (previous : GeneralPaperRayAffineScoreStep.Table S K) (lo hi : ℚ)
    (hLen : (GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous).1.length≤N)
    (hC : (GeneralPaperParametricStageBits.run model W matrix x w h beta field previous lo hi).2≤C) :
    window model W matrix x w h beta field previous lo hi≤profile W K S N C := by
  let points := GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous
  let refined := GeneralPaperRayBitRefinement.run model W matrix x w S h beta lo hi points.1
  let result := GeneralPaperParametricStageBits.run model W matrix x w h beta field previous lo hi
  change points.1.length≤N at hLen
  change result.2≤C at hC
  have hShape : result.2=(match refined.bracket with
      | none => points.2+refined.work+8*W
      | some b =>
        let midpoint := GeneralPaperRayMidpointPrice.run model.rat W b.lower b.upper
        let selected := GeneralPaperAffineStepPrice.run model.rat W midpoint.1 field previous
        points.2+refined.work+midpoint.2+selected.2+16*W) := by
    change (match refined.bracket with
      | none => (none,points.2+refined.work+8*W)
      | some b =>
        let midpoint := GeneralPaperRayMidpointPrice.run model.rat W b.lower b.upper
        let selected := GeneralPaperAffineStepPrice.run model.rat W midpoint.1 field previous
        (some (b,selected.1),points.2+refined.work+midpoint.2+selected.2+16*W)).2=_
    cases refined.bracket <;> rfl
  have hBase : points.2+refined.work+8*W≤C := by
    rw [hShape] at hC
    cases hp : refined.bracket with
    | none => simpa only [hp] using hC
    | some b => simp only [hp] at hC; omega
  have hFields := fields_bound W (natBits (metadataCap W K S N C))
    [S,K,h,points.1.length,points.2,refined.work,result.2,points.2+refined.work,points.2+refined.work+8*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤9*(natBits (metadataCap W K S N C)+W)+32*W at hFields
  have hActive : (match refined.bracket with
      | none => 0
      | some b =>
        let midpoint := GeneralPaperRayMidpointPrice.run model.rat W b.lower b.upper
        let selected := GeneralPaperAffineStepPrice.run model.rat W midpoint.1 field previous
        GeneralPaperEncodedScalarStorage.fields W [midpoint.2,selected.2,points.2+refined.work+midpoint.2,
          points.2+refined.work+midpoint.2+selected.2,points.2+refined.work+midpoint.2+selected.2+16*W]+128*W)≤
      5*(natBits (metadataCap W K S N C)+W)+160*W := by
    cases hp : refined.bracket with
    | none => simp only; omega
    | some b =>
      let midpoint := GeneralPaperRayMidpointPrice.run model.rat W b.lower b.upper
      let selected := GeneralPaperAffineStepPrice.run model.rat W midpoint.1 field previous
      have hBranch : result.2=points.2+refined.work+midpoint.2+selected.2+16*W := by simpa only [hp] using hShape
      have hCurrent := fields_bound W (natBits (metadataCap W K S N C))
        [midpoint.2,selected.2,points.2+refined.work+midpoint.2,points.2+refined.work+midpoint.2+selected.2,
          points.2+refined.work+midpoint.2+selected.2+16*W] (by
          intro a ha
          apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
          simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl|rfl|rfl|rfl|rfl
          all_goals unfold metadataCap; omega)
      change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (metadataCap W K S N C)+W)+32*W at hCurrent
      dsimp only
      exact (Nat.add_le_add_right hCurrent (128*W)).trans_eq (by ring)
  change GeneralPaperEncodedScalarStorage.fields W
    [S,K,h,points.1.length,points.2,refined.work,result.2,points.2+refined.work,points.2+refined.work+8*W]+256*W+_≤_
  dsimp only
  dsimp only [refined,points] at hActive
  unfold profile
  omega

def price (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  GeneralPaperParametricStageBits.profile ((S+1)*(K*K)) m S K W (model.rat (6*R+9))

theorem native_bounded {m S K : ℕ} (model : RationalCostModel) (W D E X V P n : ℕ)
    (hD : 0<D) (hE : 0<E) (hED : E∣D) (hn : n+1≤m)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a)) (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a))
    (h : ℕ) (beta : ℚ) (hb : GeneralPaperRayRationalBound.Bounded D P beta) (hhS : h≤S)
    (field : Field K) (previous : GeneralPaperRayAffineScoreStep.Table S K)
    (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous)
    (lo hi : ℚ) (hLo : 0≤lo) (ho : lo≤hi) (hHi : hi≤1)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P))
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) (hBatch : binaryWordWidth ((S+1)*(K*K)+3)≤W) :
    window model W matrix x w h beta field previous lo hi≤profile W K S ((S+1)*(K*K)) (price model W m K S (width D E m X V P)) := by
  have hLen : (GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous).1.length≤(S+1)*(K*K) := by
    rw [GeneralPaperNativeAffinePrices.crossings_data]
    exact GeneralPaperRayAffineScoreStep.crossings_length field previous
  have hWork := (GeneralPaperParametricStageBits.work model W D E X V P n hD hE hED hn matrix x w hx hw h beta hb
    field previous hf hp lo hi hLo ho hHi hl hh hW hK hM hIndex hBatch).trans
      (GeneralPaperParametricPriceProfiles.stage_batch_mono (GeneralPaperRayAffineScoreStep.crossings_length field previous) m S K W _)
  exact bounded model W _ _ matrix x w h beta hhS field previous lo hi hLen hWork

end Blotto.GeneralPaperParametricStageCallerStorage
