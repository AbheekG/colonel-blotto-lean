import Blotto.GeneralPaperParametricOutputStorage

/-! Native recursive caller frames. Complete child/parent output tables and
brackets are conservatively retained at every prefix. Actual child, stage,
parent and partial-work counters are encoded; no traversal time is used as
scratch. The final native theorem derives the work cap internally. -/
namespace Blotto.GeneralPaperParametricRunStorage
open RationalOrderCell GeneralPaperRayAffineScoreStep GeneralPaperRayParametricDP
open GeneralPaperRayUniformSize GeneralPaperParametricOutputStorage GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

theorem child_work_le {S K : ℕ} (W : ℕ) (initial : Unit → Table S K×ℕ)
    (stage : GeneralPaperParametricRecursionPrice.Stage S K) (field : Field K) (rest : List (Field K)) (lo hi : ℚ) :
    (GeneralPaperParametricRecursionPrice.run W initial stage rest lo hi).2≤
      (GeneralPaperParametricRecursionPrice.run W initial stage (field::rest) lo hi).2 := by
  rw [GeneralPaperParametricRecursionPrice.run]
  cases (GeneralPaperParametricRecursionPrice.run W initial stage rest lo hi).1 <;> dsimp only <;> omega

theorem branch_work {S K : ℕ} (W : ℕ) (initial : Unit → Table S K×ℕ)
    (stage : GeneralPaperParametricRecursionPrice.Stage S K) (field : Field K) (rest : List (Field K)) (lo hi : ℚ)
    (previous : Output S K) (hp : (GeneralPaperParametricRecursionPrice.run W initial stage rest lo hi).1=some previous) :
    (GeneralPaperParametricRecursionPrice.run W initial stage (field::rest) lo hi).2=
      (GeneralPaperParametricRecursionPrice.run W initial stage rest lo hi).2+
        (stage field previous.table previous.bracket.lower previous.bracket.upper).2+24*W := by
  rw [GeneralPaperParametricRecursionPrice.run,hp]

def metadataCap (W m K S C : ℕ) : ℕ := m+K+2*S+1+3*C+32*W

def frame {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (S h : ℕ) (beta : ℚ) : List (Field K) → ℚ → ℚ → ℕ
  | [],lo,hi =>
    let initial := GeneralPaperParametricInitialPrice.run (fun w => w) W S K
    let result := GeneralPaperParametricRunBits.run model W matrix x w S h beta [] lo hi
    outputFoot W result.1+fields W [S,K,h,0,initial.2,result.2,16*W]+128*W
  | field::rest,lo,hi =>
    let earlier := GeneralPaperParametricRunBits.run model W matrix x w S h beta rest lo hi
    let result := GeneralPaperParametricRunBits.run model W matrix x w S h beta (field::rest) lo hi
    outputFoot W earlier.1+2*outputFoot W result.1+
      fields W [S,K,h,(field::rest).length,earlier.2,result.2,8*W]+128*W+
      match earlier.1 with
      | none => 0
      | some previous =>
        let current := GeneralPaperParametricStageBits.run model W matrix x w h beta field previous.table previous.bracket.lower previous.bracket.upper
        fields W [current.2,earlier.2+current.2,earlier.2+current.2+24*W,24*W]+128*W

def frameProfile (W m K S R C : ℕ) : ℕ :=
  3*outputProfile W m K S R+11*(natBits (metadataCap W m K S C)+W)+320*W

theorem frame_bound {m K : ℕ} (model : RationalCostModel) (W D E X V P C : ℕ) (hD : 0<D) (hE : 0<E)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ) (S h : ℕ) (beta : ℚ) (hhS : h≤S)
    (xs : List (Field K)) (hLen : xs.length≤m) (hf : ∀ f∈xs,GeneralPaperRayAffineDPSize.FieldBounded D E X V f)
    (lo hi : ℚ) (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P))
    (hC : (GeneralPaperParametricRunBits.run model W matrix x w S h beta xs lo hi).2≤C) :
    frame model W matrix x w S h beta xs lo hi≤frameProfile W m K S (width D E m X V P) C := by
  have hResult := GeneralPaperParametricOutputStorage.bounded model W D E X V P hD hE matrix x w S h beta xs hLen hf lo hi hl hh
  cases xs with
  | nil =>
    let initial := GeneralPaperParametricInitialPrice.run (fun w => w) W S K
    let result := GeneralPaperParametricRunBits.run model W matrix x w S h beta [] lo hi
    have hShape : result.2=initial.2+16*W := rfl
    change result.2≤C at hC
    have hFields := fields_bound W (natBits (metadataCap W m K S C)) [S,K,h,0,initial.2,result.2,16*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤7*(natBits (metadataCap W m K S C)+W)+32*W at hFields
    change outputFoot W result.1+GeneralPaperEncodedScalarStorage.fields W [S,K,h,0,initial.2,result.2,16*W]+128*W≤_
    change outputFoot W result.1≤_ at hResult
    unfold frameProfile
    omega
  | cons field rest =>
    let initial := fun (_ : Unit) => GeneralPaperParametricInitialPrice.run (fun w => w) W S K
    let stage : GeneralPaperParametricRecursionPrice.Stage S K := fun f t l u => GeneralPaperParametricStageBits.run model W matrix x w h beta f t l u
    let earlier := GeneralPaperParametricRunBits.run model W matrix x w S h beta rest lo hi
    let result := GeneralPaperParametricRunBits.run model W matrix x w S h beta (field::rest) lo hi
    have hRestLen : rest.length≤m := by simp only [List.length_cons] at hLen; omega
    have hRest := GeneralPaperParametricOutputStorage.bounded model W D E X V P hD hE matrix x w S h beta rest hRestLen
      (fun f ht => hf f (List.mem_cons_of_mem _ ht)) lo hi hl hh
    change outputFoot W earlier.1≤_ at hRest
    change outputFoot W result.1≤_ at hResult
    change result.2≤C at hC
    have hEarlier : earlier.2≤C := (child_work_le W initial stage field rest lo hi).trans hC
    have hFields := fields_bound W (natBits (metadataCap W m K S C)) [S,K,h,(field::rest).length,earlier.2,result.2,8*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤7*(natBits (metadataCap W m K S C)+W)+32*W at hFields
    have hActive : (match earlier.1 with
        | none => 0
        | some previous =>
          let current := stage field previous.table previous.bracket.lower previous.bracket.upper
          GeneralPaperEncodedScalarStorage.fields W [current.2,earlier.2+current.2,earlier.2+current.2+24*W,24*W]+128*W)≤
        4*(natBits (metadataCap W m K S C)+W)+160*W := by
      cases hp : earlier.1 with
      | none => simp only; omega
      | some previous =>
        let current := stage field previous.table previous.bracket.lower previous.bracket.upper
        have hShape : result.2=earlier.2+current.2+24*W := branch_work W initial stage field rest lo hi previous hp
        have hCurrent := fields_bound W (natBits (metadataCap W m K S C)) [current.2,earlier.2+current.2,earlier.2+current.2+24*W,24*W] (by
          intro a ha
          apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
          simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl|rfl|rfl|rfl
          all_goals unfold metadataCap; omega)
        change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (metadataCap W m K S C)+W)+32*W at hCurrent
        dsimp only
        exact (Nat.add_le_add_right hCurrent (128*W)).trans_eq (by ring)
    dsimp only [stage,earlier] at hActive
    change outputFoot W earlier.1+2*outputFoot W result.1+
      GeneralPaperEncodedScalarStorage.fields W [S,K,h,(field::rest).length,earlier.2,result.2,8*W]+128*W+_≤_
    dsimp only
    unfold frameProfile
    omega

def frames {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (S h : ℕ) (beta : ℚ) : List (Field K) → ℚ → ℚ → ℕ
  | [],lo,hi => frame model W matrix x w S h beta [] lo hi
  | field::rest,lo,hi => frame model W matrix x w S h beta (field::rest) lo hi+frames model W matrix x w S h beta rest lo hi

theorem frames_bound {m K : ℕ} (model : RationalCostModel) (W D E X V P C : ℕ) (hD : 0<D) (hE : 0<E)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ) (S h : ℕ) (beta : ℚ) (hhS : h≤S)
    (xs : List (Field K)) (hLen : xs.length≤m) (hf : ∀ f∈xs,GeneralPaperRayAffineDPSize.FieldBounded D E X V f)
    (lo hi : ℚ) (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P))
    (hC : (GeneralPaperParametricRunBits.run model W matrix x w S h beta xs lo hi).2≤C) :
    frames model W matrix x w S h beta xs lo hi≤(xs.length+1)*frameProfile W m K S (width D E m X V P) C := by
  induction xs with
  | nil => simpa only [frames,List.length_nil,Nat.zero_add,Nat.one_mul] using frame_bound model W D E X V P C hD hE matrix x w S h beta hhS [] hLen hf lo hi hl hh hC
  | cons field rest ih =>
    have hFrame := frame_bound model W D E X V P C hD hE matrix x w S h beta hhS (field::rest) hLen hf lo hi hl hh hC
    have hRestCost : (GeneralPaperParametricRunBits.run model W matrix x w S h beta rest lo hi).2≤C :=
      (child_work_le W (fun _ => GeneralPaperParametricInitialPrice.run (fun w => w) W S K)
        (fun f t l u => GeneralPaperParametricStageBits.run model W matrix x w h beta f t l u) field rest lo hi).trans hC
    have hRest := ih (by simp only [List.length_cons] at hLen; omega)
      (fun f ht => hf f (List.mem_cons_of_mem _ ht)) hRestCost
    exact (Nat.add_le_add hFrame hRest).trans_eq (by simp only [List.length_cons]; ring)

def window {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (S h : ℕ) (beta : ℚ) (xs : List (Field K)) (lo hi : ℚ) : ℕ :=
  frames model W matrix x w S h beta xs lo hi+outputFoot W (GeneralPaperParametricRunBits.run model W matrix x w S h beta xs lo hi).1

def profile (W m K S R C : ℕ) : ℕ := (m+1)*frameProfile W m K S R C+outputProfile W m K S R

def price (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  GeneralPaperParametricPriceProfiles.profile m m S K W (model.rat (6*R+9))

theorem native_bounded {m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ)
    (hD : 0<D) (hE : 0<E) (hED : E∣D) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a))
    (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a)) (S h : ℕ) (beta : ℚ)
    (hb : GeneralPaperRayRationalBound.Bounded D P beta) (hhS : h≤S) (xs : List (Field K)) (hLen : xs.length≤m)
    (hf : ∀ f∈xs,GeneralPaperRayAffineDPSize.FieldBounded D E X V f)
    (lo hi : ℚ) (hLo : 0≤lo) (ho : lo≤hi) (hHi : hi≤1)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P))
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) (hBatch : binaryWordWidth ((S+1)*(K*K)+3)≤W) :
    window model W matrix x w S h beta xs lo hi≤profile W m K S (width D E m X V P) (price model W m K S (width D E m X V P)) := by
  have hWork := (GeneralPaperParametricRunBits.work model W D E X V P hD hE hED matrix x w hx hw S h beta hb xs hLen hf
    lo hi hLo ho hHi hl hh hW hK hM hIndex hBatch).trans (show
      GeneralPaperParametricPriceProfiles.profile xs.length m S K W (model.rat (6*width D E m X V P+9))≤
        price model W m K S (width D E m X V P) by
          unfold price GeneralPaperParametricPriceProfiles.profile GeneralPaperParametricRecursionPrice.profile
          gcongr)
  have hFrames := (frames_bound model W D E X V P _ hD hE matrix x w S h beta hhS xs hLen hf lo hi hl hh hWork).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hLen 1))
  have hResult := GeneralPaperParametricOutputStorage.bounded model W D E X V P hD hE matrix x w S h beta xs hLen hf lo hi hl hh
  unfold window profile
  omega

end Blotto.GeneralPaperParametricRunStorage
