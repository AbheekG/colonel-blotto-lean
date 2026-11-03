import Blotto.GeneralPaperFixedViolationCandidateStorage

/-! Early-exit fixed-table scan: visited frames retain optional entries and
encoded child/return work. Exactly one candidate arithmetic window is
active; native table/iterator/budget/sample owners and run counters join. -/
namespace Blotto.GeneralPaperFixedViolationScanStorage
open RationalOrderCell GeneralPaperRayAffineScoreStep GeneralPaperRayFixedViolation
open GeneralPaperFixedViolationCandidateStorage GeneralPaperAffineWitnessStorage GeneralPaperEncodedScalarStorage
open GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

theorem scan_entry {S K : ℕ} (model : RationalCostModel) (W m R : ℕ) (table : Table S K) (hp : Good m R table)
    (h : ℕ) (beta t : ℚ) (xs : List (Fin (S+1))) :
    entryFoot W (GeneralPaperFixedViolationPrice.scan model.rat W table h beta t xs).value≤entryProfile W m K S R := by
  apply entry_bound W m R table hp
  intro e he
  rw [GeneralPaperFixedViolationPrice.scan_data] at he
  exact (GeneralPaperRayFixedViolation.scan_valid table h beta t xs e he).2.1

def workCap (model : RationalCostModel) (W R u N : ℕ) : ℕ := (cap model W R u+8*W)*N+2*W
def metadataCap (model : RationalCostModel) (W S R u N : ℕ) : ℕ := S+N+1+3*workCap model W R u N+cap model W R u+8*W

def frame {S K : ℕ} (model : RationalCostModel) (W : ℕ) (table : Table S K) (h : ℕ) (beta t : ℚ) : List (Fin (S+1)) → ℕ
  | [] => entryFoot (S:=S) (K:=K) W none+fields W [0,2*W]+128*W
  | s::rest =>
    let current := GeneralPaperFixedViolationPrice.candidateRun model.rat W table h beta t s
    let result := GeneralPaperFixedViolationPrice.scan model.rat W table h beta t (s::rest)
    entryFoot W current.1+entryFoot W result.value+
      fields W [(s::rest).length,current.2,result.work,current.2+8*W,8*W]+128*W

def frameProfile (model : RationalCostModel) (W m K S R u N : ℕ) : ℕ :=
  2*entryProfile W m K S R+5*(natBits (metadataCap model W S R u N)+W)+160*W

theorem frame_bound {S K : ℕ} (model : RationalCostModel) (W m R u N : ℕ) (table : Table S K) (hp : Good m R table)
    (h : ℕ) (beta t : ℚ) (hb : RationalHeight beta R) (ht : RationalHeight t u)
    (xs : List (Fin (S+1))) (hn : xs.length≤N) : frame model W table h beta t xs≤frameProfile model W m K S R u N := by
  cases xs with
  | nil =>
    have hf := fields_bound W (natBits (metadataCap model W S R u N)) [0,2*W] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl
      all_goals unfold metadataCap workCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤2*(natBits (metadataCap model W S R u N)+W)+32*W at hf
    unfold frame frameProfile entryFoot entryProfile
    dsimp only
    omega
  | cons s rest =>
    let current := GeneralPaperFixedViolationPrice.candidateRun model.rat W table h beta t s
    let result := GeneralPaperFixedViolationPrice.scan model.rat W table h beta t (s::rest)
    have hCurrent := entry_bound W m R table hp current.1 (by
      intro e he; rw [GeneralPaperFixedViolationPrice.candidate_data] at he
      exact (GeneralPaperRayFixedViolation.candidate_valid table h beta t s e he).2.1)
    have hResult := scan_entry model W m R table hp h beta t (s::rest)
    change entryFoot W result.value≤entryProfile W m K S R at hResult
    have hCurrentWork := GeneralPaperFixedViolationCandidateStorage.work model W m R u table hp h beta t hb ht s
    change current.2≤cap model W R u at hCurrentWork
    have hWork := (GeneralPaperFixedViolationPrice.scan_work model.rat W (cap model W R u) table h beta t (s::rest)
      (fun q _ => GeneralPaperFixedViolationCandidateStorage.work model W m R u table hp h beta t hb ht q)).trans
        (show (cap model W R u+8*W)*(s::rest).length+2*W≤workCap model W R u N by unfold workCap; gcongr)
    change result.work≤workCap model W R u N at hWork
    have hf := fields_bound W (natBits (metadataCap model W S R u N)) [(s::rest).length,current.2,result.work,current.2+8*W,8*W] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (metadataCap model W S R u N)+W)+32*W at hf
    change entryFoot W current.1+entryFoot W result.value+GeneralPaperEncodedScalarStorage.fields W [(s::rest).length,current.2,result.work,current.2+8*W,8*W]+128*W≤_
    unfold frameProfile
    omega

def frames {S K : ℕ} (model : RationalCostModel) (W : ℕ) (table : Table S K) (h : ℕ) (beta t : ℚ) : List (Fin (S+1)) → ℕ
  | [] => frame model W table h beta t []
  | s::rest => frame model W table h beta t (s::rest)+
      match (GeneralPaperFixedViolationPrice.candidateRun model.rat W table h beta t s).1 with
      | some _ => 0
      | none => frames model W table h beta t rest

theorem frames_bound {S K : ℕ} (model : RationalCostModel) (W m R u N : ℕ) (table : Table S K) (hp : Good m R table)
    (h : ℕ) (beta t : ℚ) (hb : RationalHeight beta R) (ht : RationalHeight t u)
    (xs : List (Fin (S+1))) (hn : xs.length≤N) : frames model W table h beta t xs≤(xs.length+1)*frameProfile model W m K S R u N := by
  induction xs with
  | nil => simpa only [frames,List.length_nil,Nat.zero_add,Nat.one_mul] using frame_bound model W m R u N table hp h beta t hb ht [] hn
  | cons s rest ih =>
    have hFrame := frame_bound model W m R u N table hp h beta t hb ht (s::rest) hn
    have hRest := ih (by simp only [List.length_cons] at hn; omega)
    change frame model W table h beta t (s::rest)+_≤_
    split
    · simp only [List.length_cons]
      nlinarith only [hFrame,Nat.zero_le ((rest.length+1)*frameProfile model W m K S R u N)]
    · exact (Nat.add_le_add hFrame hRest).trans_eq (by simp only [List.length_cons]; ring)

def runPrice (model : RationalCostModel) (W S R u : ℕ) : ℕ := workCap model W R u (S+1)+16*(S+2)*W

def callerCap (model : RationalCostModel) (W S R u : ℕ) : ℕ := S+1+3*runPrice model W S R u+16*(S+2)*W

def caller {S K : ℕ} (model : RationalCostModel) (W : ℕ) (table : Table S K) (h : ℕ) (beta t : ℚ) : ℕ :=
  let body := GeneralPaperFixedViolationPrice.scan model.rat W table h beta t (List.finRange (S+1))
  let result := GeneralPaperFixedViolationPrice.run model.rat W table h beta t
  fields W [S,h,body.work,result.work,16*(S+2)*W,body.work+16*(S+2)*W]+256*W

def window {S K : ℕ} (model : RationalCostModel) (W copied : ℕ) (table : Table S K) (h : ℕ) (beta t : ℚ) (active : Option (Fin (S+1))) : ℕ :=
  tableFoot W table+rationalWordWidth beta+rationalWordWidth t+
    frames model W table h beta t (List.finRange (S+1))+entryFoot W (GeneralPaperFixedViolationPrice.run model.rat W table h beta t).value+
    GeneralPaperPricedListStreamStorage.activeSpace (GeneralPaperFixedViolationCandidateStorage.window model W table h beta t) active+
    GeneralPaperFinRangeStorage.window W (S+1) copied+caller model W table h beta t

def profile (model : RationalCostModel) (W m K S R u : ℕ) : ℕ :=
  tableProfile W S K m R+(1+2*R)+(1+2*u)+(S+2)*frameProfile model W m K S R u (S+1)+entryProfile W m K S R+
    GeneralPaperFixedViolationCandidateStorage.profile model W m K S R u+GeneralPaperFinRangeStorage.profile W (S+1)+
      6*(natBits (callerCap model W S R u)+W)+288*W

theorem bounded {S K : ℕ} (model : RationalCostModel) (W m R u copied : ℕ) (table : Table S K) (hp : Good m R table)
    (hTable : tableFoot W table≤tableProfile W S K m R) (h : ℕ) (hhS : h≤S) (beta t : ℚ) (hb : RationalHeight beta R) (ht : RationalHeight t u)
    (active : Option (Fin (S+1))) : window model W copied table h beta t active≤profile model W m K S R u := by
  let body := GeneralPaperFixedViolationPrice.scan model.rat W table h beta t (List.finRange (S+1))
  let result := GeneralPaperFixedViolationPrice.run model.rat W table h beta t
  have hFrames := frames_bound model W m R u (S+1) table hp h beta t hb ht (List.finRange (S+1)) (by simp only [List.length_finRange,le_refl])
  simp only [List.length_finRange,Nat.add_assoc,Nat.reduceAdd] at hFrames
  have hEntry := scan_entry model W m R table hp h beta t (List.finRange (S+1))
  change entryFoot W result.value≤entryProfile W m K S R at hEntry
  have hBeta := rationalWordWidth_of_height hb
  have hSample := rationalWordWidth_of_height ht
  have hActive := GeneralPaperPricedListStreamStorage.active_bound (GeneralPaperFixedViolationCandidateStorage.profile model W m K S R u)
    (GeneralPaperFixedViolationCandidateStorage.window model W table h beta t) active (List.finRange (S+1))
    (fun s _ => GeneralPaperFixedViolationCandidateStorage.bounded model W m R u table hp h hhS beta t hb ht s) (fun s _ => List.mem_finRange s)
  have hRange := GeneralPaperFinRangeStorage.bounded W (S+1) copied
  have hBody := GeneralPaperFixedViolationPrice.scan_work model.rat W (cap model W R u) table h beta t (List.finRange (S+1))
    (fun s _ => GeneralPaperFixedViolationCandidateStorage.work model W m R u table hp h beta t hb ht s)
  simp only [List.length_finRange] at hBody
  change body.work≤workCap model W R u (S+1) at hBody
  have hShape : result.work=body.work+16*(S+2)*W := rfl
  have hf := fields_bound W (natBits (callerCap model W S R u)) [S,h,body.work,result.work,16*(S+2)*W,body.work+16*(S+2)*W] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold callerCap runPrice; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (callerCap model W S R u)+W)+32*W at hf
  unfold window profile caller
  dsimp only
  dsimp only [body,result] at hf hEntry
  omega

theorem native_bounded {S K : ℕ} (model : RationalCostModel) (W copied D E m X V P : ℕ) (hD : 0<D) (hE : 0<E)
    (table : Table S K) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V m table) (h : ℕ) (hhS : h≤S)
    (beta t : ℚ) (hb : GeneralPaperRayRationalBound.Bounded D P beta) (ht : RationalHeight t (2*width D E m X V P+3))
    (active : Option (Fin (S+1))) : window model W copied table h beta t active≤profile model W m K S (width D E m X V P) (2*width D E m X V P+3) := by
  exact bounded model W m _ _ copied table (processed_good D E X V m m P hD hE le_rfl table hp)
    (table_bound W D E X V m m P hD hE le_rfl table hp) h hhS beta t (GeneralPaperRayOperandStorageHeight.budget hD hb) ht active

end Blotto.GeneralPaperFixedViolationScanStorage
