import Blotto.GeneralPaperSourceSortStorageRates

/-! Literal native binary-search caller storage. Rank GeneralPaperRankMidpoint.midpoint construction,
returned records and encoded native work/probe counters are explicit. Query
scratch is active only at its chosen index; the child stack follows the
actual Boolean branch. All size/price/space bounds are erased analysis. -/
namespace Blotto.GeneralPaperRaySearchStorage
open GeneralPaperEncodedScalarStorage GeneralPaperRankMidpoint
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def workCap (W E depth : ℕ) : ℕ := depth*((12*depth+34)*W+E)+8*W
def metadataCap (W E depth N : ℕ) : ℕ := N+depth+1+3*workCap W E depth+E+(12*depth+2)*(W+1)+32*W
def frameProfile (W E depth N : ℕ) : ℕ := 18*(natBits (metadataCap W E depth N)+W)+640*W

theorem rank_range {n : ℕ} (query : Fin n → Bool×ℕ) (W depth fuel lo hi : ℕ)
    (hOrder : lo≤hi) (hHi : hi≤n) (hs : n<2^depth) :
    lo≤(GeneralPaperPricedRaySearch.run query W depth fuel lo hi).rank ∧
      (GeneralPaperPricedRaySearch.run query W depth fuel lo hi).rank≤hi := by
  induction fuel generalizing lo hi with
  | zero => exact ⟨le_rfl,hOrder⟩
  | succ fuel ih =>
    rw [GeneralPaperPricedRaySearch.run]
    split
    · rename_i hOpen
      have hm := midpoint_inside n depth lo hi hOpen hHi hs
      have hMid : (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient<n := hm.2.trans_le hHi
      rw [dite_eq_left hMid]
      dsimp only
      split
      · have hc := ih ((GeneralPaperRankMidpoint.midpoint depth lo hi).quotient+1) hi (by omega) hHi
        exact ⟨by dsimp only; omega,hc.2⟩
      · have hc := ih lo (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient hm.1 (by omega)
        exact ⟨hc.1,by dsimp only; omega⟩
    · exact ⟨le_rfl,hOrder⟩

theorem work_bound {n : ℕ} (query : Fin n → Bool×ℕ) (W E depth fuel lo hi : ℕ)
    (hf : fuel≤depth) (hE : ∀ i,(query i).2≤E) :
    (GeneralPaperPricedRaySearch.run query W depth fuel lo hi).work≤workCap W E depth :=
  (GeneralPaperPricedRaySearch.work query W depth fuel lo hi E hE).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hf) _)

theorem probes_bound {n : ℕ} (query : Fin n → Bool×ℕ) (W depth fuel lo hi : ℕ) :
    (GeneralPaperPricedRaySearch.run query W depth fuel lo hi).probes≤fuel := by
  rw [(GeneralPaperPricedRaySearch.trace query W depth fuel lo hi).2]
  exact GeneralPaperRayOracleSearch.run_probes query depth fuel lo hi

def record (W : ℕ) (r : GeneralPaperRayOracleSearch.Result) : ℕ := fields W [r.rank,r.work,r.probes]+64*W

theorem record_bound (W E depth N : ℕ) (r : GeneralPaperRayOracleSearch.Result)
    (hr : r.rank≤N) (hw : r.work≤workCap W E depth) (hp : r.probes≤depth) :
    record W r≤3*(natBits (metadataCap W E depth N)+W)+96*W := by
  have hf := fields_bound W (natBits (metadataCap W E depth N)) [r.rank,r.work,r.probes] (by
    intro a ha
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (metadataCap W E depth N)+W)+32*W at hf
  unfold record
  omega

def baseFrame {n : ℕ} (query : Fin n → Bool×ℕ) (W depth fuel lo hi : ℕ) : ℕ :=
  record W (GeneralPaperPricedRaySearch.run query W depth fuel lo hi)+fields W [depth,fuel,lo,hi]+128*W

theorem base_bound {n : ℕ} (query : Fin n → Bool×ℕ) (W E depth fuel lo hi : ℕ)
    (hf : fuel≤depth) (ho : lo≤hi) (hh : hi≤n) (hs : n<2^depth) (hE : ∀ i,(query i).2≤E) :
    baseFrame query W depth fuel lo hi≤7*(natBits (metadataCap W E depth n)+W)+256*W := by
  have hr := rank_range query W depth fuel lo hi ho hh hs
  have hw := work_bound query W E depth fuel lo hi hf hE
  have hp := (probes_bound query W depth fuel lo hi).trans hf
  have hRecord := record_bound W E depth n _ (hr.2.trans hh) hw hp
  have hFields := fields_bound W (natBits (metadataCap W E depth n)) [depth,fuel,lo,hi] (by
    intro a ha
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl
    all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (metadataCap W E depth n)+W)+32*W at hFields
  unfold baseFrame
  omega

def nextLo {n : ℕ} (query : Fin n → Bool×ℕ) (i : Fin n) (lo : ℕ) : ℕ := if (query i).1=true then i.val+1 else lo
def nextHi {n : ℕ} (query : Fin n → Bool×ℕ) (i : Fin n) (hi : ℕ) : ℕ := if (query i).1=true then hi else i.val

theorem next_bounds {n : ℕ} (query : Fin n → Bool×ℕ) (i : Fin n) (lo hi : ℕ)
    (hlo : lo≤ i.val) (hhi : i.val<hi) (hh : hi≤n) : nextLo query i lo≤nextHi query i hi ∧ nextHi query i hi≤n := by
  unfold nextLo nextHi
  split_ifs <;> omega

def frame {n : ℕ} (query : Fin n → Bool×ℕ) (W depth fuel lo hi : ℕ) (i : Fin n) : ℕ :=
  let mid := GeneralPaperRankMidpoint.midpoint depth lo hi
  let current := query i
  let child := GeneralPaperPricedRaySearch.run query W depth fuel (nextLo query i lo) (nextHi query i hi)
  baseFrame query W depth (fuel+1) lo hi+record W child+
    fields W [i.val,mid.work,mid.work*W,current.2,if current.1=true then 1 else 0,
      child.work+mid.work*W,child.work+mid.work*W+current.2,32*W]+128*W

theorem frame_bound {n : ℕ} (query : Fin n → Bool×ℕ) (W E depth fuel lo hi : ℕ) (i : Fin n)
    (hf : fuel+1≤depth) (hlo : lo≤ i.val) (hhi : i.val<hi) (hh : hi≤n) (hs : n<2^depth)
    (hE : ∀ i,(query i).2≤E) : frame query W depth fuel lo hi i≤frameProfile W E depth n := by
  let mid := GeneralPaperRankMidpoint.midpoint depth lo hi
  let current := query i
  let child := GeneralPaperPricedRaySearch.run query W depth fuel (nextLo query i lo) (nextHi query i hi)
  have hb := next_bounds query i lo hi hlo hhi hh
  have hr := rank_range query W depth fuel _ _ hb.1 hb.2 hs
  have hw := work_bound query W E depth fuel (nextLo query i lo) (nextHi query i hi) (by omega) hE
  have hp := (probes_bound query W depth fuel (nextLo query i lo) (nextHi query i hi)).trans (show fuel≤depth by omega)
  have hRecord := record_bound W E depth n child (hr.2.trans hb.2) hw hp
  have hBase := base_bound query W E depth (fuel+1) lo hi hf (by omega) hh hs hE
  have hCurrent : current.2≤E := hE i
  have hMid : mid.work=12*depth+2 := midpoint_work depth lo hi
  have hScaled : mid.work*W=(12*depth+2)*W := congrArg (·*W) hMid
  have hParts : (12*depth+2)*(W+1)=(12*depth+2)*W+(12*depth+2) := by ring
  have hBool : (if current.1=true then 1 else 0)≤1 := by split_ifs <;> omega
  change child.work≤workCap W E depth at hw
  have hFields := fields_bound W (natBits (metadataCap W E depth n))
    [i.val,mid.work,mid.work*W,current.2,if current.1=true then 1 else 0,
      child.work+mid.work*W,child.work+mid.work*W+current.2,32*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; have hi := i.isLt; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤8*(natBits (metadataCap W E depth n)+W)+32*W at hFields
  change baseFrame query W depth (fuel+1) lo hi+record W child+GeneralPaperEncodedScalarStorage.fields W
    [i.val,mid.work,mid.work*W,current.2,if current.1=true then 1 else 0,
      child.work+mid.work*W,child.work+mid.work*W+current.2,32*W]+128*W≤_
  unfold frameProfile
  omega

def peak {n : ℕ} (model : RationalCostModel) (query : Fin n → Bool×ℕ) (space : Fin n → ℕ) (W depth : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,lo,hi => baseFrame query W depth 0 lo hi
  | fuel+1,lo,hi =>
    if lo<hi then
      let mid := GeneralPaperRankMidpoint.midpoint depth lo hi
      if hMid : mid.quotient<n then
        let i : Fin n := ⟨mid.quotient,hMid⟩
        frame query W depth fuel lo hi i+GeneralPaperRankMidpointStorage.window model W depth lo hi+
          max (space i) (peak model query space W depth fuel (nextLo query i lo) (nextHi query i hi))
      else baseFrame query W depth (fuel+1) lo hi+GeneralPaperRankMidpointStorage.window model W depth lo hi
    else baseFrame query W depth (fuel+1) lo hi

def coefficient (model : RationalCostModel) (W E depth N : ℕ) : ℕ :=
  frameProfile W E depth N+GeneralPaperRankMidpointStorage.profile model W depth N

theorem coefficient_mono (model : RationalCostModel) (W E d e n N : ℕ) (hd : d≤e) (hn : n≤N) :
    coefficient model W E d n≤coefficient model W E e N := by
  unfold coefficient frameProfile metadataCap workCap GeneralPaperRankMidpointStorage.profile
    GeneralPaperRankMidpointStorage.argumentHeight GeneralPaperRankMidpointStorage.metadataCap
    GeneralPaperQuotientConstructionStorage.frameCap GeneralPaperQuotientConstructionStorage.localCap
    GeneralPaperBoundedQuotient.heightBudget natBits
  dsimp only
  gcongr <;> (apply model.monotone; gcongr)

theorem bounded {n : ℕ} (model : RationalCostModel) (query : Fin n → Bool×ℕ) (space : Fin n → ℕ)
    (W E Q depth fuel lo hi : ℕ) (hf : fuel≤depth) (ho : lo≤hi) (hh : hi≤n) (hs : n<2^depth)
    (hE : ∀ i,(query i).2≤E) (hQ : ∀ i,space i≤Q) :
    peak model query space W depth fuel lo hi≤(fuel+1)*coefficient model W E depth n+Q := by
  have hBase := base_bound query W E depth fuel lo hi hf ho hh hs hE
  have hCap : 7*(natBits (metadataCap W E depth n)+W)+256*W≤coefficient model W E depth n := by
    unfold coefficient frameProfile
    omega
  induction fuel generalizing lo hi with
  | zero =>
    simpa only [peak,Nat.zero_add,Nat.one_mul] using (hBase.trans hCap).trans (Nat.le_add_right _ Q)
  | succ fuel ih =>
    rw [peak]
    split
    · rename_i hOpen
      have hm := midpoint_inside n depth lo hi hOpen hh hs
      have hMid : (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient<n := hm.2.trans_le hh
      rw [dite_eq_left hMid]
      dsimp only
      let i : Fin n := ⟨(GeneralPaperRankMidpoint.midpoint depth lo hi).quotient,hMid⟩
      have hb := next_bounds query i lo hi hm.1 hm.2 hh
      have hChild := ih (nextLo query i lo) (nextHi query i hi) (by omega) hb.1 hb.2
        (base_bound query W E depth fuel _ _ (by omega) hb.1 hb.2 hs hE)
      have hF := frame_bound query W E depth fuel lo hi i hf hm.1 hm.2 hh hs hE
      have hM := GeneralPaperRankMidpointStorage.bounded model W depth n lo hi ho hh hs
      have hMax := max_le ((hQ i).trans (Nat.le_add_left Q _)) hChild
      have hLocal : frame query W depth fuel lo hi i+GeneralPaperRankMidpointStorage.window model W depth lo hi≤coefficient model W E depth n :=
        Nat.add_le_add hF hM
      exact (Nat.add_le_add hLocal hMax).trans_eq (by ring)
    · exact (hBase.trans hCap).trans ((Nat.le_mul_of_pos_left _ (by omega)).trans (Nat.le_add_right _ Q))

end Blotto.GeneralPaperRaySearchStorage
