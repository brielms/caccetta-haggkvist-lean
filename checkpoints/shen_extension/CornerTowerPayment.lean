import checkpoints.shen_extension.CornerBlockTower

namespace LeanCH.BR.Closure.CornerTowerPayment
open Finset BRq2 BRq3 BR45 WeightedSD CornerBlockTower CornerBlockSubstitution

private theorem scaledOut (D : CH.Digraph) (L : Finset ℕ) (w : ℕ→ℚ) (c : ℚ) (i : ℕ) :
    outW D L (fun j=>c*w j) i=c*outW D L w i := by
  simp only [outW,mul_sum]; apply sum_congr rfl; intro j _; split <;> simp_all

/-- Both contacts of the replacement are taken from a single actual vertex.
    Their losses against the block mass are exactly one unit of point weight. -/
theorem threshold {q : ℕ} {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} {z p : ℕ→ℚ}
    (hq : 2≤q) (mz : 0<mass S z) (mp : 0<mass S p) (stop : CannotReplace q D V S y z p)
    (j : ℕ) (room : q*j+1<S.card) :
    let W := (V.erase y)\S
    let M := (q+1:ℚ)^j
    (q:ℚ)*outW D W z y+mass S z-mass S z/M<1 ∨
      (q:ℚ)*inW D W p y+mass S p-mass S p/M<1 := by
  intro W M
  obtain ⟨L,ls,size⟩ := exists_subset_card_eq room.le
  have less : L⊂S := Finset.ssubset_iff_subset_ne.mpr ⟨ls,fun eq=>by rw [←eq,size] at room; omega⟩
  obtain ⟨P⟩ := tower hq j L size
  let I := inN P.graph L P.root
  let O := outN P.graph L P.root
  have mpos : 0<M := by dsimp [M]; positivity
  let b (v : ℚ) := fun i=>v/M*P.w i
  have norm (v : ℚ) : mass L (b v)=v := by
    change (∑i∈L,v/M*P.w i)=v
    rw [←mul_sum,show (∑i∈L,P.w i)=M from P.total,div_mul_cancel₀ _ mpos.ne']
  have rows (v : ℚ) (i) (il : i∈L) :
      WeightedSD.row q P.graph L (b v) i=v ∧ WeightedSD.col q P.graph L (b v) i=v := by
    obtain ⟨f,g⟩ := P.flat i il
    have bill (E : CH.Digraph) (h : WeightedSD.row q E L P.w i=M) : WeightedSD.row q E L (b v) i=v := by
      dsimp only [WeightedSD.row,b]
      rw [scaledOut]
      calc
        _ = v/M*WeightedSD.row q E L P.w i := by unfold WeightedSD.row; ring
        _ = v := by rw [h,div_mul_cancel₀ _ mpos.ne']
    exact ⟨bill P.graph f,bill (fun a c=>P.graph c a) g⟩
  have cut := stop P.graph L I O less (filter_subset _ _) (filter_subset _ _) P.free
    (fun v vo t ti k short path=>P.free P.root (k+1+1) (by omega) (by omega)
      (.step (mem_outN.mp vo).1 (mem_outN.mp vo).2 (path.snoc P.member (mem_inN.mp ti).2)))
    (b (mass S z)) (b (mass S p))
    (fun i il=>⟨mul_pos (div_pos mz mpos) (P.positive i il),mul_pos (div_pos mp mpos) (P.positive i il)⟩)
    (norm _) (norm _) (fun i il=>⟨(rows _ i il).1,(rows _ i il).2⟩)
  have cost (E : CH.Digraph) (v : ℚ) (paid : WeightedSD.row q E L (b v) P.root=v) :
      (q:ℚ)*mass (outN E L P.root) (b v)=v-v/M := by
    rw [WeightedSD.row,outW_eq_mass,show b v P.root=v/M by simp [b,P.unit]] at paid
    linarith
  have co := cost P.graph (mass S z) (rows _ _ P.member).1
  have ci := cost (fun a c=>P.graph c a) (mass S p) (rows _ _ P.member).2
  change (q:ℚ)*mass O _=_ at co
  change (q:ℚ)*mass I _=_ at ci
  rcases cut with h|h
  · left; dsimp only [W]; linarith only [h,co]
  · right; dsimp only [W]; linarith only [h,ci]

private theorem capacity {q : ℕ} (hq : 2≤q) (e : ℕ) :
    (q*(e+3)+1:ℕ)≤(q+1)^(e+2) := by
  induction e with
  | zero => simp only [zero_add,pow_two]; nlinarith
  | succ e ih =>
    have h := Nat.mul_le_mul_right (q+1) ih
    rw [show e+1+2=(e+2)+1 by omega,pow_succ]
    nlinarith only [h,hq,Nat.zero_le (q*q*e),Nat.zero_le (q*q)]

open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SharedArcBarrier SharedArcComponentExchange

/-- A stopped regular block of degree at least three has more pivot contacts
    than twice its internal degree, for every order and every cutoff. -/
theorem on_source {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {J : Family} {r : ℕ→ℚ} (rp : ∀i∈X.V,0<r i)
    (back : ∀i∈X.V,mass X.V r<WeightedSD.col q (graph X.D J) X.V r i)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (many : 1<(targets X.D X.V F B).card) {y h : X.V} (fresh : Fresh X F (y,h))
    (stuck : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) y h) X.V)
    {S} (bl : CornerHeadRecurrence.OldBlockAt X.D (graph X.D F) X.V y S)
    {e : ℕ} (reg : ∀i∈S,(outN X.D S i).card=e+3 ∧ (inN X.D S i).card=e+3) :
    2*(e+3)<(outN X.D S y).card+(inN X.D S y).card := by
  by_contra! cheap
  obtain ⟨co,ci⟩ := CornerBlockRegular.on_source X hq small rp back step least many fresh stuck bl
    (d:=e+2) (by omega) reg cheap
  obtain ⟨z,p,pos,_,_,_,flat,heavyO,heavyI,stop⟩ := CornerBlockSubstitution.on_source X hq small rp back step least many fresh stuck bl
  obtain ⟨t,ts,_⟩ := bl.2.2.1
  have mz : 0<mass S z := sum_pos (fun i si=>(pos i (bl.1.1 si)).1) ⟨t,ts⟩
  have mp : 0<mass S p := sum_pos (fun i si=>(pos i (bl.1.1 si)).2) ⟨t,ts⟩
  let B : ℚ := (q*(e+3)+1:ℕ)
  let T : ℚ := (q+1:ℚ)^(e+2)
  have bp : 0<B := by dsimp [B]; positivity
  have tp : 0<T := by dsimp [T]; positivity
  have bt : B≤T := by dsimp [B,T]; exact_mod_cast capacity hq e
  have inspect (A : CH.Digraph) (w : ℕ→ℚ) (mpos : 0<mass S w) (deg : ∀i∈S,(outN A S i).card=e+3)
      (inside : ∀i∈S,WeightedSD.row q A S w i=mass S w) (contacts : (outN A S y).card=e+3) :
      (S.card:ℚ)=B ∧ (q:ℚ)*outW A S w y≤mass S w-mass S w/T := by
    have uni := CornerBlockRegular.uniform hq deg inside
    have eq := CornerBlockRegular.mass_constant uni
    change mass S w=(S.card:ℚ)*(mass S w/B) at eq
    rw [←mul_div_assoc,eq_div_iff bp.ne'] at eq
    have card : (S.card:ℚ)=B := by nlinarith only [eq,mpos]
    have os : outW A S w y=(e+3:ℕ)*(mass S w/B) := by
      rw [outW_eq_mass,CornerBlockRegular.mass_constant (fun i (ih : i∈outN A S y)=>uni i (mem_filter.mp ih).1),contacts]
    have bound := div_le_div_of_nonneg_left mpos.le bp bt
    have eqB : (q:ℚ)*(e+3:ℕ)=B-1 := by dsimp [B]; push_cast; ring
    have cancel : B*(mass S w/B)=mass S w := mul_div_cancel₀ _ bp.ne'
    rw [os,←mul_assoc,eqB]
    exact ⟨card,by linarith only [bound,cancel]⟩
  obtain ⟨sz,o⟩ := inspect X.D z mz (fun i si=>(reg i si).1) (fun i si=>(flat i si).1) co
  obtain ⟨_,i⟩ := inspect (fun a c=>X.D c a) p mp (fun i si=>(reg i si).2) (fun i si=>(flat i si).2) ci
  have card : S.card=q*(e+3)+1 := by dsimp only [B] at sz; exact_mod_cast sz
  have room : q*(e+2)+1<S.card := by rw [card]; nlinarith
  rw [outW_split bl.1.1] at heavyO
  have splitI := outW_split (D:=fun a c=>X.D c a) bl.1.1 p y
  change inW X.D _ p y=inW X.D S p y+inW X.D _ p y at splitI
  change (q:ℚ)*inW X.D S p y≤mass S p-mass S p/T at i
  rw [splitI] at heavyI
  rcases threshold hq mz mp stop (e+2) room with h|h
  · change (q:ℚ)*outW X.D _ z y+mass S z-mass S z/T<1 at h
    linarith only [h,o,heavyO]
  · change (q:ℚ)*inW X.D _ p y+mass S p-mass S p/T<1 at h
    linarith only [h,i,heavyI]

/-- The family of sources for which the replacement removes this alternative. -/
def SparseBlock {q n} (X : Model q n) (F : Family) (B : Finset ℕ) : Prop :=
  1<(targets X.D X.V F B).card ∧ ∃ y h : X.V, Fresh X F (y,h) ∧
    ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) y h) X.V ∧
    ∃S,CornerHeadRecurrence.OldBlockAt X.D (graph X.D F) X.V y S ∧
    ∃e : ℕ,(∀i∈S,(outN X.D S i).card=e+3 ∧ (inN X.D S i).card=e+3) ∧
      (outN X.D S y).card+(inN X.D S y).card≤2*(e+3)

theorem excludes {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {J : Family} {r : ℕ→ℚ} (rp : ∀i∈X.V,0<r i)
    (back : ∀i∈X.V,mass X.V r<WeightedSD.col q (graph X.D J) X.V r i)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card) :
    ¬SparseBlock X F B := by
  rintro ⟨many,y,h,fresh,stuck,S,bl,e,reg,cheap⟩
  exact (on_source X hq small rp back step least many fresh stuck bl reg).not_ge cheap

#print axioms threshold
#print axioms on_source
#print axioms excludes
end LeanCH.BR.Closure.CornerTowerPayment
