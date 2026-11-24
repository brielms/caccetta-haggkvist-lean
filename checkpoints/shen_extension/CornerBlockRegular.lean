import checkpoints.shen_extension.CornerBlockInterval

namespace LeanCH.BR.Closure.CornerBlockRegular
open Finset BRq2 BRq3 BR45 WeightedSD
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SharedArcBarrier SharedArcComponentExchange

private theorem allocation {q d h t : ℕ} (hq : 2≤q) (hh : 0<h) (ht : 0<t)
    (total : h+t≤2*d+2) (off : ¬(h=d+1 ∧ t=d+1)) :
    ∃k,1≤k ∧ k≤2*d ∧ h*(q*d+1)≤(2*d+1-k)*(q*(d+1)+1) ∧ t*(q*d+1)≤k*(q*(d+1)+1) := by
  have weak (a b : ℕ) (le : a≤b) : a*(q*d+1)≤b*(q*(d+1)+1) :=
    Nat.mul_le_mul le (by nlinarith)
  have down (j : ℕ) (dj : d+1≤j) : (j+1)*(q*d+1)≤j*(q*(d+1)+1) := by
    nlinarith only [Nat.mul_le_mul_left q dj,hq]
  by_cases cheap : h+t≤2*d+1
  · exact ⟨t,ht,by omega,weak _ _ (by omega),weak _ _ le_rfl⟩
  by_cases high : d+2≤t
  · have adj := down (t-1) (by omega)
    rw [show t-1+1=t by omega] at adj
    exact ⟨t-1,by omega,by omega,weak _ _ (by omega),adj⟩
  · have adj := down (2*d+1-t) (by omega)
    rw [show 2*d+1-t+1=h by omega] at adj
    exact ⟨t,ht,by omega,adj,weak _ _ le_rfl⟩

theorem mass_constant {T : Finset ℕ} {z : ℕ→ℚ} {c : ℚ} (eq : ∀i∈T,z i=c) :
    mass T z=T.card*c := by
  calc
    _ = ∑_i∈T,c := sum_congr rfl eq
    _ = _ := by simp

theorem uniform {q e : ℕ} {D : CH.Digraph} {S : Finset ℕ} {z : ℕ→ℚ}
    (hq : 2≤q) (deg : ∀i∈S,(outN D S i).card=e)
    (flat : ∀i∈S,WeightedSD.row q D S z i=mass S z) :
    ∀i∈S,z i=mass S z/(q*e+1:ℕ) := by
  let m := mass S z
  let M : ℚ := (q*e+1:ℕ)
  have npos : 0<M := by dsimp [M]; positivity
  apply row_laws_unique_on hq flat (b:=fun _=>m/M)
  intro i si
  rw [WeightedSD.row,outW_eq_mass,mass_constant (c:=m/M) (fun _ _=>rfl),deg i si]
  change m/M+(q:ℚ)*(e*(m/M))=m
  have eq : M=1+(q:ℚ)*e := by dsimp [M]; push_cast; ring
  calc
    _ = (1+(q:ℚ)*e)*(m/M) := by ring
    _ = m := by rw [←eq]; exact mul_div_cancel₀ _ npos.ne'

private theorem scale {a b M N : ℕ} (hM : 0<M) (hN : 0<N) (ab : a*N≤b*M) {m : ℚ} (hm : 0≤m) :
    (a:ℚ)*(m/M)≤(b:ℚ)*(m/N) := by
  have f : (a:ℚ)/M≤(b:ℚ)/N := (div_le_div_iff₀ (by exact_mod_cast hM) (by exact_mod_cast hN)).mpr
    (by exact_mod_cast ab)
  convert mul_le_mul_of_nonneg_right f hm using 1 <;> ring

/-- In a regular old block, a pivot with at most twice the internal degree
    in contacts must have exactly that degree in each direction. -/
theorem on_source {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {J : Family} {r : ℕ→ℚ} (rp : ∀i∈X.V,0<r i)
    (back : ∀i∈X.V,mass X.V r<WeightedSD.col q (graph X.D J) X.V r i)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (many : 1<(targets X.D X.V F B).card) {y h : X.V} (fresh : Fresh X F (y,h))
    (stuck : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) y h) X.V)
    {S} (bl : CornerHeadRecurrence.OldBlockAt X.D (graph X.D F) X.V y S)
    {d : ℕ} (hd : 1≤d)
    (reg : ∀i∈S,(outN X.D S i).card=d+1 ∧ (inN X.D S i).card=d+1)
    (total : (outN X.D S y).card+(inN X.D S y).card≤2*(d+1)) :
    (outN X.D S y).card=d+1 ∧ (inN X.D S y).card=d+1 := by
  by_contra off
  obtain ⟨t,ts,ty⟩ := bl.2.2.1
  obtain ⟨v,vs,yv⟩ := bl.2.2.2.1
  have hi : 0<(inN X.D S y).card := card_pos.mpr ⟨t,mem_filter.mpr ⟨ts,(bl.2.1 t ts).1 ▸ ty⟩⟩
  have ho : 0<(outN X.D S y).card := card_pos.mpr ⟨v,mem_filter.mpr ⟨vs,(bl.2.1 v vs).2 ▸ yv⟩⟩
  obtain ⟨k,hk,kb,oa,ia⟩ := allocation (d:=d) hq ho hi (by omega) off
  obtain ⟨z,p,pos,_,_,_,flat,heavyO,heavyI,stop⟩ := CornerBlockSubstitution.on_source X hq small rp back step least many fresh stuck bl
  have mz : 0<mass S z := sum_pos (fun i si=>(pos i (bl.1.1 si)).1) ⟨t,ts⟩
  have mp : 0<mass S p := sum_pos (fun i si=>(pos i (bl.1.1 si)).2) ⟨t,ts⟩
  have uz := uniform hq (fun i si=>(reg i si).1) (fun i si=>(flat i si).1)
  have up := uniform (D:=fun i j=>X.D j i) hq (fun i si=>(reg i si).2) (fun i si=>(flat i si).2)
  have big : 0<q*(d+1)+1 := by omega
  have bigQ : 0<((q*(d+1)+1:ℕ):ℚ) := by exact_mod_cast big
  have cardEq := mass_constant uz
  rw [←mul_div_assoc,eq_div_iff bigQ.ne'] at cardEq
  have sizeQ : ((q*(d+1)+1:ℕ):ℚ)=S.card := by nlinarith only [cardEq,mz] 
  have size : q*(d+1)+1=S.card := by exact_mod_cast sizeQ
  have room : q*d+1<S.card := by rw [←size]; nlinarith
  have lower : 0<q*d+1 := by omega
  have ow := scale big lower oa mz.le
  have iw := scale big lower ia mp.le
  have os : outW X.D S z y=_ := (outW_eq_mass ..).trans
    (mass_constant (fun i (ii : i∈outN X.D S y)=>uz i (mem_filter.mp ii).1))
  have ins : inW X.D S p y=(inN X.D S y).card*(mass S p/(q*(d+1)+1:ℕ)) := (outW_eq_mass (fun i j=>X.D j i) S p y).trans
    (mass_constant (fun i (ii : i∈inN X.D S y)=>up i (mem_filter.mp ii).1))
  rw [←os] at ow
  rw [←ins] at iw
  rw [outW_split bl.1.1] at heavyO
  have isp := outW_split (D:=fun i j=>X.D j i) bl.1.1 p y
  change inW X.D _ p y=inW X.D S p y+inW X.D _ p y at isp
  rw [isp] at heavyI
  rcases CornerBlockInterval.threshold hq mz mp stop hd room hk kb with lo|li
  · linarith only [lo,heavyO,mul_le_mul_of_nonneg_left ow (Nat.cast_nonneg (α:=ℚ) q)]
  · linarith only [li,heavyI,mul_le_mul_of_nonneg_left iw (Nat.cast_nonneg (α:=ℚ) q)]

#print axioms on_source
end LeanCH.BR.Closure.CornerBlockRegular
