import checkpoints.shen_extension.VariablePaidTensor
import checkpoints.shen_extension.ShellTrafficTensor

namespace LeanCH.BR.ShenFirstDeficient
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip DotTwoPassShellTransport
open Classical

/-- At the first failure of ideal growth, the actual table has two
wide layers and few missing entries. Its radius need not be central. -/
theorem offset_table {q s h k u m : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (gap : q+h=2*s) (hp : 2≤h) (large : 4096*h≤s) (scale : 64*(h*h)≤s)
    (hf : QFree D V q) (hm : ∀ x∈V,s≤(outN D V x).card) (hu : u∈V)
    (hk : k+2≤s)
    (h0 : s*k+1≤(ball D V u k).card+m) (h1 : s*(k+1)+1≤(ball D V u (k+1)).card+m)
    (dip : (ball D V u (k+2)).card+m≤s*(k+2)) :
    let S := ball D V u (k+1) \ ball D V u k
    let T := ball D V u (k+2) \ ball D V u (k+1)
    s*(k+2)+1≤(ball D V u (k+2)).card+m+(h+1) ∧
    s≤S.card+2*h ∧ 7*s≤8*T.card ∧ (∑ x∈S,(T \ outN D T x).card)≤s*h := by
  let S := ball D V u (k+1) \ ball D V u k
  let T := ball D V u (k+2) \ ball D V u (k+1)
  let U := (ball D V u (k+1)).erase u
  let H := ∑ v∈S,(T \ outN D T v).card
  have sc : S.card+(ball D V u k).card=(ball D V u (k+1)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have tc : T.card+(ball D V u (k+1)).card=(ball D V u (k+2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have uc : U.card+1=(ball D V u (k+1)).card := Finset.card_erase_add_one (self_mem_ball hu)
  obtain ⟨x,hx⟩ : ∃ x, (ball D V u (k+1)).card+m=s*(k+1)+1+x :=
    ⟨(ball D V u (k+1)).card+m-(s*(k+1)+1),by omega⟩
  have p1 : s*(k+1)=s*k+s := by ring
  have p2 : s*(k+2)=s*(k+1)+s := by ring
  obtain ⟨y,hy⟩ : ∃ y,T.card+x+y+1=s := ⟨s-(T.card+x+1),by omega⟩
  obtain ⟨z,hz⟩ : ∃ z,S.card+z=s+x := ⟨s+x-S.card,by omega⟩
  have pay := ShenVariablePaid.payment (k:=k) gap (by omega) scale hf hm hu (by omega)
    (show T.card<s by omega)
    (show U.card≤s*s by have := Nat.mul_le_mul_left s hk; omega)
    (by simp only [layer,Nat.add_sub_cancel]; change S.card≤2*s; omega)
  change q*s+1+H≤U.card+S.card*T.card at pay
  have budget : H+x*x+s*y+z*T.card≤s*h := by
    nlinarith only [pay,hx,uc,congrArg (fun j : ℕ => j*s) gap,
      congrArg (fun j : ℕ => j*T.card) hz,congrArg (fun j : ℕ => (s+x)*j) hy,
      Nat.mul_le_mul_left s (show k≤s by omega),Nat.zero_le (x*y),Nat.zero_le m]
  have tiny : 64*x≤s := by
    by_contra! bad
    have hsq := Nat.mul_lt_mul_of_pos_right bad (show 0<64*x by omega)
    have hsq' := Nat.mul_lt_mul_of_pos_left bad (show 0<s by omega)
    nlinarith only [hsq,hsq',Nat.mul_le_mul_left s large,budget,
      Nat.zero_le H,Nat.zero_le (s*y),Nat.zero_le (z*T.card)]
  have yl : y≤h := Nat.le_of_mul_le_mul_left (by omega : s*y≤s*h) (by omega : 0<s)
  have tall : 7*s≤8*T.card := by omega
  have zl : z≤2*h := by
    by_contra! bad
    have mul := Nat.mul_lt_mul_of_pos_right bad (show 0<T.card by omega)
    have mul' := Nat.mul_le_mul_left h (show s≤2*T.card by omega)
    nlinarith only [budget,mul,mul',Nat.zero_le H,Nat.zero_le (x*x),Nat.zero_le (s*y)]
  change _ ∧ s≤S.card+2*h ∧ 7*s≤8*T.card ∧ H≤s*h
  exact ⟨by omega,by omega,tall,by omega⟩

theorem first_table {q s h k u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (gap : q+h=2*s) (hp : 2≤h) (large : 4096*h≤s) (scale : 64*(h*h)≤s)
    (hf : QFree D V q) (hm : ∀ x∈V,s≤(outN D V x).card) (hu : u∈V)
    (hk : k+2≤s)
    (h0 : s*k+1≤(ball D V u k).card) (h1 : s*(k+1)+1≤(ball D V u (k+1)).card)
    (dip : (ball D V u (k+2)).card≤s*(k+2)) :
    let S := ball D V u (k+1) \ ball D V u k
    let T := ball D V u (k+2) \ ball D V u (k+1)
    s≤S.card+2*h ∧ 7*s≤8*T.card ∧ (∑ x∈S,(T \ outN D T x).card)≤s*h := by
  exact (offset_table (m:=0) gap hp large scale hf hm hu hk h0 h1 dip).2

/-- Compare the dense rows at a middle radius independent of the two
layers' own distance from their root. -/
theorem table_false {D : CH.Digraph} {V S T X : Finset ℕ} {q s h r E d : ℕ}
    (gap : q+h=2*s) (middle : q≤2*(r+1)) (half : 2*r≤q)
    (big : 1024*(d+E+h+1)≤s) (hp : 2≤h) (hf : QFree D V q)
    (sv : S⊆V) (tv : T⊆V) (wide : s≤S.card+2*h) (heads : 7*s≤8*T.card)
    (hits : 8*(S∩X).card≤s) (holes : (∑ x∈S,(T \ outN D T x).card)≤s*h)
    (floor : ∀ z∈T,s*r≤(ball D V z r).card+E)
    (upper : ∀ x∈S \ X,(ball D V x (r+1)).card≤s*(r+1)+d)
    (missing : ∀ x∈S \ X,(V.filter (fun y => y∉ball D V x (r+1) ∧ x∉ball D V y (r+1))).card≤d) :
    False := by
  let miss := fun x => (T \ outN D T x).card
  let W := S \ X
  let A := W.filter (fun x => miss x≤8*h)
  have sub : A⊆W := Finset.filter_subset _ _
  have ws : W⊆S := Finset.sdiff_subset
  have sw : W.card+(S∩X).card=S.card := Finset.card_sdiff_add_card_inter _ _
  have wa := Finset.card_sdiff_add_card_eq_card sub
  have hi (x) (hx : x∈W \ A) : 8*h≤miss x := by
    obtain ⟨hw,hn⟩ := Finset.mem_sdiff.mp hx
    by_contra! lo
    exact hn (Finset.mem_filter.mpr ⟨hw,by omega⟩)
  have sum := Finset.sum_le_sum hi
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at sum
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (f:=miss)
    ((Finset.sdiff_subset (s:=W) (t:=A)).trans ws) (fun _ _ _ => Nat.zero_le _)
  have hb := sum.trans (hsub.trans holes)
  rw [← Nat.mul_assoc] at hb
  have discard := Nat.le_of_mul_le_mul_right hb (by omega : 0<h)
  have ne := Finset.card_pos.mp (show 0<A.card by omega)
  let e := 5*s/8
  have close (x) (hx : x∈A) (y) (hy : y∈A) :
      (ball D V x (r+1) \ ball D V y (r+1)).card≤e := by
    apply ShenCommonSuccessor.pair_row_diff (b:=s*r-E) (N:=s*(r+1)+d) (g:=8*h) hf tv half
      (fun z hz => by have := floor z hz; omega) (upper x (sub hx))
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 (by omega) _
    rw [show s*(r+1)=s*r+s by ring]; dsimp [e]; omega
  have cap := ShenNearTotal.row_capacity hf (sub.trans (ws.trans sv)) ne
    (by dsimp [e]; omega : r+1+e+1≤q) (by dsimp [e]; omega : 3*e≤q) close (by
      intro x hx
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (sub.trans (ws.trans sv)))).trans
        (missing x (sub hx)))
  dsimp [e] at cap
  omega

#print axioms first_table
#print axioms table_false

private theorem count_tail (V : Finset ℕ) (f : ℕ → ℕ) (t : ℕ) :
    (V.filter (fun x => t≤f x)).card*t≤∑ x∈V,f x := by
  let X := V.filter (fun x => t≤f x)
  have hi (x) (hx : x∈X) : t≤f x := (Finset.mem_filter.mp hx).2
  have h := Finset.sum_le_sum hi
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at h
  exact h.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _))

/-- Select one root with a central deficit or outer deficit and few exceptional vertices
in the entire annulus containing its possible first deficient layer. -/
theorem choose_dip {q s h p i l E : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (start : p+h=s) (cut : p+s=q) (pair : i+l=q) (ordR : i≤l)
    (pi : p≤i) (ls : l≤s) (ne : V.Nonempty) (hp : 2≤h)
    (hf : QFree D V q) (ord : V.card≤q*s)
    (floors : ∀ k,p≤k → k≤s → ∀ x∈V,s*k+1≤(ball D V x k).card+E)
    (ideal : ∀ x∈V,s*p+1≤(ball D V x p).card)
    (scale : 1024*(32*h*(2*E+1)+E+h+1)≤s) :
    let d := 32*h*(2*E+1)
    ∃ X⊆V, ∃ u∈V,
      (∃ j≤s,(ball D V u j).card≤s*j) ∧
      8*(X.filter (fun x => x∈ball D V u s ∧ x∉ball D V u p)).card≤s ∧
      ∀ x∈V \ X,(ball D V x l).card≤s*l+d ∧
        (V.filter (fun y => y∉ball D V x l ∧ x∉ball D V y l)).card≤d := by
  let F := 2*E+1
  let d := 32*h*F
  let loss := fun x => (V.filter (fun y => y∉ball D V x l ∧ x∉ball D V y l)).card
  let exc := fun x => (ball D V x l).card-(s*l+1)
  let X := V.filter (fun x => d≤loss x+exc x)
  let P := fun x => ∃ j≤s,(ball D V x j).card≤s*j
  let Z := V.filter P
  have subX : X⊆V := Finset.filter_subset _ _
  have subZ : Z⊆V := Finset.filter_subset _ _
  have natF : 0<F := by dsimp [F]; omega
  have budget := ShenNearTotal.pair_budget (l:=l) hf pair.le ordR le_rfl
  have cells : (ShenNearTotal.incomparablePairs D V V l).card=∑ x∈V,loss x := by
    simp only [ShenNearTotal.incomparablePairs,loss,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_product V V _
  rw [cells] at budget
  have ceil : V.card*(V.card+1)≤V.card*(s*q)+V.card := by
    have m := Nat.mul_le_mul_left V.card ord
    nlinarith only [m]
  have rad : s*i+s*l=s*q := by rw [← Nat.mul_add,pair]
  let cost := fun x => if x∈Z then E else 0
  have costSum : (∑ x∈V,cost x)=Z.card*E := by
    dsimp only [cost]; rw [← Finset.sum_filter,Finset.sum_const_nat (fun _ _ => rfl)]
    congr 1
    have eq : V.filter (fun x => x∈Z)=Z := by
      ext x; exact ⟨fun h => (Finset.mem_filter.mp h).2,fun h => Finset.mem_filter.mpr ⟨subZ h,h⟩⟩
    rw [eq]
  have localFloor (k) (hk : p≤k) (ku : k≤s) (x) (hx : x∈V) :
      s*k+1≤(ball D V x k).card+cost x := by
    by_cases hz : x∈Z
    · simpa [cost,hz] using floors k hk ku x hx
    · have good : ¬P x := fun w => hz (Finset.mem_filter.mpr ⟨hx,w⟩)
      have gt : ¬(ball D V x k).card≤s*k := fun v => good ⟨k,ku,v⟩
      simp [cost,hz]; omega
  have row (x) (hx : x∈V) : s*q+2+exc x≤(ball D V x i).card+(ball D V x l).card+
      (cost x+cost x) := by
    have := localFloor i pi (by omega) x hx
    have := localFloor l (by omega) ls x hx
    dsimp [exc]; omega
  have sum := Finset.sum_le_sum row
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,costSum] at sum
  have mark := count_tail V (fun x => loss x+exc x) d
  rw [Finset.sum_add_distrib] at mark
  change X.card*d≤_ at mark
  have charged : X.card*d+V.card≤Z.card*(2*E) := by
    nlinarith only [sum,budget,ceil,mark]
  have zpos : 0<Z.card := by
    by_contra! bad; have zero : Z.card=0 := by omega
    rw [zero,Nat.zero_mul] at charged
    have := Finset.card_pos.mpr ne; omega
  have xcap : X.card*(32*h)≤Z.card := by
    apply Nat.le_of_mul_le_mul_right _ natF
    have more := Nat.mul_le_mul_left Z.card (show 2*E≤F by dsimp [F]; omega)
    dsimp only [d] at charged
    nlinarith only [charged,more,Nat.zero_le V.card]
  have width : s*p+s*h=s*s := by rw [← Nat.mul_add,start]
  have sz : s*p+s*s=s*q := by rw [← Nat.mul_add,cut]
  rw [Nat.mul_comm q s] at ord
  have rp (x) (hx : x∈V) : (reverseBall D V x p).card≤s*p+cost x := by
    have := reverseBall_add_ball_le (v:=x) hf (by omega : s+p≤q)
    have := localFloor s (by omega) le_rfl x hx
    omega
  have rs (x) (hx : x∈V) : (reverseBall D V x s).card≤s*s := by
    have := reverseBall_add_ball_le (v:=x) hf cut.le
    have := ideal x hx
    omega
  let shortage := fun x => s*p-(reverseBall D V x p).card
  have account (x) (hx : x∈V) : shortage x+(reverseBall D V x p).card≤s*p+cost x := by
    dsimp only [shortage]; have := rp x hx; omega
  have balance := Finset.sum_le_sum account
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,sum_reverseBall_eq_sum_ball,
    Finset.sum_const_nat (fun _ _ => rfl),costSum] at balance
  have lower := Finset.sum_le_sum (fun x hx => (ideal x hx).trans' (Nat.le_succ _))
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at lower
  have charge : (∑ x∈V,shortage x)≤Z.card*E := by omega
  let hit := fun u => (X.filter (fun x => x∈ball D V u s ∧ x∉ball D V u p)).card
  have cellBound (x) (hx : x∈X) :
      (reverseBall D V x s \ reverseBall D V x p).card≤s*h+shortage x := by
    have inc : reverseBall D V x p ⊆ reverseBall D V x s := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1,
        ball_mono_radius (by omega : p≤s) (Finset.mem_filter.mp hv).2⟩
    have := Finset.card_sdiff_add_card_eq_card inc
    have := rs x (subX hx)
    dsimp [shortage]; omega
  have ex := Finset.sum_le_sum cellBound
  rw [Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl),← ShenShellTraffic.transpose_between] at ex
  change (∑ u∈V,hit u)≤_ at ex
  have restricted := Finset.sum_le_sum_of_subset_of_nonneg (f:=shortage) subX (fun _ _ _ => Nat.zero_le _)
  have elig := Finset.sum_le_sum_of_subset_of_nonneg (f:=hit) subZ (fun _ _ _ => Nat.zero_le _)
  have small : 32*E≤s := by omega
  have avail : 8*(∑ u∈Z,hit u)≤Z.card*s := by
    have h1 := Nat.mul_le_mul_right s xcap
    have h2 := Nat.mul_le_mul_left Z.card small
    nlinarith only [h1,h2,ex,restricted,elig,charge,Nat.zero_le (∑ u∈Z,hit u)]
  have found : ∃ u∈Z,8*hit u≤s := by
    by_contra! allBad
    have count := Finset.sum_le_sum (fun u hu => (show s+1≤8*hit u from allBad u hu))
    rw [Finset.sum_const_nat (fun _ _ => rfl),← Finset.mul_sum,Nat.mul_add,Nat.mul_one] at count
    omega
  obtain ⟨u,uz,hits⟩ := found
  refine ⟨X,subX,u,subZ uz,(Finset.mem_filter.mp uz).2,hits,?_⟩
  intro x hx
  obtain ⟨hv,hn⟩ := Finset.mem_sdiff.mp hx
  have ht : loss x+exc x<d := by
    by_contra! z
    exact hn (Finset.mem_filter.mpr ⟨hv,z⟩)
  dsimp only [exc] at ht
  change (ball D V x l).card≤s*l+d ∧ loss x≤d
  omega

#print axioms choose_dip

/-- No fixed strip or parity. Every root that goes below ideal at either
central radius has a first dip after the ideal interval. Choose the root
on its entire annulus before selecting the exact deficient layer. -/
theorem order_strict {q s h : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (gap : q+h=2*s) (hp : 2≤h) (large : 131072*(h+1)^3≤s)
    (hf : QFree D V q) (hm : ∀ x∈V,s≤(outN D V x).card) (ne : V.Nonempty) :
    q*s<V.card := by
  by_contra! ord
  let E := 2*(h*h)
  let d := 32*h*(2*E+1)
  have big : 1024*(d+E+h+1)≤s := by
    apply le_trans _ large
    dsimp [d,E]; ring_nf; omega
  have scale : 64*(h*h)≤s := by dsimp [E] at big; omega
  have lin : 4096*h≤s := by
    apply le_trans _ large; ring_nf; omega
  let p := s-h
  let i := q/2
  let l := q-i
  have ps : p+h=s := by dsimp [p]; omega
  have pl : p+s=q := by omega
  have ij : i+l=q := by dsimp [l,i]; omega
  have il : i≤l := by dsimp [i,l]; omega
  have pi : p≤i := by dsimp [p,i]; omega
  have ls : l≤s := by dsimp [l,i]; omega
  have floor (k) (hk : p≤k) (ku : k≤s) (u) (hu : u∈V) :
      s*k+1≤(ball D V u k).card+E := by
    let b := s-2*h
    have sb : b+2*h=s := by dsimp [b]; omega
    have qb : 2*b+3*h=q := by omega
    have hb : h≤b := by dsimp [b]; omega
    have grow := ShenVariableCutoff.outer_growth (by omega : 1≤h) hb (qb ▸ hf)
      (fun x hx => sb ▸ hm x hx) hu (k-b) (by omega)
    rw [sb,show b+(k-b)=k by omega] at grow
    have hc := Nat.mul_le_mul_left h (show k-b≤2*h by omega)
    dsimp [E]; nlinarith only [grow,hc]
  have ideal (u) (hu : u∈V) (j) (hj : j≤p+2) : s*j+1≤(ball D V u j).card := by
    have qeq : 2*p+h=q := by omega
    have h := ShenVariablePaid.ideal (b:=p) (h:=h) hp (by omega) (qeq ▸ hf)
      (fun x hx => ps ▸ hm x hx) hu j hj
    rwa [ps] at h
  obtain ⟨X,xsub,u,hu,mid,hit,good⟩ := choose_dip (i:=i) (l:=l) ps pl ij il pi ls ne hp hf ord floor (fun x hx => ideal x hx p (by omega)) big
  let fail := fun j => (ball D V u j).card≤s*j
  obtain ⟨j,js,dip⟩ := mid
  have ex : ∃ j,fail j := ⟨j,dip⟩
  let t := Nat.find ex
  have bad : (ball D V u t).card≤s*t := Nat.find_spec ex
  have old (j) (hj : j<t) : s*j+1≤(ball D V u j).card := by
    have neg := Nat.find_min ex hj; dsimp [fail] at neg; omega
  have ts : t≤s := (Nat.find_min' ex dip).trans js
  have beyond : p+2<t := by by_contra! small; have := ideal u hu t small; omega
  obtain ⟨k,hk⟩ : ∃ k,t=k+2 := ⟨t-2,by omega⟩
  rw [hk] at bad
  let S := ball D V u (k+1) \ ball D V u k
  let T := ball D V u (k+2) \ ball D V u (k+1)
  obtain ⟨wide,heads,holes⟩ := first_table gap hp lin scale hf hm hu (by omega : k+2≤s)
    (old k (by omega)) (old (k+1) (by omega)) bad
  have sv : S⊆V := Finset.sdiff_subset.trans ball_subset
  have tv : T⊆V := Finset.sdiff_subset.trans ball_subset
  have inc : S∩X ⊆ X.filter (fun x => x∈ball D V u s ∧ x∉ball D V u p) := by
    intro x hx
    obtain ⟨hs,hx⟩ := Finset.mem_inter.mp hx
    obtain ⟨outer,inner⟩ := Finset.mem_sdiff.mp hs
    exact Finset.mem_filter.mpr ⟨hx,ball_mono_radius (by omega : k+1≤s) outer,
      fun hh => inner (ball_mono_radius (by omega : p≤k) hh)⟩
  obtain ⟨r,hr⟩ : ∃ r,l=r+1 := ⟨l-1,by omega⟩
  have pr : p≤r := by dsimp [l,i,p] at *; omega
  apply table_false (S:=S) (T:=T) (X:=X) (r:=r) gap (by omega) (by dsimp [i,l] at hr; omega)
    big hp hf sv tv wide heads ((Nat.mul_le_mul_left 8 (Finset.card_le_card inc)).trans hit) holes
  · intro z hz; have := floor r pr (by omega) z (tv hz); omega
  · intro x hx
    rw [← hr]
    exact (good x (Finset.mem_sdiff.mpr ⟨sv (Finset.mem_sdiff.mp hx).1,(Finset.mem_sdiff.mp hx).2⟩)).1
  · intro x hx
    rw [← hr]
    exact (good x (Finset.mem_sdiff.mpr ⟨sv (Finset.mem_sdiff.mp hx).1,(Finset.mem_sdiff.mp hx).2⟩)).2

theorem cycle_in_window {q s h n : ℕ} {D : CH.Digraph}
    (gap : q+h=2*s) (hp : 2≤h) (large : 131072*(h+1)^3≤s)
    (hn : 0<n) (hc : n≤q*s) (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  have := order_strict gap hp large (qfree_of_noShort hl no)
    (fun x hx => Compose.FloorSix.out_card hm (Finset.mem_range.mp hx)) ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at this; omega

#print axioms order_strict
#print axioms cycle_in_window
end LeanCH.BR.ShenFirstDeficient
