import checkpoints.shen_extension.CumulativeDeficitTensor

/-!
# The cumulative-deficit strip with tightened numerals

The same argument as `CumulativeDeficitTensor`, with every numerical constant
lowered as far as its own inequality allows. The threshold `35840·(h+1)² ≤ s`
becomes `424·(h+1)² ≤ s`. Only numerals and their arithmetic side goals differ
from the original; the capstone still uses the original file.
-/

namespace LeanCH.BR.CumulativeDeficitSharp
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip DotTwoPassShellTransport
open Classical

theorem offset_table {q s h k u m : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (gap : q+h=2*s) (hp : 2≤h) (large : 1600*h≤s) (scale : 64*(h*h)≤s)
    (hf : QFree D V q) (hm : ∀ x∈V,s≤(outN D V x).card) (hu : u∈V)
    (hk : k+2≤s)
    (h0 : s*k+1≤(ball D V u k).card+m) (h1 : s*(k+1)+1≤(ball D V u (k+1)).card+m)
    (dip : (ball D V u (k+2)).card+m≤s*(k+2)) :
    let S := ball D V u (k+1) \ ball D V u k
    let T := ball D V u (k+2) \ ball D V u (k+1)
    s*(k+2)+1≤(ball D V u (k+2)).card+m+(h+1) ∧
    s≤S.card+2*h ∧ 37*s≤38*T.card ∧ (∑ x∈S,(T \ outN D T x).card)≤s*h := by
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
  have pay := ShenVariablePaid.payment (k:=k) gap (by omega) (by omega : 64*(h*h)≤s) hf hm hu (by omega)
    (show T.card<s by omega)
    (show U.card≤s*s by have := Nat.mul_le_mul_left s hk; omega)
    (by simp only [layer,Nat.add_sub_cancel]; change S.card≤2*s; omega)
  change q*s+1+H≤U.card+S.card*T.card at pay
  have budget : H+x*x+s*y+z*T.card≤s*h := by
    nlinarith only [pay,hx,uc,congrArg (fun j : ℕ => j*s) gap,
      congrArg (fun j : ℕ => j*T.card) hz,congrArg (fun j : ℕ => (s+x)*j) hy,
      Nat.mul_le_mul_left s (show k≤s by omega),Nat.zero_le (x*y),Nat.zero_le m]
  have tiny : 40*x≤s := by
    by_contra! bad
    have hsq := Nat.mul_lt_mul_of_pos_right bad (show 0<40*x by omega)
    have hsq' := Nat.mul_lt_mul_of_pos_left bad (show 0<s by omega)
    nlinarith only [hsq,hsq',Nat.mul_le_mul_left s large,budget,
      Nat.zero_le H,Nat.zero_le (s*y),Nat.zero_le (z*T.card)]
  have yl : y≤h := Nat.le_of_mul_le_mul_left (by omega : s*y≤s*h) (by omega : 0<s)
  have tall : 37*s≤38*T.card := by omega
  have zl : z≤2*h := by
    by_contra! bad
    have mul := Nat.mul_lt_mul_of_pos_right bad (show 0<T.card by omega)
    have mul' := Nat.mul_le_mul_left h (show s≤2*T.card by omega)
    nlinarith only [budget,mul,mul',Nat.zero_le H,Nat.zero_le (x*x),Nat.zero_le (s*y)]
  change _ ∧ s≤S.card+2*h ∧ 37*s≤38*T.card ∧ H≤s*h
  exact ⟨by omega,by omega,tall,by omega⟩

theorem table_false {D : CH.Digraph} {V S T X : Finset ℕ} {q s h r E d : ℕ}
    (gap : q+h=2*s) (middle : q≤2*(r+1)) (half : 2*r≤q)
    (big : 35*d+21*E+568*h+40≤s) (hp : 2≤h) (hf : QFree D V q)
    (sv : S⊆V) (tv : T⊆V) (wide : s≤S.card+2*h) (heads : 37*s≤38*T.card)
    (hits : 5*(S∩X).card≤s) (holes : (∑ x∈S,(T \ outN D T x).card)≤s*h)
    (floor : ∀ z∈T,s*r≤(ball D V z r).card+E)
    (upper : ∀ x∈S \ X,(ball D V x (r+1)).card≤s*(r+1)+d)
    (missing : ∀ x∈S \ X,(V.filter (fun y => y∉ball D V x (r+1) ∧ x∉ball D V y (r+1))).card≤d) :
    False := by
  let miss := fun x => (T \ outN D T x).card
  let W := S \ X
  let A := W.filter (fun x => miss x≤28*h)
  have sub : A⊆W := Finset.filter_subset _ _
  have ws : W⊆S := Finset.sdiff_subset
  have sw : W.card+(S∩X).card=S.card := Finset.card_sdiff_add_card_inter _ _
  have wa := Finset.card_sdiff_add_card_eq_card sub
  have hi (x) (hx : x∈W \ A) : 28*h≤miss x := by
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
  let e := 36*s/64
  have close (x) (hx : x∈A) (y) (hy : y∈A) :
      (ball D V x (r+1) \ ball D V y (r+1)).card≤e := by
    apply ShenCommonSuccessor.pair_row_diff (b:=s*r-E) (N:=s*(r+1)+d) (g:=28*h) hf tv half
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

private noncomputable def hits (D : CH.Digraph) (V X : Finset ℕ) (u p k : ℕ) : ℕ :=
  (X ∩ (ball D V u k \ ball D V u p)).card

private theorem hits_mono {D : CH.Digraph} {V X : Finset ℕ} {u p i j : ℕ} (h : i≤j) :
    hits D V X u p i≤hits D V X u p j := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hX,ho,hn⟩ := (show x∈X ∧ x∈ball D V u i ∧ x∉ball D V u p by simpa [Finset.mem_inter,Finset.mem_sdiff] using hx)
  exact Finset.mem_inter.mpr ⟨hX, Finset.mem_sdiff.mpr ⟨ball_mono_radius h ho,hn⟩⟩

private theorem hits_add {D : CH.Digraph} {V X : Finset ℕ} {u p k : ℕ} (pk : p≤k) :
    hits D V X u p (k+1)=hits D V X u p k+((ball D V u (k+1) \ ball D V u k)∩X).card := by
  let A := X ∩ (ball D V u k \ ball D V u p)
  let B := (ball D V u (k+1) \ ball D V u k)∩X
  have ab : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x ha hb
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hb).1).2 (Finset.mem_sdiff.mp (Finset.mem_inter.mp ha).2).1
  have eq : X∩(ball D V u (k+1) \ ball D V u p)=A∪B := by
    ext x
    simp only [A,B,Finset.mem_inter,Finset.mem_union,Finset.mem_sdiff]
    constructor
    · rintro ⟨hx,ho,hn⟩
      by_cases hk : x∈ball D V u k
      · exact Or.inl ⟨hx,hk,hn⟩
      · exact Or.inr ⟨⟨ho,hk⟩,hx⟩
    · rintro (⟨hx,hk,hn⟩|⟨⟨ho,hn⟩,hx⟩)
      · exact ⟨hx,ball_mono_radius (by omega : k≤k+1) hk,hn⟩
      · exact ⟨hx,ho,fun hp => hn (ball_mono_radius pk hp)⟩
  unfold hits
  rw [eq]
  exact Finset.card_union_of_disjoint ab

theorem charge_root {q s h p r E d u : ℕ} {D : CH.Digraph} {V X : Finset ℕ}
    (gap : q+h=2*s) (hp : 2≤h) (lin : 1600*h≤s) (scale : 64*(h*h)≤s)
    (middle : q≤2*(r+1)) (half : 2*r≤q) (big : 35*d+21*E+568*h+40≤s)
    (hf : QFree D V q) (hm : ∀ x∈V,s≤(outN D V x).card) (hu : u∈V)
    (ideal : ∀ k,k≤p+2 → s*k+1≤(ball D V u k).card)
    (floor : ∀ z∈V,s*r≤(ball D V z r).card+E)
    (upper : ∀ x∈V \ X,(ball D V x (r+1)).card≤s*(r+1)+d)
    (missing : ∀ x∈V \ X,(V.filter (fun y => y∉ball D V x (r+1) ∧ x∉ball D V y (r+1))).card≤d) :
    ∀ k,k≤s → s*(s*k+1-(ball D V u k).card)≤5*(h+1)*hits D V X u p (k-1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro ks
    by_cases early : k≤p+2
    · rw [Nat.sub_eq_zero_of_le (ideal k early),Nat.mul_zero]; omega
    obtain ⟨j,rfl⟩ : ∃ j,k=j+2 := ⟨k-2,by omega⟩
    let m := max (s*j+1-(ball D V u j).card) (s*(j+1)+1-(ball D V u (j+1)).card)
    have a : s*j+1≤(ball D V u j).card+m := by dsimp [m]; omega
    have b : s*(j+1)+1≤(ball D V u (j+1)).card+m := by dsimp [m]; omega
    let w := 5*(h+1)
    have prev : s*m≤w*hits D V X u p j := by
      have old := ih j (by omega) (by omega)
      have next := ih (j+1) (by omega) (by omega)
      rw [Nat.add_sub_cancel] at next
      have grow := Nat.mul_le_mul_left w (hits_mono (D:=D) (V:=V) (X:=X) (u:=u) (p:=p) (by omega : j-1≤j))
      dsimp only [m]; rcases le_total (s*j+1-(ball D V u j).card) (s*(j+1)+1-(ball D V u (j+1)).card) with le|le
      · rwa [max_eq_right le]
      · rw [max_eq_left le]; exact old.trans grow
    change s*(s*(j+2)+1-(ball D V u (j+2)).card)≤w*hits D V X u p (j+1)
    by_cases dip : (ball D V u (j+2)).card+m≤s*(j+2)
    · obtain ⟨jump,wide,heads,holes⟩ := offset_table gap hp lin scale hf hm hu ks a b dip
      let S := ball D V u (j+1) \ ball D V u j
      let T := ball D V u (j+2) \ ball D V u (j+1)
      have sv : S⊆V := Finset.sdiff_subset.trans ball_subset
      have tv : T⊆V := Finset.sdiff_subset.trans ball_subset
      have bridge : S \ X ⊆ V \ X := by
        intro x hx; obtain ⟨hx,hn⟩ := Finset.mem_sdiff.mp hx
        exact Finset.mem_sdiff.mpr ⟨sv hx,hn⟩
      have marked : s≤5*(S∩X).card := by
        by_contra! no
        exact table_false gap middle half big hp hf sv tv wide heads no.le holes
          (fun x hx => floor x (tv hx)) (fun x hx => upper x (bridge hx)) (fun x hx => missing x (bridge hx))
      have inc := Nat.mul_le_mul_left s (show s*(j+2)+1-(ball D V u (j+2)).card≤m+(h+1) by omega)
      have price := Nat.mul_le_mul_right (h+1) marked
      rw [hits_add (by omega : p≤j)]
      dsimp only [w,S] at *
      nlinarith only [inc,prev,price]
    · have small := Nat.mul_le_mul_left s (show s*(j+2)+1-(ball D V u (j+2)).card≤m by omega)
      exact (small.trans prev).trans (Nat.mul_le_mul_left w (hits_mono (by omega)))

theorem order_strict {q s h : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (gap : q+h=2*s) (hp : 2≤h) (large : 424*(h+1)^2≤s)
    (hf : QFree D V q) (hm : ∀ x∈V,s≤(outN D V x).card) (ne : V.Nonempty) :
    q*s<V.card := by
  by_contra! ord
  let E := 3*(h*h)/2
  let d := 11*(h*(h+1))
  have hh : 2*h≤h*h := Nat.mul_le_mul_right h hp
  have big : 35*d+21*E+568*h+40≤s := by
    apply le_trans _ large
    have Ele : 2*E≤3*(h*h) := by dsimp [E]; omega
    dsimp only [d]; zify at Ele ⊢; nlinarith [sq_nonneg ((h:ℤ)-8), (show (2:ℤ)≤h by exact_mod_cast hp)]
  have scale : 64*(h*h)≤s := by
    apply le_trans _ large; ring_nf; nlinarith only [hh,hp]
  have lin : 1600*h≤s := by
    apply le_trans _ large; ring_nf; nlinarith only [hh,hp]
  let p := s-h
  let i := q/2
  let l := q-i
  have ps : p+h=s := by dsimp [p]; omega
  have pl : p+s=q := by omega
  have ij : i+l=q := by dsimp [l,i]; omega
  have il : i≤l := by dsimp [i,l]; omega
  have pi : p≤i := by dsimp [p,i]; omega
  have ls : l≤s := by dsimp [l,i]; omega
  obtain ⟨r,hr⟩ : ∃ r,l=r+1 := ⟨l-1,by dsimp [l,i]; omega⟩
  have pr : p≤r := by dsimp [l,i,p] at *; omega
  have floor (u) (hu : u∈V) : s*r≤(ball D V u r).card+E := by
    let b := s-2*h
    have sb : b+2*h=s := by dsimp [b]; omega
    have qb : 2*b+3*h=q := by omega
    have hb : h≤b := by dsimp [b]; omega
    have grow := ShenVariableCutoff.outer_growth (by omega : 1≤h) hb (qb ▸ hf)
      (fun x hx => sb ▸ hm x hx) hu (r-b) (by omega)
    rw [sb,show b+(r-b)=r by omega] at grow
    have rb : 2*(r-b)≤3*h := by dsimp [b,l,i] at *; omega
    have hc := Nat.mul_le_mul_left h rb
    have hc2 : 2*(h*(r-b))≤3*(h*h) := by nlinarith only [hc]
    dsimp [E]; omega
  have ideal (u) (hu : u∈V) (j) (hj : j≤p+2) : s*j+1≤(ball D V u j).card := by
    have qeq : 2*p+h=q := by omega
    have h := ShenVariablePaid.ideal (b:=p) (h:=h) hp (by omega) (qeq ▸ hf)
      (fun x hx => ps ▸ hm x hx) hu j hj
    rwa [ps] at h
  let deficit := fun x k => s*k+1-(ball D V x k).card
  let cost := fun x => max (deficit x s) (max (deficit x i) (deficit x l))
  let loss := fun x => (V.filter (fun y => y∉ball D V x l ∧ x∉ball D V y l)).card
  let exc := fun x => (ball D V x l).card-(s*l+1)
  let X := V.filter (fun x => d≤loss x+exc x)
  have subX : X⊆V := Finset.filter_subset _ _
  have xs : ∀ x∈V \ X,loss x+exc x<d := by
    intro x hx
    obtain ⟨hv,hn⟩ := Finset.mem_sdiff.mp hx
    by_contra! ge
    exact hn (Finset.mem_filter.mpr ⟨hv,ge⟩)
  let total := ∑ x∈V,cost x
  have rad : s*i+s*l=s*q := by rw [← Nat.mul_add,ij]
  have row (x) (_ : x∈V) : s*q+2+exc x≤(ball D V x i).card+(ball D V x l).card+
      (cost x+cost x) := by dsimp [exc,cost,deficit]; omega
  have sum := Finset.sum_le_sum row
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at sum
  have budget := ShenNearTotal.pair_budget (l:=l) hf ij.le il le_rfl
  have cells : (ShenNearTotal.incomparablePairs D V V l).card=∑ x∈V,loss x := by
    simp only [ShenNearTotal.incomparablePairs,loss,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_product V V _
  rw [cells] at budget
  have costs := Finset.sum_le_sum (fun x hx => (show d≤loss x+exc x from (Finset.mem_filter.mp (show x∈X from hx)).2))
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at costs
  have mark := costs.trans (Finset.sum_le_sum_of_subset_of_nonneg subX (fun _ _ _ => Nat.zero_le _))
  rw [Finset.sum_add_distrib] at mark
  have ceil := Nat.mul_le_mul_left V.card ord
  have charged : X.card*d+V.card≤2*total := by
    dsimp [total]; nlinarith only [sum,budget,ceil,mark]
  have width : s*p+s*h=s*s := by rw [← Nat.mul_add,ps]
  have sz : s*p+s*s=s*q := by rw [← Nat.mul_add,pl]
  rw [Nat.mul_comm q s] at ord
  let shortage := fun x => s*p-(reverseBall D V x p).card
  have account (x) (_ : x∈V) : shortage x+(reverseBall D V x p).card≤s*p+cost x := by
    have := reverseBall_add_ball_le (v:=x) hf (by omega : s+p≤q)
    dsimp [shortage,cost,deficit]; omega
  have balance := Finset.sum_le_sum account
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,sum_reverseBall_eq_sum_ball,
    Finset.sum_const_nat (fun _ _ => rfl)] at balance
  have lower := Finset.sum_le_sum (fun x hx => (ideal x hx p (by omega)).trans' (Nat.le_succ _))
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at lower
  have charge : (∑ x∈V,shortage x)≤total := by dsimp [total]; omega
  have cellBound (x) (hx : x∈X) :
      (reverseBall D V x s \ reverseBall D V x p).card≤s*h+shortage x := by
    have inc : reverseBall D V x p ⊆ reverseBall D V x s := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1,
        ball_mono_radius (by omega : p≤s) (Finset.mem_filter.mp hv).2⟩
    have := Finset.card_sdiff_add_card_eq_card inc
    have := reverseBall_add_ball_le (v:=x) hf pl.le
    have := ideal x (subX hx) p (by omega)
    dsimp [shortage]; omega
  have ex := Finset.sum_le_sum cellBound
  rw [Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl),← ShenShellTraffic.transpose_between] at ex
  have eq (u) : X.filter (fun x => x∈ball D V u s ∧ x∉ball D V u p)=X∩(ball D V u s \ ball D V u p) := by
    ext x; simp only [Finset.mem_filter,Finset.mem_inter,Finset.mem_sdiff]
  simp only [eq] at ex
  have restricted := Finset.sum_le_sum_of_subset_of_nonneg (f:=shortage) subX (fun _ _ _ => Nat.zero_le _)
  let traffic := ∑ u∈V,hits D V X u p s
  have trafficCap : traffic≤X.card*(s*h)+total := by
    change traffic≤X.card*(s*h)+(∑ x∈X,shortage x) at ex
    omega
  let w := 5*(h+1)
  have bill (u) (hu : u∈V) : s*cost u≤w*hits D V X u p s := by
    have root := charge_root (X:=X) gap hp lin scale (by omega : q≤2*(r+1))
      (by dsimp [i,l] at hr; omega : 2*r≤q) big hf hm hu (ideal u hu)
      floor
      (by intro x hx; have := xs x hx; dsimp [exc] at this; rw [← hr]; omega)
      (by intro x hx; have := xs x hx; rw [← hr]; change loss x≤d; omega)
    have bound (k) (hk : k≤s) : s*deficit u k≤w*hits D V X u p s :=
      (root k hk).trans (Nat.mul_le_mul_left w (hits_mono (by omega)))
    dsimp only [cost]
    rcases le_total (deficit u i) (deficit u l) with il'|li'
    · rw [max_eq_right il']; rcases le_total (deficit u s) (deficit u l) with h|h
      · rw [max_eq_right h]; exact bound l ls
      · rw [max_eq_left h]; exact bound s le_rfl
    · rw [max_eq_left li']; rcases le_total (deficit u s) (deficit u i) with h|h
      · rw [max_eq_right h]; exact bound i (by omega)
      · rw [max_eq_left h]; exact bound s le_rfl
  have bills := Finset.sum_le_sum bill
  simp only [← Finset.mul_sum] at bills
  change s*total≤w*traffic at bills
  have pay := Nat.mul_le_mul_left w trafficCap
  have cheap : 11*(w*h)≤5*d := by dsimp [w,d]; ring_nf; nlinarith only [hh,hp]
  have costX := Nat.mul_le_mul_left X.card cheap
  have capacity := Nat.mul_le_mul_right s charged
  have price := Nat.mul_le_mul_right s costX
  have unit : 12*w≤s := by dsimp [w]; nlinarith only [lin,hp]
  have minOrder := Finset.card_pos.mpr ne
  have nonzero : 0<V.card*s := Nat.mul_pos minOrder (by omega)
  have keep := Nat.mul_le_mul_right total unit
  nlinarith only [bills,pay,capacity,price,nonzero,keep,Nat.zero_le (s*total)]

#print axioms order_strict
/-- The cycle bound at cutoff `q = 2s - h` for every order up to `q·s`. -/
theorem cycle_in_window {q s h n : ℕ} {D : CH.Digraph}
    (gap : q+h=2*s) (hp : 2≤h) (large : 424*(h+1)^2≤s)
    (hn : 0<n) (hc : n≤q*s) (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  have := order_strict gap hp large (qfree_of_noShort hl no)
    (fun x hx => Compose.FloorSix.out_card hm (Finset.mem_range.mp hx)) ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at this; omega

#print axioms cycle_in_window
end LeanCH.BR.CumulativeDeficitSharp
