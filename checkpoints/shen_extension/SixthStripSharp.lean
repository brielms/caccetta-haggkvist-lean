import checkpoints.shen_extension.SixthStripTraffic

/-!
# The sixth strip with a tightened threshold

The argument of `ShellTrafficTensor` and `SixthStripTraffic` with the growth
parameter passed to `paid_growth` lowered as far as its own inequalities allow.
The threshold `8192 ≤ s` becomes `6276 ≤ s`. The capstone still uses the
original files.
-/

namespace LeanCH.BR.SixthStripSharp
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip DotTwoPassShellTransport
open Classical
set_option maxRecDepth 8192
/-- At a selected almost-flat even-cutoff root, the exceptional vertices
and row holes cannot account for all of the nearly coincident reach rows. -/
theorem selected_table_false {D : CH.Digraph} {V S T X : Finset ℕ} {s r b : ℕ}
    (scale : 6276≤s) (radius : r+5=s) (hf : QFree D V (2*(r+1)))
    (hSV : S⊆V) (hTV : T⊆V)
    (wide : s≤S.card+2) (heads : 7*s≤8*(T.card+1)) (badCount : 8*(S∩X).card≤s)
    (holes : (∑ x∈S,(T \ outN D T x).card)≤2*s)
    (low : ∀ y∈T, b+1≤(ball D V y r).card+s)
    (upper : ∀ x∈S \ X, (ball D V x (r+1)).card≤b+63)
    (missing : ∀ x∈S \ X,
      (V.filter (fun y => y∉ball D V x (r+1) ∧ x∉ball D V y (r+1))).card≤63) : False := by
  let miss := fun x => (T \ outN D T x).card
  let W := S \ X
  let A := W.filter (fun x => miss x≤8)
  let e := (9*s)/16+71
  have sub : A⊆W := Finset.filter_subset _ _
  have subW : W⊆S := Finset.sdiff_subset
  have splitS : W.card+(S∩X).card=S.card := Finset.card_sdiff_add_card_inter _ _
  have splitW := Finset.card_sdiff_add_card_eq_card sub
  have high (x) (hx : x∈W \ A) : 9≤miss x := by
    obtain ⟨hxW,hno⟩ := Finset.mem_sdiff.mp hx
    by_contra! lo
    exact hno (Finset.mem_filter.mpr ⟨hxW,by omega⟩)
  have discarded := Finset.sum_le_sum high
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at discarded
  have hh := (Finset.sum_le_sum_of_subset_of_nonneg (f:=miss)
    ((Finset.sdiff_subset (s:=W) (t:=A)).trans subW) (fun _ _ _ => Nat.zero_le _))
  have hd : (W \ A).card*9≤2*s := discarded.trans (hh.trans holes)
  have ne := Finset.card_pos.mp (show 0<A.card by omega)
  have close (x) (hx : x∈A) (y) (hy : y∈A) :
      (ball D V x (r+1) \ ball D V y (r+1)).card≤e := by
    apply ShenCommonSuccessor.pair_row_diff (b:=b+1-s) (N:=b+63) (g:=8) hf hTV (by omega)
      (fun z hz => by have := low z hz; omega) (upper x (sub hx))
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 (by omega) _
    dsimp [e]; omega
  have bound := ShenNearTotal.row_capacity (d:=63) hf (sub.trans (subW.trans hSV)) ne
    (by dsimp [e]; omega) (by dsimp [e]; omega) close (by
      intro x hx
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (sub.trans (subW.trans hSV)))).trans
        (missing x (sub hx)))
  dsimp [e] at bound
  omega

#print axioms selected_table_false

theorem tail_count (V : Finset ℕ) (f : ℕ → ℕ) (t : ℕ) :
    (V.filter (fun x => t≤f x)).card*t≤∑ x∈V,f x := by
  let X := V.filter (fun x => t≤f x)
  have bound (x) (hx : x∈X) : t≤f x := (Finset.mem_filter.mp hx).2
  have h := Finset.sum_le_sum bound
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at h
  exact h.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _))

/-- The even top-order packet from the local next-depth paper suffices
for contradiction. The assumptions are forward ball floors and the
boundary width and hole bound at all minimum middle-ball roots. -/
theorem even_packet_false {D : CH.Digraph} {V : Finset ℕ} {s k b : ℕ}
    (scale : 6276≤s) (radius : k+6=s) (roomB : 2*s≤b)
    (hf : QFree D V (2*(k+2))) (ne : V.Nonempty) (ord : V.card≤2*b)
    (floor0 : ∀ x∈V, b-2*s+1≤(ball D V x k).card)
    (floor1 : ∀ x∈V, b-s+1≤(ball D V x (k+1)).card)
    (floor2 : ∀ x∈V, b≤(ball D V x (k+2)).card)
    (floor3 : ∀ x∈V, b+s-1≤(ball D V x (k+3)).card)
    (floor4 : ∀ x∈V, b+2*s-5≤(ball D V x (k+4)).card)
    (wide : ∀ u∈V, (ball D V u (k+2)).card=b →
      s≤(ball D V u (k+1) \ ball D V u k).card+2)
    (holes : ∀ u∈V, (ball D V u (k+2)).card=b →
      (∑ x∈ball D V u (k+1) \ ball D V u k,
        ((ball D V u (k+2) \ ball D V u (k+1)) \ outN D (ball D V u (k+2) \ ball D V u (k+1)) x).card)≤2*s) :
    False := by
  let e := fun x => (ball D V x (k+2)).card-b
  let a := fun x => (ball D V x (k+1)).card-(b-s+1)
  let d := fun x => (V.filter (fun y => y∉ball D V x (k+2) ∧ x∉ball D V y (k+2))).card
  let X := V.filter (fun x => 64≤e x+d x)
  let Z := V.filter (fun x => e x=0)
  have hZ : Z⊆V := Finset.filter_subset _ _
  have counts {i v : ℕ} (f : ∀ x∈V,v≤(ball D V x i).card) :
      (∑ x∈V,((ball D V x i).card-v))+V.card*v=∑ x∈V,(ball D V x i).card := by
    have he := Finset.sum_congr (s₁:=V) rfl (fun x hx => Nat.sub_add_cancel (f x hx))
    rwa [Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl)] at he
  have ec := counts floor2
  change (∑ x∈V,e x)+V.card*b=_ at ec
  have ac := counts floor1
  change (∑ x∈V,a x)+V.card*(b-s+1)=_ at ac
  have gb := ShenNearTotal.pair_budget (l:=k+2) hf (by omega : (k+2)+(k+2)≤2*(k+2)) le_rfl le_rfl
  have dc : (ShenNearTotal.incomparablePairs D V V (k+2)).card= ∑ x∈V,d x := by
    simp only [ShenNearTotal.incomparablePairs,d,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_product V V _
  rw [dc] at gb
  have ar : V.card*(V.card+1)≤2*(V.card*b)+V.card := by
    nlinarith only [Nat.mul_le_mul_left V.card ord]
  have both : (∑ x∈V,d x)+2*(∑ x∈V,e x)≤V.card := by omega
  have bad := tail_count V (fun x => e x+d x) 64
  change X.card*64≤_ at bad
  rw [Finset.sum_add_distrib] at bad
  have m : X.card*64≤V.card := by omega
  have lc := tail_count V e 1
  have missingMin : V.filter (fun x => 1≤e x)=V \ Z := by
    ext x
    simp only [Z,Finset.mem_sdiff,Finset.mem_filter]
    by_cases hx : x∈V <;> simp [hx] <;> omega
  rw [missingMin,Nat.mul_one] at lc
  have sc := Finset.card_sdiff_add_card_eq_card hZ
  have zLarge : V.card≤2*Z.card := by omega
  have zne := Finset.card_pos.mp (show 0<Z.card by have := Finset.card_pos.mpr ne; omega)
  have ca := tensor_capacity_identity hf (by omega : (k+1)+(k+3)≤2*(k+2))
  have lb := Finset.sum_le_sum floor3
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at lb
  have prod := congrArg (fun n : ℕ => V.card*n) (show (b-s+1)+(b+s-1)=2*b by omega)
  rw [Nat.mul_add] at prod
  have sa : (∑ u∈Z,a u)≤V.card := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (f:=a) hZ (fun _ _ _ => Nat.zero_le _)
    nlinarith only [this,ac,ca,lb,prod,ar,Nat.zero_le (∑ u∈V,
      (V \ (ball D V u (k+1) ∪ reverseBall D V u (k+3))).card)]
  have rev0 (u) (hu : u∈V) : (reverseBall D V u k).card≤b-2*s+6 := by
    have := reverseBall_add_ball_le (v:=u) hf (by omega : (k+4)+k≤2*(k+2))
    have := floor4 u hu; omega
  have rev1 (u) (hu : u∈V) : (reverseBall D V u (k+1)).card≤b-s+2 := by
    have := reverseBall_add_ball_le (v:=u) hf (by omega : (k+3)+(k+1)≤2*(k+2))
    have := floor3 u hu; omega
  have afford : V.card+X.card*((b-s+2)-(b-2*s+6))+V.card*((b-2*s+6)-(b-2*s+1))
      ≤Z.card*(s/8) := by
    rw [show (b-2*s+6)-(b-2*s+1)=5 by omega]
    have h1 := Nat.mul_le_mul_left X.card (show (b-s+2)-(b-2*s+6)≤s by omega)
    have h2 := Nat.mul_le_mul_right s m
    have h3 := Nat.mul_le_mul_right (s/8) zLarge
    have h4 := Nat.mul_le_mul_left V.card (show 384+s≤32*(s/8) by omega)
    nlinarith only [h1,h2,h3,h4]
  obtain ⟨u,uz,sel⟩ := ShenShellTraffic.select_root (show X⊆V from Finset.filter_subset _ _) hZ zne
    (by omega) (by omega) floor0 rev0 rev1 a sa afford
  have uv := hZ uz
  have mid : (ball D V u (k+2)).card=b := by
    have h := (Finset.mem_filter.mp uz).2; change e u=0 at h
    dsimp [e] at h; have := floor2 u uv; omega
  let S := ball D V u (k+1) \ ball D V u k
  let T := ball D V u (k+2) \ ball D V u (k+1)
  have Ssub : S⊆V := Finset.sdiff_subset.trans ball_subset
  have eqX : X.filter (fun x => x∈ball D V u (k+1) ∧ x∉ball D V u k)=S∩X := by
    ext x; simp [S]; tauto
  rw [eqX] at sel
  have tc : T.card+(ball D V u (k+1)).card=(ball D V u (k+2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have au : a u+(b-s+1)=(ball D V u (k+1)).card := Nat.sub_add_cancel (floor1 u uv)
  have good (x) (hx : x∈S \ X) : e x+d x≤63 := by
    obtain ⟨hxS,hn⟩ := Finset.mem_sdiff.mp hx
    by_contra! large
    exact hn (Finset.mem_filter.mpr ⟨Ssub hxS,by omega⟩)
  apply selected_table_false (r:=k+1) (b:=b) (X:=X) scale (by omega) hf Ssub
    (show T⊆V from Finset.sdiff_subset.trans ball_subset) (wide u uv mid) (by omega) (by omega) (holes u uv mid)
  · intro y hy; have := floor1 y (ball_subset (Finset.mem_sdiff.mp hy).1); omega
  · intro x hx
    have h := good x hx
    change (ball D V x (k+2)).card≤b+63
    dsimp only [e] at h; omega
  · intro x hx; have := good x hx; change d x≤63; omega

#print axioms even_packet_false
local macro "strip_arith" : tactic =>
  `(tactic| (simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] at * <;> omega))

theorem prefix_payment {a k u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 6260≤a) (hf : QFree D V (2*a+24)) (hm : ∀ v∈V,a+16≤(outN D V v).card)
    (hu : u∈V) (hk : k+2≤a+16) (thin : (shell D V (k+1) u).card<a+16)
    (small : (ball D V u (k+2)).card≤(a+16)*(k+2))
    (prev : (a+16)*k≤(ball D V u k).card) :
    (2*a+24)*(a+16)+128+holes D V (k+1) u≤((ball D V u (k+1)).erase u).card+
      (layer D V (k+1) u).card*(shell D V (k+1) u).card := by
  let s := a+16
  let B := s*(a+12)-7
  let q := 2*a+24
  have hBC : B+B+14=q*s := by dsimp [B,s,q]; strip_arith
  have j : ((ball D V u (k+1)).erase u).card≤s*s := by
    have := Finset.card_le_card (Finset.erase_subset u (ball D V u (k+1)))
    have := Finset.card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (show k+1≤k+2 by omega))
    have := Nat.mul_le_mul_left (a+16) hk
    dsimp [s]; omega
  have m : (layer D V (k+1) u).card≤2*s := by
    have h := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (show k≤k+1 by omega))
    have := Finset.card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (show k+1≤k+2 by omega))
    rw [Nat.mul_add] at small
    simp only [layer,Nat.add_sub_cancel,s]; omega
  apply ShenMixedClone.prefix_price (s:=s) (i:=a+12) (j:=a+12) (B:=B) (C:=B)
    (by omega) _ hf hm hu (by dsimp [s]; omega) (by omega) thin j m _
  · intro F W h md _ v hv
    have hq : 2*a+24=2*(a+8)+8 := by omega
    rw [hq] at h
    have h := ShenVariablePaid.outer (h:=8) (b:=a+8) (by decide) (by omega) h md hv 4 (by decide)
    change (a+16)*(a+12)+1≤(ball F W v (a+12)).card+8 at h
    dsimp [B,s]; constructor <;> omega
  · change (2*s)*(q*s+128)*((q*s+128)-(B+B)) < (B+B-1-s*s)^2
    rw [show q*s+128-(B+B)=142 by omega]
    have hsmall : q*s+128≤2*(s*s) := by dsimp [s,q]; strip_arith
    have hbig : s*s≤2*(B+B-1-s*s) := by
      have sq : s*s+16*s+30≤2*(s*s) := by dsimp [s]; nlinarith only [ha,Nat.zero_le (a*a)]
      have eq : q*s+8*s=2*(s*s) := by dsimp [q,s]; ring
      omega
    have h₁ := Nat.mul_le_mul_right 142 (Nat.mul_le_mul_left (2*s) hsmall)
    have h₂ := Nat.pow_le_pow_left hbig 2
    have h₃ := Nat.mul_lt_mul_of_pos_right (show 2272<s by dsimp [s]; omega)
      (show 0<s*s*s by dsimp [s]; positivity)
    nlinarith only [h₁,h₂,h₃]

/-- Source growth at the five consecutive radii used by the global
exceptional-vertex count. Every completion uses only the unrestricted floor. -/
theorem profile {a : ℕ} {D : CH.Digraph} {V : Finset ℕ} (ha : 6260≤a)
    (hf : QFree D V (2*a+24)) (hm : ∀ v∈V,a+16≤(outN D V v).card)
    (hn : V.card≤(2*a+24)*(a+16)) :
    ∀ u∈V, (a+16)*(a+10)+1≤(ball D V u (a+10)).card ∧
      (a+16)*(a+11)+1≤(ball D V u (a+11)).card ∧
      (a+16)*(a+12)≤(ball D V u (a+12)).card ∧
      (a+16)*(a+12)+(a+15)≤(ball D V u (a+13)).card ∧
      (a+16)*(a+14)≤(ball D V u (a+14)).card+5 := by
  let s := a+16
  let L := (2*a+24)*s+128
  have hq : 2*a+24=2*(a+8)+8 := by omega
  have free := hf
  rw [hq] at free
  have ideal (v) (hv : v∈V) := ShenVariablePaid.ideal (b:=a+8) (h:=8) (by decide) (by omega) free hm hv
  have base (u) (hu : u∈V) : s*(a+10)+1≤(ball D V u (a+10)).card := ideal u hu _ (by omega)
  have first (u) (hu : u∈V) : s*(a+11)+1≤(ball D V u (a+11)).card := by
    have h := ShenMixedClone.paid_growth (k:=a+9) (r:=a+14) (c:=s) (t:=a+15)
      (L:=L) (H:=s*(a+14)+1-112) (e:=111) hf hu (fun v hv => ideal v hv _ (by omega)) (base u hu)
      (fun v hv => by
        have h := ShenVariableCutoff.outer_growth (h:=8) (b:=a) (by decide) (by omega) hf hm hv 14 (by decide)
        change (a+16)*(a+14)+1≤(ball D V v (a+14)).card+112 at h
        dsimp [s]; omega)
      (by dsimp [s]; ring) (by dsimp [s]; omega) (by dsimp [L,s]; strip_arith)
      (by dsimp [s]; strip_arith) (by omega) (by omega) (by omega) (by
        intro bad
        have ht := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u)
          (show a+10≤a+11 by omega))
        have hb := base u hu
        apply prefix_payment ha hf hm hu (by omega) _ _ (Nat.le_of_succ_le (ideal u hu _ (by omega)))
        · unfold shell; simp only [Nat.add_assoc,Nat.reduceAdd] at bad ⊢; dsimp [s] at *; strip_arith
        · dsimp [s] at *; strip_arith)
    rw [show a+9+2=a+11 by omega] at h; dsimp [s] at *; strip_arith
  have mid (u) (hu : u∈V) : s*(a+12)≤(ball D V u (a+12)).card := by
    have h := ShenMixedClone.paid_growth (k:=a+10) (r:=a+13) (c:=s) (t:=a+14)
      (L:=L) (H:=s*(a+13)+1-104) (e:=103) hf hu base (first u hu)
      (fun v hv => by
        have h := ShenVariableCutoff.outer_growth (h:=8) (b:=a) (by decide) (by omega) hf hm hv 13 (by decide)
        change (a+16)*(a+13)+1≤(ball D V v (a+13)).card+104 at h
        dsimp [s]; omega)
      (by dsimp [s]; ring) (by dsimp [s]; omega) (by dsimp [L,s]; strip_arith)
      (by dsimp [s]; strip_arith) (by omega) (by omega) (by omega) (by
        intro bad
        have ht := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u)
          (show a+11≤a+12 by omega))
        have hb := first u hu
        apply prefix_payment ha hf hm hu (by omega) _ _ (Nat.le_of_succ_le (base u hu))
        · unfold shell; simp only [Nat.add_assoc,Nat.reduceAdd] at bad ⊢; dsimp [s] at *; strip_arith
        · dsimp [s] at *; strip_arith)
    rw [show a+10+2=a+12 by omega] at h; dsimp [s] at *; strip_arith
  have next (u) (hu : u∈V) : s*(a+12)+(a+15)≤(ball D V u (a+13)).card := by
    have h := ShenMixedClone.paid_growth (k:=a+11) (r:=a+12) (c:=a+15) (t:=a+14)
      (L:=L) (e:=2) hf hu first (mid u hu) mid
      (by dsimp [s]; ring) (by omega) (by dsimp [L,s]; strip_arith)
      (by dsimp [s]; strip_arith) (by omega) (by omega) (by omega) (by
        intro bad
        have ht := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u)
          (show a+12≤a+13 by omega))
        have hb := mid u hu
        apply prefix_payment ha hf hm hu (by omega) _ _ (Nat.le_of_succ_le (first u hu))
        · unfold shell; simp only [Nat.add_assoc,Nat.reduceAdd] at bad ⊢; dsimp [s] at *; strip_arith
        · dsimp [s] at *; strip_arith)
    rw [show a+11+2=a+13 by omega] at h; dsimp [s] at *; strip_arith
  intro u hu
  refine ⟨base u hu,first u hu,mid u hu,next u hu,?_⟩
  have h := ShenMixedClone.paid_growth (k:=a+12) (r:=a+11) (c:=a+15) (t:=a+11)
    (L:=L) (e:=2) hf hu mid (next u hu) first
    (by rfl) (by omega) (by dsimp [L,s]; strip_arith)
    (by dsimp [s]; strip_arith) (by omega) (by omega) (by omega) (by
      intro bad
      have ht := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u)
        (show a+13≤a+14 by omega))
      have hb := next u hu
      apply prefix_payment ha hf hm hu (by omega) _ _ (mid u hu)
      · unfold shell; simp only [Nat.add_assoc,Nat.reduceAdd] at bad ⊢; dsimp [s] at *; strip_arith
      · dsimp [s] at *; strip_arith)
  rw [show a+12+2=a+14 by omega] at h; dsimp [s] at *; strip_arith

#print axioms profile

/-- At every minimum middle-ball root, the actual boundary has almost
s rows and at most 2s missing cells. No exact boundary packet is needed. -/
theorem minimum_table {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 6260≤a) (hf : QFree D V (2*a+24)) (hm : ∀ v∈V,a+16≤(outN D V v).card)
    (hn : V.card≤(2*a+24)*(a+16)) (hu : u∈V)
    (eqR : (ball D V u (a+12)).card=(a+16)*(a+12)) :
    let S := ball D V u (a+11) \ ball D V u (a+10)
    let T := ball D V u (a+12) \ ball D V u (a+11)
    a+16≤S.card+2 ∧ (∑ x∈S,(T \ outN D T x).card)≤2*(a+16) := by
  let S := ball D V u (a+11) \ ball D V u (a+10)
  let T := ball D V u (a+12) \ ball D V u (a+11)
  let U := (ball D V u (a+11)).erase u
  let H := ∑ x∈S,(T \ outN D T x).card
  obtain ⟨h0,h1,_,_,_⟩ := profile ha hf hm hn u hu
  have sc : S.card+(ball D V u (a+10)).card=(ball D V u (a+11)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have tc : T.card+(ball D V u (a+11)).card=(ball D V u (a+12)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have uc : U.card+1=(ball D V u (a+11)).card := Finset.card_erase_add_one (self_mem_ball hu)
  have thin : T.card<a+16 := by strip_arith
  let d := a+15-T.card
  have dt : T.card+d=a+15 := by dsimp [d]; omega
  have sup : S.card≤a+16+d := by strip_arith
  have pay := prefix_payment (k:=a+10) ha hf hm hu (by omega) (show T.card<a+16 from thin)
    (show (ball D V u (a+12)).card≤(a+16)*(a+12) from eqR.le) (Nat.le_of_succ_le h0)
  change (2*a+24)*(a+16)+128+H≤U.card+S.card*T.card at pay
  change a+16≤S.card+2 ∧ H≤2*(a+16)
  constructor
  · by_contra! small
    have ub := Nat.mul_le_mul (show S.card≤a+13 by omega) (show T.card≤a+15 by omega)
    nlinarith only [ub,pay,uc,tc,eqR,Nat.zero_le T.card,Nat.zero_le H]
  · have ub := Nat.mul_le_mul_right T.card sup
    have id := congrArg (fun v : ℕ => (a+16+d)*v) dt
    nlinarith only [ub,id,dt,pay,uc,tc,eqR,Nat.zero_le (d*d)]

theorem order_strict {a : ℕ} {D : CH.Digraph} {V : Finset ℕ} (ha : 6260≤a)
    (hf : QFree D V (2*a+24)) (hm : ∀ v∈V,a+16≤(outN D V v).card) (ne : V.Nonempty) :
    (2*a+24)*(a+16)<V.card := by
  by_contra! hn
  have p := profile ha hf hm hn
  apply even_packet_false (k:=a+10) (s:=a+16) (b:=(a+16)*(a+12))
    (by omega) (by omega) (by strip_arith) (by simpa only [show 2*(a+10+2)=2*a+24 by omega] using hf)
    ne (by strip_arith)
  · intro v hv; have := (p v hv).1; strip_arith
  · intro v hv; have := (p v hv).2.1
    rw [show a+10+1=a+11 by omega]; strip_arith
  · intro v hv; exact (p v hv).2.2.1
  · intro v hv; have := (p v hv).2.2.2.1
    rw [show a+10+3=a+13 by omega]; strip_arith
  · intro v hv; have := (p v hv).2.2.2.2
    rw [show a+10+4=a+14 by omega]; strip_arith
  · intro u hu eqR; exact (minimum_table ha hf hm hn hu eqR).1
  · intro u hu eqR; exact (minimum_table ha hf hm hn hu eqR).2

theorem cycle_sixth_strip_closed {s q n : ℕ} {D : CH.Digraph}
    (hs : 6276≤s) (hq : q=2*s-8) (hn : 0<n) (hc : n≤q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨a,rfl⟩ : ∃ a,s=a+16 := ⟨s-16,by omega⟩
  have he : q=2*a+24 := by omega
  rw [he] at hc ⊢
  by_contra no
  have h := order_strict (by omega : 6260≤a) (qfree_of_noShort hl no)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv)) ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at h; omega

#print axioms order_strict
#print axioms cycle_sixth_strip_closed

theorem ch_above_sixth_threshold {s n : ℕ} {D : CH.Digraph} (hs : 6276≤s)
    (hn : 0<n) (horder : (2*s-9)*s<n)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n s) := by
  by_cases earlier : (2*s-8)*s<n
  · exact ShenFifthStrip.ch_above_fifth_threshold (by omega) hn earlier hl hm
  have hcover : n≤CH.ceilDiv n s*s := by
    have hr := Nat.mod_lt (n+s-1) (by omega : 0<s)
    have hd := Nat.mod_add_div (n+s-1) s
    rw [Nat.mul_comm s] at hd
    unfold CH.ceilDiv
    omega
  have hlow : 2*s-8≤CH.ceilDiv n s := by
    by_contra! bad
    exact (Nat.not_le_of_lt horder) (hcover.trans (Nat.mul_le_mul_right s (by omega)))
  have hupp : CH.ceilDiv n s≤2*s-8 := by
    by_contra! bad
    have hd := Nat.div_mul_le_self (n+s-1) s
    change CH.ceilDiv n s*s≤n+s-1 at hd
    have hmul := Nat.mul_le_mul_right s (show 2*s-8+1≤CH.ceilDiv n s by omega)
    rw [Nat.add_mul,Nat.one_mul] at hmul
    omega
  exact cycle_sixth_strip_closed hs (by omega) hn hcover hl hm

#print axioms ch_above_sixth_threshold
end LeanCH.BR.SixthStripSharp
