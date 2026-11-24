import checkpoints.shen_extension.VariablePaidTensor
import checkpoints.shen_extension.ShellTrafficTensor
import checkpoints.shen_extension.FifthStripMixedClone

namespace LeanCH.BR.ShenSixthTraffic
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip DotTwoPassShellTransport
open Classical
set_option maxRecDepth 8192

local macro "strip_arith" : tactic =>
  `(tactic| (simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] at * <;> omega))

private theorem prefix_payment {a k u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 8176≤a) (hf : QFree D V (2*a+24)) (hm : ∀ v∈V,a+16≤(outN D V v).card)
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
theorem profile {a : ℕ} {D : CH.Digraph} {V : Finset ℕ} (ha : 8176≤a)
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
      (L:=L) (H:=s*(a+14)+1-112) (e:=114) hf hu (fun v hv => ideal v hv _ (by omega)) (base u hu)
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
      (L:=L) (H:=s*(a+13)+1-104) (e:=114) hf hu base (first u hu)
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
private theorem minimum_table {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 8176≤a) (hf : QFree D V (2*a+24)) (hm : ∀ v∈V,a+16≤(outN D V v).card)
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

theorem order_strict {a : ℕ} {D : CH.Digraph} {V : Finset ℕ} (ha : 8176≤a)
    (hf : QFree D V (2*a+24)) (hm : ∀ v∈V,a+16≤(outN D V v).card) (ne : V.Nonempty) :
    (2*a+24)*(a+16)<V.card := by
  by_contra! hn
  have p := profile ha hf hm hn
  apply ShenShellTraffic.even_packet_false (k:=a+10) (s:=a+16) (b:=(a+16)*(a+12))
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
    (hs : 8192≤s) (hq : q=2*s-8) (hn : 0<n) (hc : n≤q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨a,rfl⟩ : ∃ a,s=a+16 := ⟨s-16,by omega⟩
  have he : q=2*a+24 := by omega
  rw [he] at hc ⊢
  by_contra no
  have h := order_strict (by omega : 8176≤a) (qfree_of_noShort hl no)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv)) ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at h; omega

#print axioms order_strict
#print axioms cycle_sixth_strip_closed

theorem ch_above_sixth_threshold {s n : ℕ} {D : CH.Digraph} (hs : 8192≤s)
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
end LeanCH.BR.ShenSixthTraffic
