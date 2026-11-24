import checkpoints.shen_extension.FifthStripEndpoints
import checkpoints.shen_extension.RectangleTransfer
import checkpoints.shen_extension.LabelledReachTensor

namespace LeanCH.BR.ShenFifthStrip
open BRq2 BRq3 BR45 ShenFirstStrip

local macro "strip_arith" : tactic =>
  `(tactic| (simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] at * <;> omega))

/-- Three instances of the same rectangle transfer. The parameter e allows
the common-container budget to vary with the order of the host. -/
theorem iterated_profile {a e : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v∈V, a+7≤(outN D V v).card)
    (he : e+1≤a) (hcycle : e*(e+2)≤2*a+7)
    (hcap : V.card+8≤(2*a+7)*(a+7)+e) :
    ∀ v∈V, (a+7)*(a+2)+1≤(ball D V v (a+2)).card ∧
      (a+7)*(a+3)≤(ball D V v (a+3)).card ∧
      (a+7)*(a+4)≤(ball D V v (a+4)).card+1 := by
  let L := (2*a+7)*(a+7)-3
  have ord (F : CH.Digraph) (W : Finset ℕ) (h : QFree F W (2*a+7))
      (m : ∀ w∈W, a+7≤(outN F W w).card) (ne : W.Nonempty) : L≤W.card := by
    have := order_to_three h m ne; dsimp [L]; omega
  have hL : L+3=(2*a+7)*(a+7) := by dsimp [L]; strip_arith
  have near (v) (hv : v∈V) : (a+7)*(a+2)+1≤(ball D V v (a+2)).card := by
    have h := ShenRectangleTransfer.growth (k:=a) (r:=a+6) (c:=a+7) (t:=a+6) (e:=e)
      (H:=(a+7)*(a+6)-8) ord hf hm hv
      (fun w hw => inner_growth hf hm hw a (by omega)) (inner_growth hf hm hv (a+1) le_rfl)
      (fun w hw => by have := (outer_growth hf hm (u:=w) hw).2; omega)
      (by ring) (by omega) (by omega) (by strip_arith) (by strip_arith)
      (by omega) (by omega) (by omega) hcycle
    strip_arith
  have mid (v) (hv : v∈V) : (a+7)*(a+3)≤(ball D V v (a+3)).card := by
    have h := ShenRectangleTransfer.growth (k:=a+1) (r:=a+5) (c:=a+7) (t:=a+5) (e:=e)
      (H:=(a+7)*(a+5)-5) ord hf hm hv
      (fun w hw => inner_growth hf hm hw (a+1) le_rfl) (near v hv)
      (fun w hw => by have := (outer_growth hf hm (u:=w) hw).1; omega)
      (by ring) (by omega) (by omega) (by strip_arith) (by strip_arith)
      (by omega) (by omega) (by omega) hcycle
    rw [show a+1+2=a+3 by omega] at h
    strip_arith
  intro v hv
  refine ⟨near v hv,mid v hv,?_⟩
  have h := ShenRectangleTransfer.growth (k:=a+2) (r:=a+4) (c:=a+6) (t:=a+5) (e:=e)
    (H:=(a+7)*(a+4)-3) ord hf hm hv near (mid v hv)
    (fun w hw => by have := (middle_growth hf hm (u:=w) hw).2.2; omega)
    (by ring) (by omega) (by omega) (by strip_arith) (by strip_arith)
    (by omega) (by omega) (by omega) hcycle
  rw [show a+2+2=a+4 by omega] at h
  strip_arith

theorem order_to_two {a : ℕ} {D : CH.Digraph} {V : Finset ℕ} (ha : 14≤a)
    (hf : QFree D V (2*a+7)) (hm : ∀ v∈V, a+7≤(outN D V v).card) (ne : V.Nonempty) :
    (2*a+7)*(a+7)≤V.card+2 := by
  by_contra! hbad
  have hp := iterated_profile (e:=5) hf hm (by omega) (by omega) (by omega)
  have h := card_ge_of_two_balls hf (by omega : (a+3)+(a+4)≤2*a+7)
    (fun v hv => (hp v hv).2.1) (b:=(a+7)*(a+4)-1)
    (fun v hv => by have := (hp v hv).2.2; omega) ne
  strip_arith

/-- At qs-2 the complementary balls attain their two floors at every root.
This includes the backward ball without assuming any minimum indegree. -/
theorem second_from_top_rigid {a : ℕ} {D : CH.Digraph} {V : Finset ℕ} (ha : 21≤a)
    (hf : QFree D V (2*a+7)) (hm : ∀ v∈V, a+7≤(outN D V v).card)
    (hn : V.card+2=(2*a+7)*(a+7)) :
    ∀ v∈V, (ball D V v (a+3)).card=(a+7)*(a+3) ∧
      (ball D V v (a+4)).card=(a+7)*(a+4)-1 ∧
      (reverseBall D V v (a+4)).card=(a+7)*(a+4)-1 := by
  have hp := iterated_profile (e:=6) hf hm (by omega) (by omega) (by omega)
  exact two_balls_boundary_cards hf (by omega : (a+3)+(a+4)≤2*a+7)
    (fun v hv => (hp v hv).2.1)
    (fun v hv => by have := (hp v hv).2.2; omega) (by strip_arith)

theorem cycle_below_two {s q n : ℕ} {D : CH.Digraph}
    (hs : 21≤s) (hq : q=2*s-7) (hn : 0<n) (hc : n+3≤q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨a,rfl⟩ : ∃ a, s=a+7 := ⟨s-7,by omega⟩
  have he : q=2*a+7 := by omega
  rw [he] at hc ⊢
  by_contra hno
  have h := order_to_two (a:=a) (by omega) (qfree_of_noShort hl hno)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv))
    ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at h
  omega

/-- At the surviving order qs-2, every pair in the exact (R+1)-layer
has at least R private labels in the first enlarged ball. -/
theorem second_from_top_separation {a u y : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 21≤a) (hf : QFree D V (2*a+7))
    (hm : ∀ v∈V, a+7≤(outN D V v).card) (hn : V.card+2=(2*a+7)*(a+7))
    (hu : u∈V) (hy : y∈ball D V u (a+4) \ ball D V u (a+3)) :
    a+3≤(ball D V u (a+4) \ ball D V y (a+4)).card := by
  have rig := second_from_top_rigid ha hf hm hn
  have sep := ShenLabelledReach.saturated_separation hf
    (by omega : (a+3)+(a+4)≤2*a+7) (by omega : a+4≤2*a+7)
    (fun v hv => (rig v hv).1.ge) (fun v hv => (rig v hv).2.1.ge)
    (by strip_arith) hu hy
  omega

#print axioms iterated_profile
#print axioms order_to_two
#print axioms second_from_top_rigid
#print axioms cycle_below_two
#print axioms second_from_top_separation
end LeanCH.BR.ShenFifthStrip
