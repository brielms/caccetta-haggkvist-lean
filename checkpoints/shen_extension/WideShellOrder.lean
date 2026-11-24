import checkpoints.shen_extension.WidePrefixCapacity
import checkpoints.shen_extension.OneOmissionExpansion
import checkpoints.shen_extension.RootLayerTransit
namespace LeanCH.BR.WideShellOrder
open Finset BRq2 BRq3 BR45 BRsGen WidePrefixCapacity

def Capacity (q r s : ℕ) : Prop :=
  4≤r ∧ r+2≤q ∧ 3≤s ∧ s≤r ∧ 2*s≤q ∧ 2*r+s≤2*q+3 ∧
  Room q r s (2*r) r 0 (3*r+2) (4*r) ∧ Room q r s (3*r) (2*r) r (4*r+1) (5*r-1)
instance (q r s) : Decidable (Capacity q r s) := by unfold Capacity; infer_instance

/-- The retained score forces small third and fourth balls together.
Only two nonconstant layer profiles survive the arithmetic. A shifted
one-omission window excludes each; the equal-layer rule excludes the
remaining profile at arbitrary depth. -/
theorem fifth {D V q r s u} (free : QFree D V q) (root : u∈V) (reg : OutEq r D V)
    (capacity : Capacity q r s) : 5*r+1≤(ball D V u 5).card := by
  obtain ⟨hr,time,sr,rs,radii,room,middle,outer⟩ := capacity
  have deg x (xm : x∈V) := (reg x xm).ge
  have sec x (xm : x∈V) := card_ball_two_ge_twice (by omega : 2≤r)
    (free.mono_bound (by omega)) deg xm
  have three x (xm : x∈V) := third_floor free xm deg hr time
  have b1 := card_B1 (free.mono_bound (by omega : 4≤q)) root
  rw [reg u root] at b1
  have b0 : (ball D V u 0).card=1 := by
    have sub : ball D V u 0⊆{u} := fun _ h=>mem_singleton.mpr (eq_of_mem_ball_zero h)
    have le := card_le_card sub
    rw [card_singleton] at le
    have pos := card_pos.mpr (show (ball D V u 0).Nonempty from ⟨u,self_mem_ball root⟩)
    omega
  have b2 := sec u root
  have b3 := three u root
  have count2 := @card_B2 D V u
  have count3 := @card_B3 D V u
  have diff (j : ℕ) := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (show j≤j+1 by omega))
  by_contra! small
  have hi4 := squeeze (k:=1) free root deg (by omega) radii rs sr room sec three
    (show (ball D V u 5).card≤5*r-1+1 by omega) b3 b2 b1.ge (by omega) outer
  change (ball D V u 4).card≤4*r+1 at hi4
  have hi3 := squeeze (k:=0) free root deg (by omega) radii rs sr room sec three hi4
    b2 b1.ge b0.ge (by omega) middle
  change (ball D V u 3).card≤3*r+2 at hi3
  have grow := short_third free root deg hr time hi3
  have g4 := diff 3
  have g5 := diff 4
  change (ball D V u 4\ball D V u 3).card+(ball D V u 3).card=(ball D V u 4).card at g4
  change (ball D V u 5\ball D V u 4).card+(ball D V u 4).card=(ball D V u 5).card at g5
  have ylow : r≤(N2 D V u).card := by omega
  by_cases ybig : r<(N2 D V u).card
  · have w := OneOmissionSinkBank.fourth_layer free root deg hr time (reg u root) (by omega) (by omega)
    omega
  by_cases zbig : r<(N3 D V u).card
  · have w := SinkReturnAncestors.shifted_layers free root (by omega) deg (reg u root)
      time (by omega) (by omega)
    omega
  have e1 := diff 0
  change (ball D V u 1\ball D V u 0).card+(ball D V u 0).card=(ball D V u 1).card at e1
  have initial (i : ℕ) (h : i<3) : (ball D V u (i+1)\ball D V u i).card=r := by
    interval_cases i
    · change (ball D V u 1\ball D V u 0).card=r
      omega
    · change (N2 D V u).card=r; omega
    · change (N3 D V u).card=r; omega
  have w := EqualLayerTransit.next_layer free root deg (by omega) (by omega)
    (by omega : r/2+3≤q) (by decide) initial
  change r≤(ball D V u 4\ball D V u 3).card at w
  have exit := EqualLayerTransit.next_layer free root deg (by omega) (by omega)
    (by omega : r/2+4≤q) (by decide) (fun i hi=>by
      by_cases old : i<3
      · exact initial i old
      · have eq : i=3 := by omega
        subst i
        change (ball D V u 4\ball D V u 3).card=r
        omega)
  change r≤(ball D V u 5\ball D V u 4).card at exit
  omega

theorem order {D V q r s} (free : QFree D V q) (live : V.Nonempty)
    (degree : ∀x∈V,r≤(outN D V x).card) (radii : 5+5≤q) (room : Capacity q r s) :
    10*r+1≤V.card := by
  obtain ⟨F,sub,reg⟩ := exists_outEq degree
  have ff := qfree_sub sub free
  have ball5 x (xm : x∈V) := fifth ff xm reg room
  have fit := card_ge_of_two_balls (i:=5) (j:=5) ff radii ball5 ball5 live
  omega

attribute [aesop safe forward (immediate := [free,root,reg,capacity]) (rule_sets := [CHGraphFamilies])] fifth
attribute [aesop safe forward (immediate := [free,live,degree,radii,room]) (rule_sets := [CHGraphFamilies])] order
#print axioms fifth
#print axioms order
end LeanCH.BR.WideShellOrder
