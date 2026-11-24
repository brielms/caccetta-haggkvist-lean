import checkpoints.shen_extension.MarkedRectangleRows
import checkpoints.shen_extension.RegularFirstLayer
import LeanCH.CompromiseTenTwoException

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 BypassRepair CHRuleCatalog CompromiseQuotaTransfer

/-- Consume any conclusion about exactly this labelled finite adjacency.
All induction and witness premises are supplied on that same adjacency. -/
def Recipe {V : Type} [Fintype V] [DecidableEq V] (A : V→V→Prop) [DecidableRel A]
    (d b : ℕ) (P : Prop) : Prop :=
    (∀v,¬A v v) → (∀u v,A u v → ¬A v u) → (∀u v w,A u v → A v w → ¬A w u) →
    LowerTest (CH.CompromiseSeven.outN A) d → LowerTest (CH.CompromiseSeven.inN A) d →
    (∀v,(CH.CompromiseSeven.outN A v).card=d) →
    (∀v,(CH.CompromiseSeven.second A v).card+(CH.CompromiseSeven.inN A v).card≤b) →
    (∃v,(CH.CompromiseSeven.outN A v).card≤(CH.CompromiseSeven.second A v).card) → P

theorem image_heads {D : CH.Digraph} {U : Finset ℕ} (v : ↥U) :
    (CH.CompromiseSeven.outN (adjacency D U) v).image Subtype.val=outN D U v := by
  ext x
  constructor
  · intro p; obtain ⟨a,am,rfl⟩ := mem_image.mp p
    exact mem_outN.mpr ⟨a.property,(by simpa only [CH.CompromiseSeven.mem_outN] using am : adjacency D U v a)⟩
  · intro p; obtain ⟨xm,vx⟩ := mem_outN.mp p
    exact mem_image.mpr ⟨⟨x,xm⟩,(CH.CompromiseSeven.mem_outN _ _ _).mpr vx,rfl⟩

theorem image_shell {D : CH.Digraph} {U : Finset ℕ} (v : ↥U) :
    (CH.CompromiseSeven.second (adjacency D U) v).image Subtype.val =
      ball D U v 2 \ ball D U v 1 := by
  ext z
  constructor
  · intro p
    obtain ⟨a,am,rfl⟩ := mem_image.mp p
    obtain ⟨ne,off,h,vh,ha⟩ := (CH.CompromiseSeven.mem_second _ _ _).mp am
    exact mem_sdiff.mpr ⟨ball_step (ball_of_adj h.property vh) a.property ha,
      fun near=>((mem_ball_one v.property).mp near).elim (fun eq=>ne (Subtype.ext eq))
        (fun arc=>off (mem_outN.mp arc).2)⟩
  · intro zm
    obtain ⟨two,off⟩ := mem_sdiff.mp zm
    let a : ↥U := ⟨z,ball_subset two⟩
    obtain ⟨h,h1,hz⟩ := RegularFirstLayer.first_parent v.property zm
    have hh := ((mem_ball_one v.property).mp (mem_erase.mp h1).2).resolve_left (mem_erase.mp h1).1
    obtain ⟨hm,vh⟩ := mem_outN.mp hh
    refine mem_image.mpr ⟨a,(CH.CompromiseSeven.mem_second _ _ _).mpr ⟨?_,?_,⟨⟨h,hm⟩,vh,hz⟩⟩,rfl⟩
    · intro eq; apply off; change a.val∈ball D U v.val 1; rw [show a.val=v.val from congrArg Subtype.val eq]; exact self_mem_ball v.property
    · intro arc; exact off (ball_of_adj a.property arc)

theorem run {D U q d b} {P : Prop} (rule : Recipe (adjacency D U) d b P)
    (free : QFree D U q) (live : U.Nonempty) (cut : 3≤q) (reg : OutEq d D U)
    (lower : ∀k,0<k → k<d → NoHost q k) (room : U.card≤d+b+1) : P := by
  classical
  let A := adjacency D U
  have hs (v : ↥U) := image_heads (D:=D) v
  have counts (v : ↥U) : (CH.CompromiseSeven.outN A v).card=d := by
    have eq := congrArg card (hs v)
    rwa [card_image_of_injective _ Subtype.val_injective,reg v v.property] at eq
  have score (v : ↥U) : (CH.CompromiseSeven.second A v).card+(CH.CompromiseSeven.inN A v).card≤b := by
    have shell := congrArg card (image_shell (D:=D) v)
    have inn := congrArg card (image_heads (D:=fun x y=>D y x) v)
    have rev : CH.CompromiseSeven.inN A v=CH.CompromiseSeven.outN (adjacency (fun x y=>D y x) U) v := by ext; simp [A,adjacency]
    rw [rev]
    rw [card_image_of_injective _ Subtype.val_injective] at inn
    rw [card_image_of_injective _ Subtype.val_injective,card_sdiff_of_subset (ball_mono_radius (by omega)),
      ReachLedger.ball_one free (by omega) v.property,reg v v.property] at shell
    change _=(inN D U v).card at inn
    change (CH.CompromiseSeven.second A v).card=_ at shell
    have cap := ReachLedger.parent_cap (i:=2) free cut v.property
    have grow := card_le_card (ball_mono_radius (D:=D) (W:=U) (u:=v.val) (by decide : 1≤2))
    rw [ReachLedger.ball_one free (by omega) v.property,reg v v.property] at grow
    omega
  have lo (x : ↥U) : ¬A x x := loopfree free (by omega) x.property
  have di (x y : ↥U) : A x y → ¬A y x := digonfree free (by omega) x.property y.property
  have tri (x y z : ↥U) (xy : A x y) (yz : A y z) (zx : A z x) : False :=
    free x 3 (by decide) cut (.step y.property xy (.step z.property yz (.step x.property zx (.refl _))))
  let : Nonempty ↥U := ⟨⟨live.choose,live.choose_spec⟩⟩
  obtain ⟨y,good⟩ := OAI.SeymourSecondNeighborhood.exists_goodVertex A ⟨lo,fun {x y}=>di x y⟩
  have first : OAI.SeymourSecondNeighborhood.firstNeighbors A y=CH.CompromiseSeven.outN A y := by ext; simp
  have second : OAI.SeymourSecondNeighborhood.secondNeighbors A y=CH.CompromiseSeven.second A y := by ext; simp
  change (OAI.SeymourSecondNeighborhood.firstNeighbors A y).card≤(OAI.SeymourSecondNeighborhood.secondNeighbors A y).card at good
  rw [first,second] at good
  exact rule lo di tri (test_subsets free cut lower) (test_subsets free.reverse cut lower) counts score ⟨y,good⟩

#print axioms image_heads
#print axioms image_shell
#print axioms run
end LeanCH.BR.LabelledCompromiseRecipe
