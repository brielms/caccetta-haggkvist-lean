import checkpoints.shen_extension.CycleRowMultiplicity
import checkpoints.shen_extension.EqualShellEscape

namespace LeanCH.BR.ShellCycleSupply
open Finset BRq2 BRq3 BR45 BRsGen OneSpareGrowth BankReachTransfer ExteriorPacking

theorem rooted_on_small_set {D V X q x} (free : QFree D V q) (hq : 1≤q) (sub : X⊆V)
    (small : X.card≤q+1) (internal : ∀a∈X,1≤(outN D X a).card) (xm : x∈X) :
    Rooted D V x X := by
  classical
  have fx := free.mono_set sub
  refine ⟨sub,xm,EqualShellEscape.one_head fx hq small internal,?_⟩
  let P := X.filter (fun y=>∃k,Walk D X x y k)
  have px : x∈P := mem_filter.mpr ⟨xm,0,.refl x⟩
  intro y ym
  by_contra no
  have cap : P⊆X.erase y := by
    intro a am
    exact mem_erase.mpr ⟨fun eq=>no (eq ▸ (mem_filter.mp am).2),(mem_filter.mp am).1⟩
  have size := (card_le_card cap).trans_eq (card_erase_of_mem ym)
  obtain ⟨a,am,sink⟩ := exists_sink (T:=P) (fx.mono_set (show P⊆X from filter_subset _ _)) ⟨x,px⟩ (show P.card≤q by omega)
  obtain ⟨b,bm⟩ := card_pos.mp (internal a (mem_filter.mp am).1)
  obtain ⟨k,way⟩ := (mem_filter.mp am).2
  exact sink b (mem_filter.mpr ⟨outN_subset bm,k+1,way.snoc (outN_subset bm) (mem_outN.mp bm).2⟩) (mem_outN.mp bm).2

theorem lift_ball {D V X w j} (sub : X⊆V) : ball D X w j⊆ball D V w j := by
  intro y ym
  obtain ⟨yx,l,fit,path⟩ := mem_ball.mp ym
  exact mem_ball.mpr ⟨sub yx,l,fit,path.mono sub⟩

/-- Identify the exterior by its actual heads, with no supply assumption. -/
theorem head_exterior {D V u q} (free : QFree D V q) (hq : 2≤q) (uv : u∈V) :
    exterior D V (outN D V u)=N2 D V u := by
  ext y
  constructor
  · intro ym
    obtain ⟨access,off⟩ := mem_sdiff.mp ym
    obtain ⟨x,xm,yx⟩ := mem_biUnion.mp access
    refine mem_N2.mpr ⟨ball_step (X_B1 xm) (outN_subset yx) (mem_outN.mp yx).2,?_⟩
    intro early
    rcases (mem_ball_one uv).mp early with yu|edge
    · subst y
      exact free u 2 (by decide) hq (.step (outN_subset xm) (mem_outN.mp xm).2
        (.step uv (mem_outN.mp yx).2 (.refl u)))
    · exact off edge
  · intro ym
    obtain ⟨x,xm,arc⟩ := ball_succ_pred uv (mem_N2.mp ym).1 (mem_N2.mp ym).2
    have head := ((mem_ball_one uv).mp xm).resolve_left (fun xu=>by
      subst x
      exact (mem_N2.mp ym).2 (ball_of_adj (N2_subV ym) arc))
    exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨x,head,mem_outN.mpr ⟨N2_subV ym,arc⟩⟩,
      fun edge=>(mem_N2.mp ym).2 (X_B1 edge)⟩

/-- When the second shell is one smaller than the degree, each first
row sees it in one step and retains its entire internal ball as well. -/
theorem narrow_supply {D V q r u} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (uv : u∈V) (fit : r≤q+1) (narrow : (N2 D V u).card+1=r) :
    ∀w∈outN D V u, Rooted D V w (outN D V u) ∧
      ∀k,k+2≤q → k+2+((ball D V u (k+2)).card-(ball D V u 1).card)≤(ball D V w (k+1)).card := by
  let X := outN D V u
  have xv : X⊆V := outN_subset
  have pos x (xm : x∈X) : 1≤(outN D X x).card := internal_positive free hq uv reg narrow xm
  intro w wm
  have cr := rooted_on_small_set free (by omega) xv ((reg u uv).le.trans fit) pos wm
  refine ⟨cr,?_⟩
  have toY := sends_layer free hq uv reg narrow wm (cr.one w wm)
  intro k kq
  have out := count_with_prefix (j:=1) (d:=1) (k:=k) uv
    (fun a (am : a∈ball D X w (1+k))=>X_B1 (ball_subset am)) (lift_ball xv)
    (fun y (ym : y∈N2 D V u)=>ball_of_adj (N2_subV ym) (toY y ym))
  have count := ball_one_growth (free.mono_set xv) pos wm (k+1) (by omega)
  rw [show 1+1+k=k+2 by omega,show 1+k=k+1 by omega] at out
  omega

#print axioms rooted_on_small_set
#print axioms head_exterior
#print axioms narrow_supply
end LeanCH.BR.ShellCycleSupply
