import checkpoints.shen_extension.UniformShellTurn
namespace LeanCH.BR.UniformProfileCapacity
open Finset BRq2 BRq3 BR45 BRsGen

/-- The rank d is the lower-degree order bound available on the punctured
third ball. The remaining tests are cardinal and radius budgets. -/
def Fits (q r d : ℕ) : Prop :=
  5≤q ∧ 4≤r ∧ r+2≤2*q ∧ (2*r)*(2*r+1)≤r*(2*r+6)+r*12 ∧
  2≤d ∧ d≤5 ∧ d+1≤r ∧ 3*r≤q*d+1 ∧ r≤q+3 ∧
  r≤2*min q (r-(d-2)) ∧ r-1+(d-2)≤2*q
instance (q r d) : Decidable (Fits q r d) := by unfold Fits; infer_instance

/-- Exact inclusive two- and three-ball sizes at every vertex cannot
coexist under these budgets, regardless of the order of the graph. -/
theorem excluded {D V q r d} (free : QFree D V q) (live : V.Nonempty) (reg : OutEq r D V)
    (fit : Fits q r d) (profile : ∀x∈V,(ball D V x 2).card=2*r+1 ∧ (ball D V x 3).card=3*r) : False := by
  classical
  obtain ⟨hq,hr,space,cost,dl,du,rank,small,width,large,retained⟩ := fit
  obtain ⟨u,uv⟩ := live
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have zv : Z⊆V := fun _ h=>N3_subV h
  have cut := free.mono_bound (show 4≤q by omega)
  have one := card_B1 cut uv
  rw [reg u uv] at one
  obtain ⟨two,three⟩ := profile u uv
  have second := @card_B2 D V u
  have third := @card_B3 D V u
  have dy : (N2 D V u).card=r := by omega
  have dz : (N3 D V u).card+1=r := by omega
  have inside : ∀v∈X,(outN D X v).Nonempty := by
    intro s sx
    obtain ⟨twoS,threeS⟩ := profile s (xv sx)
    have no := SinkBankReturn.no_sink free hq reg uv sx dy dz twoS threeS.le
      dl du rank small width large retained
    by_contra none
    exact no (fun a am arc=>none ⟨a,mem_outN.mpr ⟨am,arc⟩⟩)
  obtain ⟨c,cx,y,head,big⟩ := ThinRowTurn.seed free hq uv reg hr space cost dy dz
  have sep : Disjoint (X∪Y) Z := by
    apply disjoint_left.mpr
    intro a am az
    apply (mem_N3.mp az).2
    rcases mem_union.mp am with ax|ay
    · exact ball_mono_radius (by decide : 1≤2) (X_B1 ax)
    · exact (mem_N2.mp ay).1
  have extra := ThinRowTurn.propagate free hq xv yv zv disjXY sep reg (by omega) width dz
    (fun _ xm _ am=>headX cut uv xm (outN_subset am) (mem_outN.mp am).2)
    inside cx head big (fun x xm=>(profile x (xv xm)).1.le)
  have fixed := (profile c (xv cx)).2
  omega

/-- An order supplier from mixed capacity at radii two and three.
Other sources of the uniform profile can use the preceding rule directly. -/
theorem order {D V q r d} (free : QFree D V q) (live : V.Nonempty) (degree : ∀x∈V,r≤(outN D V x).card)
    (room : MixedShellUniform.Room q r) (fit : Fits q r d) : 5*r+1≤V.card := by
  by_contra! small
  obtain ⟨F,sub,reg⟩ := exists_outEq degree
  have ff := qfree_sub sub free
  exact excluded ff live reg fit (MixedShellUniform.uniform ff reg (by omega) room)

attribute [aesop safe forward (immediate := [free,live,reg,fit,profile]) (rule_sets := [CHGraphFamilies])] excluded
attribute [aesop safe forward (immediate := [free,live,degree,room,fit]) (rule_sets := [CHGraphFamilies])] order
#print axioms excluded
#print axioms order
end LeanCH.BR.UniformProfileCapacity
