import checkpoints.shen_extension.PrivateCompletionOrder
import checkpoints.shen_extension.dot_tensor_research.DotFullReturnCut_20261118

namespace LeanCH.BR.Closure.UnitBatch
open BRq2 BRq3 Finset DotFullReturnCut DeleteRepair

structure Unit (q d : ℕ) (U : Finset ℕ) where
  graph : CH.Digraph
  root : ℕ
  live : root ∈ U
  free : QFree graph U q
  short : (outN graph U root).card = d
  full : ∀ x ∈ U, x ≠ root → d+1 ≤ (outN graph U x).card

/-- P is a bank of actual incoming arcs to cut. Every short return from each
new target ends in this bank, measured in the same current graph. -/
structure Batch {q d U} (a : Unit q d U) (P Y : Finset ℕ) : Prop where
  parents : P ⊆ BR45.inN a.graph U a.root
  targets : Y ⊆ U
  live : Y.Nonempty
  fresh : ∀ y ∈ Y, y ≠ a.root ∧ a.graph a.root y ≠ true
  cover : ∀ y ∈ Y, donors a.graph U q a.root y ⊆ P

def edit {q d U} (a : Unit q d U) (P Y : Finset ℕ) :=
  repair (cut a.graph P a.root) {a.root} (fun _ => Y)

def arcs (D : CH.Digraph) (U : Finset ℕ) := ∑ x ∈ U, (outN D U x).card

def tightCut {q d U} (a : Unit q d U) (P : Finset ℕ) :=
  P.filter (fun x => (outN a.graph U x).card = d+1)

theorem batch_safe {q d U} {a : Unit q d U} {P Y} (h : Batch a P Y) (hq : 2 ≤ q) :
    QFree (edit a P Y) U q := by
  apply repair_qfree (qfree_sub (fun _ _ e => cut_sub e) a.free)
  intro x hx y hy z hz m hmq path
  rw [mem_singleton.mp hz] at path
  apply no_short_return_after_cut (D:=a.graph) hq (h.targets hy) (h.fresh y hy).1.symm hmq
  apply walk_sub _ path
  intro i j e
  obtain ⟨old,guard⟩ := cut_edge.mp e
  exact cut_edge.mpr ⟨old,guard.imp (fun notP donor => notP (h.cover y hy donor)) id⟩

/-- This equation retains each row label on both sides of the edit. -/
theorem row_balance {q d U} {a : Unit q d U} {P Y} (h : Batch a P Y) (hq : 2 ≤ q)
    (x : ℕ) :
    (outN (edit a P Y) U x).card + (if x ∈ P then 1 else 0) =
    (outN a.graph U x).card + (if x = a.root then Y.card else 0) := by
  classical
  by_cases eq : x = a.root
  · subst x
    have np : a.root ∉ P := fun hp => loopfree a.free (by omega) a.live (BR45.mem_inN.mp (h.parents hp)).2
    have row : outN (edit a P Y) U a.root = outN a.graph U a.root ∪ Y := by
      ext z
      simp only [edit,mem_outN,repair,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,
        mem_singleton_self,true_and,cut_edge,np,not_false_eq_true,true_or,and_true,mem_union]
      grind [h.targets]
    have dis : Disjoint (outN a.graph U a.root) Y := disjoint_left.mpr
      (fun z hz hy => (h.fresh z hy).2 (mem_outN.mp hz).2)
    simp [row,card_union_of_disjoint dis,np]
  have row : outN (edit a P Y) U x = outN (cut a.graph P a.root) U x := by
    ext z
    simp [edit,mem_outN,repair,eq]
  by_cases hit : x ∈ P
  · have old : a.root ∈ outN a.graph U x := mem_outN.mpr ⟨a.live,(BR45.mem_inN.mp (h.parents hit)).2⟩
    simp [row,cut_donor_row hit,hit,eq,card_erase_add_one old]
  · simp [row,cut_outside_row hit,hit,eq]

theorem arc_balance {q d U} {a : Unit q d U} {P Y} (h : Batch a P Y) (hq : 2 ≤ q) :
    arcs (edit a P Y) U + P.card = arcs a.graph U + Y.card := by
  classical
  have pay := sum_congr (s₁:=U) rfl (fun x _ => row_balance h hq x)
  rw [sum_add_distrib,sum_add_distrib] at pay
  have sub : P ⊆ U := h.parents.trans (filter_subset _ _)
  have cutters : U.filter (fun x => x ∈ P) = P := by ext x; simp; exact fun hx => sub hx
  have debt : (∑ x ∈ U, if x ∈ P then 1 else (0:ℕ)) = P.card := by rw [← card_filter,cutters]
  simp only [debt,sum_ite_eq',a.live,ite_true] at pay
  exact pay

def Step {q d U} (a b : Unit q d U) := ∃ P Y, Batch a P Y ∧ b.graph = edit a P Y

/-- A nonempty install must hit a parent whose original row was exactly full.
If it hits just one, the result is an actual unit state with that parent short. -/
theorem next {q d U} (O : Origin q (d+1)) (proper : U.card < O.V.card)
    {a : Unit q d U} {P Y} (h : Batch a P Y) (hq : 2 ≤ q) (one : (tightCut a P).card ≤ 1) :
    (tightCut a P).card = 1 ∧ ∃ b : Unit q d U, Step a b ∧ b.graph = edit a P Y := by
  classical
  let E := edit a P Y
  have safe := batch_safe h hq
  have rows (x) (hx : x ∈ U) (notTight : x ∉ tightCut a P) : d+1 ≤ (outN E U x).card := by
    have bal := row_balance h hq x
    change (outN E U x).card + _ = _ at bal
    by_cases root : x = a.root
    · subst x
      have np : a.root ∉ P := fun hit => loopfree a.free (by omega) a.live (BR45.mem_inN.mp (h.parents hit)).2
      simp only [np,ite_false,add_zero,ite_true,a.short] at bal
      have := card_pos.mpr h.live
      omega
    have full := a.full x hx root
    by_cases xp : x ∈ P
    · have diff : (outN a.graph U x).card ≠ d+1 := fun eq => notTight (mem_filter.mpr ⟨xp,eq⟩)
      simp only [xp,ite_true,root,ite_false,add_zero] at bal
      omega
    · simp only [xp,root,ite_false,add_zero] at bal
      exact bal.symm ▸ full
  have existsT : (tightCut a P).Nonempty := by
    by_contra empty
    have paid := O.least E U safe (fun x hx => rows x hx (fun h => empty ⟨x,h⟩)) ⟨a.root,a.live⟩
    omega
  have count : (tightCut a P).card = 1 := by have := card_pos.mpr existsT; omega
  obtain ⟨t,ts⟩ := card_eq_one.mp count
  have tm : t ∈ tightCut a P := ts ▸ mem_singleton_self t
  obtain ⟨tp,tight⟩ := mem_filter.mp tm
  have tU := (BR45.mem_inN.mp (h.parents tp)).1
  have ne : t ≠ a.root := fun eq => loopfree a.free (by omega) tU (eq ▸ (BR45.mem_inN.mp (h.parents tp)).2)
  have bal := row_balance h hq t
  simp only [tp,ne,ite_true,ite_false,add_zero,tight] at bal
  let b : Unit q d U := ⟨E,t,tU,safe,by change (outN (edit a P Y) U t).card = d; omega,
    fun x hx n => rows x hx (fun mem => n (mem_singleton.mp (ts ▸ mem)))⟩
  exact ⟨count,b,⟨P,Y,h,rfl⟩,rfl⟩

/-- Maximize actual arcs over the reachable family, including its neutral
loops. Every jointly repairable target set then costs at least as many cuts
when at most one cut parent is tight. -/
theorem component_cut_bound {q d U} (O : Origin q (d+1)) (proper : U.card < O.V.card)
    (hq : 2 ≤ q) (start : Unit q d U) :
    ∃ a, Reach Step start a ∧
      (∀ b, Reach Step a b → arcs b.graph U ≤ arcs a.graph U) ∧
      ∀ P Y, Batch a P Y → (tightCut a P).card ≤ 1 →
        (tightCut a P).card = 1 ∧ Y.card ≤ P.card := by
  classical
  let score (k : ℕ) := ∃ a, Reach Step start a ∧ arcs a.graph U = k
  have cap (a : Unit q d U) : arcs a.graph U ≤ U.card * U.card := by
    have le := sum_le_sum (s:=U) (f:=fun x => (outN a.graph U x).card) (g:=fun _ => U.card)
      (fun _ _ => card_le_card outN_subset)
    simpa [arcs] using le
  have base : score (arcs start.graph U) := ⟨start,.refl,rfl⟩
  obtain ⟨a,path,top⟩ := Nat.findGreatest_spec (cap start) base
  have maximal (b) (pb : Reach Step a b) : arcs b.graph U ≤ arcs a.graph U := by
    rw [top]
    exact Nat.le_findGreatest (cap b) (show score (arcs b.graph U) from ⟨b,path.trans pb,rfl⟩)
  refine ⟨a,path,maximal,?_⟩
  intro P Y h one
  obtain ⟨tight,b,step,output⟩ := next O proper h hq one
  have topB := maximal b (.single step)
  rw [output] at topB
  have balance := arc_balance h hq
  exact ⟨tight,by omega⟩

#print axioms batch_safe
#print axioms row_balance
#print axioms arc_balance
#print axioms next
#print axioms component_cut_bound

/-- Neutral and increasing edits on actual unit graphs. On a fixed carrier
the number of absent arcs bounds the number of strict increases. -/
def Extension {q d U} (a b : Unit q d U) := a.root = b.root ∧
  ∀ x ∈ U, ∀ y ∈ U, a.graph x y = true → b.graph x y = true

def Ascent {q d U} (a b : Unit q d U) := (Step a b ∨ Extension a b) ∧ arcs a.graph U ≤ arcs b.graph U

def CutBound {q d U} (a : Unit q d U) := ∀ P Y, Batch a P Y →
  (tightCut a P).card ≤ 1 → (tightCut a P).card = 1 ∧ Y.card ≤ P.card

/-- The same obstruction holds after every further neutral detour, however
long. A loop can be traversed before taking the strict exit. -/
theorem plateau {q d U} (O : Origin q (d+1)) (proper : U.card < O.V.card)
    (hq : 2 ≤ q) (start : Unit q d U) :
    ∃ a, Reach Ascent start a ∧ ∀ b, Reach Ascent a b →
      arcs b.graph U = arcs a.graph U ∧ CutBound b := by
  classical
  let score (k : ℕ) := ∃ a, Reach Ascent start a ∧ arcs a.graph U = k
  have cap (a : Unit q d U) : arcs a.graph U ≤ U.card * U.card := by
    have le := sum_le_sum (s:=U) (f:=fun x => (outN a.graph U x).card) (g:=fun _ => U.card)
      (fun _ _ => card_le_card outN_subset)
    simpa [arcs] using le
  have base : score (arcs start.graph U) := ⟨start,.refl,rfl⟩
  obtain ⟨a,path,top⟩ := Nat.findGreatest_spec (cap start) base
  have ceiling (b) (pb : Reach Ascent a b) : arcs b.graph U ≤ arcs a.graph U := by
    rw [top]
    exact Nat.le_findGreatest (cap b) (show score (arcs b.graph U) from ⟨b,path.trans pb,rfl⟩)
  refine ⟨a,path,?_⟩
  intro b pb
  have ge := invariant_of_reach (inv:=fun z => arcs a.graph U ≤ arcs z.graph U)
    (fun _ _ prior (edge : Ascent _ _) => prior.trans edge.2) (Nat.le_refl _) pb
  have eq := le_antisymm (ceiling b pb) ge
  refine ⟨eq,?_⟩
  intro P Y h one
  obtain ⟨tight,c,step,editEq⟩ := next O proper h hq one
  refine ⟨tight,?_⟩
  by_contra! more
  have balance := arc_balance h hq
  rw [← editEq] at balance
  have improve : Ascent b c := ⟨Or.inl step,by omega⟩
  have bound := ceiling c (pb.tail improve)
  omega

/-- A falsifiable certificate against a whole unit-state branch. It suffices
to exhibit a profitable batch after some neutral or increasing itinerary
from every possible state, including states with surplus rows. -/
theorem exclude_by_escape {q d U} (O : Origin q (d+1)) (proper : U.card < O.V.card)
    (hq : 2 ≤ q) (start : Unit q d U)
    (escape : ∀ a, Reach Ascent start a → ∃ b, Reach Ascent a b ∧
      ∃ P Y, Batch b P Y ∧ (tightCut b P).card ≤ 1 ∧ P.card < Y.card) : False := by
  obtain ⟨a,path,stop⟩ := plateau O proper hq start
  obtain ⟨b,pb,P,Y,h,one,gain⟩ := escape a path
  exact (Nat.not_lt_of_ge ((stop b pb).2 P Y h one).2) gain

#print axioms plateau
#print axioms exclude_by_escape

theorem saturate {q d U} (O : Origin q (d+1)) (proper : U.card < O.V.card)
    (a : Unit q d U) : ∃ b, Ascent a b ∧ BRsub.Sat q b.graph U := by
  obtain ⟨E,keep,safe,maximal⟩ := BRsub.exists_satQ a.free
  have rows (x) (hx : x ∈ U) : (outN a.graph U x).card ≤ (outN E U x).card := by
    apply card_le_card
    intro y hy
    obtain ⟨yu,edge⟩ := mem_outN.mp hy
    exact mem_outN.mpr ⟨yu,keep x hx y yu edge⟩
  have full (x) (hx : x ∈ U) (ne : x ≠ a.root) := (a.full x hx ne).trans (rows x hx)
  have short : (outN E U a.root).card = d := by
    have lower := rows a.root a.live
    rw [a.short] at lower
    by_contra diff
    have paid := O.least E U safe (fun x hx => by
      by_cases eq : x = a.root
      · subst x; omega
      · exact full x hx eq) ⟨a.root,a.live⟩
    omega
  exact ⟨⟨E,a.root,a.live,safe,short,full⟩,⟨Or.inr ⟨rfl,keep⟩,sum_le_sum rows⟩,maximal⟩

/-- Saturation and the obstruction to all further profitable itineraries
hold together at one reachable state. -/
theorem saturated_plateau {q d U} (O : Origin q (d+1)) (proper : U.card < O.V.card)
    (hq : 2 ≤ q) (start : Unit q d U) :
    ∃ a, Reach Ascent start a ∧ BRsub.Sat q a.graph U ∧ ∀ b, Reach Ascent a b →
      arcs b.graph U = arcs a.graph U ∧ CutBound b := by
  obtain ⟨m,path,stop⟩ := plateau O proper hq start
  obtain ⟨a,step,sat⟩ := saturate O proper m
  have link : Reach Ascent m a := .single step
  exact ⟨a,path.tail step,sat,fun b pb =>
    ⟨(stop b (link.trans pb)).1.trans (stop a link).1.symm,(stop b (link.trans pb)).2⟩⟩

/-- Direct interface with the recursive capstone's proper one-unit state. -/
theorem native_saturated_plateau {q d} (O : Origin q (d+1)) {st : State} (valid : Valid O st)
    (proper : st.U.card < O.V.card) (hq : 2 ≤ q) (unit : DeficitLevels.total (d+1) st.H st.U = 1) :
    ∃ start a : Unit q d st.U, start.graph = st.H ∧ Reach Ascent start a ∧
      BRsub.Sat q a.graph st.U ∧ ∀ b, Reach Ascent a b →
      arcs b.graph st.U = arcs a.graph st.U ∧ CutBound b := by
  obtain ⟨u,hu,short,full⟩ := PrivateCompletion.unit_profile unit
  let start : Unit q d st.U := ⟨st.H,u,hu,valid.2.2,by omega,full⟩
  obtain ⟨a,path,sat,stop⟩ := saturated_plateau O proper hq start
  exact ⟨start,a,rfl,path,sat,stop⟩

#print axioms saturate
#print axioms saturated_plateau
#print axioms native_saturated_plateau
end LeanCH.BR.Closure.UnitBatch
