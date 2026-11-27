import checkpoints.shen_extension.FourLayerReversal
import checkpoints.shen_extension.LabelledTrianglePatch

/-! With four targets, the edit absorbs one specified exterior payer.
A further obstruction must be a different vertex in a reversal on one
of the two overlapping triples. -/
namespace LeanCH.BR.FourTargetPayment
open Finset BRq2 BRq3 BR45 JointFreeTargets TripleBank TwoRowShared
open LabelledTrianglePatch (chargesOf)

inductive Role | a | b | c | x | j | u | z | w | f₄ | payer
  deriving DecidableEq
open Role
instance : Fintype Role := ⟨{a,b,c,x,j,u,z,w,f₄,payer},fun i => by cases i <;> simp⟩
local instance (p : Role → Prop) [DecidablePred p] : Decidable (∀ i, p i) :=
  Fintype.decidableForallFintype

def shortRows : Finset Role := {a,b,c}
def middles : Finset Role := {x,j}
def targets : Finset Role := {u,z,w,f₄}
def upper : Finset Role := {u,z}
def lower : Finset Role := {w,f₄}

def gains : Role → Finset Role
  | .a => {z} | .b | .c => {u} | .x => {w,f₄} | _ => ∅
def cuts : Role → Finset Role
  | .w | .f₄ | .payer => {x} | .u => {j} | .z => {payer}
  | .j => {a} | .x => {a,b,c} | _ => ∅

def allowed (i k : Role) : Bool := decide (i≠k ∧
  ¬(i∈shortRows ∧ k∈middles) ∧ ¬(i∈middles ∧ k∈targets) ∧
  ¬(i∈shortRows ∧ k∈targets) ∧ ¬(i∈targets ∧ k∈shortRows) ∧
  ¬(i=j ∧ k=x) ∧ ¬(i∈lower ∧ k∈upper) ∧ ¬(i=payer ∧ (k=b ∨ k=c)))

private theorem shape :
    (∀ i, ∀ h ∈ gains i, h ≠ i ∧ allowed i h = false ∧
      (allowed h i = false ∨ i ∈ cuts h) ∧ gains h = ∅) ∧
    (∀ i, ∀ h ∈ gains i, ∀ m, allowed h m=true → allowed m i=true →
      m∈cuts h ∨ i∈cuts m) ∧
    (∀ i, if i∈shortRows then (cuts i).card+1≤(gains i).card
      else (cuts i).card≤1+(gains i).card) := by decide

/-- The specified payer is included among the ten vertices whose cost has
already been paid. Each other vertex pays for its distinct remaining legs. -/
theorem repair {D : CH.Digraph} {U : Finset ℕ} {t : ℕ} (v : Role ↪ ℕ)
    (free : QFree D U 3) (inside : ∀ i, v i∈U)
    (internal : ∀ i k, D (v i) (v k)=true → allowed i k=true)
    (need : ∀ i∈shortRows, t≤(outN D U (v i)).card+1)
    (spare : ∀ i∉shortRows, t+1≤(outN D U (v i)).card)
    (pay : ∀ e∈U, (∀ i, e≠v i) → t+(chargesOf gains D v e).card ≤ (outN D U e).card) :
    ∃ G : CH.Digraph, QFree G U 3 ∧ (∀ i, ∀ h∈gains i, G (v i) (v h)=true) ∧
      ∀ e∈U, t≤(outN G U e).card :=
  LabelledTrianglePatch.repair_of_shape v shortRows gains cuts allowed shape.1 shape.2.1 shape.2.2
    free inside internal need spare pay

private theorem forbidden : ∀ i k, allowed i k=false →
    i=k ∨ (i∈shortRows ∧ k∈middles) ∨ (i∈middles ∧ k∈targets) ∨
    (i∈shortRows ∧ k∈targets) ∨ (i∈targets ∧ k∈shortRows) ∨ (i=j ∧ k=x) ∨
    (i∈lower ∧ k∈upper) ∨ (i=payer ∧ (k=b ∨ k=c)) := by decide

theorem different_payer {D : CH.Digraph} {V : Finset ℕ} {t p y : ℕ} (v : Role ↪ ℕ)
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t)
    (live : ∀ i, v i ∈ V) (pv : p ∈ V) (yv : y ∈ V) (py : p ≠ y)
    (hit : ∀ i ∈ shortRows, D (v i) p = true ∧ D (v i) y = true)
    (heads : ∀ k ∈ targets, D p (v k) = true ∧ D y (v k) = true)
    (back : ∀ k ∈ targets, ∀ i ∈ middles, D (v k) (v i) = true)
    (legs : ∀ i ∈ middles, ∀ k ∈ shortRows, D (v i) (v k) = true)
    (orderX : D (v j) (v x) ≠ true) (split : ∀ i∈lower, ∀ k∈upper, D (v i) (v k) ≠ true)
    (payerNeutral : FourLayerReversal.neutral D p y (v payer))
    (retained : v payer≠p ∧ v payer≠y)
    (payerRows : D (v payer) (v b)≠true ∧ D (v payer) (v c)≠true)
    (others : ∀ r ∈ inN D V p ∩ inN D V y, r ∉ shortRows.map v →
      ∃ l, FreeTarget D V r l ∧ l ∉ inN D V p ∩ inN D V y) :
    ∃ m ∈ V, (∀ i, m ≠ v i) ∧ FourLayerReversal.neutral D p y m ∧
      2 ≤ (chargesOf gains D v m).card := by
  classical
  let B : Finset ℕ := {p,y}
  let U := V \ B
  let S := inN D V p ∩ inN D V y
  let R := S \ shortRows.map v
  have bv : B ⊆ V := insert_subset pv (singleton_subset_iff.mpr yv)
  have tri {l m n} (lv : l∈V) (mv : m∈V) (nv : n∈V)
      (lm : D l m=true) (mn : D m n=true) : D n l ≠ true := fun nl =>
    free l 3 (by decide) (by decide) (.step mv lm (.step nv mn (.step lv nl (.refl _))))
  have su {r} (rs : r∈S) : r∈U := by
    obtain ⟨rp,ry⟩ := mem_inter.mp rs
    obtain ⟨rv,rp⟩ := mem_inN.mp rp
    have np : r≠p := fun e => loopfree free (by decide) pv (e ▸ rp)
    have ny : r≠y := fun e => loopfree free (by decide) yv (e ▸ (mem_inN.mp ry).2)
    exact mem_sdiff.mpr ⟨rv,by simp [B,np,ny]⟩
  have short {i} (im : i∈shortRows) : v i ∈ S :=
    mem_inter.mpr ⟨mem_inN.mpr ⟨live i,(hit i im).1⟩,mem_inN.mpr ⟨live i,(hit i im).2⟩⟩
  have head {k} (km : k∈targets) : v k ∈ U ∧ v k ∉ S ∧ ∀ h ∈ B, D h (v k) = true := by
    obtain ⟨pk,yk⟩ := heads k km
    have np : v k ≠ p := fun e => loopfree free (by decide) pv (e ▸ pk)
    have ny : v k ≠ y := fun e => loopfree free (by decide) yv (e ▸ yk)
    refine ⟨mem_sdiff.mpr ⟨live k,by simp [B,np,ny]⟩,
      fun ks => digonfree free (by decide) pv (live k) pk (mem_inN.mp (mem_inter.mp ks).1).2,?_⟩
    intro h hb
    rcases mem_insert.mp hb with rfl | hb
    · exact pk
    · exact mem_singleton.mp hb ▸ yk
  have bankMiss {k m} (km : k∈targets) (mv : m∈V) (arc : D (v k) m=true) :
      D m p ≠ true ∧ D m y ≠ true :=
    ⟨tri pv (live k) mv (heads k km).1 arc,tri yv (live k) mv (heads k km).2 arc⟩
  have middle {i} (im : i∈middles) : v i ∈ U ∧ v i ∉ S := by
    have ua : u ∈ targets := by decide
    have ui := back u ua i im
    obtain ⟨pu,yu⟩ := heads u ua
    have np : v i ≠ p := fun e => digonfree free (by decide) pv (live u) pu (e ▸ ui)
    have ny : v i ≠ y := fun e => digonfree free (by decide) yv (live u) yu (e ▸ ui)
    exact ⟨mem_sdiff.mpr ⟨live i,by simp [B,np,ny]⟩,
      fun is' => (bankMiss ua (live i) ui).1 (mem_inN.mp (mem_inter.mp is').1).2⟩
  have payerU : v payer∈U := mem_sdiff.mpr ⟨live _,by simp [B,retained.1,retained.2]⟩
  have payerOff : v payer∉S := fun hh => payerNeutral.1 (mem_inN.mp (mem_inter.mp hh).1).2
  have payerRich : t+1≤(outN D U (v payer)).card := by
    have eq : outN D U (v payer) = outN D V (v payer) := by
      ext h
      simp only [mem_outN,mem_sdiff, B,U]
      constructor
      · intro h
        exact ⟨h.1.1,h.2⟩
      · rintro ⟨hv,ed⟩
        refine ⟨⟨hv,?_⟩,ed⟩
        simp only [mem_insert,mem_singleton]
        rintro (rfl | rfl)
        · exact payerNeutral.1 ed
        · exact payerNeutral.2.2.1 ed
    rw [eq,reg _ (live _)]
  have parts : ∀ i, i∈shortRows ∨ i∈middles ∨ i∈targets ∨ i=payer := by decide
  have core (i) : v i∈U ∧ v i∉R := by
    rcases parts i with si | mi | hi | rfl
    · exact ⟨su (short si),fun r => (mem_sdiff.mp r).2 (mem_map.mpr ⟨i,si,rfl⟩)⟩
    · exact ⟨(middle mi).1,fun r => (middle mi).2 (mem_sdiff.mp r).1⟩
    · exact ⟨(head hi).1,fun r => (head hi).2.1 (mem_sdiff.mp r).1⟩
    · exact ⟨payerU,fun r => payerOff (mem_sdiff.mp r).1⟩
  have internal (i k) (ik : D (v i) (v k) = true) : allowed i k = true := by
    by_contra! off
    rcases forbidden i k (by simpa using off) with rfl | ⟨is',km⟩ | ⟨im,kh⟩ | ⟨is',kh⟩ |
        ⟨ih,ks⟩ | ⟨rfl,rfl⟩ | ⟨ih,kh⟩ | ⟨rfl,kr⟩
    · exact loopfree free (by decide) (live i) ik
    · exact digonfree free (by decide) (live i) (live k) ik (legs k km i is')
    · exact digonfree free (by decide) (live i) (live k) ik (back k kh i im)
    · exact tri (live k) (live x) (live i) (back k kh x (by decide)) (legs x (by decide) i is') ik
    · exact tri (live k) pv (live i) (hit k ks).1 (heads i ih).1 ik
    · exact orderX ik
    · exact split i ih k kh ik
    · rcases kr with rfl | rfl
      · exact payerRows.1 ik
      · exact payerRows.2 ik
  have exits (r) (rr : r∈R) := others r (mem_sdiff.mp rr).1 (mem_sdiff.mp rr).2
  let f (r : ℕ) := if rr : r∈R then (exits r rr).choose else p
  have chosen {r} (rr : r∈R) : FreeTarget D V r (f r) ∧ f r∉S := by
    simpa only [f,dite_eq_left rr] using (exits r rr).choose_spec
  let E := addTargets D R f
  obtain ⟨safe,deg⟩ := free_repair (f:=f) (free.mono_set (show U⊆V from sdiff_subset))
    (fun r rr => ⟨retained_target (mem_sdiff.mp rr).1 (chosen rr).1,
      fun e => (chosen rr).2 (mem_sdiff.mp e).1⟩)
  have unchanged {m n} (mr : m∉R) : E m n = true ↔ D m n = true := by simp [E,addTargets,mr]
  have gain (m) : (outN D U m).card ≤ (outN E U m).card := by rw [deg]; omega
  have base {m} (mu : m∈U) : t ≤ (outN D U m).card+1 := by
    simpa [U,B] using retained_floor reg (mem_sdiff.mp mu).1 py
  have rich {k} (kh : k∈targets) := bank_rich free reg bv (head kh).1 (head kh).2.2
  have floor {m} (mu : m∈U) (ext : ∀ i, m ≠ v i) : t ≤ (outN E U m).card := by
    by_cases ms : m∈S
    · have mr : m∈R := mem_sdiff.mpr ⟨ms,fun e => by
        obtain ⟨i,_,eq⟩ := mem_map.mp e; exact ext i eq.symm⟩
      change t ≤ (outN (addTargets D R f) U m).card
      rw [deg,ite_eq_left mr]
      exact base mu
    · apply le_trans _ (gain m)
      by_contra! low
      have sh : m∈ U.filter (fun k => (outN D U k).card < t+1-1) :=
        mem_filter.mpr ⟨mu,by simpa using low⟩
      rw [BypassBankReplay.short_rows_eq_jointParents free (by decide) reg pv yv py (by omega)] at sh
      exact ms (mem_inter.mpr ⟨(mem_inN.mp sh).1,mem_inN.mpr ⟨(mem_sdiff.mp mu).1,(mem_inN.mp sh).2⟩⟩)
  have menus : ∀ i, ∀ k ∈ gains i, k∈targets := by decide
  by_contra absent
  have pay (m) (mu : m∈U) (ext : ∀ i, m ≠ v i) :
      t+(chargesOf gains E v m).card ≤ (outN E U m).card := by
    by_cases empty : chargesOf gains E v m = ∅
    · simpa [empty] using floor mu ext
    obtain ⟨i,im⟩ := nonempty_iff_ne_empty.mpr empty
    obtain ⟨_,_,k,hk,km⟩ := mem_filter.mp im
    have arc := (unchanged (core k).2).mp km
    have mv := (mem_sdiff.mp mu).1
    obtain ⟨mp,my⟩ := bankMiss (menus i k hk) mv arc
    have mr : m∉R := fun rr => mp (mem_inN.mp (mem_inter.mp (mem_sdiff.mp rr).1).1).2
    have eq : chargesOf gains E v m = chargesOf gains D v m := by
      ext h
      simp only [chargesOf,mem_filter,mem_univ,true_and,unchanged mr,unchanged (core _).2]
    have rg := ((rich (menus i k hk)).2 m mu arc).ge.trans (gain m)
    by_contra! deficit
    have two : 2 ≤ (chargesOf gains D v m).card := by rw [eq] at deficit; omega
    have sa : ∃ r ∈ shortRows, r ∈ chargesOf gains D v m := by
      by_contra! none
      have sub : chargesOf gains D v m ⊆ {x} := by
        intro r rm
        obtain ⟨_,_,h,hr,_⟩ := mem_filter.mp rm
        have classified : ∀ i, ∀ k ∈ gains i, i ∈ shortRows ∨ i=x := by decide
        exact mem_singleton.mpr ((classified r h hr).resolve_left (fun rs => none r rs rm))
      have small := card_le_card sub
      simp at small
      omega
    obtain ⟨r,rs,rm⟩ := sa
    have leg := (mem_filter.mp rm).2.1
    exact absent ⟨m,mv,ext,⟨mp,tri mv (live r) pv leg (hit r rs).1,my,
      tri mv (live r) yv leg (hit r rs).2⟩,two⟩
  obtain ⟨G,ok,_,paid⟩ := repair v safe (fun i => (core i).1)
    (fun i k ed => internal i k ((unchanged (core i).2).mp ed))
    (fun i _ => (base (core i).1).trans (Nat.add_le_add_right (gain _) 1))
    (fun i ns => by
      rcases parts i with si | mi | hi | rfl
      · exact False.elim (ns si)
      · exact ((rich (show u∈targets by decide)).2 _ (core i).1
          (back u (by decide) i mi)).ge.trans (gain _)
      · exact (rich hi).1.ge.trans (gain _)
      · exact payerRich.trans (gain _)) pay
  have size : U.card ≤ 3*t := by
    rw [show U = V \ {p,y} from rfl,card_sdiff_of_subset bv,card_pair py,order]
    omega
  exact no G U ⟨v a,(core a).1⟩ size ok paid


private abbrev Old := FourLayerReversal.Role

/-- Put the charged row in the first slot of the original reversal, with
the charged lower target as its sink. Its other targets are u and z. -/
def layout (l r : Role) : Old → Role
  | .a => r
  | .b => if r=a then b else if r=b then c else a
  | .c => if r=a then c else if r=b then a else b
  | .x => x | .j => j
  | .u => if r=a then z else u
  | .w => l
  | .z => if r=a then u else z

def reversalLabels (v : Role ↪ ℕ) (l r : Role) (hl : l∈lower) (hr : r∈shortRows) :
    FourLayerReversal.Role ↪ ℕ where
  toFun i := v (layout l r i)
  inj' := by
    intro i k eq
    exact (show ∀ l∈lower, ∀ r∈shortRows, ∀ i k, layout l r i=layout l r k → i=k by decide)
      l hl r hr i k (v.injective eq)

/-- Each of the six reversals tested really has the designated sink. -/
theorem reversal_sink {D : CH.Digraph} {V : Finset ℕ} (v : Role ↪ ℕ)
    (free : QFree D V 3) (live : ∀ i, v i∈V)
    (split : ∀ l∈lower, ∀ h∈upper, D (v l) (v h)≠true)
    {l r : Role} (hl : l∈lower) (hr : r∈shortRows) :
    ∀ i∈FourLayerReversal.targets,
      D (v l) (reversalLabels v l r hl hr i)≠true := by
  intro i hi
  change D (v l) (v (layout l r i))≠true
  rcases (show ∀ l∈lower, ∀ r∈shortRows, ∀ i∈FourLayerReversal.targets,
      layout l r i=l ∨ layout l r i∈upper by decide) l hl r hr i hi with eq | up
  · rw [eq]; exact loopfree free (by decide) (live _)
  · exact split _ hl _ up

/-- Only one short row can be hit. A double charge therefore includes
that row and the reversing middle x. -/
theorem cross_charge {D : CH.Digraph} (v : Role ↪ ℕ) {e : ℕ}
    (two : 2≤(chargesOf gains D v e).card)
    (one : ∀ r∈shortRows, ∀ s∈shortRows, D e (v r)=true → D e (v s)=true → r=s) :
    ∃ r∈shortRows, r∈chargesOf gains D v e ∧ x∈chargesOf gains D v e := by
  classical
  let C := chargesOf gains D v e
  have hit {i} (hi : i∈C) := (mem_filter.mp hi).2.1
  have via {i} (hi : i∈C) := (mem_filter.mp hi).2.2
  have part {i} (hi : i∈C) : i=x ∨ i∈shortRows := by
    obtain ⟨h,hh,_⟩ := via hi
    exact (show ∀ i, ∀ h∈gains i, i=x ∨ i∈shortRows by decide) i h hh
  obtain ⟨i,ih,k,kh,ne⟩ := one_lt_card.mp two
  rcases part ih with rfl | ri <;> rcases part kh with rfl | rk
  · exact False.elim (ne rfl)
  · exact ⟨k,rk,kh,ih⟩
  · exact ⟨i,ri,ih,kh⟩
  · exact False.elim (ne (one _ ri _ rk (hit ih) (hit kh)))

/-- With at most one row hit by e, its double charge is visible in an
ordinary reversal on one of the two overlapping triples. -/
theorem paid_twice_in_reversal {D : CH.Digraph} (v : Role ↪ ℕ) {e : ℕ}
    (two : 2≤(chargesOf gains D v e).card)
    (one : ∀ r∈shortRows, ∀ s∈shortRows, D e (v r)=true → D e (v s)=true → r=s) :
    ∃ l, ∃ hl : l∈lower, ∃ r, ∃ hr : r∈shortRows,
      2≤(FourLayerReversal.charges D (reversalLabels v l r hl hr) e).card := by
  classical
  let C := chargesOf gains D v e
  have hit {i} (hi : i∈C) := (mem_filter.mp hi).2.1
  have via {i} (hi : i∈C) := (mem_filter.mp hi).2.2
  obtain ⟨r,hr,rc,xc⟩ := cross_charge v two one
  obtain ⟨l,hl,le⟩ := via xc
  have lo : l∈lower := by simpa [lower,gains] using hl
  obtain ⟨h,hg,he⟩ := via rc
  have hEq := (show ∀ r∈shortRows, ∀ h∈gains r, ∀ l, h=layout l r .u by decide) r hr h hg l
  refine ⟨l,lo,r,hr,one_lt_card.mpr ⟨.a,?_,.x,?_,by decide⟩⟩
  · exact mem_filter.mpr ⟨mem_univ _,hit rc,.u,by decide,by change D (v (layout l r .u)) e=true; rwa [←hEq]⟩
  · exact mem_filter.mpr ⟨mem_univ _,hit xc,.w,by decide,le⟩

theorem second_reversal_payer {D : CH.Digraph} {V : Finset ℕ} {t p y : ℕ} (v : Role ↪ ℕ)
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t)
    (live : ∀ i, v i ∈ V) (pv : p ∈ V) (yv : y ∈ V) (py : p ≠ y)
    (hit : ∀ i ∈ shortRows, D (v i) p = true ∧ D (v i) y = true)
    (heads : ∀ k ∈ targets, D p (v k) = true ∧ D y (v k) = true)
    (back : ∀ k ∈ targets, ∀ i ∈ middles, D (v k) (v i) = true)
    (legs : ∀ i ∈ middles, ∀ k ∈ shortRows, D (v i) (v k) = true)
    (orderX : D (v j) (v x) ≠ true) (split : ∀ i∈lower, ∀ k∈upper, D (v i) (v k) ≠ true)
    (payerNeutral : FourLayerReversal.neutral D p y (v payer))
    (retained : v payer≠p ∧ v payer≠y)
    (payerRows : D (v payer) (v b)≠true ∧ D (v payer) (v c)≠true)
    (others : ∀ r ∈ inN D V p ∩ inN D V y, r ∉ shortRows.map v →
      ∃ l, FreeTarget D V r l ∧ l ∉ inN D V p ∩ inN D V y)
    (exactS : inN D V (v a) ∩ inN D V (v b) = {v x,v j})
    (noSwap : ¬∃ e∈V, (∀ i, e≠v i) ∧ FourLayerReversal.neutral D p y e ∧
      D e (v c)=true ∧ (D e (v a)=true ∨ D e (v b)=true)) :
    ∃ e∈V, (∀ i, e≠v i) ∧ FourLayerReversal.neutral D p y e ∧
      ∃ l, ∃ hl : l∈lower, ∃ r, ∃ hr : r∈shortRows,
      2≤(FourLayerReversal.charges D (reversalLabels v l r hl hr) e).card := by
  obtain ⟨e,ev,off,neu,two⟩ := different_payer v free reg ht order no live pv yv py hit heads
    back legs orderX split payerNeutral retained payerRows others
  refine ⟨e,ev,off,neu,paid_twice_in_reversal v two ?_⟩
  have ab : ¬(D e (v a)=true ∧ D e (v b)=true) := by
    rintro ⟨ea,eb⟩
    have ep : e ∈ inN D V (v a) ∩ inN D V (v b) :=
      mem_inter.mpr ⟨mem_inN.mpr ⟨ev,ea⟩,mem_inN.mpr ⟨ev,eb⟩⟩
    rw [exactS] at ep
    simp [off x,off j] at ep
  have ca : ¬(D e (v c)=true ∧ (D e (v a)=true ∨ D e (v b)=true)) :=
    fun ⟨ec,er⟩ => noSwap ⟨e,ev,off,neu,ec,er⟩
  intro r hr s hs er es
  have part : ∀ r∈shortRows, r=a ∨ r=b ∨ r=c := by decide
  rcases part _ hr with rfl | rfl | rfl <;> rcases part _ hs with rfl | rfl | rfl <;> tauto

#print axioms repair
#print axioms different_payer
#print axioms reversal_sink
#print axioms cross_charge
#print axioms paid_twice_in_reversal
#print axioms second_reversal_payer
end LeanCH.BR.FourTargetPayment
