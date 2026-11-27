import checkpoints.shen_extension.FourLayerReversal
import checkpoints.shen_extension.LabelledTrianglePatch

/-! A second edit of the complete four layers. All three short rows take the
same target u, a source of the chosen triple. The middle j, which does not
point to x, takes the other two targets. Payments: u→x, w→j, z→j, x→j and
the three arcs of j into the short rows.

* `repair_of_shape`: the patch argument of `FourLayerReversal.repair` for any
  table of gains and cuts on the eight labels.
* `shared_source_obstruction`: in a source some exterior vertex is charged
  twice by this edit.
* `shared_source_returns`: without a third common parent from a bank swap,
  that vertex lies on u→m→r for a short row r and on w→m→j or z→m→j.
* `single_payer_forced`: one exterior vertex defeating both this edit and the
  reversal edit points to both middles. -/

namespace LeanCH.BR.FourLayerSharedSource
open Finset BRq2 BRq3 BR45 JointFreeTargets TripleBank TwoRowShared FourLayerReversal
open FourLayerReversal.Role

local instance (p : Role → Prop) [DecidablePred p] : Decidable (∀ i, p i) :=
  Fintype.decidableForallFintype

/-- Distinct legs remaining for an exterior payment. -/
def chargesOf (gains : Role → Finset Role) (D : CH.Digraph) (v : Role ↪ ℕ) (m : ℕ) :
    Finset Role :=
  univ.filter (fun i => D m (v i) = true ∧ ∃ h ∈ gains i, D (v h) m = true)

/-- An edit of a residual graph prescribed on the eight labels by tables of
new heads and cut heads. The three conditions on the tables say that new arcs
are fresh, every internal return is cut, and every label keeps its quota. -/
theorem repair_of_shape {D : CH.Digraph} {U : Finset ℕ} {t : ℕ} (v : Role ↪ ℕ)
    (gains cuts : Role → Finset Role) (allowed : Role → Role → Bool)
    (s1 : ∀ i, ∀ h ∈ gains i, h ≠ i ∧ allowed i h = false ∧
      (allowed h i = false ∨ i ∈ cuts h) ∧ gains h = ∅)
    (s2 : ∀ i, ∀ h ∈ gains i, ∀ m, allowed h m = true → allowed m i = true →
      m ∈ cuts h ∨ i ∈ cuts m)
    (s3 : ∀ i, if i ∈ shortRows then (cuts i).card + 1 ≤ (gains i).card
      else (cuts i).card ≤ 1 + (gains i).card)
    (free : QFree D U 3) (inside : ∀ i, v i ∈ U)
    (internal : ∀ i k, D (v i) (v k) = true → allowed i k = true)
    (need : ∀ i ∈ shortRows, t ≤ (outN D U (v i)).card + 1)
    (spare : ∀ i ∉ shortRows, t+1 ≤ (outN D U (v i)).card)
    (pay : ∀ m ∈ U, (∀ i, m ≠ v i) → t + (chargesOf gains D v m).card ≤ (outN D U m).card) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ (∀ i, ∀ h ∈ gains i, E (v i) (v h) = true) ∧
      ∀ m ∈ U, t ≤ (outN E U m).card :=
  LabelledTrianglePatch.repair_of_shape v shortRows gains cuts allowed s1 s2 s3 free inside
    internal need spare pay

/-- New heads of the shared-source edit. -/
def gainsS : Role → Finset Role
  | .a => {u} | .b => {u} | .c => {u} | .j => {w,z} | _ => ∅

/-- Cut heads of the shared-source edit. -/
def cutsS : Role → Finset Role
  | .u => {x}
  | .w | .z => {j}
  | .x => {j}
  | .j => {a,b,c}
  | _ => ∅

/-- Permitted old arcs. Among the three targets u has no incoming arc. The
middle j misses x. -/
def allowedS (i k : Role) : Bool := decide (i ≠ k ∧
  ((i ∈ shortRows ∧ k ∈ shortRows) ∨ (i ∈ middles ∧ k ∈ shortRows) ∨
   (i ∈ targets ∧ k ∈ middles) ∨ (i ∈ targets ∧ k ∈ targets ∧ k ≠ u) ∨
   (i = x ∧ k = j)))

private theorem shapeS :
    (∀ i, ∀ h ∈ gainsS i, h ≠ i ∧ allowedS i h = false ∧
      (allowedS h i = false ∨ i ∈ cutsS h) ∧ gainsS h = ∅) ∧
    (∀ i, ∀ h ∈ gainsS i, ∀ m, allowedS h m = true → allowedS m i = true →
      m ∈ cutsS h ∨ i ∈ cutsS m) ∧
    (∀ i, if i ∈ shortRows then (cutsS i).card + 1 ≤ (gainsS i).card
      else (cutsS i).card ≤ 1 + (gainsS i).card) := by decide

private theorem forbiddenS : ∀ i k, allowedS i k = false →
    i=k ∨ (i∈shortRows ∧ k∈middles) ∨ (i∈middles ∧ k∈targets) ∨
    (i∈shortRows ∧ k∈targets) ∨ (i∈targets ∧ k∈shortRows) ∨
    (i=j ∧ k=x) ∨ (i∈targets ∧ k=u) := by decide

/-- The shared-source edit on a residual graph. Each exterior middle pays
its own bill. -/
theorem shared_source_repair {D : CH.Digraph} {U : Finset ℕ} {t : ℕ} (v : Role ↪ ℕ)
    (free : QFree D U 3) (inside : ∀ i, v i ∈ U)
    (internal : ∀ i k, D (v i) (v k) = true → allowedS i k = true)
    (need : ∀ i ∈ shortRows, t ≤ (outN D U (v i)).card + 1)
    (spare : ∀ i ∉ shortRows, t+1 ≤ (outN D U (v i)).card)
    (pay : ∀ m ∈ U, (∀ i, m ≠ v i) → t + (chargesOf gainsS D v m).card ≤ (outN D U m).card) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ (∀ i, ∀ h ∈ gainsS i, E (v i) (v h) = true) ∧
      ∀ m ∈ U, t ≤ (outN E U m).card :=
  repair_of_shape v gainsS cutsS allowedS shapeS.1 shapeS.2.1 shapeS.2.2
    free inside internal need spare pay

/-- In a source with the complete four layers, every labelling in which u
receives no arc from w or z, and j misses x, forces a double charge of the
shared-source edit outside the four layers. The witness is nonadjacent to
each bank label in both directions. -/
theorem shared_source_obstruction {D : CH.Digraph} {V : Finset ℕ} {t p y : ℕ} (v : Role ↪ ℕ)
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t)
    (live : ∀ i, v i ∈ V) (pv : p ∈ V) (yv : y ∈ V) (py : p ≠ y)
    (hit : ∀ i ∈ shortRows, D (v i) p = true ∧ D (v i) y = true)
    (heads : ∀ k ∈ targets, D p (v k) = true ∧ D y (v k) = true)
    (back : ∀ k ∈ targets, ∀ i ∈ middles, D (v k) (v i) = true)
    (legs : ∀ i ∈ middles, ∀ k ∈ shortRows, D (v i) (v k) = true)
    (orderX : D (v j) (v x) ≠ true) (source : ∀ i ∈ targets, D (v i) (v u) ≠ true)
    (others : ∀ r ∈ inN D V p ∩ inN D V y, r ∉ shortRows.map v →
      ∃ l, FreeTarget D V r l ∧ l ∉ inN D V p ∩ inN D V y) :
    ∃ m ∈ V, (∀ i, m ≠ v i) ∧ neutral D p y m ∧
      2 ≤ (chargesOf gainsS D v m).card := by
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
  have parts : ∀ i, i∈shortRows ∨ i∈middles ∨ i∈targets := by decide
  have core (i) : v i∈U ∧ v i∉R := by
    rcases parts i with si | mi | hi
    · exact ⟨su (short si),fun r => (mem_sdiff.mp r).2 (mem_map.mpr ⟨i,si,rfl⟩)⟩
    · exact ⟨(middle mi).1,fun r => (middle mi).2 (mem_sdiff.mp r).1⟩
    · exact ⟨(head hi).1,fun r => (head hi).2.1 (mem_sdiff.mp r).1⟩
  have internal (i k) (ik : D (v i) (v k) = true) : allowedS i k = true := by
    by_contra! off
    rcases forbiddenS i k (by simpa using off) with rfl | ⟨is',km⟩ | ⟨im,kh⟩ | ⟨is',kh⟩ |
        ⟨ih,ks⟩ | ⟨rfl,rfl⟩ | ⟨ih,rfl⟩
    · exact loopfree free (by decide) (live i) ik
    · exact digonfree free (by decide) (live i) (live k) ik (legs k km i is')
    · exact digonfree free (by decide) (live i) (live k) ik (back k kh i im)
    · exact tri (live k) (live x) (live i) (back k kh x (by decide)) (legs x (by decide) i is') ik
    · exact tri (live k) pv (live i) (hit k ks).1 (heads i ih).1 ik
    · exact orderX ik
    · exact source i ih ik
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
  have menus : ∀ i, ∀ k ∈ gainsS i, k∈targets := by decide
  by_contra absent
  have pay (m) (mu : m∈U) (ext : ∀ i, m ≠ v i) :
      t+(chargesOf gainsS E v m).card ≤ (outN E U m).card := by
    by_cases empty : chargesOf gainsS E v m = ∅
    · simpa [empty] using floor mu ext
    obtain ⟨i,im⟩ := nonempty_iff_ne_empty.mpr empty
    obtain ⟨_,_,k,hk,km⟩ := mem_filter.mp im
    have arc := (unchanged (core k).2).mp km
    have mv := (mem_sdiff.mp mu).1
    obtain ⟨mp,my⟩ := bankMiss (menus i k hk) mv arc
    have mr : m∉R := fun rr => mp (mem_inN.mp (mem_inter.mp (mem_sdiff.mp rr).1).1).2
    have eq : chargesOf gainsS E v m = chargesOf gainsS D v m := by
      ext h
      simp only [chargesOf,mem_filter,mem_univ,true_and,unchanged mr,unchanged (core _).2]
    have rg := ((rich (menus i k hk)).2 m mu arc).ge.trans (gain m)
    by_contra! deficit
    have two : 2 ≤ (chargesOf gainsS D v m).card := by rw [eq] at deficit; omega
    have sa : ∃ r ∈ shortRows, r ∈ chargesOf gainsS D v m := by
      by_contra! none
      have sub : chargesOf gainsS D v m ⊆ {j} := by
        intro r rm
        obtain ⟨_,_,h,hr,_⟩ := mem_filter.mp rm
        have classified : ∀ i, ∀ k ∈ gainsS i, i ∈ shortRows ∨ i=j := by decide
        exact mem_singleton.mpr ((classified r h hr).resolve_left (fun rs => none r rs rm))
      have small := card_le_card sub
      simp at small
      omega
    obtain ⟨r,rs,rm⟩ := sa
    have leg := (mem_filter.mp rm).2.1
    exact absent ⟨m,mv,ext,⟨mp,tri mv (live r) pv leg (hit r rs).1,my,
      tri mv (live r) yv leg (hit r rs).2⟩,two⟩
  obtain ⟨G,ok,_,paid⟩ := shared_source_repair v safe (fun i => (core i).1)
    (fun i k ed => internal i k ((unchanged (core i).2).mp ed))
    (fun i _ => (base (core i).1).trans (Nat.add_le_add_right (gain _) 1))
    (fun i ns => by
      rcases parts i with si | mi | hi
      · exact False.elim (ns si)
      · exact ((rich (show u∈targets by decide)).2 _ (core i).1
          (back u (by decide) i mi)).ge.trans (gain _)
      · exact (rich hi).1.ge.trans (gain _)) pay
  have size : U.card ≤ 3*t := by
    rw [show U = V \ {p,y} from rfl,card_sdiff_of_subset bv,card_pair py,order]
    omega
  exact no G U ⟨v a,(core a).1⟩ size ok paid

/-- A double charge of the shared-source edit that is not a common parent of
a and b either is a common parent of c and another row, or lies on a return
into j from w or z and on a return from u into a short row. -/
theorem classify_shared {D : CH.Digraph} {v : Role ↪ ℕ} {m : ℕ}
    (two : 2 ≤ (chargesOf gainsS D v m).card) (off : ¬(D m (v a)=true ∧ D m (v b)=true)) :
    (D m (v c)=true ∧ (D m (v a)=true ∨ D m (v b)=true)) ∨
    (D m (v j)=true ∧ (D (v w) m=true ∨ D (v z) m=true) ∧ D (v u) m=true ∧
      ∃ i ∈ shortRows, D m (v i)=true) := by
  classical
  let M := chargesOf gainsS D v m
  have head {i} (h : i∈M) : D m (v i)=true := (mem_filter.mp h).2.1
  have cover {i} (h : i∈M) : i=a ∨ i=b ∨ i=c ∨ i=j := by
    obtain ⟨_,_,k,km,_⟩ := mem_filter.mp h
    exact (show ∀ i, ∀ k ∈ gainsS i, i=a ∨ i=b ∨ i=c ∨ i=j by decide) i k km
  have viaU {i} (h : i∈M) (is' : i∈shortRows) : D (v u) m=true := by
    obtain ⟨_,_,k,kg,km⟩ := mem_filter.mp h
    have ku : k=u := (show ∀ i∈shortRows, ∀ k ∈ gainsS i, k=u by decide) i is' k kg
    exact ku ▸ km
  obtain ⟨r,rm,s,sm,rs⟩ := one_lt_card.mp two
  by_cases jm : j∈M
  · right
    obtain ⟨_,mj,k,kg,km⟩ := mem_filter.mp jm
    have kw : k=w ∨ k=z := by simpa [gainsS] using kg
    have selected {i} (h : i∈M) (ij : i≠j) :
        D (v u) m=true ∧ ∃ i∈shortRows, D m (v i)=true := by
      rcases cover h with rfl | rfl | rfl | hj
      · exact ⟨viaU h (by decide),a,by decide,head h⟩
      · exact ⟨viaU h (by decide),b,by decide,head h⟩
      · exact ⟨viaU h (by decide),c,by decide,head h⟩
      · exact False.elim (ij hj)
    have rest : D (v u) m=true ∧ ∃ i∈shortRows, D m (v i)=true := by
      by_cases rj : r=j
      · exact selected sm (fun e => rs (rj.trans e.symm))
      · exact selected rm rj
    exact ⟨mj,kw.elim (fun e => Or.inl (e ▸ km)) (fun e => Or.inr (e ▸ km)),rest.1,rest.2⟩
  · left
    have ma {i} (h : i∈M) := head h
    rcases cover rm with rfl | rfl | rfl | rfl <;>
      rcases cover sm with rfl | rfl | rfl | rfl <;>
      first
        | exact False.elim (rs rfl)
        | exact False.elim (jm rm)
        | exact False.elim (jm sm)
        | exact False.elim (off ⟨ma rm,ma sm⟩)
        | exact False.elim (off ⟨ma sm,ma rm⟩)
        | exact ⟨ma rm,Or.inl (ma sm)⟩
        | exact ⟨ma rm,Or.inr (ma sm)⟩
        | exact ⟨ma sm,Or.inl (ma rm)⟩
        | exact ⟨ma sm,Or.inr (ma rm)⟩

/-- On the branch where no exterior vertex is a common parent of c and of a
or b, the shared-source edit leaves an exterior vertex m with u→m, m→j,
w→m or z→m, and m pointing to a short row. -/
theorem shared_source_returns {D : CH.Digraph} {V : Finset ℕ} {t p y : ℕ} (v : Role ↪ ℕ)
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t)
    (live : ∀ i, v i ∈ V) (pv : p ∈ V) (yv : y ∈ V) (py : p ≠ y)
    (exactS : inN D V (v a) ∩ inN D V (v b) = {v x,v j})
    (hit : ∀ i ∈ shortRows, D (v i) p = true ∧ D (v i) y = true)
    (heads : ∀ k ∈ targets, D p (v k) = true ∧ D y (v k) = true)
    (back : ∀ k ∈ targets, ∀ i ∈ middles, D (v k) (v i) = true)
    (legs : ∀ i ∈ middles, ∀ k ∈ shortRows, D (v i) (v k) = true)
    (orderX : D (v j) (v x) ≠ true) (source : ∀ i ∈ targets, D (v i) (v u) ≠ true)
    (others : ∀ r ∈ inN D V p ∩ inN D V y, r ∉ shortRows.map v →
      ∃ l, FreeTarget D V r l ∧ l ∉ inN D V p ∩ inN D V y)
    (noSwap : ¬∃ m∈V, (∀ i, m ≠ v i) ∧ neutral D p y m ∧ D m (v c)=true ∧
      (D m (v a)=true ∨ D m (v b)=true)) :
    ∃ m ∈ V, (∀ i, m ≠ v i) ∧ neutral D p y m ∧
      D (v u) m=true ∧ D m (v j)=true ∧ (D (v w) m=true ∨ D (v z) m=true) ∧
      ∃ i ∈ shortRows, D m (v i)=true := by
  classical
  obtain ⟨m,mv,ext,neu,two⟩ := shared_source_obstruction v free reg ht order no live pv yv py
    hit heads back legs orderX source others
  have off : ¬(D m (v a)=true ∧ D m (v b)=true) := by
    rintro ⟨ma,mb⟩
    have pred : m ∈ inN D V (v a) ∩ inN D V (v b) := mem_inter.mpr
      ⟨mem_inN.mpr ⟨mv,ma⟩,mem_inN.mpr ⟨mv,mb⟩⟩
    rw [exactS] at pred
    simp [ext x,ext j] at pred
  rcases classify_shared two off with ⟨mc,ab⟩ | ⟨mj,wz,um,row⟩
  · exact False.elim (noSwap ⟨m,mv,ext,neu,mc,ab⟩)
  · exact ⟨m,mv,ext,neu,um,mj,wz,row⟩

/-- One-sink triple, labelled with w its sink and u a source. If a single
exterior vertex m carries every double charge of the reversal edit and of
the shared-source edit, then m lies on w→m→x and on u→m, points to j as
well, and points to a short row. -/
theorem single_payer_forced {D : CH.Digraph} {V : Finset ℕ} {t p y m : ℕ} (v : Role ↪ ℕ)
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t)
    (live : ∀ i, v i ∈ V) (pv : p ∈ V) (yv : y ∈ V) (py : p ≠ y)
    (exactS : inN D V (v a) ∩ inN D V (v b) = {v x,v j})
    (hit : ∀ i ∈ shortRows, D (v i) p = true ∧ D (v i) y = true)
    (heads : ∀ k ∈ targets, D p (v k) = true ∧ D y (v k) = true)
    (back : ∀ k ∈ targets, ∀ i ∈ middles, D (v k) (v i) = true)
    (legs : ∀ i ∈ middles, ∀ k ∈ shortRows, D (v i) (v k) = true)
    (orderX : D (v j) (v x) ≠ true)
    (sink : ∀ i ∈ targets, D (v w) (v i) ≠ true)
    (source : ∀ i ∈ targets, D (v i) (v u) ≠ true)
    (others : ∀ r ∈ inN D V p ∩ inN D V y, r ∉ shortRows.map v →
      ∃ l, FreeTarget D V r l ∧ l ∉ inN D V p ∩ inN D V y)
    (noSwap : ¬∃ e∈V, (∀ i, e ≠ v i) ∧ neutral D p y e ∧ D e (v c)=true ∧
      (D e (v a)=true ∨ D e (v b)=true))
    (single : ∀ e ∈ V, (∀ i, e ≠ v i) → neutral D p y e →
      (2 ≤ (charges D v e).card ∨ 2 ≤ (chargesOf gainsS D v e).card) → e = m) :
    D (v w) m=true ∧ D m (v x)=true ∧ D (v u) m=true ∧ D m (v j)=true ∧
      ∃ i ∈ shortRows, D m (v i)=true := by
  classical
  have offOf {e} (ev : e∈V) (ext : ∀ i, e ≠ v i) :
      ¬(D e (v a)=true ∧ D e (v b)=true) := by
    rintro ⟨ma,mb⟩
    have pred : e ∈ inN D V (v a) ∩ inN D V (v b) := mem_inter.mpr
      ⟨mem_inN.mpr ⟨ev,ma⟩,mem_inN.mpr ⟨ev,mb⟩⟩
    rw [exactS] at pred
    simp [ext x,ext j] at pred
  obtain ⟨e,ev,ext,ep,pe,ey,ye,two⟩ := exterior_obstruction v free reg ht order no live pv yv py
    hit heads back legs orderX sink others
  have neu : neutral D p y e := ⟨ep,pe,ey,ye⟩
  have em : e = m := single e ev ext neu (Or.inl two)
  obtain ⟨g,gv,gext,gneu,gtwo⟩ := shared_source_obstruction v free reg ht order no live pv yv py
    hit heads back legs orderX source others
  have gm : g = m := single g gv gext gneu (Or.inr gtwo)
  have sees {i} (h : i ∈ charges D v e) : D e (v i)=true := (mem_filter.mp h).2.1
  rcases classify_charge two (offOf ev ext) with ⟨cm,ab⟩ | ⟨wm,mx,_⟩
  · exact False.elim (noSwap ⟨e,ev,ext,neu,sees cm,ab.imp sees sees⟩)
  rcases classify_shared gtwo (offOf gv gext) with ⟨gc,gab⟩ | ⟨gj,_,gu,row⟩
  · exact False.elim (noSwap ⟨g,gv,gext,gneu,gc,gab⟩)
  exact ⟨em ▸ wm,em ▸ mx,gm ▸ gu,gm ▸ gj,gm ▸ row⟩

/-- The same triple is closed if the single exterior payer misses j. -/
theorem single_payer_closure {D : CH.Digraph} {V : Finset ℕ} {t p y m : ℕ} (v : Role ↪ ℕ)
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t)
    (live : ∀ i, v i ∈ V) (pv : p ∈ V) (yv : y ∈ V) (py : p ≠ y)
    (exactS : inN D V (v a) ∩ inN D V (v b) = {v x,v j})
    (hit : ∀ i ∈ shortRows, D (v i) p = true ∧ D (v i) y = true)
    (heads : ∀ k ∈ targets, D p (v k) = true ∧ D y (v k) = true)
    (back : ∀ k ∈ targets, ∀ i ∈ middles, D (v k) (v i) = true)
    (legs : ∀ i ∈ middles, ∀ k ∈ shortRows, D (v i) (v k) = true)
    (orderX : D (v j) (v x) ≠ true)
    (sink : ∀ i ∈ targets, D (v w) (v i) ≠ true)
    (source : ∀ i ∈ targets, D (v i) (v u) ≠ true)
    (others : ∀ r ∈ inN D V p ∩ inN D V y, r ∉ shortRows.map v →
      ∃ l, FreeTarget D V r l ∧ l ∉ inN D V p ∩ inN D V y)
    (noSwap : ¬∃ e∈V, (∀ i, e ≠ v i) ∧ neutral D p y e ∧ D e (v c)=true ∧
      (D e (v a)=true ∨ D e (v b)=true))
    (single : ∀ e ∈ V, (∀ i, e ≠ v i) → neutral D p y e →
      (2 ≤ (charges D v e).card ∨ 2 ≤ (chargesOf gainsS D v e).card) → e = m)
    (mj : D m (v j) ≠ true) : False :=
  mj (single_payer_forced v free reg ht order no live pv yv py exactS hit heads back legs
    orderX sink source others noSwap single).2.2.2.1

#print axioms repair_of_shape
#print axioms shared_source_repair
#print axioms shared_source_obstruction
#print axioms classify_shared
#print axioms shared_source_returns
#print axioms single_payer_forced
#print axioms single_payer_closure
end LeanCH.BR.FourLayerSharedSource


