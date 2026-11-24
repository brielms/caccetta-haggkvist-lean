import checkpoints.shen_extension.FedMiddleTiers

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- All labels of the exterior must enter the next shell if none is an
extra first-layer head. Equality of cardinalities then fixes its actual set. -/
theorem exterior_key {D V q u C} (free : QFree D V q) (hq : 4≤q) (uv : u∈V)
    (first : C⊆outN D V u) (small : (N2 D V u).card≤(exterior D V C).card)
    (apart : Disjoint (outN D V u\C) (exterior D V C)) :
    N2 D V u=exterior D V C := by
  exact (eq_of_subset_of_card_le (fun e em=> (mem_union.mp (exterior_subset_menu free hq uv first em)).resolve_left
    (fun h=>disjoint_left.mp apart h em)) small).symm

/-- At the same marked cycle, a fed extra first head exceeds the booked
price ceiling. Every class is therefore the same physical exterior. -/
theorem unique_middle_claim {D V q r δ cap C A} (free : QFree D V q) (hq : 6≤q)
    (reg : OutEq r D V) (t : Selection D V q r 3 (3*r)) (mark : RemainingPayer t C δ cap A)
    (mid : MiddleRows t C) (fit : r≤q+2) (width : (exterior D V C).card=r)
    (size : C.card+1=r) (room : 4*(r-q+1)<C.card+6) :
    claims t C={exterior D V C} ∧ rowStock t (booked t) C≤1 := by
  classical
  have scale K (km : K∈booked t) : omissions D V K r≤r-q := by
    obtain ⟨Z,zk,rfl⟩ := mem_image.mp km; exact t.loss _ (t.assigned _ zk)
  have bound := booked_score_cap free reg (by omega : r-q+2≤q) t scale mark.bookedHere (allowance:=2) (by simpa using mid.ceiling)
  have om : omissions D V C r=1 := by unfold omissions; rw [width]; omega
  rw [om,pow_one] at bound
  have fixed Y (ym : Y∈claims t C) : Y=exterior D V C := by
    obtain ⟨key,id⟩ := mem_filter.mp ym
    obtain ⟨first,y,z,_⟩ := mid.each Y ym
    have uv := rep_native t key
    have eq := rep_key t key
    have cy := t.rooted _ (t.assigned _ key)
    have len := t.length _ (t.assigned _ key)
    rw [id] at cy len
    have apart : Disjoint (outN D V (t.rep Y)\C) (exterior D V C) := by
      apply disjoint_left.mpr
      intro w wm we
      have diff := card_sdiff_of_subset first
      rw [reg _ uv] at diff
      have fed : outN D V (t.rep Y)\C⊆exterior D V C := by
        intro v vm
        exact (card_le_one.mp (show (outN D V (t.rep Y)\C).card≤1 by omega) _ vm _ wm) ▸ we
      have hi := fed_middle_tiers free hq reg uv fit len cy first ((congrArg card eq).trans y)
        (by omega) size fed
      have lo := hi.trans (tier_stock D V C 3 (3*r))
      omega
    exact eq.symm.trans (exterior_key free (by omega) uv first (by rw [eq,y,width]) apart)
  obtain ⟨Y,yk,atC⟩ := mem_image.mp mark.bookedHere
  have ym : Y∈claims t C := mem_filter.mpr ⟨yk,atC⟩
  have same := fixed Y ym
  have all : claims t C={exterior D V C} := by
    ext Z
    simpa only [mem_singleton] using Iff.intro (fixed Z) (fun e=>e ▸ same ▸ ym)
  have unit : shellDebt D V 3 (3*r) Y≤1 := by
    apply (class_residual (m:=1) _).trans (by decide)
    intro v vm
    have least := t.least Y yk v vm
    have upper := (mem_filter.mp (mem_filter.mp vm).1).2
    have exactSize := (mid.each Y ym).2.2.2
    rw [show (ball D V v 3).card=3*r by omega]; simp [debit]
  have empty : A=∅ := eq_empty_iff_forall_notMem.mpr (fun Z zm=>by
    have := (mark.routed Z zm).2.2.2.2.1.nextSize; omega)
  have due := mark.due
  rw [empty,sum_empty,add_zero,netDebt,all,←same,sum_singleton] at due
  have nonneg : (0:ℚ)≤(receipts t C).card := by positivity
  exact ⟨all,le_trans (le_trans due (sub_le_self _ nonneg)) (by exact_mod_cast unit)⟩

attribute [aesop safe forward (immediate := [free,hq,reg,mark,mid,fit,width,size,room]) (rule_sets := [CHGraphFamilies])] unique_middle_claim
/-- A booked cycle of limited stock must name a row below the ball target
whenever the number of its rows exceeds its entire score budget. -/
theorem booked_small_row {D V q r k b c allowance C} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r k b) (cut : c+2≤q)
    (scale : ∀K∈booked t,omissions D V K r≤c) (cm : C∈booked t)
    (stock : rowStock t (booked t) C≤(allowance:ℕ))
    (room : allowance*((c+1)*2^(omissions D V C r))<C.card) :
    ∃v∈C,(ball D V v k).card≤b := by
  classical
  by_contra! high
  have lo := tier_stock D V C k b
  rw [filter_true_of_mem high] at lo
  have hi := booked_score_cap free reg cut t scale cm stock
  omega

attribute [aesop safe forward (immediate := [free,reg,cut,scale,cm,stock,room]) (rule_sets := [CHGraphFamilies])] booked_small_row
#print axioms booked_small_row
#print axioms exterior_key
#print axioms unique_middle_claim
end LeanCH.BR.LowShellCycleSelection
