import checkpoints.shen_extension.ReceiverReturnCapacity

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 BypassRepair CHRuleCatalog

/-- A column with the minimum omission budget can support only a single
return pair in any complete subrectangle containing it. -/
theorem tight_rectangle {D V q r v z} {Z B : Finset ℕ} (free : QFree D V q)
    (cut : 3≤q) (vm : v∈V) (reg : OutEq r D V) (zm : z∈Z)
    (zs : Z⊆ball D V v 2 \ ball D V v 1) (bh : B⊆outN D V v)
    (live : B.Nonempty) (size : B.card≤q)
    (turns : ∀w∈Z,∀b∈B,D w b=true)
    (tight : (ball D V v 2 \ ball D V v 1).card+
      (outN D V v \ inN D V z).card≤r+2) : Z.card+B.card≤2 := by
  classical
  have sub : missedBy (D:=D) (outN D V v) Z⊆outN D V v\inN D V z := by
    intro h hm
    obtain ⟨hh,off⟩ := mem_filter.mp hm
    exact mem_sdiff.mpr ⟨hh,fun hit=>off z zm (mem_inN.mp hit).2⟩
  have room := return_capacity free cut vm reg zs bh live (a:=1)
    (by simpa using size) ReachLedger.noHost_one turns
  have := card_le_card sub
  omega

/-- On a tight returning column the physical pair z→b is private on
both sides: changing either endpoint while retaining the other is impossible. -/
theorem tight_return {D V q r v z b} (free : QFree D V q)
    (cut : 3≤q) (vm : v∈V) (reg : OutEq r D V)
    (zy : z∈ball D V v 2 \ ball D V v 1) (bh : b∈outN D V v)
    (zb : D z b=true) (tight : (ball D V v 2 \ ball D V v 1).card+
      (outN D V v \ inN D V z).card≤r+2) :
    (∀h∈outN D V v,D z h=true → h=b) ∧
    (∀w∈ball D V v 2 \ ball D V v 1,D w b=true → w=z) := by
  classical
  constructor
  · intro h hm zh
    by_contra ne
    have hb : ({h,b} : Finset ℕ).card=2 := by simp [ne]
    have cap := tight_rectangle (Z:={z}) (B:={h,b}) free cut vm reg (mem_singleton_self z)
      (by simpa using zy) (insert_subset hm (singleton_subset_iff.mpr bh))
      (insert_nonempty ..) (by omega)
      (by simpa using And.intro zh zb) tight
    simp only [card_singleton,hb] at cap
    omega
  · intro w wm wb
    by_contra ne
    have wz : ({w,z} : Finset ℕ).card=2 := by simp [ne]
    have cap := tight_rectangle (Z:={w,z}) (B:={b}) free cut vm reg (z:=z) (by simp)
      (insert_subset wm (singleton_subset_iff.mpr zy)) (by simpa using bh)
      (singleton_nonempty b) (by simp; omega)
      (by simpa using And.intro wb zb) tight
    simp only [card_singleton,wz] at cap
    omega

attribute [aesop safe forward (immediate := [free,cut,vm,reg,zy,bh,zb,tight])
  (rule_sets := [CHGraphFamilies])] tight_return
#print axioms tight_rectangle
#print axioms tight_return
end LeanCH.BR.LabelledCompromiseRecipe
