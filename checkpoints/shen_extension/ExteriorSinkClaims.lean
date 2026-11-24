import checkpoints.shen_extension.ExteriorSinkContacts

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

theorem narrow_second_is_bank {D V q r u C} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (uv : u∈V) (first : C⊆outN D V u) (one : (outN D V u\C).card≤1)
    (paid : ∀c∈C,exterior D V C⊆outN D V c)
    (few : (N2 D V u).card<r) (bound : (N2 D V u).card≤(exterior D V C).card) :
    N2 D V u=exterior D V C := by
  classical
  apply Eq.symm
  apply eq_of_subset_of_card_le _ bound
  intro z ze
  rcases mem_union.mp (exterior_subset_menu free hq uv first ze) with zx|zy
  · have zv := outN_subset (mem_sdiff.mp zx).1
    have lone := card_le_one.mp one
    have all : outN D V z⊆N2 D V u := by
      intro d dm
      apply (mem_union.mp (headX (free.mono_bound hq) uv (mem_sdiff.mp zx).1 (outN_subset dm) (mem_outN.mp dm).2)).resolve_left
      intro dx
      by_cases dc : d∈C
      · exact digonfree free (by omega) zv (outN_subset dm) (mem_outN.mp dm).2 (mem_outN.mp (paid d dc ze)).2
      have eq := lone d (mem_sdiff.mpr ⟨dx,dc⟩) z zx
      subst d
      exact loopfree free (by omega) zv (mem_outN.mp dm).2
    have count := card_le_card all
    rw [reg _ zv] at count
    omega
  · exact zy

/-- A short first claim or a switched claim needs an actual internal head
of every exterior label, on the same booked account. -/
theorem sink_claim_shapes {D V q r C A target e} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (ready : RoutingRoom q r V.card target)
    (account : CompleteAccount t C A) (length : C.card+1=r) (long : q<C.card)
    (roots : ∀c∈C,Rooted D V c C)
    (ee : e∈exterior D V C) (sink : ∀a∈exterior D V C,D e a≠true) :
    C∉shortSwitches t ∧ ∀Y∈claims t C,C⊆outN D V (t.rep Y) →
      3*r≤(ball D V (t.rep Y) 3).card := by
  classical
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  have fit := ready.close
  have width := account.width
  have zero : outN D (exterior D V C) e=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro a am
    exact sink a (outN_subset am) (mem_outN.mp am).2
  have noRoot (rt : Rooted D V e (exterior D V C)) : False := by
    have one := rt.one e ee
    simp [zero] at one
  constructor
  · intro moved
    obtain ⟨key,yw,zw,ww⟩ := mem_filter.mp moved
    have ey := rep_key t key
    obtain good|state := short_shell_payer free (by omega) reg (rep_native t key) fit hr ((congrArg card ey).trans yw) zw
    · have := good.1; omega
    obtain ⟨outer,yz,rest,_⟩ := state
    rw [ey] at yz
    have small := (congrArg card rest).trans outer
    have inside : N3 D V (t.rep C)⊆V := fun _ m=>N3_subV m
    have rooted := (short_exterior free (by omega : 2≤q) reg inside (by omega : (N3 D V (t.rep C)).card≤q+1)
      (card_pos.mp (by omega : 0<(N3 D V (t.rep C)).card)) small.le (by omega)).2
    exact noRoot (yz.symm ▸ rooted e (yz ▸ ee))
  · intro Y ym first
    by_contra! short
    obtain ⟨key,id⟩ := mem_filter.mp ym
    have uv := rep_native t key
    obtain ⟨ys,zs⟩|⟨ys,zs⟩ := short_shapes free reg ready uv short
    · have slot := card_sdiff_of_subset first
      rw [reg _ uv] at slot
      have eq := narrow_second_is_bank free (by omega) reg uv first (by omega) account.allHeads (by omega) (by omega)
      obtain ⟨_,_,_,_,_,_,_,bank,_⟩ := narrow_cycle free (by omega) reg uv fit hr ys zs
      exact noRoot (eq ▸ (bank e (eq.symm ▸ ee)).1)
    · exact short_large_second_escape free hq reg uv fit long roots first length ys (by omega)

#print axioms narrow_second_is_bank
#print axioms sink_claim_shapes
end LeanCH.BR.LowShellCycleSelection
