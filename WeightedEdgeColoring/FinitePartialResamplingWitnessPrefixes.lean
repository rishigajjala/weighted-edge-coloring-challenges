import WeightedEdgeColoring.FinitePartialResamplingWitnessCylinder
import WeightedEdgeColoring.FinitePartialResamplingTracePrefixes
import WeightedEdgeColoring.FinitePartialResamplingWitnessProducts
import WeightedEdgeColoring.FinitePartialResamplingWitnessCertificates
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Data.Fintype.Fin

/-!
# Prefixes forced by a fixed partial-resampling witness

This file connects the intrinsic ranks in a canonical occurrence witness to
the actual prefixes read by a finite partial-resampling run.  It has three
jobs.

* The source pointer before an occurrence is the number of earlier history
  steps which use that source.  Consequently a table which realizes the
  whole history realizes every intrinsic table-cell requirement of every
  endpoint witness.
* The row rank of a witness node orders the selected patches in the same
  order as the visits to that row.  These ordered patches form the row-prefix
  requirements consumed by the adaptive trace.
* The two products attached to the source and row requirements are rewritten
  as products over the witness nodes.

All statements are finite.  In particular, no probability space or
termination theorem is used here.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingWitnessPrefixes

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingExponential
open WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
open WeightedEdgeColoring.FinitePartialResamplingProcess
open WeightedEdgeColoring.FinitePartialResamplingFiniteRun
open WeightedEdgeColoring.FinitePartialResamplingTracePrefixes
open WeightedEdgeColoring.FinitePartialResamplingWitnessStructure
open WeightedEdgeColoring.FinitePartialResamplingWitnessCylinder
open WeightedEdgeColoring.FinitePartialResamplingWitnessProducts

noncomputable section

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

section SourcePointers

/-- Number of steps of a list which refresh a fixed source. -/
def sourceUseCount (i : Source) :
    List (ResamplingStep Source State Row) → Nat
  | [] => 0
  | step :: history =>
      (if UsesSource step.2 i then 1 else 0) + sourceUseCount i history

/-- Running a pointer through a list adds exactly the number of steps which
use the source. -/
theorem runPointer_eq_add_sourceUseCount
    (p : Pointer Source)
    (history : List (ResamplingStep Source State Row)) (i : Source) :
    runPointer p history i = p i + sourceUseCount i history := by
  induction history generalizing p with
  | nil => simp [runPointer, sourceUseCount]
  | cons step history ih =>
      simp only [runPointer, sourceUseCount]
      rw [ih]
      cases hstep : step.2 i with
      | none =>
          have hnot : ¬ UsesSource step.2 i := by
            simp [UsesSource, hstep]
          simp [advancePointer, hstep, hnot]
      | some a =>
          have huses : UsesSource step.2 i := by
            simp [UsesSource, hstep]
          simp [advancePointer, hstep, huses, Nat.add_assoc]

/-- Counting uses in `List.ofFn` is the same as counting indices with the
corresponding property. -/
theorem sourceUseCount_ofFn {n : Nat}
    (history : Fin n → ResamplingStep Source State Row) (i : Source) :
    sourceUseCount i (List.ofFn history) =
      (Finset.univ.filter fun time ↦ UsesSource (history time).2 i).card := by
  induction n with
  | zero => simp [sourceUseCount]
  | succ n ih =>
      rw [List.ofFn_succ]
      simp only [sourceUseCount]
      rw [Fin.card_filter_univ_succ']
      congr 1
      exact ih (fun time ↦ history time.succ)

/-- The chronological list of all history steps strictly before `time`. -/
def historyBefore {n : Nat}
    (history : Fin n → ResamplingStep Source State Row) (time : Fin n) :
    List (ResamplingStep Source State Row) :=
  List.ofFn (Fin.take time.1 (Nat.le_of_lt time.2) history)

theorem historyBefore_eq_take {n : Nat}
    (history : Fin n → ResamplingStep Source State Row) (time : Fin n) :
    historyBefore history time = (List.ofFn history).take time.1 := by
  exact Fin.ofFn_take_eq_take_ofFn (Nat.le_of_lt time.2) history

/-- The use count in the chronological prefix is the cardinality of the
previous-use finset already used by the intrinsic witness rank theorem. -/
theorem sourceUseCount_historyBefore_eq_priorSourceTimes_card {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n)
    (i : Source) :
    sourceUseCount i (historyBefore history time) =
      (priorSourceTimes history time i).card := by
  classical
  let lift : Fin time.1 → Fin n :=
    fun earlier ↦ ⟨earlier.1, Nat.lt_trans earlier.2 time.2⟩
  have hlift : Function.Injective lift := by
    intro left right heq
    apply Fin.ext
    exact congrArg (fun occurrence : Fin n ↦ occurrence.1) heq
  have hsets :
      ((Finset.univ.filter fun earlier : Fin time.1 ↦
          UsesSource (history (lift earlier)).2 i).image lift) =
        priorSourceTimes history time i := by
    ext earlier
    constructor
    · intro hearlier
      obtain ⟨small, hsmall, rfl⟩ := Finset.mem_image.mp hearlier
      have hdata := Finset.mem_filter.mp hsmall
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, small.2, hdata.2⟩
    · intro hearlier
      have hdata := Finset.mem_filter.mp hearlier
      let small : Fin time.1 := ⟨earlier.1, hdata.2.1⟩
      apply Finset.mem_image.mpr
      refine ⟨small, ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by simpa [lift, small] using hdata.2.2⟩
      · apply Fin.ext
        rfl
  rw [historyBefore, sourceUseCount_ofFn]
  change
    (Finset.univ.filter fun earlier : Fin time.1 ↦
      UsesSource (history (lift earlier)).2 i).card = _
  rw [← Finset.card_image_of_injective _ hlift, hsets]

/-- Exact source pointer before a history time, from the all-zero pointer. -/
theorem runPointer_historyBefore_eq_priorSourceTimes_card {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n)
    (i : Source) :
    runPointer (initialPointer : Pointer Source) (historyBefore history time) i =
      (priorSourceTimes history time i).card := by
  rw [runPointer_eq_add_sourceUseCount,
    sourceUseCount_historyBefore_eq_priorSourceTimes_card]
  simp [initialPointer]

/-- Every step in a realized list is compatible with the table state after
running precisely the earlier prefix. -/
theorem realizesFrom_compatible_at
    (T : ResamplingTable Source State) (p : Pointer Source)
    (history : List (ResamplingStep Source State Row))
    (hreal : RealizesFrom T p history)
    (time : Fin history.length) :
    Compatible (history.get time).2
      (tableChoice T (runPointer p (history.take time.1))) := by
  induction history generalizing p with
  | nil => exact Fin.elim0 time
  | cons step history ih =>
      rcases hreal with ⟨hhead, htail⟩
      refine Fin.cases ?_ (fun later ↦ ?_) time
      · simpa [runPointer] using hhead
      · have hcompat := ih (p := advancePointer p step.2) htail later
        simpa [runPointer] using hcompat

/-- Function-indexed version of `realizesFrom_compatible_at`. -/
theorem realizes_compatible_at {n : Nat}
    (T : ResamplingTable Source State)
    (history : Fin n → Label Source State Row)
    (hreal : Realizes T (List.ofFn history)) (time : Fin n) :
    Compatible (history time).2
      (tableChoice T
        (runPointer (initialPointer : Pointer Source)
          (historyBefore history time))) := by
  have hcompat := realizesFrom_compatible_at
    (Row := Row) T (initialPointer : Pointer Source)
    (List.ofFn history) hreal
    ⟨time.1, by simp⟩
  simpa [List.get_ofFn, historyBefore_eq_take] using hcompat

/-- A finite table which realizes a whole history realizes every intrinsic
table-cell requirement of each canonical endpoint witness. -/
theorem realizesWitnessTable_of_realizes_history {n h : Nat}
    (history : Fin n → Label Source State Row) (endpoint : Fin n)
    (hcard : (witnessAt history endpoint).nodes.card < h + 1)
    (fallback : Source → State)
    (T : FiniteResamplingTable Source State h)
    (hreal : Realizes (extendFiniteTable fallback T) (List.ofFn history)) :
    RealizesWitnessTable (witnessAt history endpoint) hcard T := by
  intro requirement
  obtain ⟨time, hnode, hrank⟩ :=
    witnessRequirementCell_val_eq_priorSourceTimes_card
      history endpoint hcard requirement
  have hcompat := realizes_compatible_at
    (Row := Row) (extendFiniteTable fallback T) history hreal time
  have hpatch :
      (history time).2 requirement.2.1 = some requirement.2.2.1 := by
    simpa only [hnode] using requirement.2.2.2
  have hstate := hcompat requirement.2.1 requirement.2.2.1 hpatch
  rw [tableChoice,
    runPointer_historyBefore_eq_priorSourceTimes_card history time
      requirement.2.1] at hstate
  have hcellVal :
      (witnessRequirementCell (witnessAt history endpoint) hcard
        requirement).2.1 =
        (priorSourceTimes history time requirement.2.1).card := hrank
  have hlt :
      (priorSourceTimes history time requirement.2.1).card < h + 1 := by
    simpa [hcellVal] using
      (witnessRequirementCell (witnessAt history endpoint) hcard
        requirement).2.2
  rw [extendFiniteTable_apply_of_lt fallback T _ _ hlt] at hstate
  have hcell :
      (witnessRequirementCell (witnessAt history endpoint) hcard
        requirement).2 =
        ⟨(priorSourceTimes history time requirement.2.1).card, hlt⟩ := by
    apply Fin.ext
    exact hcellVal
  change
    T requirement.2.1
        (witnessRequirementCell (witnessAt history endpoint) hcard
          requirement).2 =
      requirement.2.2.1
  rw [hcell]
  exact hstate

end SourcePointers

section RowRequirements

/-- Patches selected on visits to one row, in chronological order. -/
def rowPatches (r : Row) :
    List (ResamplingStep Source State Row) →
      List (PartialAssignment Source State)
  | [] => []
  | step :: history =>
      if step.1 = r then step.2 :: rowPatches r history
      else rowPatches r history

/-- The patch at a history time is found in its row list at the index equal
to the number of earlier visits to that row. -/
theorem rowPatches_get_priorRowTimes {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n) (r : Row)
    (hrow : (history time).1 = r) :
    ∃ hlt : (priorRowTimes history time r).card <
        (rowPatches r (List.ofFn history)).length,
      (rowPatches r (List.ofFn history)).get
          ⟨(priorRowTimes history time r).card, hlt⟩ =
        (history time).2 := by
  induction n with
  | zero => exact Fin.elim0 time
  | succ n ih =>
      revert hrow
      refine Fin.cases ?_ (fun later ↦ ?_) time
      · intro hrow
        have hhead : (history 0).1 = r := hrow
        have hprior : (priorRowTimes history 0 r).card = 0 := by
          simp [priorRowTimes]
        have hlength : 0 < (rowPatches r (List.ofFn history)).length := by
          simp [List.ofFn_succ, rowPatches, hhead]
        refine ⟨by simpa [hprior] using hlength, ?_⟩
        simp [List.ofFn_succ, rowPatches, hhead, hprior]
      · intro hrow
        let tail : Fin n → Label Source State Row := Fin.tail history
        have hrowTail : (tail later).1 = r := by
          simpa [tail] using hrow
        obtain ⟨htailLt, htailGet⟩ := ih tail later hrowTail
        have hprior :
            (priorRowTimes history later.succ r).card =
              (if (history 0).1 = r then 1 else 0) +
                (priorRowTimes tail later r).card := by
          unfold priorRowTimes
          rw [Fin.card_filter_univ_succ']
          simp only [Fin.val_zero, Nat.zero_lt_succ, true_and,
            Fin.val_succ, Nat.succ_lt_succ_iff]
          congr 1
        by_cases hhead : (history 0).1 = r
        · have hlength :
              (priorRowTimes history later.succ r).card <
                (rowPatches r (List.ofFn history)).length := by
            simpa [List.ofFn_succ, rowPatches, hhead, hprior,
              Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              Nat.succ_lt_succ htailLt
          refine ⟨hlength, ?_⟩
          have hcons :
              ((history 0).2 :: rowPatches r (List.ofFn tail)).get
                  (Fin.succ ⟨(priorRowTimes tail later r).card, htailLt⟩) =
                (tail later).2 := by
            simpa only [List.get_cons_succ] using htailGet
          simpa [List.ofFn_succ, rowPatches, hhead, hprior, tail,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcons
        · have hlength :
              (priorRowTimes history later.succ r).card <
                (rowPatches r (List.ofFn history)).length := by
            simpa [List.ofFn_succ, rowPatches, hhead, hprior, tail] using
              htailLt
          refine ⟨hlength, ?_⟩
          simpa [List.ofFn_succ, rowPatches, hhead, hprior, tail] using
            htailGet

/-- A canonical endpoint witness never prescribes more patches on a row
than the complete history contains on that row. -/
theorem rowNodeCount_witnessAt_le_rowPatches_length {n : Nat}
    (history : Fin n → Label Source State Row) (endpoint : Fin n)
    (r : Row) :
    rowNodeCount (witnessAt history endpoint) r ≤
      (rowPatches r (List.ofFn history)).length := by
  classical
  let tree := witnessAt history endpoint
  let htree : RowDepthInjective tree :=
    witnessAt_rowDepthInjective_property history endpoint
  cases hcount : rowNodeCount tree r with
  | zero => simp [hcount]
  | succ count =>
      let rank : Fin (rowNodeCount tree r) := ⟨count, by omega⟩
      let node : RowNode tree r := (rowRankEquiv tree htree r).symm rank
      have hnodeData := (mem_rowNodes tree r node.1).mp node.2
      obtain ⟨time, _htime, hnode⟩ :=
        witnessAt_node_provenance history endpoint hnodeData.1
      have hrow : (history time).1 = r := by
        simpa [tree, hnode] using hnodeData.2
      have hrankFin := congrArg Fin.val
        ((rowRankEquiv tree htree r).apply_symm_apply rank)
      have hrank : rowRank tree node.1 r = count := by
        change rowRank tree node.1 r = count at hrankFin
        exact hrankFin
      have hcanonical := witnessAt_rowRank_eq_priorRowTimes_card
        history endpoint time (by simpa [tree, hnode] using hnodeData.1)
      have hprior : (priorRowTimes history time r).card = count := by
        have : rowRank tree node.1 r =
            (priorRowTimes history time r).card := by
          simpa [tree, hnode, hrow] using hcanonical
        omega
      obtain ⟨hlt, _hget⟩ :=
        rowPatches_get_priorRowTimes history time r hrow
      rw [hprior] at hlt
      omega

/-- The intrinsic rank list of one row is the corresponding initial segment
of the complete chronological row-patch list. -/
theorem witnessRowRequirements_eq_take_rowPatches {n : Nat}
    (history : Fin n → Label Source State Row) (endpoint : Fin n)
    (r : Row) :
    witnessRowRequirements (witnessAt history endpoint)
        (witnessAt_rowDepthInjective_property history endpoint) r =
      (rowPatches r (List.ofFn history)).take
        (rowNodeCount (witnessAt history endpoint) r) := by
  classical
  let tree := witnessAt history endpoint
  let htree : RowDepthInjective tree :=
    witnessAt_rowDepthInjective_property history endpoint
  have hle : rowNodeCount tree r ≤
      (rowPatches r (List.ofFn history)).length := by
    simpa [tree] using
      rowNodeCount_witnessAt_le_rowPatches_length history endpoint r
  apply List.ext_get
  · simp [witnessRowRequirements, tree, htree, hle]
  · intro index hleft hright
    have hindex : index < rowNodeCount tree r := by
      simpa [witnessRowRequirements, tree, htree] using hleft
    let rank : Fin (rowNodeCount tree r) := ⟨index, hindex⟩
    let node : RowNode tree r := (rowRankEquiv tree htree r).symm rank
    have hnodeData := (mem_rowNodes tree r node.1).mp node.2
    obtain ⟨time, _htime, hnode⟩ :=
      witnessAt_node_provenance history endpoint hnodeData.1
    have hrow : (history time).1 = r := by
      simpa [tree, hnode] using hnodeData.2
    have hrankFin := congrArg Fin.val
      ((rowRankEquiv tree htree r).apply_symm_apply rank)
    have hrank : rowRank tree node.1 r = index := by
      change rowRank tree node.1 r = index at hrankFin
      exact hrankFin
    have hcanonical := witnessAt_rowRank_eq_priorRowTimes_card
      history endpoint time (by simpa [tree, hnode] using hnodeData.1)
    have hprior : (priorRowTimes history time r).card = index := by
      have : rowRank tree node.1 r =
          (priorRowTimes history time r).card := by
        simpa [tree, hnode, hrow] using hcanonical
      omega
    obtain ⟨hlt, hget⟩ :=
      rowPatches_get_priorRowTimes history time r hrow
    have hgetAtIndex :
        (rowPatches r (List.ofFn history)).get ⟨index, by omega⟩ =
          node.1.2.2 := by
      simpa [hprior, hnode] using hget
    have hleftValue :
        (witnessRowRequirements (witnessAt history endpoint)
          (witnessAt_rowDepthInjective_property history endpoint) r).get
            ⟨index, hleft⟩ = node.1.2.2 := by
      simp [witnessRowRequirements, tree, htree, rank, node]
    rw [hleftValue]
    simpa only [List.get_eq_getElem, List.getElem_take] using
      hgetAtIndex.symm

/-- Canonical witness row requirements are prefixes of the actual row
patch lists of the full history. -/
theorem witnessRowRequirements_prefix_rowPatches {n : Nat}
    (history : Fin n → Label Source State Row) (endpoint : Fin n)
    (r : Row) :
    (witnessRowRequirements (witnessAt history endpoint)
      (witnessAt_rowDepthInjective_property history endpoint) r).IsPrefix
        (rowPatches r (List.ofFn history)) := by
  rw [witnessRowRequirements_eq_take_rowPatches history endpoint r]
  exact List.take_prefix _ _

/-- Any family of row lists which is a prefix of the patches actually seen
on every row is consumed by the adaptive trace. -/
theorem consumesRequirements_of_rowPrefixes
    (rowPolicy : (Source → State) → Row)
    (T : ResamplingTable Source State) :
    ∀ (n : Nat) (requirements : RowRequirements Source State Row)
      (p : Pointer Source) (trace : PatchTrace Source State n),
      (∀ r, (requirements r).IsPrefix
        (rowPatches r (traceHistory rowPolicy T p n trace))) →
      ConsumesRequirements rowPolicy T requirements p n trace := by
  intro n
  induction n with
  | zero =>
      intro requirements p trace hprefix
      simp only [ConsumesRequirements]
      intro r
      have hr := hprefix r
      simpa [traceHistory, rowPatches] using List.prefix_nil.mp hr
  | succ n ih =>
      intro requirements p trace hprefix
      let currentRow := rowPolicy (tableChoice T p)
      let currentPatch := trace 0
      cases hcurrent : requirements currentRow with
      | nil =>
          simp only [ConsumesRequirements, currentRow, hcurrent]
          apply ih
          intro r
          by_cases hr : r = currentRow
          · subst r
            simp [hcurrent]
          · have hp := hprefix r
            simpa [traceHistory, rowPatches, currentRow, currentPatch,
              Ne.symm hr] using hp
      | cons required rest =>
          have hprefixCurrent := hprefix currentRow
          have hhead : required = currentPatch ∧
              rest.IsPrefix
                (rowPatches currentRow
                  (traceHistory rowPolicy T
                    (advancePointer p currentPatch) n (Fin.tail trace))) := by
            apply List.cons_prefix_cons.mp
            simpa [traceHistory, rowPatches, currentRow, currentPatch,
              hcurrent] using hprefixCurrent
          simp only [ConsumesRequirements, currentRow, hcurrent]
          refine ⟨hhead.1.symm, ?_⟩
          apply ih
          intro r
          by_cases hr : r = currentRow
          · subst r
            have hconsume :
                consumeHead requirements currentRow currentRow = rest := by
              simp [consumeHead, hcurrent]
            rw [hconsume]
            exact hhead.2
          · have hp := hprefix r
            simpa [consumeHead, traceHistory, rowPatches, currentRow,
              currentPatch, hr, Ne.symm hr] using hp

/-- If a generated trace history is presented as a finite function, every
endpoint witness prescribes row prefixes consumed by that trace. -/
theorem consumes_witnessRowRequirements_of_history_eq {n : Nat}
    (rowPolicy : (Source → State) → Row)
    (T : ResamplingTable Source State) (p : Pointer Source)
    (trace : PatchTrace Source State n)
    (history : Fin n → Label Source State Row)
    (hhistory : List.ofFn history = traceHistory rowPolicy T p n trace)
    (endpoint : Fin n) :
    ConsumesRequirements rowPolicy T
      (witnessRowRequirements (witnessAt history endpoint)
        (witnessAt_rowDepthInjective_property history endpoint))
      p n trace := by
  apply consumesRequirements_of_rowPrefixes
  intro r
  rw [← hhistory]
  exact witnessRowRequirements_prefix_rowPatches history endpoint r

/-- Function view of the list generated by an adaptive trace. -/
def traceHistoryFunction
    (rowPolicy : (Source → State) → Row)
    (T : ResamplingTable Source State) (p : Pointer Source)
    (n : Nat) (trace : PatchTrace Source State n) :
    Fin n → Label Source State Row :=
  fun time ↦
    let hlength := traceHistory_length rowPolicy T p n trace
    (traceHistory rowPolicy T p n trace).get
      (Fin.cast hlength.symm time)

theorem ofFn_traceHistoryFunction
    (rowPolicy : (Source → State) → Row)
    (T : ResamplingTable Source State) (p : Pointer Source)
    (n : Nat) (trace : PatchTrace Source State n) :
    List.ofFn (traceHistoryFunction rowPolicy T p n trace) =
      traceHistory rowPolicy T p n trace := by
  let history := traceHistory rowPolicy T p n trace
  have hlength : history.length = n :=
    traceHistory_length rowPolicy T p n trace
  apply List.ext_get
  · simpa [history, hlength]
  · intro index hleft hright
    simp [traceHistoryFunction, history]

/-- Forgetting the recorded rows from a generated history recovers exactly
the patch trace. -/
theorem map_snd_traceHistory
    (rowPolicy : (Source → State) → Row)
    (T : ResamplingTable Source State) (p : Pointer Source) :
    ∀ (n : Nat) (trace : PatchTrace Source State n),
      (traceHistory rowPolicy T p n trace).map Prod.snd =
        List.ofFn trace := by
  intro n
  induction n generalizing p with
  | zero =>
      intro trace
      simp [traceHistory]
  | succ n ih =>
      intro trace
      simp only [traceHistory, List.map_cons, Prod.snd,
        List.ofFn_succ]
      rw [ih]
      congr 1

/-- The patch stored by the function view of a generated history is the
patch at the same trace time. -/
theorem traceHistoryFunction_patch_eq
    (rowPolicy : (Source → State) → Row)
    (T : ResamplingTable Source State) (p : Pointer Source)
    (n : Nat) (trace : PatchTrace Source State n) (time : Fin n) :
    (traceHistoryFunction rowPolicy T p n trace time).2 = trace time := by
  have hlists :
      List.ofFn (fun time : Fin n ↦
        (traceHistoryFunction rowPolicy T p n trace time).2) =
        List.ofFn trace := by
    calc
      _ = (List.ofFn
          (traceHistoryFunction rowPolicy T p n trace)).map Prod.snd := by
        simpa using List.ofFn_comp'
          (traceHistoryFunction rowPolicy T p n trace) Prod.snd
      _ = (traceHistory rowPolicy T p n trace).map Prod.snd := by
        rw [ofFn_traceHistoryFunction]
      _ = List.ofFn trace :=
        map_snd_traceHistory rowPolicy T p n trace
  have hfunctions := List.ofFn_inj.mp hlists
  exact congrFun hfunctions time

/-- Nonempty patches in a trace give a nonempty patch at every time of its
function-valued history. -/
theorem traceHistoryFunction_nonempty
    (rowPolicy : (Source → State) → Row)
    (T : ResamplingTable Source State) (p : Pointer Source)
    (n : Nat) (trace : PatchTrace Source State n)
    (hnonempty : ∀ time, NonemptyPartial (trace time)) :
    ∀ time, NonemptyPartial
      (traceHistoryFunction rowPolicy T p n trace time).2 := by
  intro time
  rw [traceHistoryFunction_patch_eq]
  exact hnonempty time

/-- Every endpoint witness of a generated adaptive trace supplies row
requirements which the entire trace consumes. -/
theorem trace_consumes_endpoint_witness_requirements
    (rowPolicy : (Source → State) → Row)
    (T : ResamplingTable Source State) (p : Pointer Source)
    (n : Nat) (trace : PatchTrace Source State n)
    (endpoint : Fin n) :
    ConsumesRequirements rowPolicy T
      (witnessRowRequirements
        (witnessAt (traceHistoryFunction rowPolicy T p n trace) endpoint)
        (witnessAt_rowDepthInjective_property
          (traceHistoryFunction rowPolicy T p n trace) endpoint))
      p n trace := by
  apply consumes_witnessRowRequirements_of_history_eq
  exact ofFn_traceHistoryFunction rowPolicy T p n trace

end RowRequirements

end

end WeightedEdgeColoring.FinitePartialResamplingWitnessPrefixes
