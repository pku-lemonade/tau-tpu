import Tau.IR.Compiled
import Tau.Proofs.SliceLevel.Issues
import Tau.Proofs.IR.MemMap

/-!
# The timeline of a compiled program does not depend on its values

`issues_map` (`Tau/Proofs/SliceLevel/Issues.lean`) carried over to events:
the timeline of a run from a mapped memory image is the mapped timeline.
-/

namespace Tau

variable {V W : Type}

theorem Compiled.timelineFrom_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f)
    (c : Compiled) (image : List (List V)) :
    c.timelineFrom T (image.map (List.map f)) =
      (c.timelineFrom S image).map (Event.map f) := by
  unfold Compiled.timelineFrom
  rw [issues_map S T f h]
  exact filterMap_event_map f c.map _

end Tau
