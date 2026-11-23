import Qed.Proto

namespace Qed

inductive Resource (α : Type) where
  | idle | loading | ok (val : α) | failed (err : String)
deriving Inhabited, Repr
structure Cached (α : Type) where
  state : Resource α := .idle
  seen  : List (String × α) := []
deriving Inhabited
inductive RpcOutcome (ε α : Type) where
  | ok (val : α) | err (tag : ε) (message : String) | failed (message : String)
deriving Inhabited, DecidableEq, Repr
inductive RpcSimpleOutcome (α : Type) where
  | ok (val : α) | failed (message : String)
deriving Inhabited, DecidableEq, Repr

class RpcCallback (α : Type) (msg : outParam Type) (cb : Type) where adapt : cb → Except String α → msg
instance {α msg : Type} : RpcCallback α msg (Resource α → msg) :=
  ⟨fun | f, .ok a => f (.ok a) | f, .error e => f (.failed e)⟩
instance (priority := low) {α msg : Type} : RpcCallback (Option α) msg (Resource α → msg) :=
  ⟨fun | f, .ok (some a) => f (.ok a) | f, .ok none => f (.failed "Not found") | f, .error e => f (.failed e)⟩
instance {ε α msg : Type} : RpcCallback (Except (RpcDomainError ε) α) msg (RpcOutcome ε α → msg) :=
  ⟨fun | f, .ok (.ok a) => f (.ok a) | f, .ok (.error d) => f (.err d.tag d.message) | f, .error s => f (.failed s)⟩
instance {α msg : Type} : RpcCallback α msg (RpcSimpleOutcome α → msg) :=
  ⟨fun | f, .ok a => f (.ok a) | f, .error s => f (.failed s)⟩
instance (priority := low) {ε α β msg : Type} [RpcCallback α msg (Resource β → msg)] :
    RpcCallback (Except (RpcDomainError ε) α) msg (Resource β → msg) :=
  ⟨fun | f, .ok (.ok a) => RpcCallback.adapt (α := α) f (.ok a) | f, .ok (.error d) => f (.failed d.message) | f, .error s => f (.failed s)⟩
instance {α msg : Type} : RpcCallback α msg (Except String α → msg) := ⟨id⟩
end Qed
