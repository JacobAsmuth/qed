import Qed.Proto

namespace Qed

inductive Resource (α : Type) where
  | idle
  | loading
  | ok (val : α)
  | failed (err : String)
deriving Inhabited, Repr

structure Cached (α : Type) where
  state : Resource α := .idle
  seen  : List (String × α) := []
deriving Inhabited

/-- Outcome of an RPC declared with typed `fail(.tag)` domain errors. -/
inductive RpcOutcome (ε : Type) (α : Type) where
  | ok     (val : α)
  | err    (tag : ε) (message : String)
  | failed (message : String)
deriving Inhabited, DecidableEq, Repr

/-- Outcome of an RPC without typed domain error tags. -/
inductive RpcSimpleOutcome (α : Type) where
  | ok     (val : α)
  | failed (message : String)
deriving Inhabited, DecidableEq, Repr

/-- Overloaded callback adapter allowing generated `server` RPC client functions to accept
    `Resource α → msg`, `RpcOutcome ε α → msg`, `RpcSimpleOutcome α → msg`, or `Except String α → msg`. -/
class RpcCallback (α : Type) (msg : outParam Type) (cb : Type) where
  adapt : cb → Except String α → msg

instance {α msg : Type} : RpcCallback α msg (Resource α → msg) :=
  ⟨fun f => fun | .ok a => f (.ok a) | .error e => f (.failed e)⟩

instance (priority := low) {α msg : Type} : RpcCallback (Option α) msg (Resource α → msg) :=
  ⟨fun f => fun | .ok (some a) => f (.ok a) | .ok none => f (.failed "Not found") | .error e => f (.failed e)⟩

instance {ε α msg : Type} :
    RpcCallback (Except (RpcDomainError ε) α) msg (RpcOutcome ε α → msg) :=
  ⟨fun f => fun
    | .ok (.ok a)    => f (.ok a)
    | .ok (.error d) => f (.err d.tag d.message)
    | .error s       => f (.failed s)⟩

instance {α msg : Type} : RpcCallback α msg (RpcSimpleOutcome α → msg) :=
  ⟨fun f => fun | .ok a => f (.ok a) | .error s => f (.failed s)⟩

instance (priority := low) {ε α β msg : Type} [RpcCallback α msg (Resource β → msg)] :
    RpcCallback (Except (RpcDomainError ε) α) msg (Resource β → msg) :=
  ⟨fun f => fun
    | .ok (.ok a)    => RpcCallback.adapt (α := α) f (.ok a)
    | .ok (.error d) => f (.failed d.message)
    | .error s       => f (.failed s)⟩

instance {α msg : Type} : RpcCallback α msg (Except String α → msg) := ⟨id⟩

end Qed
