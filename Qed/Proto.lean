import Qed.Proto.Basic
import Qed.Proto.Proofs
import Qed.Proto.Lawful

namespace Qed

/-- Typed application-level RPC failure transmitted cleanly inside binary Protobuf responses. -/
structure RpcDomainError (ε : Type) where
  tag     : ε
  message : String
deriving Inhabited, DecidableEq, Repr

instance {ε : Type} [ToJson ε] : ToJson (RpcDomainError ε) := .ofEquiv fun e => (e.tag, e.message)
instance {ε : Type} [FromJson ε] : FromJson (RpcDomainError ε) := .ofEquiv fun p : ε × String => ⟨p.1, p.2⟩
instance {ε : Type} [LawfulJson ε] : LawfulJson (RpcDomainError ε) :=
  .ofEquiv (fun e => (e.tag, e.message)) (fun p => ⟨p.1, p.2⟩) (fun ⟨_, _⟩ => rfl)

instance {ε : Type} [ToJson ε] : NonNullJson (RpcDomainError ε) := ⟨nofun⟩

instance {ε : Type} [ToProto ε]   : ToProto (RpcDomainError ε)   := .ofEquiv fun e => (e.tag, e.message)
instance {ε : Type} [FromProto ε] : FromProto (RpcDomainError ε) := .ofEquiv fun p : ε × String => RpcDomainError.mk p.1 p.2
instance {ε : Type} [LawfulProto ε] : LawfulProto (RpcDomainError ε) :=
  .ofEquiv (fun e => (e.tag, e.message)) (fun p => RpcDomainError.mk p.1 p.2) (fun ⟨_, _⟩ => rfl)

end Qed
