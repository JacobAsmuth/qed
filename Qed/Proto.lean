import Qed.Proto.Basic
import Qed.Proto.Proofs
import Qed.Proto.Lawful

namespace Qed

/-- Typed application-level RPC failure transmitted cleanly inside binary Protobuf responses. -/
structure RpcDomainError (ε : Type) where
  tag     : ε
  message : String
deriving Inhabited, DecidableEq, Repr

instance {ε : Type} [ToJson ε] : ToJson (RpcDomainError ε) where
  toJson e := toJson (e.tag, e.message)

instance {ε : Type} [FromJson ε] : FromJson (RpcDomainError ε) where
  fromJson j := (FromJson.fromJson (α := ε × String) j).map fun p => RpcDomainError.mk p.1 p.2

instance {ε : Type} [LawfulJson ε] : LawfulJson (RpcDomainError ε) where
  depthBound := LawfulJson.depthBound (ε × String)
  depth_toJson e := LawfulJson.depth_toJson (e.tag, e.message)
  fromJson_toJson e := by
    rcases e with ⟨t, m⟩
    change (FromJson.fromJson (toJson (t, m)) : Except String (ε × String)).map
      (fun p => RpcDomainError.mk p.1 p.2) = .ok (RpcDomainError.mk t m)
    rw [LawfulJson.fromJson_toJson (t, m)]
    rfl

instance {ε : Type} [ToJson ε] : NonNullJson (RpcDomainError ε) := ⟨nofun⟩

instance {ε : Type} [ToProto ε]   : ToProto (RpcDomainError ε)   := .ofEquiv fun e => (e.tag, e.message)
instance {ε : Type} [FromProto ε] : FromProto (RpcDomainError ε) := .ofEquiv fun p : ε × String => RpcDomainError.mk p.1 p.2
instance {ε : Type} [LawfulProto ε] : LawfulProto (RpcDomainError ε) :=
  .ofEquiv (fun e => (e.tag, e.message)) (fun p => RpcDomainError.mk p.1 p.2) (fun ⟨_, _⟩ => rfl)

end Qed
