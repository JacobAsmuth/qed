import Qed.Proto.Basic
import Qed.Proto.Proofs
import Qed.Proto.Lawful

namespace Qed

/-- Typed application-level RPC failure transmitted cleanly inside binary Protobuf responses. -/
structure RpcDomainError (ε : Type) where
  tag     : ε
  message : String
deriving Inhabited, DecidableEq, Repr

qed_equiv_codec% json [ε] (RpcDomainError ε,
  fun e => (e.tag, e.message), fun p : ε × String => ⟨p.1, p.2⟩, fun ⟨_, _⟩ => rfl)
qed_equiv_codec% proto [ε] (RpcDomainError ε,
  fun e => (e.tag, e.message), fun p : ε × String => RpcDomainError.mk p.1 p.2, fun ⟨_, _⟩ => rfl)

end Qed
